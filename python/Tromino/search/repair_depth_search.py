#!/usr/bin/env python3
"""Long-run adversarial repair-depth search for DkMath Tromino experiments.

The generator keeps a planted four-coloring while increasing combinatorial
complexity by legal diagonal flips. The solver is *not* given the planted
colors. It restores vertices in their refinement birth order, protects the
Missing-Color Invariant, and uses two-color Kempe-component swaps as the current
GapSwap proxy when direct lifting stalls.

This is an experimental search harness, not a proof and not production code.
It uses only the Python standard library.
"""

from __future__ import annotations

from collections import deque
from concurrent.futures import ProcessPoolExecutor, as_completed
from dataclasses import dataclass
from pathlib import Path
import argparse
import itertools
import json
import math
import os
import random
import statistics
import time
from typing import Iterable

COLORS = (0, 1, 2, 3)
SEA = -1
BOUNDARY = (0, 1, 2)
LOCKED = frozenset((SEA, 0, 1, 2))
FORMAT_VERSION = 2


def face_key(a: int, b: int, c: int) -> tuple[int, int, int]:
    return tuple(sorted((int(a), int(b), int(c))))


@dataclass
class PlantedTriangulation:
    faces: set[tuple[int, int, int]]
    outer_face: tuple[int, int, int]
    planted: dict[int, int]
    birth_order: list[int]
    flip_history: list[tuple[int, int, int, int]]

    @staticmethod
    def base() -> "PlantedTriangulation":
        planted = {0: 1, 1: 2, 2: 3, 3: 0}
        faces = {
            face_key(0, 1, 2),
            face_key(0, 1, 3),
            face_key(1, 2, 3),
            face_key(2, 0, 3),
        }
        return PlantedTriangulation(
            faces=faces,
            outer_face=face_key(0, 1, 2),
            planted=planted,
            birth_order=[3],
            flip_history=[],
        )

    def copy(self) -> "PlantedTriangulation":
        return PlantedTriangulation(
            faces=set(self.faces),
            outer_face=self.outer_face,
            planted=dict(self.planted),
            birth_order=list(self.birth_order),
            flip_history=list(self.flip_history),
        )

    def internal_faces(self) -> list[tuple[int, int, int]]:
        return [face for face in self.faces if face != self.outer_face]

    def edges(self) -> set[tuple[int, int]]:
        out: set[tuple[int, int]] = set()
        for a, b, c in self.faces:
            out.add(tuple(sorted((a, b))))
            out.add(tuple(sorted((b, c))))
            out.add(tuple(sorted((c, a))))
        return out

    def adjacency(self, *, include_sea: bool = True) -> dict[int, set[int]]:
        vertices: set[int] = set()
        for face in self.faces:
            vertices.update(face)
        adjacency = {v: set() for v in vertices}
        for u, v in self.edges():
            adjacency[u].add(v)
            adjacency[v].add(u)
        if include_sea:
            adjacency[SEA] = set(BOUNDARY)
            for v in BOUNDARY:
                adjacency[v].add(SEA)
        return adjacency

    def subdivide_face(self, face: tuple[int, int, int]) -> int:
        face = face_key(*face)
        if face == self.outer_face or face not in self.faces:
            raise ValueError("only an existing internal face may be subdivided")
        face_colors = {self.planted[v] for v in face}
        if len(face_colors) != 3:
            raise ValueError("planted face is not tricolored")
        missing = next(c for c in COLORS if c not in face_colors)
        new_vertex = max(self.planted) + 1
        a, b, c = face
        self.faces.remove(face)
        self.faces.update(
            {
                face_key(a, b, new_vertex),
                face_key(b, c, new_vertex),
                face_key(c, a, new_vertex),
            }
        )
        self.planted[new_vertex] = missing
        self.birth_order.append(new_vertex)
        return new_vertex

    def flippable_preserving(self) -> list[tuple[int, int, int, int]]:
        edge_faces: dict[tuple[int, int], list[tuple[int, int, int]]] = {}
        for face in self.faces:
            a, b, c = face
            for u, v in ((a, b), (b, c), (c, a)):
                edge_faces.setdefault(tuple(sorted((u, v))), []).append(face)

        current_edges = self.edges()
        boundary_edges = {(0, 1), (1, 2), (0, 2)}
        moves: list[tuple[int, int, int, int]] = []

        for (u, v), incident in edge_faces.items():
            if (u, v) in boundary_edges or len(incident) != 2:
                continue
            a = next(x for x in incident[0] if x not in (u, v))
            b = next(x for x in incident[1] if x not in (u, v))
            if a == b:
                continue
            if tuple(sorted((a, b))) in current_edges:
                continue
            if self.planted[a] == self.planted[b]:
                continue
            moves.append((u, v, a, b))
        return moves

    def apply_flip(self, move: tuple[int, int, int, int]) -> None:
        u, v, a, b = move
        old_a = face_key(u, v, a)
        old_b = face_key(u, v, b)
        if old_a not in self.faces or old_b not in self.faces:
            raise ValueError(f"stale flip: {move}")
        self.faces.remove(old_a)
        self.faces.remove(old_b)
        self.faces.add(face_key(a, b, u))
        self.faces.add(face_key(a, b, v))
        self.flip_history.append(move)

    def planted_is_proper(self) -> bool:
        adjacency = self.adjacency(include_sea=False)
        return all(
            self.planted[u] != self.planted[v]
            for u in adjacency
            for v in adjacency[u]
            if u < v
        )


def generate_planted(vertices: int, seed: int) -> PlantedTriangulation:
    if vertices < 4:
        raise ValueError("vertices must be at least 4")
    rng = random.Random(seed)
    tri = PlantedTriangulation.base()
    while len(tri.planted) < vertices:
        tri.subdivide_face(rng.choice(tri.internal_faces()))
    if not tri.planted_is_proper():
        raise AssertionError("generator lost planted proper coloring")
    return tri


def palette(
    adjacency: dict[int, set[int]], colored: dict[int, int], v: int
) -> set[int]:
    return {colored[u] for u in adjacency[v] if u in colored}


def invariant_holds(
    adjacency: dict[int, set[int]], colored: dict[int, int], remaining: set[int]
) -> bool:
    return all(len(palette(adjacency, colored, v)) <= 3 for v in remaining)


def safe_candidates(
    adjacency: dict[int, set[int]],
    colored: dict[int, int],
    remaining: set[int],
    v: int,
) -> list[int]:
    forbidden = palette(adjacency, colored, v)
    available = [c for c in COLORS if c not in forbidden]
    future = remaining - {v}
    scored: list[tuple[tuple[int, int, int], int]] = []

    for color in available:
        safe = True
        for w in adjacency[v]:
            if w not in future:
                continue
            before = palette(adjacency, colored, w)
            if len(before) >= 3 and color not in before:
                safe = False
                break
        if not safe:
            continue

        critical = 0
        square_sum = 0
        for w in adjacency[v]:
            if w not in future:
                continue
            after = palette(adjacency, colored, w) | {color}
            critical += int(len(after) == 3)
            square_sum += len(after) ** 2
        scored.append(((critical, square_sum, color), color))

    scored.sort()
    return [color for _, color in scored]


def kempe_components(
    adjacency: dict[int, set[int]], colored: dict[int, int]
) -> Iterable[tuple[int, int, frozenset[int]]]:
    nodes = set(colored)
    for a, b in itertools.combinations(COLORS, 2):
        allowed = {v for v in nodes if colored[v] in (a, b)}
        seen: set[int] = set()
        for start in sorted(allowed):
            if start in seen:
                continue
            component = {start}
            stack = [start]
            seen.add(start)
            while stack:
                x = stack.pop()
                for y in adjacency[x]:
                    if y in allowed and y not in seen:
                        seen.add(y)
                        component.add(y)
                        stack.append(y)
            if component & LOCKED:
                continue
            yield (a, b, frozenset(component))


def apply_exchange(
    colored: dict[int, int], move: tuple[int, int, frozenset[int]]
) -> dict[int, int]:
    a, b, component = move
    result = dict(colored)
    for v in component:
        result[v] = b if result[v] == a else a
    return result


def state_key(colored: dict[int, int]) -> tuple[tuple[int, int], ...]:
    return tuple(sorted(colored.items()))


def graph_distances(
    adjacency: dict[int, set[int]], start: int
) -> dict[int, int]:
    distances = {start: 0}
    queue = deque([start])
    while queue:
        v = queue.popleft()
        for w in adjacency[v]:
            if w in distances:
                continue
            distances[w] = distances[v] + 1
            queue.append(w)
    return distances


def repair_geometry(
    adjacency: dict[int, set[int]],
    current: int,
    sequence: list[tuple[int, int, frozenset[int]]],
) -> dict:
    components = [set(component) for _, _, component in sequence]
    footprint: set[int] = set()
    for component in components:
        footprint.update(component)

    distances = graph_distances(adjacency, current)
    footprint_distances = [
        distances[v] for v in footprint if v in distances
    ]
    component_sizes = [len(component) for component in components]

    return {
        "component_sizes": component_sizes,
        "max_component_size": max(component_sizes, default=0),
        "footprint_vertices": sorted(footprint),
        "footprint_size": len(footprint),
        "min_distance_from_current": (
            min(footprint_distances) if footprint_distances else None
        ),
        "max_distance_from_current": (
            max(footprint_distances) if footprint_distances else None
        ),
    }


def find_repair(
    adjacency: dict[int, set[int]],
    colored: dict[int, int],
    remaining: set[int],
    v: int,
    max_depth: int,
    node_limit: int,
    intermediate_policy: str,
):
    visited = {state_key(colored)}
    queue = deque([(dict(colored), [])])
    expanded = 0
    hit_depth_limit = False

    while queue:
        state, sequence = queue.popleft()
        if len(sequence) >= max_depth:
            hit_depth_limit = True
            continue

        for move in kempe_components(adjacency, state):
            next_state = apply_exchange(state, move)
            key = state_key(next_state)
            if key in visited:
                continue
            visited.add(key)
            expanded += 1

            if expanded > node_limit:
                return None, None, None, {
                    "status": "node_limit",
                    "expanded": expanded,
                    "hit_depth_limit": hit_depth_limit,
                }

            invariant_ok = invariant_holds(adjacency, next_state, remaining)
            if intermediate_policy == "strict" and not invariant_ok:
                continue

            candidates = (
                safe_candidates(adjacency, next_state, remaining, v)
                if invariant_ok
                else []
            )
            next_sequence = sequence + [move]
            if candidates:
                return next_state, next_sequence, candidates, {
                    "status": "ok",
                    "expanded": expanded,
                    "hit_depth_limit": hit_depth_limit,
                }
            queue.append((next_state, next_sequence))

    return None, None, None, {
        "status": "depth_limited" if hit_depth_limit else "state_space_exhausted",
        "expanded": expanded,
        "hit_depth_limit": hit_depth_limit,
    }


def restore_instance(
    tri: PlantedTriangulation,
    max_repair_depth: int,
    *,
    node_limit: int = 200_000,
    intermediate_policy: str = "strict",
    trace: bool = False,
):
    adjacency = tri.adjacency(include_sea=True)
    colored = {SEA: 0, 0: 1, 1: 2, 2: 3}
    remaining = set(tri.birth_order)
    repairs = 0
    repair_moves_total = 0
    max_depth_used = 0
    repair_log = []

    for step, v in enumerate(tri.birth_order):
        if not invariant_holds(adjacency, colored, remaining):
            return False, {
                "reason": "pre_invariant_broken",
                "step": step,
                "node": v,
            }

        candidates = safe_candidates(adjacency, colored, remaining, v)
        sequence = []
        repair_meta = None

        if not candidates:
            if max_repair_depth == 0:
                return False, {
                    "reason": "forced_repair",
                    "step": step,
                    "node": v,
                    "repairs": repairs,
                }

            next_state, sequence, candidates, repair_meta = find_repair(
                adjacency,
                colored,
                remaining,
                v,
                max_repair_depth,
                node_limit,
                intermediate_policy,
            )
            if next_state is None:
                return False, {
                    "reason": "repair_failed",
                    "repair_status": repair_meta["status"],
                    "step": step,
                    "node": v,
                    "repairs": repairs,
                    "expanded": repair_meta["expanded"],
                    "hit_depth_limit": repair_meta["hit_depth_limit"],
                }

            colored = next_state
            repairs += 1
            repair_moves_total += len(sequence)
            max_depth_used = max(max_depth_used, len(sequence))

        color = candidates[0]
        colored[v] = color
        remaining.remove(v)

        if trace and sequence:
            repair_log.append(
                {
                    "step": step,
                    "node": v,
                    "repair_depth": len(sequence),
                    "moves": [
                        {"colors": [a, b], "component": sorted(component)}
                        for a, b, component in sequence
                    ],
                    "assigned_color": color,
                    "repair_search": repair_meta,
                    "geometry": repair_geometry(adjacency, v, sequence),
                }
            )

    proper = all(
        colored[u] != colored[v]
        for u in adjacency
        for v in adjacency[u]
        if u < v
    )
    if not proper:
        raise AssertionError("repair solver produced an improper coloring")

    return True, {
        "repairs": repairs,
        "repair_moves_total": repair_moves_total,
        "max_depth_used": max_depth_used,
        "repair_log": repair_log,
    }


def restore_state_before_step(
    tri: PlantedTriangulation,
    stop_step: int,
    *,
    max_repair_depth: int,
    node_limit: int,
    intermediate_policy: str,
) -> dict:
    adjacency = tri.adjacency(include_sea=True)
    colored = {SEA: 0, 0: 1, 1: 2, 2: 3}
    remaining = set(tri.birth_order)
    repair_log = []

    for step, v in enumerate(tri.birth_order):
        if step == stop_step:
            return {
                "adjacency": adjacency,
                "colored": colored,
                "remaining": remaining,
                "step": step,
                "node": v,
                "repair_log": repair_log,
            }

        if not invariant_holds(adjacency, colored, remaining):
            raise RuntimeError(
                f"prefix invariant broken at step={step} node={v}"
            )

        candidates = safe_candidates(adjacency, colored, remaining, v)
        sequence = []
        repair_meta = None
        if not candidates:
            next_state, sequence, candidates, repair_meta = find_repair(
                adjacency,
                colored,
                remaining,
                v,
                max_repair_depth,
                node_limit,
                intermediate_policy,
            )
            if next_state is None:
                raise RuntimeError(
                    "prefix repair failed at "
                    f"step={step} node={v} status={repair_meta['status']}"
                )
            colored = next_state

        color = candidates[0]
        colored[v] = color
        remaining.remove(v)
        if sequence:
            repair_log.append(
                {
                    "step": step,
                    "node": v,
                    "repair_depth": len(sequence),
                    "assigned_color": color,
                    "moves": [
                        {
                            "colors": [a, b],
                            "component": sorted(component),
                        }
                        for a, b, component in sequence
                    ],
                }
            )

    raise ValueError(f"stop step out of range: {stop_step}")


def repair_maze_profile(
    tri: PlantedTriangulation,
    *,
    step: int,
    prefix_depth: int,
    max_depth: int,
    node_limit: int,
    intermediate_policy: str,
) -> dict:
    prefix = restore_state_before_step(
        tri,
        step,
        max_repair_depth=prefix_depth,
        node_limit=node_limit,
        intermediate_policy=intermediate_policy,
    )
    adjacency = prefix["adjacency"]
    colored = prefix["colored"]
    remaining = prefix["remaining"]
    current = prefix["node"]

    root_key = state_key(colored)
    queue = deque([(dict(colored), root_key, 0)])
    visited = {root_key}
    parent: dict = {}
    processed: dict[int, int] = {}
    generated: dict[int, int] = {0: 1}
    exits: dict[int, int] = {}
    invariant_states: dict[int, int] = {
        0: int(invariant_holds(adjacency, colored, remaining))
    }
    moves_examined: dict[int, int] = {}
    duplicates: dict[int, int] = {}
    expanded = 0
    truncated = False
    first_exit_key = None
    first_exit_depth = None
    first_exit_candidates = None

    while queue:
        state, key, depth = queue.popleft()
        processed[depth] = processed.get(depth, 0) + 1
        if depth >= max_depth:
            continue

        moves = list(kempe_components(adjacency, state))
        moves_examined[depth] = moves_examined.get(depth, 0) + len(moves)

        for move in moves:
            next_state = apply_exchange(state, move)
            next_key = state_key(next_state)
            next_depth = depth + 1
            if next_key in visited:
                duplicates[next_depth] = duplicates.get(next_depth, 0) + 1
                continue

            visited.add(next_key)
            parent[next_key] = (key, move)
            expanded += 1
            generated[next_depth] = generated.get(next_depth, 0) + 1

            if expanded > node_limit:
                truncated = True
                queue.clear()
                break

            invariant_ok = invariant_holds(
                adjacency, next_state, remaining
            )
            if invariant_ok:
                invariant_states[next_depth] = (
                    invariant_states.get(next_depth, 0) + 1
                )
                candidates = safe_candidates(
                    adjacency, next_state, remaining, current
                )
            else:
                candidates = []

            if candidates:
                exits[next_depth] = exits.get(next_depth, 0) + 1
                if first_exit_key is None:
                    first_exit_key = next_key
                    first_exit_depth = next_depth
                    first_exit_candidates = candidates
                continue

            if intermediate_policy == "strict" and not invariant_ok:
                continue
            queue.append((next_state, next_key, next_depth))

        if truncated:
            break

    first_path = []
    if first_exit_key is not None:
        key = first_exit_key
        while key != root_key:
            prev, move = parent[key]
            first_path.append(
                {
                    "colors": [move[0], move[1]],
                    "component": sorted(move[2]),
                }
            )
            key = prev
        first_path.reverse()

    all_depths = range(0, max_depth + 1)
    layers = [
        {
            "depth": depth,
            "processed_states": processed.get(depth, 0),
            "generated_states": generated.get(depth, 0),
            "invariant_states": invariant_states.get(depth, 0),
            "exit_states": exits.get(depth, 0),
            "duplicate_transitions": duplicates.get(depth, 0),
            "moves_examined_from_layer": moves_examined.get(depth, 0),
        }
        for depth in all_depths
    ]

    root_components = [
        {
            "colors": [a, b],
            "component": sorted(component),
            "size": len(component),
        }
        for a, b, component in kempe_components(adjacency, colored)
    ]

    distances = graph_distances(adjacency, current)
    return {
        "step": step,
        "node": current,
        "prefix_depth": prefix_depth,
        "max_depth": max_depth,
        "node_limit": node_limit,
        "intermediate_policy": intermediate_policy,
        "truncated": truncated,
        "expanded_unique_states": expanded,
        "visited_states": len(visited),
        "initial_safe_candidates": safe_candidates(
            adjacency, colored, remaining, current
        ),
        "initial_palette": sorted(palette(adjacency, colored, current)),
        "initial_kempe_components": root_components,
        "initial_kempe_component_count": len(root_components),
        "blocker_neighbors": sorted(adjacency[current]),
        "blocker_neighbor_distances": {
            str(v): distances[v] for v in sorted(adjacency[current])
        },
        "colored_state": {
            str(v): color for v, color in sorted(colored.items())
        },
        "remaining": sorted(remaining),
        "prefix_repairs": prefix["repair_log"],
        "layers": layers,
        "first_exit_depth": first_exit_depth,
        "first_exit_candidates": first_exit_candidates,
        "first_exit_path": first_path,
        "first_exit_geometry": (
            repair_geometry(
                adjacency,
                current,
                [
                    (
                        item["colors"][0],
                        item["colors"][1],
                        frozenset(item["component"]),
                    )
                    for item in first_path
                ],
            )
            if first_path
            else None
        ),
    }


def repair_exit_records(
    tri: PlantedTriangulation,
    *,
    step: int,
    prefix_depth: int,
    exit_depth: int,
    node_limit: int,
    intermediate_policy: str,
) -> dict:
    prefix = restore_state_before_step(
        tri,
        step,
        max_repair_depth=prefix_depth,
        node_limit=node_limit,
        intermediate_policy=intermediate_policy,
    )
    adjacency = prefix["adjacency"]
    colored = prefix["colored"]
    remaining = prefix["remaining"]
    current = prefix["node"]

    root_key = state_key(colored)
    queue = deque([(dict(colored), root_key, 0)])
    visited = {root_key}
    parent: dict = {}
    exits: list[dict] = []
    expanded = 0
    truncated = False

    while queue:
        state, key, depth = queue.popleft()
        if depth >= exit_depth:
            continue

        for move in kempe_components(adjacency, state):
            next_state = apply_exchange(state, move)
            next_key = state_key(next_state)
            next_depth = depth + 1
            if next_key in visited:
                continue

            visited.add(next_key)
            parent[next_key] = (key, move)
            expanded += 1
            if expanded > node_limit:
                truncated = True
                queue.clear()
                break

            invariant_ok = invariant_holds(
                adjacency, next_state, remaining
            )
            candidates = (
                safe_candidates(
                    adjacency, next_state, remaining, current
                )
                if invariant_ok
                else []
            )

            if candidates:
                if next_depth == exit_depth:
                    exits.append(
                        {
                            "state_key": [
                                [int(v), int(color)]
                                for v, color in next_key
                            ],
                            "candidates": list(candidates),
                        }
                    )
                continue

            if intermediate_policy == "strict" and not invariant_ok:
                continue
            if next_depth < exit_depth:
                queue.append((next_state, next_key, next_depth))

        if truncated:
            break

    def path_to(key):
        path = []
        while key != root_key:
            prev, move = parent[key]
            path.append(
                {
                    "colors": [move[0], move[1]],
                    "component": sorted(move[2]),
                }
            )
            key = prev
        path.reverse()
        return path

    for record in exits:
        key = tuple(
            (int(v), int(color)) for v, color in record["state_key"]
        )
        path = path_to(key)
        record["path"] = path
        record["geometry"] = repair_geometry(
            adjacency,
            current,
            [
                (
                    item["colors"][0],
                    item["colors"][1],
                    frozenset(item["component"]),
                )
                for item in path
            ],
        )

    return {
        "step": step,
        "node": current,
        "exit_depth": exit_depth,
        "prefix_depth": prefix_depth,
        "intermediate_policy": intermediate_policy,
        "truncated": truncated,
        "expanded_unique_states": expanded,
        "visited_states": len(visited),
        "exit_count": len(exits),
        "exits": exits,
        "colored_state": {
            str(v): color for v, color in sorted(colored.items())
        },
        "remaining": sorted(remaining),
        "prefix_repairs": prefix["repair_log"],
    }


def replay_parent_exit_path_on_child(
    child_tri: PlantedTriangulation,
    path: list[dict],
    *,
    step: int,
    prefix_depth: int,
    node_limit: int,
    intermediate_policy: str,
) -> dict:
    prefix = restore_state_before_step(
        child_tri,
        step,
        max_repair_depth=prefix_depth,
        node_limit=node_limit,
        intermediate_policy=intermediate_policy,
    )
    adjacency = prefix["adjacency"]
    state = dict(prefix["colored"])
    remaining = set(prefix["remaining"])
    current = prefix["node"]
    steps = []
    first_divergence = None

    for index, item in enumerate(path):
        colors = tuple(int(x) for x in item["colors"])
        component = frozenset(int(v) for v in item["component"])
        available = list(kempe_components(adjacency, state))
        exact = next(
            (
                move
                for move in available
                if (move[0], move[1]) == colors
                and move[2] == component
            ),
            None,
        )

        same_pair = [
            move
            for move in available
            if (move[0], move[1]) == colors
        ]
        overlaps = [
            {
                "component": sorted(move[2]),
                "size": len(move[2]),
                "intersection": sorted(move[2] & component),
                "intersection_size": len(move[2] & component),
                "contains_parent_component": component <= move[2],
                "contained_in_parent_component": move[2] <= component,
            }
            for move in same_pair
            if move[2] & component
        ]
        overlaps.sort(
            key=lambda row: (
                -row["intersection_size"],
                row["component"],
            )
        )

        row = {
            "index": index,
            "parent_move": {
                "colors": list(colors),
                "component": sorted(component),
            },
            "exact_move_available": exact is not None,
            "same_pair_components": [
                sorted(move[2]) for move in same_pair
            ],
            "overlapping_same_pair_components": overlaps,
        }
        steps.append(row)

        if exact is None:
            first_divergence = row
            break
        state = apply_exchange(state, exact)

    invariant_ok = invariant_holds(adjacency, state, remaining)
    candidates = (
        safe_candidates(adjacency, state, remaining, current)
        if invariant_ok
        else []
    )
    return {
        "step": step,
        "node": current,
        "exact_prefix_length": sum(
            int(row["exact_move_available"]) for row in steps
        ),
        "path_length": len(path),
        "first_divergence": first_divergence,
        "steps": steps,
        "state_after_exact_prefix": {
            str(v): color for v, color in sorted(state.items())
        },
        "invariant_after_exact_prefix": invariant_ok,
        "safe_candidates_after_exact_prefix": candidates,
    }


def explicit_state_proper_violations(
    adjacency: dict[int, set[int]],
    colored: dict[int, int],
) -> list[dict]:
    violations = []
    for u in sorted(colored):
        for v in sorted(adjacency[u]):
            if v not in colored or u >= v:
                continue
            if colored[u] == colored[v]:
                violations.append(
                    {
                        "edge": [u, v],
                        "color": colored[u],
                    }
                )
    return violations


def repair_maze_from_explicit_state(
    tri: PlantedTriangulation,
    *,
    colored: dict[int, int],
    remaining: set[int],
    current: int,
    max_depth: int,
    node_limit: int,
    intermediate_policy: str,
) -> dict:
    adjacency = tri.adjacency(include_sea=True)
    violations = explicit_state_proper_violations(adjacency, colored)
    invariant_ok = invariant_holds(adjacency, colored, remaining)
    initial_candidates = safe_candidates(
        adjacency, colored, remaining, current
    ) if invariant_ok else []

    base = {
        "node": current,
        "max_depth": max_depth,
        "node_limit": node_limit,
        "intermediate_policy": intermediate_policy,
        "proper_state": not violations,
        "proper_violations": violations,
        "initial_invariant": invariant_ok,
        "initial_safe_candidates": initial_candidates,
        "colored_state": {
            str(v): color for v, color in sorted(colored.items())
        },
        "remaining": sorted(remaining),
        "blocker_neighbors": sorted(adjacency[current]),
    }
    if violations:
        return {
            **base,
            "valid_intervention": False,
            "invalid_reason": "improper_colored_state",
            "first_exit_depth": None,
            "exit_counts": {},
            "expanded_unique_states": 0,
            "visited_states": 0,
            "layers": [],
        }
    if not invariant_ok:
        return {
            **base,
            "valid_intervention": False,
            "invalid_reason": "initial_invariant_broken",
            "first_exit_depth": None,
            "exit_counts": {},
            "expanded_unique_states": 0,
            "visited_states": 0,
            "layers": [],
        }

    root_key = state_key(colored)
    queue = deque([(dict(colored), 0)])
    visited = {root_key}
    generated: dict[int, int] = {0: 1}
    processed: dict[int, int] = {}
    exits: dict[int, int] = {}
    invariant_states: dict[int, int] = {0: 1}
    moves_examined: dict[int, int] = {}
    duplicates: dict[int, int] = {}
    expanded = 0
    truncated = False
    first_exit_depth = None

    while queue:
        state, depth = queue.popleft()
        processed[depth] = processed.get(depth, 0) + 1
        if depth >= max_depth:
            continue

        moves = list(kempe_components(adjacency, state))
        moves_examined[depth] = moves_examined.get(depth, 0) + len(moves)

        for move in moves:
            next_state = apply_exchange(state, move)
            key = state_key(next_state)
            next_depth = depth + 1
            if key in visited:
                duplicates[next_depth] = duplicates.get(next_depth, 0) + 1
                continue

            visited.add(key)
            expanded += 1
            generated[next_depth] = generated.get(next_depth, 0) + 1

            if expanded > node_limit:
                truncated = True
                queue.clear()
                break

            next_invariant = invariant_holds(
                adjacency, next_state, remaining
            )
            if next_invariant:
                invariant_states[next_depth] = (
                    invariant_states.get(next_depth, 0) + 1
                )
                candidates = safe_candidates(
                    adjacency, next_state, remaining, current
                )
            else:
                candidates = []

            if candidates:
                exits[next_depth] = exits.get(next_depth, 0) + 1
                if first_exit_depth is None:
                    first_exit_depth = next_depth
                continue

            if intermediate_policy == "strict" and not next_invariant:
                continue
            queue.append((next_state, next_depth))

        if truncated:
            break

    layers = [
        {
            "depth": depth,
            "processed_states": processed.get(depth, 0),
            "generated_states": generated.get(depth, 0),
            "invariant_states": invariant_states.get(depth, 0),
            "exit_states": exits.get(depth, 0),
            "duplicate_transitions": duplicates.get(depth, 0),
            "moves_examined_from_layer": moves_examined.get(depth, 0),
        }
        for depth in range(0, max_depth + 1)
    ]
    root_components = [
        {
            "colors": [a, b],
            "component": sorted(component),
            "size": len(component),
        }
        for a, b, component in kempe_components(adjacency, colored)
    ]

    return {
        **base,
        "valid_intervention": True,
        "invalid_reason": None,
        "truncated": truncated,
        "first_exit_depth": first_exit_depth,
        "exit_counts": {
            str(depth): count for depth, count in sorted(exits.items())
        },
        "expanded_unique_states": expanded,
        "visited_states": len(visited),
        "initial_kempe_component_count": len(root_components),
        "initial_kempe_components": root_components,
        "layers": layers,
    }


def evaluate(
    tri: PlantedTriangulation,
    max_depth: int,
    *,
    node_limit: int,
    intermediate_policy: str,
    trace: bool = False,
):
    ok, info = restore_instance(
        tri,
        max_depth,
        node_limit=node_limit,
        intermediate_policy=intermediate_policy,
        trace=trace,
    )
    if not ok:
        return {
            "success": False,
            "classification": info.get("repair_status", info["reason"]),
            "search_ceiling": max_depth,
            **info,
        }

    depth = info["max_depth_used"]
    verified_lower = depth == 0
    lower_result = None
    if depth > 0:
        lower_ok, lower_info = restore_instance(
            tri,
            depth - 1,
            node_limit=node_limit,
            intermediate_policy=intermediate_policy,
            trace=False,
        )
        verified_lower = not lower_ok
        lower_result = {
            "success": lower_ok,
            "classification": (
                "solved"
                if lower_ok
                else lower_info.get("repair_status", lower_info["reason"])
            ),
            "info": lower_info,
        }

    return {
        "success": True,
        "classification": "solved",
        "required_depth": depth,
        "verified_against_depth_minus_one": verified_lower,
        "depth_minus_one_result": lower_result,
        **info,
    }


def objective(result: dict) -> tuple[int, int, int, int]:
    if result["success"]:
        return (
            result["required_depth"],
            result.get("repairs", 0),
            result.get("repair_moves_total", 0),
            0,
        )
    rank = {
        "depth_limited": 3,
        "node_limit": 2,
        "state_space_exhausted": 4,
        "forced_repair": 1,
        "pre_invariant_broken": 0,
    }.get(result["classification"], 1)
    return (result["search_ceiling"] + 1, rank, result.get("repairs", 0), 1)



def resolved_objective(result: dict) -> tuple[int, int, int, int]:
    if not result["success"]:
        return (-1, 0, 0, 0)
    return (
        int(result["required_depth"]),
        int(result.get("repairs", 0)),
        int(result.get("repair_moves_total", 0)),
        1,
    )


def unresolved_objective(result: dict) -> tuple[int, int, int, int]:
    if result["success"]:
        return (-1, 0, 0, 0)
    rank = {
        "state_space_exhausted": 4,
        "depth_limited": 3,
        "node_limit": 2,
        "forced_repair": 1,
        "pre_invariant_broken": 0,
    }.get(result["classification"], 1)
    return (
        rank,
        int(result.get("repairs", 0)),
        int(result.get("expanded", 0)),
        1,
    )


def frontier_expanded(result: dict) -> int:
    if not result.get("success"):
        return int(result.get("expanded", 0))
    lower = result.get("depth_minus_one_result")
    if not lower or lower.get("success"):
        return 0
    info = lower.get("info") or {}
    if lower.get("classification") != "depth_limited":
        return 0
    if not info.get("hit_depth_limit"):
        return 0
    return int(info.get("expanded", 0))


def frontier_objective(result: dict) -> tuple[int, int, int, int]:
    if not result.get("success"):
        return (
            0,
            unresolved_objective(result)[0],
            int(result.get("expanded", 0)),
            0,
        )
    return (
        1,
        int(result["required_depth"]),
        frontier_expanded(result),
        -int(result.get("repair_moves_total", 0)),
    )


def search_objective(result: dict, mode: str) -> tuple[int, int, int, int]:
    if mode == "frontier":
        return frontier_objective(result)
    if mode == "resolved":
        if result["success"]:
            return (
                1,
                int(result["required_depth"]),
                int(result.get("repairs", 0)),
                int(result.get("repair_moves_total", 0)),
            )
        # Keep unresolved states traversable, but never let them outrank a
        # resolved witness in resolved-depth mode.
        return (
            0,
            unresolved_objective(result)[0],
            int(result.get("repairs", 0)),
            int(result.get("expanded", 0)),
        )
    return objective(result)


def search_energy(result: dict, mode: str) -> float:
    if mode == "frontier":
        if result.get("success"):
            return (
                5.0
                + float(result["required_depth"])
                + 0.1 * math.log1p(float(frontier_expanded(result)))
                - 0.001 * float(result.get("repair_moves_total", 0))
            )
        return float(unresolved_objective(result)[0])
    if mode == "resolved":
        if result["success"]:
            return (
                5.0
                + float(result["required_depth"])
                + 0.01 * float(result.get("repairs", 0))
                + 0.001 * float(result.get("repair_moves_total", 0))
            )
        # Unresolved states remain reachable under annealing, but a resolved
        # state is always preferred lexicographically.
        return float(unresolved_objective(result)[0])
    score = objective(result)
    return (
        10.0 * float(score[0])
        + float(score[1])
        + 0.01 * float(score[2])
        + 0.001 * float(score[3])
    )


def serialize_witness(
    tri: PlantedTriangulation,
    result: dict,
    *,
    job_seed: int,
    search_meta: dict,
) -> dict:
    return {
        "format_version": FORMAT_VERSION,
        "job_seed": job_seed,
        "vertices": len(tri.planted),
        "outer_face": list(tri.outer_face),
        "faces": [list(face) for face in sorted(tri.faces)],
        "planted_colors": {str(k): v for k, v in sorted(tri.planted.items())},
        "birth_order": list(tri.birth_order),
        "flip_history": [list(move) for move in tri.flip_history],
        "evaluation": result,
        "search_meta": search_meta,
    }


def triangulation_from_witness(payload: dict) -> PlantedTriangulation:
    return PlantedTriangulation(
        faces={face_key(*face) for face in payload["faces"]},
        outer_face=face_key(*payload.get("outer_face", BOUNDARY)),
        planted={int(k): int(v) for k, v in payload["planted_colors"].items()},
        birth_order=[int(v) for v in payload["birth_order"]],
        flip_history=[
            tuple(map(int, move)) for move in payload.get("flip_history", [])
        ],
    )


def one_search_job(job: dict) -> dict:
    seed = int(job["job_seed"])
    rng = random.Random(seed)

    initial_witness = job.get("initial_witness")
    initial_witness_seed = None
    if initial_witness:
        payload = json.loads(Path(str(initial_witness)).read_text(encoding="utf-8"))
        tri = triangulation_from_witness(payload)
        initial_witness_seed = payload.get("job_seed")
        if len(tri.planted) != int(job["vertices"]):
            raise ValueError(
                "initial witness vertex count does not match --vertices"
            )
    else:
        tri = generate_planted(int(job["vertices"]), seed)

    initial_flip_history_length = len(tri.flip_history)

    for _ in range(int(job["warmup_flips"])):
        moves = tri.flippable_preserving()
        if not moves:
            break
        tri.apply_flip(rng.choice(moves))

    eval_kwargs = {
        "max_depth": int(job["max_depth"]),
        "node_limit": int(job["node_limit"]),
        "intermediate_policy": str(job["intermediate_policy"]),
    }
    current = evaluate(tri, trace=False, **eval_kwargs)
    objective_mode = str(job.get("search_objective", "mixed"))
    best_tri = tri.copy()
    best = current
    accepted = 0
    temperature = float(job["temperature"])
    steps_done = 0

    for step in range(int(job["steps"])):
        steps_done = step + 1
        moves = tri.flippable_preserving()
        if not moves:
            break

        candidate_tri = tri.copy()
        candidate_tri.apply_flip(rng.choice(moves))
        candidate = evaluate(candidate_tri, trace=False, **eval_kwargs)

        old_score = search_objective(current, objective_mode)
        new_score = search_objective(candidate, objective_mode)
        accept = new_score >= old_score
        if not accept:
            delta = (
                search_energy(candidate, objective_mode)
                - search_energy(current, objective_mode)
            )
            accept = rng.random() < math.exp(delta / max(temperature, 0.05))

        if accept:
            tri = candidate_tri
            current = candidate
            accepted += 1

        if search_objective(current, objective_mode) > search_objective(
            best, objective_mode
        ):
            best_tri = tri.copy()
            best = current

        temperature *= float(job["cooling"])

        if best["success"] and best["required_depth"] >= int(job["target_depth"]):
            break

    traced = evaluate(best_tri, trace=True, **eval_kwargs)
    search_meta = {
        "steps_requested": int(job["steps"]),
        "steps_done": steps_done,
        "accepted_mutations": accepted,
        "warmup_flips": int(job["warmup_flips"]),
        "max_depth": int(job["max_depth"]),
        "node_limit": int(job["node_limit"]),
        "intermediate_policy": str(job["intermediate_policy"]),
        "temperature": float(job["temperature"]),
        "cooling": float(job["cooling"]),
        "search_objective": objective_mode,
        "initial_witness": str(initial_witness) if initial_witness else None,
        "initial_witness_seed": initial_witness_seed,
        "initial_flip_history_length": initial_flip_history_length,
        "mutation_suffix_length": (
            len(best_tri.flip_history) - initial_flip_history_length
        ),
    }
    return {
        "job_seed": seed,
        "objective": list(objective(traced)),
        "search_objective": objective_mode,
        "search_score": list(search_objective(traced, objective_mode)),
        "resolved_objective": list(resolved_objective(traced)),
        "unresolved_objective": list(unresolved_objective(traced)),
        "frontier_expanded": frontier_expanded(traced),
        "frontier_objective": list(frontier_objective(traced)),
        "classification": traced["classification"],
        "success": traced["success"],
        "required_depth": traced.get("required_depth"),
        "witness": serialize_witness(
            best_tri, traced, job_seed=seed, search_meta=search_meta
        ),
    }


def one_neighbor_job(job: dict) -> dict:
    payload = json.loads(Path(str(job["witness"])).read_text(encoding="utf-8"))
    tri = triangulation_from_witness(payload)
    move = tuple(int(x) for x in job["move"])
    tri.apply_flip(move)
    result = evaluate(
        tri,
        int(job["max_depth"]),
        node_limit=int(job["node_limit"]),
        intermediate_policy=str(job["intermediate_policy"]),
        trace=False,
    )
    return {
        "index": int(job["index"]),
        "move": list(move),
        "classification": result["classification"],
        "success": result["success"],
        "required_depth": result.get("required_depth"),
        "frontier_expanded": frontier_expanded(result),
        "frontier_objective": list(frontier_objective(result)),
        "result": result,
    }


def atomic_json(path: Path, payload: dict) -> None:
    tmp = path.with_suffix(path.suffix + ".tmp")
    tmp.write_text(
        json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8"
    )
    tmp.replace(path)


def append_jsonl(path: Path, payload: dict) -> None:
    with path.open("a", encoding="utf-8") as handle:
        handle.write(json.dumps(payload, sort_keys=True) + "\n")
        handle.flush()
        os.fsync(handle.fileno())


def completed_seeds(path: Path) -> set[int]:
    if not path.exists():
        return set()
    done = set()
    with path.open("r", encoding="utf-8") as handle:
        for line in handle:
            line = line.strip()
            if not line:
                continue
            try:
                done.add(int(json.loads(line)["job_seed"]))
            except (json.JSONDecodeError, KeyError, ValueError):
                continue
    return done


def read_rows(path: Path) -> list[dict]:
    if not path.exists():
        return []
    rows = []
    for line in path.read_text(encoding="utf-8").splitlines():
        if not line.strip():
            continue
        try:
            rows.append(json.loads(line))
        except json.JSONDecodeError:
            pass
    return rows


def summary_from_rows(rows: list[dict]) -> dict:
    resolved = [row for row in rows if row.get("success")]
    depths = [
        int(row["required_depth"])
        for row in resolved
        if row.get("required_depth") is not None
    ]
    counts: dict[str, int] = {}
    for row in rows:
        key = row.get("classification", "unknown")
        counts[key] = counts.get(key, 0) + 1
    return {
        "jobs_completed": len(rows),
        "classifications": counts,
        "resolved_jobs": len(resolved),
        "max_resolved_depth": max(depths) if depths else None,
        "mean_resolved_depth": statistics.mean(depths) if depths else None,
    }


def cmd_search(args: argparse.Namespace) -> int:
    out = Path(args.output)
    out.mkdir(parents=True, exist_ok=True)
    runs_path = out / "runs.jsonl"
    best_path = out / "best_witness.json"
    best_resolved_path = out / "best_resolved_witness.json"
    best_unresolved_path = out / "best_unresolved_witness.json"
    best_frontier_path = out / "best_frontier_witness.json"
    summary_path = out / "summary.json"
    config_path = out / "config.json"

    initial_payload = None
    initial_witness_seed = None
    if args.initial_witness:
        initial_source = Path(args.initial_witness)
        initial_payload = json.loads(
            initial_source.read_text(encoding="utf-8")
        )
        initial_tri = triangulation_from_witness(initial_payload)
        if not initial_tri.planted_is_proper():
            raise SystemExit("initial witness planted coloring is not proper")
        if len(initial_tri.planted) != args.vertices:
            raise SystemExit(
                "initial witness vertex count does not match --vertices"
            )
        initial_witness_seed = initial_payload.get("job_seed")
        frozen_initial = out / "initial_witness.json"
        if not frozen_initial.exists():
            atomic_json(frozen_initial, initial_payload)

    config = {
        "format_version": FORMAT_VERSION,
        "vertices": args.vertices,
        "jobs": args.jobs,
        "steps": args.steps,
        "warmup_flips": args.warmup_flips,
        "workers": args.workers,
        "max_depth": args.max_depth,
        "target_depth": args.target_depth,
        "node_limit": args.node_limit,
        "base_seed": args.base_seed,
        "intermediate_policy": args.intermediate_policy,
        "temperature": args.temperature,
        "cooling": args.cooling,
        "search_objective": args.search_objective,
        "stop_on_target": args.stop_on_target,
        "initial_witness": args.initial_witness,
        "initial_witness_seed": initial_witness_seed,
    }
    if not config_path.exists():
        atomic_json(config_path, config)

    done = completed_seeds(runs_path)
    seeds = [
        args.base_seed + i
        for i in range(args.jobs)
        if args.base_seed + i not in done
    ]
    rows = read_rows(runs_path)
    best_row = max(
        rows,
        key=lambda row: tuple(
            row.get("search_score", row.get("objective", [0, 0, 0, 0]))
        ),
        default=None,
    )
    best_resolved_row = max(
        (row for row in rows if row.get("success")),
        key=lambda row: tuple(
            row.get(
                "resolved_objective",
                [
                    row.get("required_depth", -1),
                    0,
                    0,
                    1,
                ],
            )
        ),
        default=None,
    )
    best_unresolved_row = max(
        (row for row in rows if not row.get("success")),
        key=lambda row: tuple(
            row.get("unresolved_objective", [0, 0, 0, 0])
        ),
        default=None,
    )
    best_frontier_row = max(
        (row for row in rows if row.get("success")),
        key=lambda row: tuple(
            row.get(
                "frontier_objective",
                frontier_objective(row["witness"]["evaluation"]),
            )
        ),
        default=None,
    )

    print(f"output={out}")
    print(
        f"already_completed={len(done)} pending={len(seeds)} "
        f"workers={args.workers}"
    )

    def job_for(seed: int) -> dict:
        return {
            "job_seed": seed,
            "vertices": args.vertices,
            "steps": args.steps,
            "warmup_flips": args.warmup_flips,
            "max_depth": args.max_depth,
            "target_depth": args.target_depth,
            "node_limit": args.node_limit,
            "intermediate_policy": args.intermediate_policy,
            "temperature": args.temperature,
            "cooling": args.cooling,
            "search_objective": args.search_objective,
            "initial_witness": args.initial_witness,
        }

    existing_target = any(
        row.get("success")
        and (row.get("required_depth") or 0) >= args.target_depth
        for row in rows
    )
    if args.stop_on_target and existing_target:
        summary = summary_from_rows(rows)
        summary.update(
            {
                "elapsed_seconds": 0.0,
                "target_depth": args.target_depth,
                "target_found": True,
                "stopped_on_target": True,
                "best_objective": (
                    best_row["objective"] if best_row else None
                ),
                "best_seed": best_row["job_seed"] if best_row else None,
                "best_resolved_seed": (
                    best_resolved_row["job_seed"]
                    if best_resolved_row
                    else None
                ),
                "best_resolved_depth": (
                    best_resolved_row.get("required_depth")
                    if best_resolved_row
                    else None
                ),
                "best_unresolved_seed": (
                    best_unresolved_row["job_seed"]
                    if best_unresolved_row
                    else None
                ),
                "best_unresolved_classification": (
                    best_unresolved_row.get("classification")
                    if best_unresolved_row
                    else None
                ),
                "best_frontier_seed": (
                    best_frontier_row["job_seed"]
                    if best_frontier_row
                    else None
                ),
                "best_frontier_depth": (
                    best_frontier_row.get("required_depth")
                    if best_frontier_row
                    else None
                ),
                "best_frontier_expanded": (
                    best_frontier_row.get(
                        "frontier_expanded",
                        frontier_expanded(
                            best_frontier_row["witness"]["evaluation"]
                        ),
                    )
                    if best_frontier_row
                    else None
                ),
            }
        )
        atomic_json(summary_path, summary)
        print("target already present; --stop-on-target requested")
        print(json.dumps(summary, indent=2, sort_keys=True))
        return 0

    started = time.time()
    target_found = False
    stopped_on_target = False

    with ProcessPoolExecutor(max_workers=args.workers) as pool:
        futures = {
            pool.submit(one_search_job, job_for(seed)): seed for seed in seeds
        }
        for index, future in enumerate(as_completed(futures), start=1):
            row = future.result()
            append_jsonl(runs_path, row)
            rows.append(row)

            row_search_score = tuple(
                row.get("search_score", row["objective"])
            )
            best_search_score = (
                tuple(
                    best_row.get("search_score", best_row["objective"])
                )
                if best_row
                else None
            )
            if best_row is None or row_search_score > best_search_score:
                best_row = row
                atomic_json(best_path, row["witness"])
                print(
                    "NEW BEST",
                    f"seed={row['job_seed']}",
                    f"class={row['classification']}",
                    f"depth={row.get('required_depth')}",
                    f"search_score={list(row_search_score)}",
                    flush=True,
                )

            if row.get("success"):
                row_resolved = tuple(
                    row.get("resolved_objective", [-1, 0, 0, 0])
                )
                best_resolved = (
                    tuple(
                        best_resolved_row.get(
                            "resolved_objective", [-1, 0, 0, 0]
                        )
                    )
                    if best_resolved_row
                    else None
                )
                if (
                    best_resolved_row is None
                    or row_resolved > best_resolved
                ):
                    best_resolved_row = row
                    atomic_json(best_resolved_path, row["witness"])
                    print(
                        "NEW BEST RESOLVED",
                        f"seed={row['job_seed']}",
                        f"depth={row.get('required_depth')}",
                        flush=True,
                    )

                row_frontier = tuple(
                    row.get(
                        "frontier_objective",
                        frontier_objective(row["witness"]["evaluation"]),
                    )
                )
                best_frontier = (
                    tuple(
                        best_frontier_row.get(
                            "frontier_objective",
                            frontier_objective(
                                best_frontier_row["witness"]["evaluation"]
                            ),
                        )
                    )
                    if best_frontier_row
                    else None
                )
                if (
                    best_frontier_row is None
                    or row_frontier > best_frontier
                ):
                    best_frontier_row = row
                    atomic_json(best_frontier_path, row["witness"])
                    print(
                        "NEW BEST FRONTIER",
                        f"seed={row['job_seed']}",
                        f"depth={row.get('required_depth')}",
                        f"expanded={row.get('frontier_expanded')}",
                        flush=True,
                    )
            else:
                row_unresolved = tuple(
                    row.get("unresolved_objective", [0, 0, 0, 0])
                )
                best_unresolved = (
                    tuple(
                        best_unresolved_row.get(
                            "unresolved_objective", [0, 0, 0, 0]
                        )
                    )
                    if best_unresolved_row
                    else None
                )
                if (
                    best_unresolved_row is None
                    or row_unresolved > best_unresolved
                ):
                    best_unresolved_row = row
                    atomic_json(best_unresolved_path, row["witness"])

            if (
                row["success"]
                and (row.get("required_depth") or 0) >= args.target_depth
            ):
                target_found = True
                if args.stop_on_target:
                    stopped_on_target = True
                    for pending in futures:
                        if pending is not future:
                            pending.cancel()

            if index % max(1, args.summary_every) == 0 or target_found:
                summary = summary_from_rows(rows)
                summary.update(
                    {
                        "elapsed_seconds": time.time() - started,
                        "target_depth": args.target_depth,
                        "target_found": target_found,
                        "stopped_on_target": stopped_on_target,
                        "best_objective": (
                            best_row["objective"] if best_row else None
                        ),
                        "best_seed": best_row["job_seed"] if best_row else None,
                        "best_resolved_seed": (
                            best_resolved_row["job_seed"]
                            if best_resolved_row
                            else None
                        ),
                        "best_resolved_depth": (
                            best_resolved_row.get("required_depth")
                            if best_resolved_row
                            else None
                        ),
                        "best_unresolved_seed": (
                            best_unresolved_row["job_seed"]
                            if best_unresolved_row
                            else None
                        ),
                        "best_unresolved_classification": (
                            best_unresolved_row.get("classification")
                            if best_unresolved_row
                            else None
                        ),
                        "best_frontier_seed": (
                            best_frontier_row["job_seed"]
                            if best_frontier_row
                            else None
                        ),
                        "best_frontier_depth": (
                            best_frontier_row.get("required_depth")
                            if best_frontier_row
                            else None
                        ),
                        "best_frontier_expanded": (
                            best_frontier_row.get(
                                "frontier_expanded",
                                frontier_expanded(
                                    best_frontier_row["witness"]["evaluation"]
                                ),
                            )
                            if best_frontier_row
                            else None
                        ),
                    }
                )
                atomic_json(summary_path, summary)

            if stopped_on_target:
                print(
                    "TARGET FOUND; pending jobs cancelled where possible",
                    flush=True,
                )
                break

    summary = summary_from_rows(rows)
    summary.update(
        {
            "elapsed_seconds": time.time() - started,
            "target_depth": args.target_depth,
            "target_found": target_found,
            "stopped_on_target": stopped_on_target,
            "best_objective": best_row["objective"] if best_row else None,
            "best_seed": best_row["job_seed"] if best_row else None,
            "best_resolved_seed": (
                best_resolved_row["job_seed"]
                if best_resolved_row
                else None
            ),
            "best_resolved_depth": (
                best_resolved_row.get("required_depth")
                if best_resolved_row
                else None
            ),
            "best_unresolved_seed": (
                best_unresolved_row["job_seed"]
                if best_unresolved_row
                else None
            ),
            "best_unresolved_classification": (
                best_unresolved_row.get("classification")
                if best_unresolved_row
                else None
            ),
            "best_frontier_seed": (
                best_frontier_row["job_seed"]
                if best_frontier_row
                else None
            ),
            "best_frontier_depth": (
                best_frontier_row.get("required_depth")
                if best_frontier_row
                else None
            ),
            "best_frontier_expanded": (
                best_frontier_row.get(
                    "frontier_expanded",
                    frontier_expanded(
                        best_frontier_row["witness"]["evaluation"]
                    ),
                )
                if best_frontier_row
                else None
            ),
        }
    )
    atomic_json(summary_path, summary)
    print(json.dumps(summary, indent=2, sort_keys=True))
    return 0


def cmd_state_subsets(args: argparse.Namespace) -> int:
    parent_payload = json.loads(
        Path(args.parent).read_text(encoding="utf-8")
    )
    child_payload = json.loads(
        Path(args.child).read_text(encoding="utf-8")
    )
    parent_tri = triangulation_from_witness(parent_payload)
    child_tri = triangulation_from_witness(child_payload)

    parent_prefix = restore_state_before_step(
        parent_tri,
        args.step,
        max_repair_depth=args.prefix_depth,
        node_limit=args.node_limit,
        intermediate_policy=args.intermediate_policy,
    )
    child_prefix = restore_state_before_step(
        child_tri,
        args.step,
        max_repair_depth=args.prefix_depth,
        node_limit=args.node_limit,
        intermediate_policy=args.intermediate_policy,
    )

    if parent_prefix["node"] != child_prefix["node"]:
        raise SystemExit("parent and child blocker nodes differ")
    if parent_prefix["remaining"] != child_prefix["remaining"]:
        raise SystemExit("parent and child remaining sets differ")

    parent_state = dict(parent_prefix["colored"])
    child_state = dict(child_prefix["colored"])
    current = parent_prefix["node"]
    remaining = set(parent_prefix["remaining"])

    diff_vertices = sorted(
        v
        for v in set(parent_state) | set(child_state)
        if parent_state.get(v) != child_state.get(v)
    )
    if len(diff_vertices) > args.max_differences:
        raise SystemExit(
            "too many differing vertices for subset enumeration: "
            f"{len(diff_vertices)} > {args.max_differences}"
        )

    out = Path(args.output)
    out.mkdir(parents=True, exist_ok=True)

    cases = []
    for mask in range(1 << len(diff_vertices)):
        changed = [
            diff_vertices[i]
            for i in range(len(diff_vertices))
            if mask & (1 << i)
        ]
        state = dict(parent_state)
        changes = []
        for v in changed:
            changes.append(
                {
                    "vertex": v,
                    "parent": parent_state.get(v),
                    "child": child_state.get(v),
                }
            )
            if v in child_state:
                state[v] = child_state[v]
            else:
                state.pop(v, None)

        profile = repair_maze_from_explicit_state(
            parent_tri,
            colored=state,
            remaining=remaining,
            current=current,
            max_depth=args.max_depth,
            node_limit=args.node_limit,
            intermediate_policy=args.intermediate_policy,
        )

        label = "none" if not changed else "-".join(str(v) for v in changed)
        filename = f"subset-{label}.json"
        atomic_json(out / filename, profile)
        cases.append(
            {
                "changed_vertices": changed,
                "changes": changes,
                "profile_file": filename,
                "valid_intervention": profile["valid_intervention"],
                "invalid_reason": profile["invalid_reason"],
                "proper_violations": profile["proper_violations"],
                "initial_invariant": profile["initial_invariant"],
                "first_exit_depth": profile["first_exit_depth"],
                "exit_counts": profile["exit_counts"],
                "expanded_unique_states": (
                    profile["expanded_unique_states"]
                ),
                "initial_kempe_component_count": (
                    profile.get("initial_kempe_component_count")
                ),
            }
        )

    baseline = next(
        case for case in cases if not case["changed_vertices"]
    )
    full = next(
        case
        for case in cases
        if case["changed_vertices"] == diff_vertices
    )

    summary = {
        "parent": args.parent,
        "child": args.child,
        "parent_seed": parent_payload.get("job_seed"),
        "child_seed": child_payload.get("job_seed"),
        "graph": "parent",
        "step": args.step,
        "node": current,
        "max_depth": args.max_depth,
        "intermediate_policy": args.intermediate_policy,
        "diff_vertices": diff_vertices,
        "difference_count": len(diff_vertices),
        "subset_count": len(cases),
        "baseline_first_exit_depth": baseline["first_exit_depth"],
        "full_child_state_first_exit_depth": full["first_exit_depth"],
        "cases": cases,
    }

    valid_cases = [
        case for case in cases if case["valid_intervention"]
    ]
    summary["valid_cases"] = len(valid_cases)
    summary["invalid_cases"] = len(cases) - len(valid_cases)
    summary["raising_subsets"] = [
        case["changed_vertices"]
        for case in valid_cases
        if baseline["first_exit_depth"] is not None
        and case["first_exit_depth"] is not None
        and case["first_exit_depth"] > baseline["first_exit_depth"]
    ]
    summary["minimal_raising_subsets"] = [
        subset
        for subset in summary["raising_subsets"]
        if not any(
            set(other) < set(subset)
            for other in summary["raising_subsets"]
        )
    ]

    atomic_json(out / "summary.json", summary)
    print(json.dumps(summary, indent=2, sort_keys=True))
    return 0


def cmd_intervention_compare(args: argparse.Namespace) -> int:
    parent_payload = json.loads(
        Path(args.parent).read_text(encoding="utf-8")
    )
    child_payload = json.loads(
        Path(args.child).read_text(encoding="utf-8")
    )
    parent_tri = triangulation_from_witness(parent_payload)
    child_tri = triangulation_from_witness(child_payload)

    parent_prefix = restore_state_before_step(
        parent_tri,
        args.step,
        max_repair_depth=args.prefix_depth,
        node_limit=args.node_limit,
        intermediate_policy=args.intermediate_policy,
    )
    child_prefix = restore_state_before_step(
        child_tri,
        args.step,
        max_repair_depth=args.prefix_depth,
        node_limit=args.node_limit,
        intermediate_policy=args.intermediate_policy,
    )

    if parent_prefix["node"] != child_prefix["node"]:
        raise SystemExit("parent and child blocker nodes differ")
    if parent_prefix["remaining"] != child_prefix["remaining"]:
        raise SystemExit("parent and child remaining sets differ")

    current = parent_prefix["node"]
    remaining = set(parent_prefix["remaining"])
    parent_state = dict(parent_prefix["colored"])
    child_state = dict(child_prefix["colored"])

    cases = [
        ("Pgraph_Pstate", parent_tri, parent_state),
        ("Pgraph_Cstate", parent_tri, child_state),
        ("Cgraph_Pstate", child_tri, parent_state),
        ("Cgraph_Cstate", child_tri, child_state),
    ]

    out = Path(args.output)
    out.mkdir(parents=True, exist_ok=True)

    profiles = {}
    for name, tri, state in cases:
        profile = repair_maze_from_explicit_state(
            tri,
            colored=state,
            remaining=remaining,
            current=current,
            max_depth=args.max_depth,
            node_limit=args.node_limit,
            intermediate_policy=args.intermediate_policy,
        )
        profiles[name] = profile
        atomic_json(out / f"{name}.json", profile)

    p_edges = parent_tri.edges()
    c_edges = child_tri.edges()
    state_keys = sorted(
        set(parent_state) | set(child_state)
    )
    colored_diff = [
        {
            "vertex": v,
            "parent": parent_state.get(v),
            "child": child_state.get(v),
        }
        for v in state_keys
        if parent_state.get(v) != child_state.get(v)
    ]

    summary = {
        "parent": args.parent,
        "child": args.child,
        "parent_seed": parent_payload.get("job_seed"),
        "child_seed": child_payload.get("job_seed"),
        "step": args.step,
        "node": current,
        "max_depth": args.max_depth,
        "intermediate_policy": args.intermediate_policy,
        "edge_removed": [
            list(edge) for edge in sorted(p_edges - c_edges)
        ],
        "edge_added": [
            list(edge) for edge in sorted(c_edges - p_edges)
        ],
        "colored_state_diff": colored_diff,
        "cases": {
            name: {
                "valid_intervention": profile["valid_intervention"],
                "invalid_reason": profile["invalid_reason"],
                "proper_violations": profile["proper_violations"],
                "initial_invariant": profile["initial_invariant"],
                "first_exit_depth": profile["first_exit_depth"],
                "exit_counts": profile["exit_counts"],
                "expanded_unique_states": (
                    profile["expanded_unique_states"]
                ),
                "initial_kempe_component_count": (
                    profile.get("initial_kempe_component_count")
                ),
            }
            for name, profile in profiles.items()
        },
    }

    pp = profiles["Pgraph_Pstate"]
    pc = profiles["Pgraph_Cstate"]
    cc = profiles["Cgraph_Cstate"]
    cp = profiles["Cgraph_Pstate"]
    summary["state_only_matches_child_exit_depth"] = (
        pc["valid_intervention"]
        and pc["first_exit_depth"] == cc["first_exit_depth"]
    )
    summary["state_only_raises_parent_exit_depth"] = (
        pc["valid_intervention"]
        and pp["first_exit_depth"] is not None
        and pc["first_exit_depth"] is not None
        and pc["first_exit_depth"] > pp["first_exit_depth"]
    )
    summary["topology_only_valid"] = cp["valid_intervention"]

    atomic_json(out / "comparison.json", summary)
    print(json.dumps(summary, indent=2, sort_keys=True))
    return 0


def cmd_exit_compare(args: argparse.Namespace) -> int:
    parent_payload = json.loads(
        Path(args.parent).read_text(encoding="utf-8")
    )
    child_payload = json.loads(
        Path(args.child).read_text(encoding="utf-8")
    )
    parent_tri = triangulation_from_witness(parent_payload)
    child_tri = triangulation_from_witness(child_payload)

    parent_exits = repair_exit_records(
        parent_tri,
        step=args.step,
        prefix_depth=args.prefix_depth,
        exit_depth=args.exit_depth,
        node_limit=args.node_limit,
        intermediate_policy=args.intermediate_policy,
    )
    child_exits = repair_exit_records(
        child_tri,
        step=args.step,
        prefix_depth=args.prefix_depth,
        exit_depth=args.exit_depth,
        node_limit=args.node_limit,
        intermediate_policy=args.intermediate_policy,
    )

    comparisons = []
    for index, exit_record in enumerate(parent_exits["exits"]):
        replay = replay_parent_exit_path_on_child(
            child_tri,
            exit_record["path"],
            step=args.step,
            prefix_depth=args.prefix_depth,
            node_limit=args.node_limit,
            intermediate_policy=args.intermediate_policy,
        )
        comparisons.append(
            {
                "parent_exit_index": index,
                "parent_candidates": exit_record["candidates"],
                "parent_path": exit_record["path"],
                "parent_geometry": exit_record["geometry"],
                "child_replay": replay,
            }
        )

    out = Path(args.output)
    out.mkdir(parents=True, exist_ok=True)
    atomic_json(out / "parent-exits.json", parent_exits)
    atomic_json(out / "child-exits.json", child_exits)

    summary = {
        "parent": args.parent,
        "child": args.child,
        "parent_seed": parent_payload.get("job_seed"),
        "child_seed": child_payload.get("job_seed"),
        "step": args.step,
        "exit_depth": args.exit_depth,
        "parent_exit_count": parent_exits["exit_count"],
        "child_exit_count": child_exits["exit_count"],
        "parent_truncated": parent_exits["truncated"],
        "child_truncated": child_exits["truncated"],
        "parent_exit_replays_on_child": comparisons,
        "all_parent_exits_diverge_on_child": all(
            item["child_replay"]["first_divergence"] is not None
            for item in comparisons
        ),
        "first_divergence_indices": [
            (
                item["child_replay"]["first_divergence"]["index"]
                if item["child_replay"]["first_divergence"] is not None
                else None
            )
            for item in comparisons
        ],
    }
    atomic_json(out / "comparison.json", summary)
    print(json.dumps(summary, indent=2, sort_keys=True))
    return 0


def cmd_maze_compare(args: argparse.Namespace) -> int:
    parent_payload = json.loads(
        Path(args.parent).read_text(encoding="utf-8")
    )
    child_payload = json.loads(
        Path(args.child).read_text(encoding="utf-8")
    )
    parent_tri = triangulation_from_witness(parent_payload)
    child_tri = triangulation_from_witness(child_payload)

    parent_profile = repair_maze_profile(
        parent_tri,
        step=args.step,
        prefix_depth=args.prefix_depth,
        max_depth=args.max_depth,
        node_limit=args.node_limit,
        intermediate_policy=args.intermediate_policy,
    )
    child_profile = repair_maze_profile(
        child_tri,
        step=args.step,
        prefix_depth=args.prefix_depth,
        max_depth=args.max_depth,
        node_limit=args.node_limit,
        intermediate_policy=args.intermediate_policy,
    )

    out = Path(args.output)
    out.mkdir(parents=True, exist_ok=True)
    atomic_json(out / "parent-profile.json", parent_profile)
    atomic_json(out / "child-profile.json", child_profile)

    parent_colored = parent_profile["colored_state"]
    child_colored = child_profile["colored_state"]
    color_keys = sorted(
        set(parent_colored) | set(child_colored),
        key=lambda x: int(x),
    )
    colored_diff = [
        {
            "vertex": int(v),
            "parent": parent_colored.get(v),
            "child": child_colored.get(v),
        }
        for v in color_keys
        if parent_colored.get(v) != child_colored.get(v)
    ]

    p_edges = parent_tri.edges()
    c_edges = child_tri.edges()
    edge_removed = [list(edge) for edge in sorted(p_edges - c_edges)]
    edge_added = [list(edge) for edge in sorted(c_edges - p_edges)]

    max_layer = max(
        len(parent_profile["layers"]),
        len(child_profile["layers"]),
    )
    layer_delta = []
    for depth in range(max_layer):
        p = (
            parent_profile["layers"][depth]
            if depth < len(parent_profile["layers"])
            else {}
        )
        c = (
            child_profile["layers"][depth]
            if depth < len(child_profile["layers"])
            else {}
        )
        layer_delta.append(
            {
                "depth": depth,
                "parent_generated": p.get("generated_states", 0),
                "child_generated": c.get("generated_states", 0),
                "generated_delta": (
                    c.get("generated_states", 0)
                    - p.get("generated_states", 0)
                ),
                "parent_exits": p.get("exit_states", 0),
                "child_exits": c.get("exit_states", 0),
                "exit_delta": (
                    c.get("exit_states", 0) - p.get("exit_states", 0)
                ),
                "parent_processed": p.get("processed_states", 0),
                "child_processed": c.get("processed_states", 0),
            }
        )

    comparison = {
        "parent": args.parent,
        "child": args.child,
        "parent_seed": parent_payload.get("job_seed"),
        "child_seed": child_payload.get("job_seed"),
        "step": args.step,
        "parent_node": parent_profile["node"],
        "child_node": child_profile["node"],
        "parent_first_exit_depth": parent_profile["first_exit_depth"],
        "child_first_exit_depth": child_profile["first_exit_depth"],
        "parent_expanded_unique_states": (
            parent_profile["expanded_unique_states"]
        ),
        "child_expanded_unique_states": (
            child_profile["expanded_unique_states"]
        ),
        "colored_state_diff": colored_diff,
        "edge_removed": edge_removed,
        "edge_added": edge_added,
        "parent_blocker_neighbors": parent_profile["blocker_neighbors"],
        "child_blocker_neighbors": child_profile["blocker_neighbors"],
        "parent_initial_kempe_component_count": (
            parent_profile["initial_kempe_component_count"]
        ),
        "child_initial_kempe_component_count": (
            child_profile["initial_kempe_component_count"]
        ),
        "layer_delta": layer_delta,
    }
    atomic_json(out / "comparison.json", comparison)
    print(json.dumps(comparison, indent=2, sort_keys=True))
    return 0


def cmd_neighbors(args: argparse.Namespace) -> int:
    source = Path(args.witness)
    payload = json.loads(source.read_text(encoding="utf-8"))
    base = triangulation_from_witness(payload)
    if not base.planted_is_proper():
        raise SystemExit("witness planted coloring is not proper")

    moves = sorted(base.flippable_preserving())
    out = Path(args.output)
    out.mkdir(parents=True, exist_ok=True)

    jobs = [
        {
            "index": index,
            "move": list(move),
            "witness": str(source),
            "max_depth": args.max_depth,
            "node_limit": args.node_limit,
            "intermediate_policy": args.intermediate_policy,
        }
        for index, move in enumerate(moves)
    ]

    rows: list[dict] = []
    started = time.time()
    print(
        f"witness={source} neighbors={len(jobs)} workers={args.workers}",
        flush=True,
    )

    with ProcessPoolExecutor(max_workers=args.workers) as pool:
        futures = {
            pool.submit(one_neighbor_job, job): job["index"] for job in jobs
        }
        for future in as_completed(futures):
            row = future.result()
            rows.append(row)
            print(
                "NEIGHBOR",
                f"index={row['index']}",
                f"move={row['move']}",
                f"class={row['classification']}",
                f"depth={row.get('required_depth')}",
                f"frontier={row.get('frontier_expanded')}",
                flush=True,
            )

    rows.sort(key=lambda row: row["index"])
    rows_path = out / "neighbors.jsonl"
    with rows_path.open("w", encoding="utf-8") as handle:
        for row in rows:
            handle.write(json.dumps(row, sort_keys=True) + "\n")

    successful = [row for row in rows if row.get("success")]
    best_depth = max(
        successful,
        key=lambda row: (
            int(row.get("required_depth") or -1),
            int(row.get("frontier_expanded") or 0),
        ),
        default=None,
    )
    best_frontier = max(
        successful,
        key=lambda row: tuple(row.get("frontier_objective", [0, 0, 0, 0])),
        default=None,
    )

    def save_neighbor(row: dict | None, name: str) -> None:
        if row is None:
            return
        tri = base.copy()
        tri.apply_flip(tuple(int(x) for x in row["move"]))
        witness = serialize_witness(
            tri,
            row["result"],
            job_seed=int(payload.get("job_seed", -1)),
            search_meta={
                "mode": "one_flip_neighbor",
                "source_witness": str(source),
                "source_seed": payload.get("job_seed"),
                "neighbor_index": row["index"],
                "neighbor_move": row["move"],
                "max_depth": args.max_depth,
                "node_limit": args.node_limit,
                "intermediate_policy": args.intermediate_policy,
            },
        )
        atomic_json(out / name, witness)

    save_neighbor(best_depth, "best_depth_neighbor_witness.json")
    save_neighbor(best_frontier, "best_frontier_neighbor_witness.json")

    depth_counts: dict[str, int] = {}
    classification_counts: dict[str, int] = {}
    for row in rows:
        depth_key = (
            str(row["required_depth"]) if row.get("success") else "unresolved"
        )
        depth_counts[depth_key] = depth_counts.get(depth_key, 0) + 1
        cls = str(row.get("classification", "unknown"))
        classification_counts[cls] = classification_counts.get(cls, 0) + 1

    summary = {
        "format_version": FORMAT_VERSION,
        "source_witness": str(source),
        "source_seed": payload.get("job_seed"),
        "source_required_depth": payload.get("evaluation", {}).get(
            "required_depth"
        ),
        "legal_preserving_neighbors": len(rows),
        "resolved_neighbors": len(successful),
        "depth_counts": depth_counts,
        "classification_counts": classification_counts,
        "max_depth_checked": args.max_depth,
        "node_limit": args.node_limit,
        "intermediate_policy": args.intermediate_policy,
        "elapsed_seconds": time.time() - started,
        "best_depth_index": best_depth["index"] if best_depth else None,
        "best_depth_move": best_depth["move"] if best_depth else None,
        "best_depth": best_depth.get("required_depth") if best_depth else None,
        "best_depth_frontier": (
            best_depth.get("frontier_expanded") if best_depth else None
        ),
        "best_frontier_index": (
            best_frontier["index"] if best_frontier else None
        ),
        "best_frontier_move": (
            best_frontier["move"] if best_frontier else None
        ),
        "best_frontier_depth": (
            best_frontier.get("required_depth") if best_frontier else None
        ),
        "best_frontier_expanded": (
            best_frontier.get("frontier_expanded")
            if best_frontier
            else None
        ),
    }
    atomic_json(out / "summary.json", summary)
    print(json.dumps(summary, indent=2, sort_keys=True))
    return 0


def cmd_replay(args: argparse.Namespace) -> int:
    payload = json.loads(Path(args.witness).read_text(encoding="utf-8"))
    tri = triangulation_from_witness(payload)
    if not tri.planted_is_proper():
        raise SystemExit("witness planted coloring is not proper")

    results = []
    for depth in range(args.min_depth, args.max_depth + 1):
        result = evaluate(
            tri,
            depth,
            node_limit=args.node_limit,
            intermediate_policy=args.intermediate_policy,
            trace=args.trace,
        )
        results.append({"depth_ceiling": depth, "result": result})
        print(
            f"depth={depth} success={result['success']} "
            f"class={result['classification']} "
            f"required={result.get('required_depth')}",
            flush=True,
        )
        if result["success"] and args.stop_on_success:
            break

    payload_out = {"witness": args.witness, "results": results}
    if args.output:
        atomic_json(Path(args.output), payload_out)
    else:
        print(json.dumps(payload_out, indent=2, sort_keys=True))
    return 0


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest="command", required=True)

    search = sub.add_parser("search", help="run parallel adversarial flip search")
    search.add_argument("--vertices", type=int, default=24)
    search.add_argument("--jobs", type=int, default=100)
    search.add_argument("--steps", type=int, default=1000)
    search.add_argument("--warmup-flips", type=int, default=32)
    search.add_argument(
        "--initial-witness",
        help=(
            "start every search job from this saved witness instead of "
            "generating a fresh planted triangulation"
        ),
    )
    search.add_argument(
        "--workers", type=int, default=max(1, (os.cpu_count() or 2) - 1)
    )
    search.add_argument("--max-depth", type=int, default=6)
    search.add_argument("--target-depth", type=int, default=5)
    search.add_argument("--node-limit", type=int, default=250_000)
    search.add_argument("--base-seed", type=int, default=6_000_000)
    search.add_argument(
        "--intermediate-policy",
        choices=("strict", "endpoint"),
        default="strict",
    )
    search.add_argument("--temperature", type=float, default=1.5)
    search.add_argument("--cooling", type=float, default=0.9995)
    search.add_argument(
        "--search-objective",
        choices=("mixed", "resolved", "frontier"),
        default="mixed",
        help=(
            "mixed preserves the original hard-state objective; resolved "
            "keeps every solved witness above unresolved states and then "
            "maximizes verified repair depth; frontier ranks solved states "
            "by required depth and then by depth-minus-one frontier expansion"
        ),
    )
    search.add_argument(
        "--stop-on-target",
        action="store_true",
        help=(
            "stop scheduling useful work once a solved witness reaches "
            "--target-depth; pending futures are cancelled where possible"
        ),
    )
    search.add_argument("--summary-every", type=int, default=10)
    search.add_argument(
        "--output", default="python/Tromino/results/repair-depth/default"
    )
    search.set_defaults(func=cmd_search)

    state_subsets = sub.add_parser(
        "state-subsets",
        help=(
            "enumerate partial parent-to-child blocker-state interventions "
            "on the parent graph"
        ),
    )
    state_subsets.add_argument("parent")
    state_subsets.add_argument("child")
    state_subsets.add_argument("--step", type=int, default=16)
    state_subsets.add_argument("--prefix-depth", type=int, default=10)
    state_subsets.add_argument("--max-depth", type=int, default=10)
    state_subsets.add_argument("--node-limit", type=int, default=6_000_000)
    state_subsets.add_argument("--max-differences", type=int, default=8)
    state_subsets.add_argument(
        "--intermediate-policy",
        choices=("strict", "endpoint"),
        default="endpoint",
    )
    state_subsets.add_argument(
        "--output",
        default="python/Tromino/results/repair-depth/state-subsets",
    )
    state_subsets.set_defaults(func=cmd_state_subsets)

    intervention = sub.add_parser(
        "intervention-compare",
        help="cross parent/child topology and blocker colored state",
    )
    intervention.add_argument("parent")
    intervention.add_argument("child")
    intervention.add_argument("--step", type=int, default=16)
    intervention.add_argument("--prefix-depth", type=int, default=10)
    intervention.add_argument("--max-depth", type=int, default=10)
    intervention.add_argument("--node-limit", type=int, default=6_000_000)
    intervention.add_argument(
        "--intermediate-policy",
        choices=("strict", "endpoint"),
        default="endpoint",
    )
    intervention.add_argument(
        "--output",
        default="python/Tromino/results/repair-depth/intervention-compare",
    )
    intervention.set_defaults(func=cmd_intervention_compare)

    exit_compare = sub.add_parser(
        "exit-compare",
        help="extract parent exits and replay their Kempe paths on a child",
    )
    exit_compare.add_argument("parent")
    exit_compare.add_argument("child")
    exit_compare.add_argument("--step", type=int, default=16)
    exit_compare.add_argument("--prefix-depth", type=int, default=10)
    exit_compare.add_argument("--exit-depth", type=int, default=9)
    exit_compare.add_argument("--node-limit", type=int, default=6_000_000)
    exit_compare.add_argument(
        "--intermediate-policy",
        choices=("strict", "endpoint"),
        default="endpoint",
    )
    exit_compare.add_argument(
        "--output",
        default="python/Tromino/results/repair-depth/exit-compare",
    )
    exit_compare.set_defaults(func=cmd_exit_compare)

    maze = sub.add_parser(
        "maze-compare",
        help="compare exchange-state repair mazes for two witnesses",
    )
    maze.add_argument("parent")
    maze.add_argument("child")
    maze.add_argument("--step", type=int, default=16)
    maze.add_argument("--prefix-depth", type=int, default=10)
    maze.add_argument("--max-depth", type=int, default=10)
    maze.add_argument("--node-limit", type=int, default=6_000_000)
    maze.add_argument(
        "--intermediate-policy",
        choices=("strict", "endpoint"),
        default="endpoint",
    )
    maze.add_argument(
        "--output",
        default="python/Tromino/results/repair-depth/maze-compare",
    )
    maze.set_defaults(func=cmd_maze_compare)

    neighbors = sub.add_parser(
        "neighbors",
        help="enumerate and evaluate every legal preserving one-flip neighbor",
    )
    neighbors.add_argument("witness")
    neighbors.add_argument("--max-depth", type=int, default=10)
    neighbors.add_argument("--node-limit", type=int, default=6_000_000)
    neighbors.add_argument(
        "--intermediate-policy",
        choices=("strict", "endpoint"),
        default="endpoint",
    )
    neighbors.add_argument(
        "--workers", type=int, default=max(1, (os.cpu_count() or 2) - 1)
    )
    neighbors.add_argument(
        "--output",
        default="python/Tromino/results/repair-depth/one-flip-neighbors",
    )
    neighbors.set_defaults(func=cmd_neighbors)

    replay = sub.add_parser("replay", help="re-evaluate one saved witness")
    replay.add_argument("witness")
    replay.add_argument("--min-depth", type=int, default=0)
    replay.add_argument("--max-depth", type=int, default=8)
    replay.add_argument("--node-limit", type=int, default=1_000_000)
    replay.add_argument(
        "--intermediate-policy",
        choices=("strict", "endpoint"),
        default="strict",
    )
    replay.add_argument("--trace", action="store_true")
    replay.add_argument("--stop-on-success", action="store_true")
    replay.add_argument("--output")
    replay.set_defaults(func=cmd_replay)

    return parser


def main() -> int:
    args = build_parser().parse_args()
    return int(args.func(args))


if __name__ == "__main__":
    raise SystemExit(main())
