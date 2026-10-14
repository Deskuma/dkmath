#!/usr/bin/env python3
"""OBS-002: Missing-Color invariant with forced local exchange.

Frozen scratch reference. The exchange move is a Kempe-component swap proxy,
not the final DkMath GapSwap definition.
"""

from __future__ import annotations

from collections import deque
import itertools
import json
import statistics

import numpy as np
from scipy.spatial import ConvexHull, Delaunay

COLORS = (0, 1, 2, 3)
SEA = -1


def generate_map(n: int, seed: int):
    rng = np.random.default_rng(seed)
    points = rng.random((n, 2))
    tri = Delaunay(points)
    adjacency = {i: set() for i in range(n)}
    for a, b, c in tri.simplices:
        a, b, c = int(a), int(b), int(c)
        for u, v in ((a, b), (b, c), (c, a)):
            adjacency[u].add(v)
            adjacency[v].add(u)
    boundary = [int(v) for v in ConvexHull(points).vertices]
    adjacency[SEA] = set(boundary)
    for v in boundary:
        adjacency[v].add(SEA)
    return adjacency


def peel_order(adjacency, k: int = 4):
    alive = set(adjacency)
    alive.discard(SEA)
    degree = {
        v: sum(1 for u in adjacency[v] if u == SEA or u in alive)
        for v in alive
    }
    queue = deque(v for v in alive if degree[v] <= k)
    queued = set(queue)
    order = []
    while queue:
        v = queue.popleft()
        queued.discard(v)
        if v not in alive or degree[v] > k:
            continue
        alive.remove(v)
        order.append(v)
        for u in adjacency[v]:
            if u in alive:
                degree[u] -= 1
                if degree[u] <= k and u not in queued:
                    queue.append(u)
                    queued.add(u)
    return order, alive


def palette(adjacency, colored, v):
    return {colored[u] for u in adjacency[v] if u in colored}


def invariant_holds(adjacency, colored, remaining):
    return all(len(palette(adjacency, colored, v)) <= 3 for v in remaining)


def safe_candidates(adjacency, colored, remaining, v):
    forbidden = palette(adjacency, colored, v)
    available = [c for c in COLORS if c not in forbidden]
    future = remaining - {v}
    scored = []
    for color in available:
        safe = True
        for w in adjacency[v]:
            if w not in future:
                continue
            p = palette(adjacency, colored, w)
            if len(p) >= 3 and color not in p:
                safe = False
                break
        if not safe:
            continue
        three = 0
        square_sum = 0
        for w in adjacency[v]:
            if w not in future:
                continue
            p = palette(adjacency, colored, w) | {color}
            three += int(len(p) == 3)
            square_sum += len(p) ** 2
        scored.append(((three, square_sum, color), color))
    scored.sort()
    return [color for _, color in scored]


def kempe_components(adjacency, colored):
    nodes = set(colored)
    moves = []
    for a, b in itertools.combinations(COLORS, 2):
        allowed = {v for v in nodes if colored[v] in (a, b)}
        seen = set()
        for start in list(allowed):
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
            if SEA not in component:
                moves.append((a, b, frozenset(component)))
    return moves


def apply_exchange(colored, move):
    a, b, component = move
    result = dict(colored)
    for v in component:
        result[v] = b if result[v] == a else a
    return result


def find_repair(adjacency, colored, remaining, v, max_depth, node_limit=200_000):
    visited = {tuple(sorted(colored.items()))}
    queue = deque([(dict(colored), [])])
    expanded = 0
    while queue:
        state, sequence = queue.popleft()
        if len(sequence) >= max_depth:
            continue
        for move in kempe_components(adjacency, state):
            next_state = apply_exchange(state, move)
            key = tuple(sorted(next_state.items()))
            if key in visited:
                continue
            visited.add(key)
            expanded += 1
            if expanded > node_limit:
                return None, None, None, expanded
            if not invariant_holds(adjacency, next_state, remaining):
                continue
            candidates = safe_candidates(adjacency, next_state, remaining, v)
            next_sequence = sequence + [move]
            if candidates:
                return next_state, next_sequence, candidates, expanded
            queue.append((next_state, next_sequence))
    return None, None, None, expanded


def restore(adjacency, order, max_repair_depth, node_limit=200_000, trace=False):
    colored = {SEA: 0}
    remaining = set(order)
    repairs = 0
    max_depth_used = 0
    repair_moves_total = 0
    repair_log = []

    for step, v in enumerate(reversed(order)):
        if not invariant_holds(adjacency, colored, remaining):
            return False, {"reason": "pre_invariant_broken", "step": step, "node": v}

        candidates = safe_candidates(adjacency, colored, remaining, v)
        sequence = []

        if not candidates:
            if max_repair_depth == 0:
                return False, {
                    "reason": "forced_repair",
                    "step": step,
                    "node": v,
                    "repairs": repairs,
                }
            next_state, sequence, candidates, expanded = find_repair(
                adjacency, colored, remaining, v, max_repair_depth, node_limit
            )
            if next_state is None:
                return False, {
                    "reason": "repair_failed",
                    "step": step,
                    "node": v,
                    "repairs": repairs,
                    "expanded": expanded,
                }
            colored = next_state
            repairs += 1
            max_depth_used = max(max_depth_used, len(sequence))
            repair_moves_total += len(sequence)

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
                }
            )

    return True, {
        "repairs": repairs,
        "max_depth_used": max_depth_used,
        "repair_moves_total": repair_moves_total,
        "repair_log": repair_log,
    }


def run_primary(n, trials, seed_start):
    success = {0: 0, 1: 0, 2: 0}
    repairs = {1: [], 2: []}
    depths = {1: [], 2: []}

    for i in range(trials):
        adjacency = generate_map(n, seed_start + i)
        order, core = peel_order(adjacency, 4)
        if core:
            raise RuntimeError("non-empty 4-core")

        for depth in (0, 1, 2):
            ok, info = restore(adjacency, order, depth)
            success[depth] += int(ok)
            if ok and depth:
                repairs[depth].append(info["repairs"])
                depths[depth].append(info["max_depth_used"])

    return {
        "n": n,
        "trials": trials,
        "seed_start": seed_start,
        "direct_success": success[0],
        "depth1_success": success[1],
        "depth2_success": success[2],
        "depth1_mean_repairs_among_successes": statistics.mean(repairs[1]),
        "depth2_mean_repairs": statistics.mean(repairs[2]),
        "depth2_max_depth_used": max(depths[2]),
    }


def run_500():
    result = {"n": 500, "trials": 50, "seed_start": 5_200_000}
    for depth in (1, 2, 3):
        successes = 0
        repairs = []
        max_depths = []
        failure_seeds = []
        for i in range(50):
            seed = 5_200_000 + i
            adjacency = generate_map(500, seed)
            order, core = peel_order(adjacency, 4)
            if core:
                raise RuntimeError("non-empty 4-core")
            ok, info = restore(adjacency, order, depth)
            successes += int(ok)
            if ok:
                repairs.append(info["repairs"])
                max_depths.append(info["max_depth_used"])
            else:
                failure_seeds.append(seed)
        result[f"depth{depth}"] = {
            "success": successes,
            "mean_repairs_among_successes": statistics.mean(repairs),
            "max_depth_used": max(max_depths),
            "failure_seeds": failure_seeds,
        }
    return result


def witness(seed=5_200_005):
    adjacency = generate_map(500, seed)
    order, core = peel_order(adjacency, 4)
    if core:
        raise RuntimeError("witness has non-empty 4-core")
    ok2, info2 = restore(adjacency, order, 2, trace=True)
    ok3, info3 = restore(adjacency, order, 3, trace=True)
    if ok2 or not ok3:
        raise RuntimeError("expected depth-2 failure and depth-3 success")
    deep = [x for x in info3["repair_log"] if x["repair_depth"] == 3]
    return {
        "seed": seed,
        "depth2_failure": info2,
        "depth3_full_run": {
            "repairs": info3["repairs"],
            "repair_moves_total": info3["repair_moves_total"],
            "max_depth_used": info3["max_depth_used"],
        },
        "depth3_repair": deep[0],
    }


def main():
    result = {
        "observation": "OBS-002-MissingColorForcedExchange",
        "primary_batches": [
            run_primary(20, 100, 350_000),
            run_primary(50, 100, 650_000),
            run_primary(100, 100, 1_150_000),
            run_primary(200, 50, 2_150_000),
        ],
        "dedicated_500_batch": run_500(),
        "depth3_witness": witness(),
    }
    print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
