#!/usr/bin/env python3
"""Scratch observation OBS-001: missing-color lift on random planar triangulations.

This is intentionally a small, non-production reference script frozen from the
2026-09-28 ChatGPT scratch experiment. It reproduces the recorded observation
before the Codex implementation is designed.
"""

from __future__ import annotations

from collections import deque
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
        for u, v in ((a, b), (b, c), (c, a)):
            u, v = int(u), int(v)
            adjacency[u].add(v)
            adjacency[v].add(u)

    hull = ConvexHull(points)
    boundary = [int(v) for v in hull.vertices]
    adjacency[SEA] = set(boundary)
    for v in boundary:
        adjacency[v].add(SEA)
    return adjacency, boundary


def peel_order(adjacency, k: int):
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


def restore(adjacency, order, *, gap_aware: bool):
    colored = {SEA: 0}
    remaining = set(order)

    for v in reversed(order):
        remaining.remove(v)
        forbidden = {colored[u] for u in adjacency[v] if u in colored}
        available = [c for c in COLORS if c not in forbidden]
        if not available:
            return False, colored, v

        if gap_aware and len(available) > 1:
            scored = []
            for color in available:
                four = three = square_sum = 0
                for w in adjacency[v]:
                    if w not in remaining:
                        continue
                    palette = {colored[u] for u in adjacency[w] if u in colored}
                    palette.add(color)
                    p = len(palette)
                    four += int(p >= 4)
                    three += int(p == 3)
                    square_sum += p * p
                scored.append(((four, three, square_sum, color), color))
            color = min(scored)[1]
        else:
            color = available[0]

        colored[v] = color

    return True, colored, None


def restore_backtracking(adjacency, order, node_limit: int = 1_000_000):
    colored = {SEA: 0}
    remaining = set(order)
    reverse_order = list(reversed(order))
    search_nodes = 0

    def rec(i: int):
        nonlocal search_nodes
        search_nodes += 1
        if search_nodes > node_limit:
            return None
        if i == len(reverse_order):
            return dict(colored)

        v = reverse_order[i]
        remaining.remove(v)
        forbidden = {colored[u] for u in adjacency[v] if u in colored}
        available = [c for c in COLORS if c not in forbidden]

        def score(color: int):
            four = three = square_sum = 0
            for w in adjacency[v]:
                if w not in remaining:
                    continue
                palette = {colored[u] for u in adjacency[w] if u in colored}
                palette.add(color)
                p = len(palette)
                four += int(p >= 4)
                three += int(p == 3)
                square_sum += p * p
            return (four, three, square_sum, color)

        available.sort(key=score)
        for color in available:
            colored[v] = color
            solution = rec(i + 1)
            if solution is not None:
                remaining.add(v)
                return solution
            del colored[v]

        remaining.add(v)
        return None

    solution = rec(0)
    return solution is not None, search_nodes


def greedy_trials(n: int, trials: int = 100, base_seed: int = 120_000):
    k3_core_sizes = []
    plain_success = 0
    gap_success = 0

    for i in range(trials):
        adjacency, _ = generate_map(n, base_seed + i)

        _, core3 = peel_order(adjacency, 3)
        k3_core_sizes.append(len(core3))

        order4, core4 = peel_order(adjacency, 4)
        if core4:
            raise RuntimeError(
                f"OBS-001 assumes empty 4-core; seed={base_seed+i}, core={len(core4)}"
            )

        plain_success += int(restore(adjacency, order4, gap_aware=False)[0])
        gap_success += int(restore(adjacency, order4, gap_aware=True)[0])

    return {
        "n": n,
        "trials": trials,
        "k3_core_mean": statistics.mean(k3_core_sizes),
        "k3_core_median": statistics.median(k3_core_sizes),
        "plain_greedy_success": plain_success,
        "gap_aware_success": gap_success,
    }


def witness(seed: int = 120_001, n: int = 20):
    adjacency, _ = generate_map(n, seed)
    order, core = peel_order(adjacency, 4)
    if core:
        raise RuntimeError("witness unexpectedly has non-empty 4-core")

    colored_plain = {SEA: 0}
    colored_gap = {SEA: 0}
    remaining_plain = set(order)
    remaining_gap = set(order)
    divergence = None

    for step, v in enumerate(reversed(order)):
        remaining_plain.remove(v)
        remaining_gap.remove(v)

        fp = {colored_plain[u] for u in adjacency[v] if u in colored_plain}
        fg = {colored_gap[u] for u in adjacency[v] if u in colored_gap}
        ap = [c for c in COLORS if c not in fp]
        ag = [c for c in COLORS if c not in fg]

        if not ap:
            return {
                "seed": seed,
                "dead_node": v,
                "dead_palette": sorted(fp),
                "colored_neighbors": sorted(
                    (u, colored_plain[u])
                    for u in adjacency[v]
                    if u in colored_plain
                ),
                "first_divergence": divergence,
            }

        cp = ap[0]

        scored = []
        for color in ag:
            four = three = square_sum = 0
            for w in adjacency[v]:
                if w not in remaining_gap:
                    continue
                palette = {colored_gap[u] for u in adjacency[w] if u in colored_gap}
                palette.add(color)
                p = len(palette)
                four += int(p >= 4)
                three += int(p == 3)
                square_sum += p * p
            scored.append(((four, three, square_sum, color), color))
        cg = min(scored)[1]

        if divergence is None and cp != cg:
            divergence = {
                "step": step,
                "node": v,
                "available": ap,
                "plain_choice": cp,
                "gap_aware_choice": cg,
            }

        colored_plain[v] = cp
        colored_gap[v] = cg

    raise RuntimeError("witness plain strategy unexpectedly succeeded")


def backtracking_trials(n: int, trials: int = 10, base_seed: int = 130_000):
    nodes = []
    successes = 0
    for i in range(trials):
        adjacency, _ = generate_map(n, base_seed + i)
        order, core = peel_order(adjacency, 4)
        if core:
            raise RuntimeError(
                f"OBS-001 assumes empty 4-core; seed={base_seed+i}, core={len(core)}"
            )
        ok, searched = restore_backtracking(adjacency, order)
        successes += int(ok)
        nodes.append(searched)

    return {
        "n": n,
        "trials": trials,
        "successes": successes,
        "search_nodes": nodes,
        "median_search_nodes": statistics.median(nodes),
        "max_search_nodes": max(nodes),
        "node_limit": 1_000_000,
    }


def main():
    result = {
        "observation": "OBS-001-MissingColorLift",
        "generator": (
            "uniform random points -> Delaunay triangulation -> "
            "outer sea joined to convex hull"
        ),
        "sea_color": 0,
        "colors": list(COLORS),
        "greedy": [greedy_trials(n) for n in (20, 50, 100)],
        "witness": witness(),
        "backtracking": [backtracking_trials(n) for n in (50, 100)],
    }
    print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
