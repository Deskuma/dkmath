#!/usr/bin/env python3
"""Deterministic diagnostics for the actual realized cubic shell count.

Run from lean/dk_math:

  python3 docs/dev/ABC-shell-count-sparsity-260915-v0/scratch/ShellDiagnostics.py

The calculation uses the production arithmetic identity
GN 3 a 1 = a^2 + 3*a + 3.  Its full repeated modulus is the product of the
prime powers whose exponents are at least two.  The script uses exact integer
factorization from SymPy; it is numerical evidence, not a proof.
"""

import argparse
import json
import math
from collections import Counter, defaultdict

import sympy


def canonical_record(a):
    value = a * a + 3 * a + 3
    factors = {int(p): int(v) for p, v in sympy.factorint(value).items()}
    M = math.prod(p ** v for p, v in factors.items() if v >= 2)
    S = math.prod(p for p, v in factors.items() if v == 1)
    r = math.prod(p for p, v in factors.items() if v % 2 == 1 and v >= 2)
    d = math.prod(p ** (v // 2) for p, v in factors.items() if v >= 2)
    e = d // r
    T = r * S
    assert M * S == value
    assert M == r * d * d == e * e * r * r * r
    assert d == r * e
    assert (2 * a + 3) ** 2 + 3 == 4 * T * d * d
    return {"a": a, "value": value, "M": M, "S": S,
            "r": r, "d": d, "e": e, "T": T,
            "omega_M": sum(1 for v in factors.values() if v >= 2)}


def dyadic_floor(n):
    return 1 << (n.bit_length() - 1)


def top_counts(values, limit=8):
    return [[int(v), int(c)] for v, c in Counter(values).most_common(limit)]


def distribution(values):
    ordered = sorted(values)
    return {
        "min": int(ordered[0]),
        "median": int(ordered[len(ordered) // 2]),
        "max": int(ordered[-1]),
        "unique_count": len(set(ordered)),
        "top_frequencies": top_counts(values),
    }


def squarefree_sieve(n):
    result = [True] * (n + 1)
    if n >= 0:
        result[0] = False
    p = 2
    while p * p <= n:
        square = p * p
        for k in range(square, n + 1, square):
            result[k] = False
        p += 1
    return result


def ambient_squarefull_pair_count(D, squarefree):
    """Count canonical (r,e) with squarefree r and D <= e^2*r^3 < 2D."""
    total = 0
    r = 1
    while r ** 3 < 2 * D:
        if squarefree[r]:
            r3 = r ** 3
            emin = math.isqrt((D - 1) // r3) + 1
            emax = math.isqrt((2 * D - 1) // r3)
            if emin <= emax:
                total += emax - emin + 1
        r += 1
    return total


def shell_summary(X, D, rows, squarefree):
    witnesses = [r for r in rows if r["M"] > X + 1 and dyadic_floor(r["M"]) == D]
    moduli = sorted({r["M"] for r in witnesses})
    by_M = Counter(r["M"] for r in witnesses)
    by_S = Counter(r["S"] for r in witnesses)
    by_T = Counter(r["T"] for r in witnesses)
    by_SU = Counter((r["S"], r["e"]) for r in witnesses)
    count = len(moduli)
    ratio = count * math.sqrt(D) / X
    r_bound_count = 0
    while (r_bound_count + 1) ** 3 < 2 * D:
        r_bound_count += 1
    S_bound = (3 * (X + 1) ** 2) // D
    e_bound_count = math.isqrt(2 * D - 1)
    return {
        "D": D,
        "D_over_X": D / X,
        "shell_count": count,
        "normalized_shell_count": ratio,
        "witness_count": len(witnesses),
        "modulus_count": count,
        "pell_parameter_count": len(by_T),
        "mordell_parameter_count": len(by_SU),
        "max_fixed_T_fiber": max(by_T.values()),
        "max_fixed_S_fiber": max(by_S.values()),
        "max_fixed_M_fiber": max(by_M.values()),
        "max_fixed_mordell_parameter_fiber": max(by_SU.values()),
        "ambient_squarefull_pair_count": ambient_squarefull_pair_count(D, squarefree),
        "raw_rS_box_count": r_bound_count * S_bound,
        "r_bound_count": r_bound_count,
        "S_bound_from_DS": S_bound,
        "raw_mordell_parameter_box_count": S_bound * e_bound_count,
        "e_bound_count": e_bound_count,
        "max_quadratic_root_budget": max(2 ** r["omega_M"] for r in witnesses),
        "witness_examples": witnesses[:8],
        "coordinates": {k: distribution([r[k] for r in witnesses])
                        for k in ("r", "d", "e", "S", "T")},
    }


def scan_grid(grid):
    max_X = max(grid)
    records = [canonical_record(a) for a in range(1, max_X + 1)]
    max_D = max(dyadic_floor(r["M"]) for r in records)
    max_r = 1
    while (max_r + 1) ** 3 < 2 * max_D:
        max_r += 1
    squarefree = squarefree_sieve(max_r)
    scans = []
    global_hard = None
    for X in grid:
        rows = records[:X]
        shell_rows = defaultdict(list)
        for row in rows:
            if row["M"] > X + 1:
                shell_rows[dyadic_floor(row["M"])].append(row)
        shells = [shell_summary(X, D, rows, squarefree) for D in sorted(shell_rows)]
        hard = max(shells, key=lambda s: s["normalized_shell_count"]) if shells else None
        if hard is not None and (global_hard is None or
                                 hard["normalized_shell_count"] >
                                 global_hard["normalized_shell_count"]):
            global_hard = {"X": X, **hard}
        scans.append({
            "X": X,
            "represented_shell_count": len(shells),
            "total_large_witnesses": sum(s["witness_count"] for s in shells),
            "total_distinct_large_moduli": len({r["M"] for r in rows if r["M"] > X + 1}),
            "hardest_shell": hard,
            "shells": shells,
        })
    return {
        "scope": "actual canonical witnesses 1 <= a <= X with M(a) > X+1, grouped by D=2^floor(log2 M)",
        "grid": grid,
        "factorization_engine": f"sympy.factorint {sympy.__version__}",
        "global_hardest_observed_shell": global_hard,
        "scans": scans,
    }


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--grid", default="100,300,1000,3000,10000,30000,100000")
    args = parser.parse_args()
    grid = sorted({int(x) for x in args.grid.split(",")})
    if not grid or grid[0] < 1:
        raise ValueError("grid values must be positive")
    print(json.dumps(scan_grid(grid), indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
