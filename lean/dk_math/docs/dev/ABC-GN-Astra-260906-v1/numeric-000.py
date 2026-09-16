"""SOL-000 diagnostics for the cubic realized shell count.

Run from lean/dk_math:
  python3 docs/dev/ABC-GN-Astra-260906-v1/numeric-000.py --limit 300000

All factorization, divisibility, shell, and regression checks use integer
arithmetic.  Decimal ratios are diagnostics only and are never proof input.
Requires sympy (tested with the repository environment).
"""

from __future__ import annotations

import argparse
import bisect
import collections
import json
import math
import random

import sympy


def factor_sieve(limit: int) -> list[list[tuple[int, int]]]:
    """Factor F(a)=a^2+3a+3 for every 0 <= a <= limit."""
    residual = [a * a + 3 * a + 3 for a in range(limit + 1)]
    factors: list[list[tuple[int, int]]] = [[] for _ in residual]
    for p0 in sympy.primerange(2, limit + 3):
        p = int(p0)
        if p == 3:
            roots = [0]
        elif p % 3 != 1:
            continue
        else:
            inv2 = pow(2, -1, p)
            roots = sorted(
                {int((z - 3) * inv2 % p) for z in sympy.sqrt_mod(-3, p, all_roots=True)}
            )
        for root in roots:
            for a in range(root, limit + 1, p):
                valuation = 0
                while residual[a] % p == 0:
                    residual[a] //= p
                    valuation += 1
                if valuation:
                    factors[a].append((p, valuation))
    for a, n in enumerate(residual):
        if n > 1:
            factors[a].append((int(n), 1))
    return factors


def cubic_coordinates(a: int, fs: list[tuple[int, int]]) -> tuple[int, int, int, int, int]:
    """Return the exact production coordinates (M,S,r,d,T)."""
    value = a * a + 3 * a + 3
    repeated = math.prod(p**e for p, e in fs if e >= 2)
    complement = value // repeated
    odd_part = math.prod(p for p, e in fs if e >= 2 and e % 2 == 1)
    even_part = math.prod(p ** (e // 2) for p, e in fs if e >= 2)
    parameter = odd_part * complement
    assert repeated * complement == value
    assert repeated == odd_part * even_part * even_part
    assert math.gcd(repeated, complement) == 1
    assert all(e == 1 for p, e in fs if complement % p == 0)
    assert all(p != 3 and p % 3 == 1 for p, e in fs if e >= 2)
    assert (2 * a + 3) ** 2 + 3 == 4 * parameter * even_part * even_part
    return repeated, complement, odd_part, even_part, parameter


def integer_cuberoot(n: int) -> int:
    """floor(n^(1/3)), corrected using exact integer comparisons."""
    if n < 0:
        raise ValueError("nonnegative input required")
    x = int(round(n ** (1.0 / 3.0))) if n else 0
    while (x + 1) ** 3 <= n:
        x += 1
    while x**3 > n:
        x -= 1
    return x


def support_tables(limit: int) -> tuple[list[bool], list[bool], list[int]]:
    """Squarefree and all-primes-1-mod-3 tables, plus allowed integers."""
    spf = list(range(limit + 1))
    for p in range(2, math.isqrt(limit) + 1):
        if spf[p] == p:
            for n in range(p * p, limit + 1, p):
                if spf[n] == n:
                    spf[n] = p
    squarefree = [False] * (limit + 1)
    allowed = [False] * (limit + 1)
    squarefree[1] = True
    allowed[1] = True
    for n in range(2, limit + 1):
        p = spf[n]
        q = n // p
        squarefree[n] = squarefree[q] and q % p != 0
        allowed[n] = allowed[q] and p % 3 == 1
    return squarefree, allowed, [n for n in range(1, limit + 1) if allowed[n]]


def squarefull_shell_counts(
    D: int, squarefree: list[bool], allowed: list[bool], allowed_values: list[int]
) -> tuple[int, int]:
    """Count M=u^2*r^3 in [D,2D), unrestricted and with p|M => p=1 mod 3."""
    rmax = integer_cuberoot(2 * D - 1)
    unrestricted = 0
    support_restricted = 0
    for r in range(1, rmax + 1):
        if not squarefree[r]:
            continue
        r3 = r**3
        lo = math.isqrt((D - 1) // r3) + 1
        hi = math.isqrt((2 * D - 1) // r3)
        if hi < lo:
            continue
        unrestricted += hi - lo + 1
        if allowed[r]:
            support_restricted += bisect.bisect_right(allowed_values, hi) - bisect.bisect_left(
                allowed_values, lo
            )
    return unrestricted, support_restricted


def valuation(n: int, p: int) -> int:
    answer = 0
    while n % p == 0:
        n //= p
        answer += 1
    return answer


def regression_ledger(rows: list[tuple[int, int, int, int, int]]) -> dict[str, object]:
    collisions: dict[int, list[int]] = collections.defaultdict(list)
    for a, (M, _S, _r, _d, _T) in enumerate(rows):
        collisions[M].append(a)
    assert collisions[169][:2] == [21, 145]
    assert collisions[8281][:4] == [2173, 3018, 5260, 6105]

    pell = []
    a, d = 0, 1
    for n in range(7):
        M, S, r, d0, T = rows[a] if a < len(rows) else (d * d, 3, 1, d, 3)
        assert a * a + 3 * a + 3 == 3 * d * d
        if a < len(rows):
            assert (M, S, r, d0, T) == (d * d, 3, 1, d, 3)
        pell.append([n, a, d])
        a, d = 7 * a + 12 * d + 9, 4 * a + 7 * d + 6

    a = 7428
    forward = a * a + 3 * a + 3
    swap = 3 * a * a + 3 * a + 1
    assert valuation(forward, 7) == 2
    assert valuation(swap, 13) == 2

    states = {}
    for residue in range(1, 49, 7):
        fdeep = (residue * residue + 3 * residue + 3) % 49 == 0
        sdeep = (3 * residue * residue + 3 * residue + 1) % 49 == 0
        state = "forward-deep" if fdeep else "swap-deep" if sdeep else "shallow"
        states[residue] = state
    assert states[29] == "forward-deep" and states[22] == "swap-deep"
    assert sum(v == "shallow" for v in states.values()) == 5

    hensel = {}
    for p in (7, 13, 19, 31, 37):
        roots_p = [a for a in range(p) if (a * a + 3 * a + 3) % p == 0]
        roots_p2 = [a for a in range(p * p) if (a * a + 3 * a + 3) % (p * p) == 0]
        assert len(roots_p) == len(roots_p2) == 2
        assert sorted(a % p for a in roots_p2) == roots_p
        hensel[p] = roots_p2

    return {
        "M=169 witnesses": collisions[169][:2],
        "M=8281 witnesses": collisions[8281][:4],
        "S=3 Pell prefix (n,a,d)": pell,
        "paired exact-depth witness": {
            "a": a,
            "v7(F)": valuation(forward, 7),
            "v13(G)": valuation(swap, 13),
        },
        "mod49 states": states,
        "Hensel roots mod p^2": hensel,
    }


def shell_ledger(X: int, rows: list[tuple[int, int, int, int, int]]) -> list[dict[str, object]]:
    shell_witnesses: dict[int, list[int]] = collections.defaultdict(list)
    for a in range(1, X + 1):
        M = rows[a][0]
        if X + 1 < M:
            D = 1 << (M.bit_length() - 1)
            shell_witnesses[D].append(a)

    if not shell_witnesses:
        return []
    max_D = max(shell_witnesses)
    table_limit = max(math.isqrt(2 * max_D - 1), integer_cuberoot(2 * max_D - 1))
    squarefree, allowed, allowed_values = support_tables(table_limit)

    output = []
    for D, witnesses in sorted(shell_witnesses.items()):
        by_M: dict[int, list[int]] = collections.defaultdict(list)
        by_T: dict[int, list[int]] = collections.defaultdict(list)
        by_Tr: dict[tuple[int, int], list[int]] = collections.defaultdict(list)
        for a in witnesses:
            M, _S, r, _d, T = rows[a]
            by_M[M].append(a)
            by_T[T].append(a)
            by_Tr[(T, r)].append(a)
            assert D * D * T**3 < 54 * (X + 1) ** 6
        generic, support = squarefull_shell_counts(D, squarefree, allowed, allowed_values)
        t_height = integer_cuberoot((54 * (X + 1) ** 6 - 1) // (D * D))
        weighted = len(by_M) * (2 * D) ** 0.375
        output.append(
            {
                "D": D,
                "N_distinct_M": len(by_M),
                "witnesses": len(witnesses),
                "max_M_fiber": max(map(len, by_M.values())),
                "distinct_T": len(by_T),
                "max_T_fiber": max(map(len, by_T.values())),
                "max_(T,r)_fiber": max(map(len, by_Tr.values())),
                "all_squarefull": generic,
                "support_squarefull": support,
                "T_height_integer_count": t_height,
                "N_sqrtD_over_X_float": len(by_M) * math.sqrt(D) / X,
                "shell_weight_over_X_float": weighted / X,
            }
        )
    return output


def main(limit: int) -> None:
    factors = factor_sieve(limit)
    rng = random.Random(1000)
    sample = sorted(set(range(min(100, limit + 1))) | {rng.randrange(limit + 1) for _ in range(128)})
    for a in sample:
        assert dict(factors[a]) == {int(p): int(e) for p, e in sympy.factorint(a * a + 3 * a + 3).items()}
    rows = [cubic_coordinates(a, fs) for a, fs in enumerate(factors)]
    print("EXACT factorization cross-check", len(sample), "points; seed=1000")
    print("REGRESSIONS", json.dumps(regression_ledger(rows), sort_keys=True))

    windows = [x for x in (1000, 3000, 10000, 30000, 100000, 300000, limit) if x <= limit]
    for X in sorted(set(windows)):
        ledger = shell_ledger(X, rows)
        print("WINDOW", X, "shells", len(ledger))
        for item in ledger:
            print("SHELL", json.dumps(item, sort_keys=True))
        total_weight = sum(item["shell_weight_over_X_float"] for item in ledger)
        print("WINDOW_WEIGHT_OVER_X_FLOAT", X, total_weight)

    global_T: dict[int, list[tuple[int, int]]] = collections.defaultdict(list)
    for a in range(1, limit + 1):
        M, _S, _r, _d, T = rows[a]
        if limit + 1 < M:
            global_T[T].append((a, M))
    repeated_T = sorted(
        ((len(points), T, points) for T, points in global_T.items() if len(points) > 1),
        reverse=True,
    )
    print("GLOBAL_T_FIBERS_AT_LIMIT", json.dumps(repeated_T[:12]))


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--limit", type=int, default=300000)
    args = parser.parse_args()
    main(args.limit)
