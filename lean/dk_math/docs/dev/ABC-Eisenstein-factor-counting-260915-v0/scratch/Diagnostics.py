#!/usr/bin/env python3
"""Exact finite Eisenstein diagnostics; no external packages.

Run from lean/dk_math:
  python3 docs/dev/ABC-Eisenstein-factor-counting-260915-v0/scratch/Diagnostics.py

Coordinates (m,n) mean m+n*omega, omega^2+omega+1=0.
The finite scan tests cubic-family values, not realized-large-shell membership.
It is reproducible evidence, not a proof of the general provider theorem.
"""

import argparse
import json
from math import isqrt, prod


def norm(z):
    m, n = z
    return m * m - m * n + n * n


def mul(z, w):
    m, n = z
    c, d = w
    return m * c - n * d, m * d + n * c - n * d


def conjugate(z):
    m, n = z
    return m - n, -n


def quotient(alpha, beta):
    """Integral quotient, or None; implements both lattice divisibilities."""
    divisor = norm(beta)
    if divisor == 0:
        return None
    first, second = mul(alpha, conjugate(beta))
    if first % divisor != 0 or second % divisor != 0:
        return None
    result = first // divisor, second // divisor
    assert mul(beta, result) == alpha
    return result


def factorization(k):
    result = {}
    p = 2
    while p * p <= k:
        while k % p == 0:
            result[p] = result.get(p, 0) + 1
            k //= p
        p += 1
    if k > 1:
        result[k] = result.get(k, 0) + 1
    return result


def coordinates_of_norm(k):
    """Complete enumeration from (2m-n)^2+3n^2=4k."""
    bound = isqrt((4 * k) // 3)
    result = set()
    for n in range(-bound, bound + 1):
        discriminant = 4 * k - 3 * n * n
        root = isqrt(discriminant)
        if root * root != discriminant:
            continue
        for signed_root in (root, -root):
            if (n + signed_root) % 2 == 0:
                m = (n + signed_root) // 2
                assert norm((m, n)) == k
                result.add((m, n))
    return sorted(result)


def shell_norm_packet(a):
    value = a * a + 3 * a + 3
    factors = factorization(value)
    repeated = prod(p ** e for p, e in factors.items() if e >= 2)
    complement = prod(p for p, e in factors.items() if e == 1)
    parity_residual = prod(p for p, e in factors.items() if e >= 2 and e % 2)
    square_root = prod(p ** (e // 2) for p, e in factors.items())
    residual_norm = parity_residual * complement
    assert repeated * complement == value
    assert residual_norm * square_root ** 2 == value
    return value, factors, repeated, complement, parity_residual, square_root


def coefficient_line_solutions(T, gamma):
    """All beta coordinates of norm T on the coefficient-one line for gamma."""
    m, n = gamma
    q = 2 * m * n - n * n
    r = m * m - 2 * m * n
    return [(b, c) for (b, c) in coordinates_of_norm(T) if b * q + c * r == 1]


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--limit", type=int, default=2000)
    args = parser.parse_args()
    assert args.limit >= 0

    # A prescribed divisor can have exactly the right norm and wrong orientation.
    alpha, beta = (3, 1), (2, -1)
    assert norm(alpha) == norm(beta) == 7
    assert quotient(alpha, beta) is None

    # Norm 49 has both a nonsquare-divisible scalar and an actual square.
    norm_seven = coordinates_of_norm(7)
    scalar_square_divisors = [g for g in norm_seven if quotient((7, 0), mul(g, g))]
    assert scalar_square_divisors == []
    assert mul((-3, -1), (-3, -1)) == (8, 5)
    assert norm((8, 5)) == norm((7, 0)) == 49

    sample_rows = []
    failures = []
    landing_counts = {}
    repeated_cases = 0
    odd_repeated_cases = 0
    full_norm_seen = set()
    line_histogram = {}
    max_line_fiber = 0
    max_line_examples = []
    factor_data_total = 0
    gamma_rep_histogram = {}
    for a in range(args.limit + 1):
        value, factors, repeated, complement, r, d = shell_norm_packet(a)
        assert value not in full_norm_seen  # Stronger injectivity is proved in Lean.
        full_norm_seen.add(value)
        assert all((p == 3 and e == 1) or p % 3 == 1 for p, e in factors.items())
        alpha = (a + 2, 1)
        assert value == norm(alpha)
        candidates = coordinates_of_norm(d)
        landings = [(g, quotient(alpha, mul(g, g))) for g in candidates]
        landings = [(g, b) for g, b in landings if b is not None]
        T = r * complement
        gamma_rep_histogram[len(candidates)] = gamma_rep_histogram.get(len(candidates), 0) + 1
        for gamma in candidates:
            fiber = coefficient_line_solutions(T, gamma)
            factor_data_total += len(fiber)
            line_histogram[len(fiber)] = line_histogram.get(len(fiber), 0) + 1
            if len(fiber) > max_line_fiber:
                max_line_fiber = len(fiber)
                max_line_examples = [(a, gamma, fiber)]
            elif len(fiber) == max_line_fiber and len(max_line_examples) < 8:
                max_line_examples.append((a, gamma, fiber))
        if not landings:
            failures.append(a)
        for gamma, beta in landings:
            assert norm(beta) == r * complement
            assert mul(beta, mul(gamma, gamma)) == alpha
        landing_counts[len(landings)] = landing_counts.get(len(landings), 0) + 1
        repeated_cases += repeated > 1
        odd_repeated_cases += r > 1
        if a in (17, 21, 29, 66, 67, 78):
            sample_rows.append({"a": a, "norm": value, "factorization": factors,
                                "M": repeated, "S": complement, "r": r, "d": d,
                                "N_beta": r * complement, "N_gamma": d,
                                "norm_candidates": len(candidates),
                                "landing_candidates": len(landings),
                                "line_fiber_sizes": {str(g): len(coefficient_line_solutions(T, g))
                                                     for g in candidates},
                                "gamma": landings[0][0], "beta": landings[0][1]})

    result = {
        "scope": "all cubic coefficient-one values 0 <= a <= limit; no shell-membership claim",
        "limit": args.limit,
        "number_of_values": args.limit + 1,
        "values_with_repeated_part": repeated_cases,
        "values_with_odd_repeated_valuation": odd_repeated_cases,
        "prescribed_norm_factorization_failures": failures,
        "number_of_landings_histogram": landing_counts,
        "fixed_gamma_T_line_fiber_histogram": line_histogram,
        "fixed_gamma_T_line_fiber_max": max_line_fiber,
        "fixed_gamma_T_line_fiber_max_examples": [
            {"a": a, "gamma": gamma, "beta_solutions": fiber}
            for a, gamma, fiber in max_line_examples],
        "gamma_norm_representation_histogram": gamma_rep_histogram,
        "factor_data_total_including_units": factor_data_total,
        "witness_value_count": args.limit + 1,
        "local_channel_violations": 0,
        "identical_full_norm_pairs": 0,
        "norm_divisibility_counterexample": {"alpha": [3, 1], "beta": [2, -1], "norm": 7},
        "norm_square_counterexample": {"alpha": [7, 0], "norm": 49,
                                       "all_norm_7_candidates": len(norm_seven),
                                       "square_divisors_with_norm_7": scalar_square_divisors},
        "same_norm_actual_square": {"alpha": [8, 5], "gamma": [-3, -1]},
        "samples": sample_rows,
    }
    print(json.dumps(result, indent=2, sort_keys=True))
    assert not failures


if __name__ == "__main__":
    main()
