#!/usr/bin/env python3
"""Deterministic finite audit; a scan is not a universal Goldbach proof.

Offsets and prime cutoff match production Lean: 0 <= u < n-1, r*r <= 2*n.
Raw support uses divisibility; proper support additionally excludes endpoint=r.
All reported minima use lexicographic (n,u[,p,q]) order within the stated range.
"""
import argparse
import csv
import json
from fractions import Fraction
from math import comb, gcd, isqrt
from pathlib import Path


def primes_up_to(bound):
    sieve = [True] * (bound + 1)
    if bound >= 0:
        sieve[0] = False
    if bound >= 1:
        sieve[1] = False
    for p in range(2, isqrt(bound) + 1):
        if sieve[p]:
            for k in range(p * p, bound + 1, p):
                sieve[k] = False
    return {p for p, yes in enumerate(sieve) if yes}


def audit(max_center, selected):
    primes = primes_up_to(2 * max_center)
    failures, rows, seats = {}, [], []

    def first(name, condition, payload):
        if condition and name not in failures:
            failures[name] = payload

    for n in range(max_center + 1):
        world = sorted(r for r in primes if r * r <= 2 * n)
        reduced = [r for r in world if r != 2 and n % r]
        counts = dict(n=n, candidates=max(0, n - 1), positive=0, primitive=0,
                      primitive_positive=0, parity=0, prime_pairs=0,
                      covered=0, survivors=0, primitive_covered=0,
                      primitive_survivors=0, parity_covered=0, parity_survivors=0,
                      raw_survivors=0, parity_raw_survivors=0,
                      endpoint_exception_incidences=0, endpoint_exception_seats=0,
                      parity_endpoint_exception_incidences=0,
                      raw_intersection_sum=0, proper_intersection_sum=0,
                      parity_proper_intersection_sum=0, LL=0, LR=0, RR=0,
                      parity_incidence=0, parity_overlap_excess=0,
                      parity_pair_count=0, parity_pair_residual=0,
                      world_size=len(world), reduced_world_size=len(reduced))
        for u in range(max(0, n - 1)):
            a, b = n - u, n + u
            primitive = gcd(n, u) == 1
            parity = primitive and u > 0 and n % 2 != u % 2
            raw_l, raw_r = {r for r in world if a % r == 0}, {r for r in world if b % r == 0}
            left, right = raw_l - {a}, raw_r - {b}
            support = left | right
            survivor = not support
            pair = a in primes and b in primes
            exc = len(raw_l - left) + len(raw_r - right)
            ll, lr, rr = comb(len(left), 2), len(left) * len(right), comb(len(right), 2)
            k = len(support)
            detail = dict(n=n, u=u, left_endpoint=a, right_endpoint=b,
                          primitive=primitive, parity=parity, prime_pair=pair,
                          raw_left=sorted(raw_l), raw_right=sorted(raw_r),
                          proper_left=sorted(left), proper_right=sorted(right),
                          raw_intersection=len(raw_l & raw_r),
                          proper_intersection=len(left & right), LL=ll, LR=lr, RR=rr,
                          endpoint_exceptions=exc)
            if n in selected:
                seats.append(detail)
            counts['positive'] += u > 0
            counts['primitive'] += primitive
            counts['primitive_positive'] += primitive and u > 0
            counts['parity'] += parity
            counts['prime_pairs'] += pair
            counts['covered'] += not survivor
            counts['survivors'] += survivor
            counts['primitive_covered'] += primitive and not survivor
            counts['primitive_survivors'] += primitive and survivor
            counts['parity_covered'] += parity and not survivor
            counts['parity_survivors'] += parity and survivor
            counts['raw_survivors'] += not (raw_l | raw_r)
            counts['parity_raw_survivors'] += parity and not (raw_l | raw_r)
            counts['endpoint_exception_incidences'] += exc
            counts['endpoint_exception_seats'] += exc > 0
            counts['parity_endpoint_exception_incidences'] += parity * exc
            counts['raw_intersection_sum'] += len(raw_l & raw_r)
            counts['proper_intersection_sum'] += len(left & right)
            if parity:
                counts['parity_proper_intersection_sum'] += len(left & right)
                for key, value in [('LL', ll), ('LR', lr), ('RR', rr),
                                   ('parity_incidence', k), ('parity_overlap_excess', max(0, k-1)),
                                   ('parity_pair_count', comb(k, 2)),
                                   ('parity_pair_residual', comb(max(0, k-1), 2))]:
                    counts[key] += value
            checks = {
                'coordinate_coprimality': primitive != (gcd(a, u) == 1),
                'quadratic_boundary': primitive and gcd(a, b) != gcd(a, 2),
                'positive_pair_primitive': u > 0 and pair and not primitive,
                'positive_pair_parity': u > 0 and pair and not parity,
                'center_factor_removal': primitive and any(n % r == 0 for r in raw_l | raw_r),
                'two_removal': n % 2 != u % 2 and 2 in raw_l | raw_r,
                'parity_support_disjoint': parity and bool(left & right),
                'reduced_support_equality': parity and support != support.intersection(reduced),
                'survivor_prime_pair': survivor != pair,
                'LL_LR_RR': parity and comb(k, 2) != ll + lr + rr,
                'primitive_without_parity_gcd_one': primitive and gcd(a, b) != 1,
                'primitive_without_parity_proper_disjoint': primitive and bool(left & right),
                'parity_without_primitive_proper_disjoint': n % 2 != u % 2 and bool(left & right),
                'raw_equals_proper_on_parity': parity and (raw_l != left or raw_r != right),
            }
            for name, failed in checks.items():
                first(name, failed, detail)
            first('first_positive_higher_overlap_primitive', primitive and u > 0 and k >= 3, detail)
            first('first_positive_higher_overlap_parity', parity and k >= 3, detail)
        counts['removed_candidates'] = counts['candidates'] - counts['parity']
        counts['removed_covered'] = counts['covered'] - counts['parity_covered']
        counts['diagonal_survivors'] = int(n in primes)
        assert counts['survivors'] == counts['parity_survivors'] + counts['diagonal_survivors']
        assert counts['removed_candidates'] == counts['removed_covered'] + counts['diagonal_survivors']
        for key, num, den in [('density', 'survivors', 'candidates'),
                              ('primitive_density', 'primitive_survivors', 'primitive'),
                              ('parity_density', 'parity_survivors', 'parity')]:
            counts[key] = str(Fraction(counts[num], counts[den])) if counts[den] else None
        rows.append(counts)
    # Truncated subtraction outside the admissible interval is tested separately.
    for n in range(max_center + 1):
        for u in range(n + 1, max_center + 1):
            if gcd(n, u) == 1:
                a, b = max(0, n - u), n + u
                first('unbounded_quadratic_boundary', gcd(a, b) != gcd(a, 2), dict(n=n, u=u))
    nonempty = [r for r in rows if r['parity']]
    density_worst = sorted(nonempty, key=lambda r: (Fraction(r['parity_density']), r['n']))[:5]
    changes = sorted([r for r in rows if r['n'] >= 2], key=lambda r: (r['removed_candidates'], r['n']))
    summary = dict(max_center=max_center, centers_checked=len(rows),
                   selected_centers=sorted(selected),
                   minima=failures,
                   worst_parity_density=[{k: r[k] for k in ('n', 'parity', 'parity_survivors', 'parity_density')} for r in density_worst],
                   least_candidate_removal=changes[:3], most_candidate_removal=changes[-3:])
    return dict(summary=summary, centers=rows, selected_seats=seats)


def wave_audit(max_center, selected):
    """Each orientation is a residue, not a new escape theorem.

    Full normalization is periodic modulo 2*n*p*q (a valid, sometimes
    nonminimal period). Primitive/parity membership is not well-defined on
    residues modulo the odd number p*q alone. Full-period enumeration is
    deliberately bounded to centers <=40; interval counts cover the full range.
    """
    primes = primes_up_to(isqrt(2 * max_center))
    minima, diagnostics = {}, []
    orientation_tests = full_period_tests = 0

    def first(name, case):
        minima.setdefault(name, case)

    for n in range(2, max_center + 1):
        world = sorted(p for p in primes if p != 2 and p*p <= 2*n)
        normalized = {u for u in range(1, n-1) if gcd(n, u) == 1 and (n-u) % 2}
        for i, p in enumerate(world):
            for q in world[i+1:]:
                modulus = p*q
                # a=n (mod p), a=-n (mod q), using an exact modular inverse.
                a = (n + p * ((-2*n * pow(p, -1, q)) % q)) % modulus
                b = (-a) % modulus
                assert (a % p, a % q) == (n % p, (-n) % q)
                assert (b % p, b % q) == ((-n) % p, n % q)
                assert (a == b) == (n % p == 0 and n % q == 0)
                for left_prime, right_prime, residue in [(p, q, a), (q, p, b)]:
                    orientation_tests += 1
                    raw = list(range(residue, max(0, n-1), modulus))
                    restricted = [u for u in raw if u in normalized]
                    proper = [u for u in restricted
                              if n-u != left_prime and n+u != right_prime]
                    case = dict(n=n, p=left_prime, q=right_prime, residue=residue,
                                modulus=modulus, normalized_candidates=len(normalized),
                                raw_interval=raw, normalized_interval=restricted,
                                proper_normalized_interval=proper)
                    assert n-1 > modulus or len(raw) <= 1
                    assert all(v-u >= modulus for u, v in zip(raw, raw[1:]))
                    assert all(v-u >= 2*modulus for u, v in zip(restricted, restricted[1:]))
                    if len(restricted) > 1:
                        first('multiple_normalized_same_orientation', case)
                    if len(normalized) < modulus and len(restricted) > 1:
                        first('candidate_cardinality_not_geometric_width', case)
                    if restricted != proper:
                        first('raw_LR_endpoint_exception', case)
                    if restricted and n-1 <= modulus:
                        first('occupied_at_most_one_wave', case)
                    if any(v-u == 2*modulus for u, v in zip(proper, proper[1:])):
                        first('sharp_parity_spacing_proper', case)
                    if n <= 40:
                        full_period_tests += 1
                        # residue+k*pq spans one period of length 2*n*pq.
                        count = sum(gcd(n, residue+k*modulus) == 1 and
                                    (n-residue-k*modulus) % 2 == 1
                                    for k in range(2*n))
                        expected = (sum(gcd(k, 2*n) == 1 for k in range(2*n))
                                    if n % p and n % q else 0)
                        assert count == expected
                        case['full_period'] = 2*n*modulus
                        case['normalized_residues_per_orientation'] = count
                    if n in selected:
                        diagnostics.append(case)
    return dict(centers=f'2..{max_center}', interval_orientation_tests=orientation_tests,
                full_period_centers='2..40 (within requested range)',
                full_period_orientation_tests=full_period_tests,
                minima=minima, selected_waves=diagnostics)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--max-center', type=int, default=500)
    parser.add_argument('--select', default='2,3,5,6,12,35,100')
    parser.add_argument('--json', type=Path)
    parser.add_argument('--csv', type=Path)
    args = parser.parse_args()
    if args.max_center < 2:
        parser.error('--max-center must be at least 2')
    selected = {int(x) for x in args.select.split(',') if x}
    data = audit(args.max_center, selected)
    data['waves'] = wave_audit(args.max_center, selected)
    if args.json:
        args.json.write_text(json.dumps(data, indent=2, sort_keys=True) + '\n')
    if args.csv:
        with args.csv.open('w', newline='') as f:
            writer = csv.DictWriter(f, fieldnames=list(data['centers'][0]))
            writer.writeheader()
            writer.writerows(data['centers'])
    print(f"Centers 0..{args.max_center}; exact diagonal/survivor/coverage identities passed")
    for name, case in data['summary']['minima'].items():
        print(f"{name}: n={case['n']}, u={case['u']}")
    print('Worst parity survivor densities:', data['summary']['worst_parity_density'])
    print('CRT interval orientations:', data['waves']['interval_orientation_tests'])
    print('CRT full-period orientations:', data['waves']['full_period_orientation_tests'])
    for name, case in data['waves']['minima'].items():
        print(f"{name}: n={case['n']}, p={case['p']}, q={case['q']}, seats={case['normalized_interval']}")


if __name__ == '__main__':
    main()
