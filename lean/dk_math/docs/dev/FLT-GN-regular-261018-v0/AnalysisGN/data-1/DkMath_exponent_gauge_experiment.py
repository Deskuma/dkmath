#!/usr/bin/env python3
"""DkMath: power-difference cofactor / completion-debt numerical audit.

No floating-point arithmetic or external dependencies.
Example:
    python3 DkMath_exponent_gauge_experiment.py --bound 80 --near-bound 150
"""
import argparse
import bisect
import csv
import math
from pathlib import Path


def cofactor(n: int, x: int, y: int) -> int:
    assert n >= 2 and x > y > 0
    numerator = x**n - y**n
    assert numerator % (x-y) == 0
    return numerator // (x-y)


def exact_kth_root(value: int, k: int) -> int | None:
    """Return integer root iff value is an exact kth power."""
    if value < 0 or k < 1:
        raise ValueError('nonnegative value and k>=1 required')
    if value == 0:
        return 0
    lo, hi = 1, 1 << ((value.bit_length() + k - 1) // k)
    while lo <= hi:
        mid = (lo + hi) // 2
        candidate = mid**k
        if candidate == value:
            return mid
        if candidate < value:
            lo = mid + 1
        else:
            hi = mid - 1
    return None


def write_csv(filename: Path, fields: list[str], rows: list[dict]):
    with filename.open('w', encoding='utf-8', newline='') as handle:
        writer = csv.DictWriter(handle, fieldnames=fields)
        writer.writeheader()
        writer.writerows(rows)


def experiment(bound: int, near_bound: int, max_degree: int, output_dir: Path):
    output_dir.mkdir(parents=True, exist_ok=True)
    pairs = [(x, y) for x in range(2, bound + 1)
             for y in range(1, x) if math.gcd(x, y) == 1]
    summary = []
    for n in range(2, max_degree + 1):
        coprime_debt = 0
        full_cofactor_powers = 0
        max_common = 0
        for x, y in pairs:
            r = cofactor(n, x, y)
            d = (x + y)**(n - 1) - r
            assert d >= 0 and (x + y)**(n-1) == r + d
            common = math.gcd(r, d)
            if common == 1:
                coprime_debt += 1
            max_common = max(max_common, common)
            if n > 2 and exact_kth_root(r, n - 1) is not None:
                full_cofactor_powers += 1
        summary.append(dict(degree=n, primitive_pairs=len(pairs),
                            gcd_R_D_is_1=coprime_debt,
                            R_is_exact_degree_minus_1_power=(full_cofactor_powers if n > 2 else 'not_applicable'),
                            max_gcd_R_D=max_common))

    x, y = 5, 3
    descent = []
    for n in range(2, max_degree + 1):
        r = cofactor(n, x, y)
        d = (x+y)**(n-1)-r
        correction = x*y*cofactor(n-2, x, y) if n >= 4 else (x*y if n == 3 else 0)
        if n >= 3:
            assert (r + correction) % (x+y) == 0
            assert (r + correction) // (x+y) == (x+y if n == 3 else cofactor(n-1, x, y))
        descent.append(dict(degree=n, x=x, y=y, R=r, D=d,
                            completion=(x+y)**(n-1),
                            gcd_R_D=math.gcd(r,d),
                            descent_correction=correction))

    near_misses = []
    upper_power_base = 2 * near_bound + 1
    for n in range(3, min(max_degree,8)+1):
        powers = [z**n for z in range(1, upper_power_base + 1)]
        best = None
        matches = []
        for a in range(2, near_bound+1):
            for b in range(a, near_bound+1):
                if math.gcd(a,b) != 1:
                    continue
                s = a**n + b**n
                idx = bisect.bisect_left(powers,s)
                for j in (idx-1,idx):
                    if not (0 <= j < len(powers)) or j+1 <= b:
                        continue
                    z = j+1
                    signed = z**n - s
                    err = abs(signed)
                    if best is None or err < best:
                        best = err
                        matches = [(a,b,z,signed)]
                    elif err == best:
                        matches.append((a,b,z,signed))
        for a,b,z,signed in matches:
            near_misses.append(dict(degree=n, a=a, b=b, z=z,
                                    signed_delta_z_power_minus_sum=signed,
                                    absolute_delta=abs(signed)))
    write_csv(output_dir/'DkMath_exponent_gauge_summary.csv',list(summary[0].keys()),summary)
    write_csv(output_dir/'DkMath_exponent_gauge_descent.csv',list(descent[0].keys()),descent)
    write_csv(output_dir/'DkMath_exponent_gauge_nearmiss.csv',list(near_misses[0].keys()),near_misses)
    print('SUMMARY (x>y>=1, gcd(x,y)=1, x<=%d)' % bound)
    for row in summary:
        print(row)
    print('\nDESCENT SAMPLE (x,y)=(5,3)')
    for row in reversed(descent):
        print(row)
    print('\nNEAR MISSES (a>=2, b>=a, gcd(a,b)=1, z>b, a,b<=%d)' % near_bound)
    for row in near_misses:
        print(row)
    print('\nCSV saved in:', output_dir)


if __name__ == '__main__':
    parser=argparse.ArgumentParser()
    parser.add_argument('--bound',type=int,default=80)
    parser.add_argument('--near-bound',type=int,default=150)
    parser.add_argument('--max-degree',type=int,default=10)
    parser.add_argument('--output-dir',type=Path,default=Path('.'))
    args=parser.parse_args()
    if args.bound<2 or args.near_bound<2 or args.max_degree<3:
        parser.error('bound>=2, near-bound>=2, max-degree>=3 required')
    experiment(args.bound, args.near_bound, args.max_degree, args.output_dir)
