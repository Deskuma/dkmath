#!/usr/bin/env python3
"""DkMath exponent-gauge numerical experiment v2.

Research: R_n(x,y)=(x^n-y^n)/(x-y), D_n=(x+y)^(n-1)-R_n,
          B_n=xy*R_{n-2} (n>=3, R_1=1), and prime valuation checks.
For primitive positive pairs 1<=y<x<=bound, exact integer arithmetic only.

Example:
  python3 DkMath_exponent_gauge_experiment_v2.py --bound 140 --max-degree 12

Does not claim to prove FLT; this tests conditional arithmetic constraints.
"""
import argparse
import csv
from collections import Counter
from math import gcd
from pathlib import Path


def R(n, x, y):
    assert n >= 1 and x > y > 0
    return (x**n-y**n)//(x-y)


def kth_root_exact(a, n):
    if a < 0 or n <= 0:
        raise ValueError('invalid root input')
    if a < 2:
        return a
    lo, hi = 1, 1 << ((a.bit_length() + n-1)//n)
    while lo <= hi:
        mid = (lo+hi)//2
        p = mid**n
        if p == a:
            return mid
        if p < a:
            lo = mid+1
        else:
            hi = mid-1
    return None


def primes_through(limit):
    buf = bytearray(b'\x01') * (limit+1)
    buf[0:2] = b'\x00\x00'
    for p in range(2, int(limit**0.5)+1):
        if buf[p]:
            buf[p*p::p] = b'\x00' * (((limit-p*p)//p)+1)
    return [p for p, flag in enumerate(buf) if flag]


def valuations_and_first_obstruction(a, n, primes):
    """First p<=limit with 0 < v_p(a) mod n; not full factorization."""
    original = a
    first = None
    count = 0
    for p in primes:
        if a % p:
            continue
        v = 0
        while a % p == 0:
            a //= p
            v += 1
        if v % n:
            count += 1
            if first is None:
                first = (p, v)
        if a == 1:
            break
    return first, count


def val(a,p):
    if a == 0:
        return None
    v=0
    while a%p==0:
        a//=p
        v+=1
    return v


def write_rows(path, rows, fields):
    with path.open('w', encoding='utf-8', newline='') as f:
        w=csv.DictWriter(f, fieldnames=fields)
        w.writeheader()
        w.writerows(rows)


def execute(bound, max_degree, prime_bound, out):
    assert bound>=3 and max_degree>=4 and prime_bound>=2
    out.mkdir(parents=True, exist_ok=True)
    primes=primes_through(prime_bound)
    pairs=[(x,y) for x in range(2,bound+1) for y in range(1,x) if gcd(x,y)==1]
    counts=[]
    witness=[]
    uncertified=[]
    compensation=[]
    for n in range(3, max_degree+1):
        s_count=Counter()
        for x,y in pairs:
            s=x+y
            a=R(n,x,y)
            prev=R(n-1,x,y)
            prev2=R(n-2,x,y)
            debt=s**(n-1)-a
            borrow=x*y*prev2
            g1=gcd(a,prev)
            g2=gcd(a,prev2)
            gb=gcd(a,borrow)
            gd=gcd(a,debt)
            formula_gd=1 if n%2 else s*gcd(n//2,s**(n-2))
            assert debt>0
            assert a+debt == s**(n-1)
            assert a+borrow == s*prev
            assert g1==1
            assert g2==(1 if n%2 else s)
            assert gb==g2
            assert gd==formula_gd
            assert gcd(a,x*y)==1
            assert gcd(a,x-y)==gcd(x-y,n)
            s_count['all_rules_verified']+=1
            cp=kth_root_exact(a,n)
            if cp is not None:
                s_count['cofactor_exact_nth_power']+=1
                witness.append(dict(degree=n,x=x,y=y,R=a,R_root=cp,
                                    x_minus_y=x-y,full_difference=(x-y)*a,
                                    full_difference_exact_nth_power=bool(kth_root_exact((x-y)*a,n) is not None)))
            full=(x-y)*a
            # Look for an exponent prime q whose valuation is incomplete in
            # each factor but completed in the product: a genuine 'loan'.
            for q in primes:
                if q > n:
                    break
                if n % q != 0:
                    continue
                vg,vr=val(x-y,q),val(a,q)
                if vg and vr and vg % n and vr % n and (vg+vr) % n == 0:
                    compensation.append(dict(degree=n,x=x,y=y,q=q,
                                             valuation_gap=vg,valuation_R=vr,
                                             valuation_full=vg+vr,
                                             gap=x-y,R=a,full=full))
            cofactor_first, _ = valuations_and_first_obstruction(a,n,primes)
            full_first, _ = valuations_and_first_obstruction(full,n,primes)
            if cofactor_first:
                s_count['cofactor_cert_by_small_prime']+=1
            if full_first:
                s_count['full_difference_cert_by_small_prime']+=1
            if not full_first:
                s_count['full_uncertified_by_small_prime']+=1
                if sum(row['degree']==n for row in uncertified)<8:
                    uncertified.append(dict(degree=n,x=x,y=y,R=a,x_minus_y=x-y,
                                            full_difference=full,
                                            cofactor_first_cert_q=cofactor_first[0] if cofactor_first else '',
                                            cofactor_first_cert_v=cofactor_first[1] if cofactor_first else '',
                                            note=f'No obstruction found among primes <= {prime_bound}; not an existence proof'))
        counts.append(dict(degree=n,primitive_pairs=len(pairs),
                           gcd_adjacent_coprime_verified=s_count['all_rules_verified'],
                           gcd_two_step_rule_verified=s_count['all_rules_verified'],
                           gcd_debt_rule_verified=s_count['all_rules_verified'],
                           cofactor_exact_nth_power=s_count['cofactor_exact_nth_power'],
                           cofactor_cert_q_le_bound=s_count['cofactor_cert_by_small_prime'],
                           full_difference_cert_q_le_bound=s_count['full_difference_cert_by_small_prime'],
                           full_difference_uncertified_q_le_bound=s_count['full_uncertified_by_small_prime']))
    trajectory=[]
    # contrast the familiar primitive pair and the smallest exact-cube cofactor
    for x,y in ((5,3),(18,1)):
        s=x+y
        for n in range(2,max_degree+1):
            a=R(n,x,y)
            debt=s**(n-1)-a
            borrow=(x*y*R(n-2,x,y)) if n>=3 else 0
            base=dict(pair=f'{x},{y}',degree=n,x=x,y=y,s=x+y,
                      R=a,debt=debt,borrow=borrow,
                      gcd_R_debt=gcd(a,debt),
                      gcd_R_Rprev=gcd(a,R(n-1,x,y)) if n>=3 else '',
                      gcd_R_Rprev2=gcd(a,R(n-2,x,y)) if n>=3 else '',
                      gcd_R_borrow=gcd(a,borrow) if n>=3 else '',
                      v2_R=val(a,2),v3_R=val(a,3),v7_R=val(a,7),
                      v17_R=val(a,17),
                      full=(x-y)*a,
                      v2_full=val((x-y)*a,2),v3_full=val((x-y)*a,3),
                      v7_full=val((x-y)*a,7),v17_full=val((x-y)*a,17))
            trajectory.append(base)
    # Prime-address phase experiment on (5,3): prime factors recur by degree.
    phase=[]
    for n in range(1,86):
        a=R(n,5,3)
        observed_2=val(a,2); observed_7=val(a,7); observed_17=val(a,17)
        expected_2=(3+val(n//2,2)) if n%2==0 else 0
        expected_7=(2+val(n//3,7)) if n%3==0 else 0
        expected_17=(1+val(n//4,17)) if n%4==0 else 0
        assert (observed_2,observed_7,observed_17)==(expected_2,expected_7,expected_17)
        phase.append(dict(degree=n, v2_R=observed_2,expected_v2=expected_2,
                          v7_R=observed_7,expected_v7=expected_7,
                          v17_R=observed_17,expected_v17=expected_17))
    write_rows(out/'DkMath_gauge_v2_prime_address.csv',phase,list(phase[0]))
    write_rows(out/'DkMath_gauge_v2_compensation.csv',compensation,list(compensation[0]))
    write_rows(out/'DkMath_gauge_v2_summary.csv',counts,list(counts[0]))
    write_rows(out/'DkMath_gauge_v2_power_witnesses.csv',witness,
               ['degree','x','y','R','R_root','x_minus_y','full_difference','full_difference_exact_nth_power'])
    write_rows(out/'DkMath_gauge_v2_uncertified.csv',uncertified,
               ['degree','x','y','R','x_minus_y','full_difference','cofactor_first_cert_q','cofactor_first_cert_v','note'])
    write_rows(out/'DkMath_gauge_v2_trajectory.csv',trajectory,list(trajectory[0]))
    print(f'Tested {len(pairs)} primitive pairs, 3<=n<={max_degree}, primes<={prime_bound}.')
    print('n, exact_R_nth, small_prime_R_certificate, small_prime_full_certificate, full_not_certified')
    for row in counts:
        print(*(row[k] for k in ['degree','cofactor_exact_nth_power',
            'cofactor_cert_q_le_bound','full_difference_cert_q_le_bound',
            'full_difference_uncertified_q_le_bound']),sep=',')
    print('\nCOMPENSATION COUNTS BY DEGREE (valuation loan at q|n)')
    print(dict(sorted(Counter(row['degree'] for row in compensation).items())))
    print('\nFirst 12 cofactor perfect-power witnesses:')
    for row in witness[:12]:print(row)
    print('\nSaved CSV files in',out)
    return counts,witness,trajectory,uncertified

if __name__=='__main__':
    parser=argparse.ArgumentParser()
    parser.add_argument('--bound',type=int,default=140)
    parser.add_argument('--max-degree',type=int,default=12)
    parser.add_argument('--prime-bound',type=int,default=251)
    parser.add_argument('--output-dir',type=Path,default=Path(__file__).resolve().parent)
    p=parser.parse_args()
    execute(p.bound,p.max_degree,p.prime_bound,p.output_dir)
