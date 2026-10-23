#!/usr/bin/env python3
"""DkMath v4: degree descent, prime-address, loan-completion, and escape for y>1.

All arithmetic is exact (Python int); primes tested by sieve/trial division.
Never interprets a finite search as a proof of general FLT.
Run: python3 DkMath_exponent_gauge_experiment_v4.py
"""
from __future__ import annotations
import argparse,csv,math
from collections import Counter
from pathlib import Path


def primes_upto(limit):
    sieve=bytearray(b'\x01')*(limit+1)
    sieve[0:2]=b'\x00\x00'
    for k in range(2,math.isqrt(limit)+1):
        if sieve[k]: sieve[k*k::k]=b'\x00'*((limit-k*k)//k+1)
    return [k for k in range(2,limit+1) if sieve[k]]

def vq(n,q):
    assert n>0
    e=0
    while n%q==0:
        n//=q;e+=1
    return e

def R(n,x,y):
    assert n>=1 and x>y>0
    return (x**n-y**n)//(x-y)

def nthroot_floor(a,n):
    assert a>=0 and n>0
    lo,hi=0,1 << ((a.bit_length()+n-1)//n)
    while lo<hi:
        m=(lo+hi+1)//2
        if m**n<=a:lo=m
        else: hi=m-1
    return lo

def fmtfactor(a):
    assert a>0
    if a==1:return '1'
    fs=[];v=a
    d=2
    while d*d<=v:
        if v%d==0:
            e=0
            while v%d==0:v//=d;e+=1
            fs.append(f'{d}^{e}' if e>1 else str(d))
        d=3 if d==2 else d+2
    if v>1:fs.append(str(v))
    return ' * '.join(fs)

def save(path,rows,fields):
    with path.open('w',newline='',encoding='utf-8') as f:
        writer=csv.DictWriter(f,fieldnames=fields)
        writer.writeheader();writer.writerows(rows)

def descent_sweep(bound,max_n,out):
    # Include n=2 in the sweep. n-2 is defined only when n>=4.
    pairs=[(x,y) for x in range(2,bound+1) for y in range(1,x) if math.gcd(x,y)==1]
    summaries=[]
    for n in range(3,max_n+1):
        counts=Counter()
        for x,y in pairs:
            s=x+y;g=x-y;r=R(n,x,y);d=s**(n-1)-r
            prev=R(n-1,x,y)
            assert r+d==s**(n-1)
            assert d>0
            assert r+ x*y*R(n-2,x,y)==s*prev
            assert math.gcd(r,prev)==1
            if n>=4: assert math.gcd(r,R(n-2,x,y))==R(math.gcd(n,n-2),x,y)
            assert math.gcd(r,s**(n-1))==math.gcd(r,d)
            if n%2:
                assert math.gcd(r,d)==1
                assert math.gcd(r,s)==1
                counts['no_shared_support']+=1
            else:
                shared=s*math.gcd(n//2,s**(n-2))
                assert math.gcd(r,d)==shared
                assert math.gcd(r,d)>1
                counts['has_shared_support']+=1
            # True integer-power check independent of whether n-th power FLT holds
            if nthroot_floor(r,n)**n==r:counts['r_perfect_nth_power']+=1
            if nthroot_floor(r,n-1)**(n-1)==r:counts['r_perfect_nminus1_power']+=1
            # Some q in original R vanish completely from the completed F for odd n.
        summaries.append(dict(degree=n,primitive_pairs=len(pairs),
            gcd_R_Rprev_one=len(pairs),
            gcd_R_D_one=counts['no_shared_support'],
            gcd_R_D_nontrivial=counts['has_shared_support'],
            R_is_perfect_nth_power=counts['r_perfect_nth_power'],
            R_is_perfect_nminus1_power=counts['r_perfect_nminus1_power']))
    save(out/'DkMath_gauge_v4_sweep.csv',summaries,list(summaries[0]))
    return summaries

def loan_trajectory(out):
    cases=[(5,3,14),(10,1,10),(18,1,8)]
    rows=[]
    for x,y,max_n in cases:
        for n in range(2,max_n+1):
            s=x+y;g=x-y;r=R(n,x,y);d=s**(n-1)-r;f=r+d
            shared=math.gcd(r,d)
            prev=R(n-1,x,y) if n>2 else 1
            assert math.gcd(r,prev)==1
            rows.append(dict(x=x,y=y,degree=n,R=str(r),R_factor=fmtfactor(r),
                D=str(d),complete_F=str(f),complete_F_factor=fmtfactor(f),
                gcd_R_D=shared,gcd_R_next_lower=math.gcd(r,prev),
                normalized_deficit=f'{d}/{f}',
                R_is_n_power=int(nthroot_floor(r,n)**n==r),
                R_is_nminus1_power=int(nthroot_floor(r,n-1)**(n-1)==r)))
    save(out/'DkMath_gauge_v4_trajectory.csv',rows,list(rows[0]))
    return rows

def prime_address(out):
    configs=[(5,3,[2,7,11,17,19,31,43]),(18,1,[2,3,7,13,17,19,37]),(10,1,[2,3,7,11,13,37,41])]
    rows=[]
    for x,y,qs in configs:
        for q in qs:
            # Check q prime by simple small trial division; skip p dividing x or y.
            if any(q%d==0 for d in range(2,math.isqrt(q)+1)):continue
            if x*y%q==0:continue
            a=x*pow(y,-1,q)%q
            order=next(r for r in range(1,q) if pow(a,r,q)==1)
            first=[(n,vq(R(n,x,y),q)) for n in range(2,61) if R(n,x,y)%q==0]
            for n, e in first:
                # For q odd and r>1: LTE on x^r-y^r.
                if q!=2 and order>1:
                    assert n%order==0
                    assert e==vq(x**order-y**order,q)+vq(n//order,q)
                elif order==1:
                    assert n%q==0 # q | x-y and q | R_n implies q | n.
                rows.append(dict(x=x,y=y,q=q,order=order,n=n,vq_R=e,
                    at_new_address=int(n==order),
                    address_multiplier=n//order if order>1 else n,
                    q_divides_gap=int((x-y)%q==0)))
    save(out/'DkMath_gauge_v4_prime_address.csv',rows,
        ['x','y','q','order','n','vq_R','at_new_address','address_multiplier','q_divides_gap'])
    return rows

def escape_extended(Bs,ys,ps,prime_cap,out):
    test_primes=primes_upto(prime_cap)
    rows=[]
    for p in ps:
        for B in Bs:
            small=[q for q in test_primes if q<=B]
            for y in ys:
                if y%p==0:continue
                M=math.prod(q for q in small if q!=p and y%q!=0)
                g=p**(p-1)*M**p
                x=y+g
                assert math.gcd(x,y)==1
                r=R(p,x,y)
                assert r%p==0
                K=r//p
                full=g*r
                # Explicit factorization for the *constructed* small-prime part
                assert full == (p*M)**p * K
                assert all(K%q!=0 for q in small)
                assert all(vq(full,q)==(0 if y%q==0 else p) for q in small)
                gap_lower=x**p-(x-1)**p
                assert y**p<gap_lower, (p,B,y)
                assert (x-1)**p<full<x**p
                # If K were pth power, full would also be pth power, contrary to interval.
                q_hit=None;e_hit=None
                for q in test_primes:
                    if q<=B or K%q:continue
                    exp=vq(K,q)
                    if exp%p:
                        assert q%p==1
                        assert pow(x*pow(y,-1,q)%q,p,q)==1
                        assert (x*pow(y,-1,q))%q != 1
                        q_hit=q;e_hit=exp;break
                rows.append(dict(p=p,B=B,y=y,x_digits=len(str(x)),
                    gcd_xy=math.gcd(x,y),small_primes_checked=len(small),
                    small_prime_nonzero_valuations_all_equal_p=True,
                    q_gt_B_with_vqK_not_multiple_p_guaranteed=True,
                    escaping_q_detected=q_hit or '',escaping_vqK=e_hit or '',
                    gap_more_than_y_power=True))
    save(out/'DkMath_gauge_v4_escape_ygt1.csv',rows,list(rows[0]))
    return rows

def primitive_loan_abc(bound,max_n,out):
    """Exact pairwise-coprime loan triples and parity/square identities."""
    pairs=[(x,y) for x in range(2,bound+1) for y in range(1,x) if math.gcd(x,y)==1]
    counters=Counter();examples=[]
    chosen={(5,3),(18,1),(10,1),(2,1)}
    for x,y in pairs:
        s=x+y
        for n in range(3,max_n+1):
            h=1 if n%2 else s
            rawA=R(n,x,y);rawB=x*y*R(n-2,x,y);rawC=s*R(n-1,x,y)
            assert rawA+rawB==rawC
            assert math.gcd(rawA,rawB)==h
            assert rawA%h==rawB%h==rawC%h==0
            A=rawA//h;B=rawB//h;C=rawC//h
            assert A+B==C and math.gcd(A,B)==math.gcd(A,C)==math.gcd(B,C)==1
            if n%2:
                assert rawC%s**2==0
                assert rawC==s**2*R((n-1)//2,x*x,y*y)
                counters['odd_square_lender']+=1
            else:
                assert rawA//s==R(n//2,x*x,y*y)
                assert rawB//s==x*y*R(n//2-1,x*x,y*y)
                counters['even_degree_halving']+=1
            if (x,y) in chosen:
                examples.append(dict(x=x,y=y,n=n,h=h,A=A,B=B,C=C,
                    A_factor=fmtfactor(A) if n<=10 else '',
                    B_factor=fmtfactor(B) if n<=10 else '',
                    C_factor=fmtfactor(C) if n<=10 else '',
                    c_has_s_squared=int(C%s**2==0)))
            counters['primitive_triples']+=1
    save(out/'DkMath_gauge_v4_primitive_abc.csv',examples,list(examples[0]))
    return counters,examples

def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('--bound',type=int,default=75)
    ap.add_argument('--max-degree',type=int,default=14)
    ap.add_argument('--prime-cap',type=int,default=20000)
    ap.add_argument('--output-dir',type=Path,default=Path(__file__).resolve().parent)
    a=ap.parse_args();assert a.bound>=6 and a.max_degree>=5 and a.prime_cap>=101
    a.output_dir.mkdir(parents=True,exist_ok=True)
    summary=descent_sweep(a.bound,a.max_degree,a.output_dir)
    traj=loan_trajectory(a.output_dir)
    addresses=prime_address(a.output_dir)
    escapes=escape_extended([11,31,97],[1,2,3,4,5,7,11,13,17],[3,5,7],a.prime_cap,a.output_dir)
    abccounts,abcexamples=primitive_loan_abc(a.bound,a.max_degree,a.output_dir)
    for row in summary:print('SWEEP',row)
    print('PRIMITIVE_ABC',dict(abccounts))
    print('ABC_SAMPLES',[(r['n'],r['A'],r['B'],r['C']) for r in abcexamples if (r['x'],r['y'])==(5,3) and r['n']<=7])
    print('PRIME_ADDRESSES',len(addresses))
    print('ESCAPE_TESTS',len(escapes),'DETECTED',sum(bool(r['escaping_q_detected']) for r in escapes))
    for row in escapes:
        if row['y'] in (2,5) and row['B'] in (11,97):
            print('ESCAPE_SAMPLE',row)
    print('TRAJ_SAMPLE',[(r['degree'],r['R_factor'],r['gcd_R_D']) for r in traj if (r['x'],r['y'])==(5,3) and r['degree']<=9])
    print('OUTPUT',a.output_dir)

if __name__=='__main__':main()
