"""Independent bounded root diagnostics; no output is used as a Lean proof."""
from pathlib import Path
import json
from math import gcd, isqrt

base = Path(__file__).resolve().parent.parent

def prime(n):
    return n >= 2 and all(n % d for d in range(2, isqrt(n)+1))

def row(n):
    ps = [p for p in range(3,n+1) if prime(p) and n % p]
    A = sum(gcd(n,r)==1 and (n*n+r)%2 for r in range(1,2*n+1))
    delta = lambda m: ((n*n+2*n)//m - n*n//m)-((n*n+2*n)//(2*m)-n*n//(2*m))
    raw = lambda m: (n*n+2*n)//m - n*n//m
    W = lambda m: delta(m)-delta(n*m)
    C = lambda p,f: sum(f(p*q) if p==3 else
        f(p*q)-f(3*p*q) if p==5 else
        f(p*q)+f(15*p*q)-f(3*p*q)-f(5*p*q) for q in ps if p<q)
    B = sum(delta(q)-delta(n*q) for q in ps)
    actual = {3:0,5:0,7:0}
    seats = []
    for r in range(1,2*n+1):
        if gcd(n,r)!=1 or (n*n+r)%2==0: continue
        support=[p for p in ps if (n*n+r)%p==0]
        if support and support[0] in actual:
            actual[support[0]] += len(support)-1
            if len(support)>1: seats.append({'r':r,'support':support})
    charges = [C(p,W) for p in [3,5,7]]
    assert charges == list(actual.values())
    odds = [C(p,delta) for p in [3,5,7]]
    rawcharges = [C(p,raw) for p in [3,5,7]]
    floorcharges = [C(p,lambda m:n//m) for p in [3,5,7]]
    # A nested clipped difference can destroy the intersection credit.
    badnat7 = sum(max(0,max(0,W(7*q)-W(21*q))-W(35*q))+W(105*q) for q in ps if q>7)
    unionbound7 = sum(max(0,W(7*q)-W(21*q)-W(35*q)) for q in ps if q>7)
    cumul = [sum(charges[:i]) for i in range(1,4)]
    D = B-A+1
    return dict(n=n,A=A,B2=B,D=D,charges=charges,cumulative=cumul,
                cutoff=next(p for p,c in zip([3,5,7],cumul) if c>=D),
                actual=actual,raw=rawcharges,odd=odds,
                parity_removed=[r-o for r,o in zip(rawcharges,odds)],
                candidate_removed=[o-c for o,c in zip(odds,charges)],
                floor_without_carry=floorcharges,
                odd_carry_net=[o-f for o,f in zip(odds,floorcharges)],
                unionbound_root7=unionbound7,nested_subtraction_root7=badnat7,
                seats=seats)

rows=[row(n) for n in [47,97,127,211,503]]
(base/'logs/root-diagnostics-011.json').write_text(json.dumps(rows,indent=2)+'\n')
for r in rows:
    print({k:v for k,v in r.items() if k!='seats'})
# Smallest prime-anchor counterexample to candidate == odd raw product wave.
for n in range(8,504):
    if not prime(n): continue
    ps=[p for p in range(3,n) if prime(p)]
    found=False
    for p in ps:
        for q in ps:
            if p>=q: continue
            m=p*q
            for r in range(1,2*n+1):
                if (n*n+r)%m==0 and (n*n+r)%2 and gcd(n,r)!=1:
                    print('smallest raw-odd/candidate counterexample:',n,p,q,r)
                    found=True; break
            if found:break
        if found:break
    if found:break
# Smallest prime-anchor instance with root7 intersection credit.
for n in range(11,504):
    if not prime(n):continue
    for q in range(11,n):
        if not prime(q):continue
        rs=[r for r in range(1,2*n+1) if (n*n+r)%(105*q)==0 and
            (n*n+r)%2 and gcd(n,r)==1]
        if rs:
            print('smallest root7 intersection-credit example:',n,q,rs)
            raise SystemExit(0)
