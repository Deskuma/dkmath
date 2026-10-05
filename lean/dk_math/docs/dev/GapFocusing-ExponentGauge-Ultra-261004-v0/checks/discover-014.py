#!/usr/bin/env python3
"""Bounded diagnostics only; production proofs never call this factorization code."""
from math import gcd, isqrt
from collections import Counter
from pathlib import Path
import json

LIMIT = 3000
prime_flags = bytearray(b'\x01') * (LIMIT + 1)
prime_flags[:2] = b'\x00\x00'
for p in range(2, isqrt(LIMIT) + 1):
    if prime_flags[p]:
        prime_flags[p*p:LIMIT+1:p] = b'\x00' * ((LIMIT-p*p)//p+1)
primes = [p for p in range(2,LIMIT+1) if prime_flags[p]]

def row(n):
    cutoff, counts, fibers = isqrt(n), Counter(), Counter()
    small = [p for p in primes if p <= cutoff]
    for r in range(1,2*n+1):
        x = n*n+r
        if x % 2 == 0 or gcd(2*n,x) != 1 or any(x%p == 0 for p in small):
            continue
        counts['R'] += 1
        y, fac = x, []
        for p in primes:
            if p*p > y: break
            if y%p == 0:
                exponent=0
                while y%p == 0: y//=p; exponent+=1
                fac.append((p,exponent))
        if y>1: fac.append((y,1))
        support = [p for p,e in fac if p <= n]
        k=len(support)
        counts['N'+str(k)] += 1
        if k==0:
            assert len(fac)==1 and fac[0][1]==1, (n,r,fac)
        elif k==1:
            p=support[0]
            if x==p**3: counts['cube']+=1
            else:
                assert fac == [(p,1),(x//p,1)] and x//p>n, (n,r,fac)
                counts['cross']+=1; fibers[p]+=1
        elif k==2:
            p,q=support
            assert x in (p*p*q,p*q*q), (n,r,fac)
            counts['repeat']+=1
        elif k==3:
            assert x==support[0]*support[1]*support[2], (n,r,fac)
            counts['triple']+=1
        else: raise AssertionError((n,r,fac))
    d={k:counts[k] for k in ['R','N0','N1','N2','N3','cube','cross','repeat','triple']}
    labels = [p for p in primes if cutoff < p < n and p != 2]
    def odd_window(m):
        return (((n*n+2*n)//m)+1)//2-((n*n//m)+1)//2
    d.update(geometric_capacity_sum=sum(2*n//p+1 for p in labels),
             odd_active_wave_capacity_sum=sum(odd_window(p)-odd_window(n*p) for p in labels),
             n=n, cutoff=cutoff, singleton_fraction=d['N1']/d['R'] if d['R'] else 0,
             max_cross_fiber=max(fibers.values(),default=0),
             dominant_fibers=[dict(p=p,count=c) for p,c in fibers.most_common(10)],
             fibers=[dict(p=p,count=c) for p,c in sorted(fibers.items())])
    assert d['N1']==d['cube']+d['cross'] and d['N2']==d['repeat'] and d['N3']==d['triple']
    assert d['R']==d['N0']+d['cube']+d['cross']+d['repeat']+d['triple']
    assert d['cube']<=1
    return d

rows=[row(n) for n in primes if n>=3]
result=dict(range=[3,LIMIT],anchor_count=len(rows),scope='prime anchors only; no asymptotic inference',
            classification_counterexamples=[], rows=rows)
path=Path(__file__).resolve().parent.parent/'logs'/'discovery-014.json'
path.write_text(json.dumps(result,indent=2)+'\n')
for d in rows:
    print(json.dumps({k:v for k,v in d.items() if k!='fibers'},sort_keys=True))
print('CALIBRATIONS')
for d in rows:
    if d['n'] in [211,503,1009,1013,1019,1021]: print(json.dumps(d,sort_keys=True))
print('SUMMARY',json.dumps(dict(anchors=len(rows), max_singleton_fraction=max(d['singleton_fraction'] for d in rows),
      max_cross_fiber=max(d['max_cross_fiber'] for d in rows),
      max_repeat=max(d['repeat'] for d in rows),max_triple=max(d['triple'] for d in rows))))
