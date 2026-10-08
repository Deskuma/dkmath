#!/usr/bin/env python3
"""Finite quotient routing diagnostics. This script supplies no Lean proof."""
from pathlib import Path
from math import isqrt, gcd
from collections import Counter, defaultdict
import json

base = Path(__file__).resolve().parent.parent
old = json.loads((base/'logs/discovery-014.json').read_text())
LIMIT = 3000
primes = []
for k in range(2, LIMIT+1):
    if all(k%p for p in primes if p*p<=k): primes.append(k)

def factors(q):
    out=[]
    for p in primes:
        if p*p>q: break
        if q%p==0:
            while q%p==0: q//=p
            out.append(p)
    if q>1: out.append(q)
    return out

def raw(n):
    labels=[p for p in primes if isqrt(n)<p<=n and p!=2 and n%p]
    owners=[]
    seats=defaultdict(list)
    for p in labels:
        c=Counter(); rejects=[]
        for q in range(n*n//p+1, (n*n+2*n)//p+1):
            if gcd(2*n,q)!=1: continue
            assert q>n and q>1
            c['total']+=1
            fs=factors(q)
            if len(fs)==1 and fs[0]==q:
                c['cross']+=1
            elif min(fs)<=isqrt(n):
                c['rejected']+=1; rejects.append(dict(q=q,small_prime=min(fs)))
            else:
                support=set(fs+[p]); seats[p*q].append(dict(p=p,q=q))
                if len(support)==1: assert q==p*p; c['cube_mass']+=1
                elif len(support)==2: c['repeat_mass']+=1
                elif len(support)==3: c['triple_mass']+=1
                else: raise AssertionError((n,p,q,fs))
            assert c['total']==sum(c[k] for k in ['cross','rejected','cube_mass','repeat_mass','triple_mass'])
        owners.append(dict(p=p,**{k:c[k] for k in ['total','cross','rejected','cube_mass','repeat_mass','triple_mass']},rejects=rejects))
    return owners,seats

rows=[]
for d in old['rows']:
    n=d['n']; owners,_=raw(n)
    sums={k:sum(o[k] for o in owners) for k in ['total','cross','rejected','cube_mass','repeat_mass','triple_mass']}
    assert sums['cross']==d['cross'] and sums['cube_mass']==d['cube']
    assert sums['repeat_mass']==2*d['repeat'] and sums['triple_mass']==3*d['triple']
    assert sums['total']==d['odd_active_wave_capacity_sum']
    total=sums['total']; comp=d['cube']+2*d['repeat']+3*d['triple']
    small_lower=sum(1 for o in owners for rq in o['rejects'] if any(rq['q']%u==0 for u in [3,5,7] if u<=isqrt(n)))
    residual=total-comp-sums['rejected']
    assert residual==d['cross']
    row=dict(n=n,R=d['R'],cube=d['cube'],repeated=d['repeat'],triple=d['triple'],**sums,
      residual=residual,rough_incidence=d['cross']+comp,
      three_prime_lower=small_lower,
      three_prime_cross_bound=total-comp-small_lower,
      three_prime_budget_holds=total<d['R']+d['repeat']+2*d['triple']+small_lower,
      three_prime_plain_budget_holds=total<d['R']+small_lower,
      cross_fraction=d['cross']/total if total else 0,
      repeated_share=sums['repeat_mass']/total if total else 0,
      triple_share=sums['triple_mass']/total if total else 0,
      rejected_share=sums['rejected']/total if total else 0,
      largest_owner_residual=max((o['cross'] for o in owners),default=0),
      cross_bound_without_rejection=total-comp,
      deficit_without_rejection=max(0,total-d['repeat']-2*d['triple']-d['R']),
      required_rejected_lower=max(0,total-d['repeat']-2*d['triple']-d['R']+1),
      near_total=sum(o['total'] for o in owners if o['p']<=2*isqrt(n)),
      far_total=sum(o['total'] for o in owners if o['p']>2*isqrt(n)),
      owners=[{k:v for k,v in o.items() if k!='rejects'} for o in owners])
    rows.append(row)
    print(json.dumps({k:v for k,v in row.items() if k!='owners'},sort_keys=True))
first_rejected=first_multi=first_prime_multi=None
for n in range(1,101):
    owners,seats=raw(n)
    if first_rejected is None:
        for o in owners:
            if o['rejects']:
                first_rejected=dict(n=n,p=o['p'],**o['rejects'][0]); break
    if first_multi is None:
        for point,os in sorted(seats.items()):
            if len(os)>1: first_multi=dict(n=n,point=point,owners=os); break
    if n in primes and first_prime_multi is None:
        for point,os in sorted(seats.items()):
            if len(os)>1: first_prime_multi=dict(n=n,point=point,owners=os); break
    if first_rejected and first_multi and first_prime_multi: break
assert first_rejected==dict(n=11,p=5,q=27,small_prime=3)
assert first_multi==dict(n=8,point=75,owners=[dict(p=3,q=25),dict(p=5,q=15)])
assert first_prime_multi==dict(n=13,point=175,owners=[dict(p=5,q=35),dict(p=7,q=25)])
summary=dict(range=[3,LIMIT],anchor_count=len(rows),scope='finite odd prime anchors; no asymptotics',
 smallest_rejected=first_rejected,smallest_multiowner=first_multi,smallest_prime_multiowner=first_prime_multi,
 finite_three_prime_successes=[d['n'] for d in rows if d['three_prime_budget_holds']],
 new_successes_without_rejection=[d['n'] for d in rows if d['total']<d['R']+d['repeated']+2*d['triple']],
 hardest_deficit=max(rows,key=lambda d:d['deficit_without_rejection'])['n'],
 max_cross_fraction=max(d['cross_fraction'] for d in rows),
 max_owner_residual=max(d['largest_owner_residual'] for d in rows),rows=rows)
(base/'logs/discovery-015.json').write_text(json.dumps(summary,separators=(',', ':'))+'\n')
print('SUMMARY',json.dumps({k:v for k,v in summary.items() if k!='rows'},sort_keys=True))

# The next-basis probe is preserved separately from kernel-checked endpoints.
next_rows=[]
for d in rows:
    if d['three_prime_budget_holds']: continue
    n=d['n']
    J4=sum(1 for o in d['owners'] for q in range(n*n//o['p']+1,(n*n+2*n)//o['p']+1)
           if gcd(2*n,q)==1 and any(q%u==0 for u in [3,5,7,11]))
    next_rows.append(dict(n=n,total=d['total'],R=d['R'],repeated=d['repeated'],triple=d['triple'],
        J3=d['three_prime_lower'],J4=J4,required=d['required_rejected_lower'],
        passes=J4>=d['required_rejected_lower']))
(base/'logs/next-basis-015.json').write_text(json.dumps(dict(
    scope='diagnostic next-step probe only; no kernel endpoint',basis=[3,5,7,11],rows=next_rows),indent=2)+'\n')
