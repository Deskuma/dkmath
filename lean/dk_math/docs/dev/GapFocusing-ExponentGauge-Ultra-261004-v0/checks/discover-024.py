"""Actual endpoint sources, finite products, and exact integer power capacities."""
from pathlib import Path
from math import gcd,isqrt,prod
from collections import Counter
import json,csv
base=Path(__file__).resolve().parent.parent

def exponent_budget(B,x):
    assert B>=2 and x>=1
    e,p=0,1
    while p*B<=x:e,p=e+1,p*B
    return e

rows=[];seats=[];examples={};counterexamples={}
old=json.loads((base/'logs/discovery-023.json').read_text())['rows']
geometry=json.loads((base/'logs/discovery-020.json').read_text())['rows']
for r,g in zip(old,geometry,strict=True):
    n,S,M,K=r['n'],set(r['S']),g['M'],g['K']
    P=max(S,default=0)
    initial=S=={q for q in range(2,P+1) if all(q%d for d in range(2,isqrt(q)+1))}
    if r['world_kind']=='initial':assert initial
    B=max(2,P+1) if initial else 2
    T={q for q in range(2,n+1) if q not in S and all(q%d for d in range(2,isqrt(q)+1))}
    V={a+j*M for a in range(1,M+1) if gcd(n*n+a,M)==1 for j in range(K)}
    f={a:{q for q in T if (n*n+a)%q==0} for a in V}
    F={q:{a for a in V if q in f[a]} for q in T}
    A={q for q in T if F[q]}
    # Minimal k with shell <= B^(k+1); deleted source.card < k.
    k,p=0,B
    while p<(n+1)**2:k,p=k+1,p*B
    uniform=max(0,k-1)
    result=dict(n=n,world_kind=r['world_kind'],S=sorted(S),P=P,initial_cutoff_valid=initial,
                power_base=B,uniform_k=k,uniform_source_capacity=uniform)
    for side,extreme in [('left',max),('right',min)]:
        end={q:extreme(F[q]) for q in A}
        C={a:{q for q in f[a] if end[q]!=a} for a in V}
        D={a for a in V if C[a]};R=V-D
        term={a:{q for q in f[a] if end[q]==a} for a in V}
        missing={q for q in A if end[q] in D}
        retained=sum(max(0,len(f[a])-1) for a in R)
        local_total=0;shared=0;maxterm=0;depth_improvements=0
        for a in sorted(D):
            t,c=term[a],C[a];point=n*n+a;s=f[a]
            e=exponent_budget(B,point);capacity=e-1
            tp,cp,sp=prod(t),prod(c),prod(s)
            assert t.isdisjoint(c) and t|c==s and c and point%sp==0 and tp*cp==sp
            assert B**len(s)<=sp<=point<(n+1)**2 and len(t)<=capacity and len(s)-1<=capacity
            assert all(q>P for q in s) if initial else True
            seat=dict(n=n,world_kind=r['world_kind'],P=P,initial_cutoff_valid=initial,side=side,
                      a=a,complete_point=point,power_base=B,support=sorted(s),terminal=sorted(t),continuing=sorted(c),
                      support_card=len(s),terminal_card=len(t),continuing_card=len(c),terminal_product=tp,
                      continuing_product=cp,support_product=sp,lower_power=B**len(s),
                      initial_lower_power=(P+1)**len(s) if initial else None,
                      local_source_capacity=capacity,uniform_source_capacity=uniform,
                      capacity_improves_support_minus_one=capacity<len(s)-1,
                      continuing_aware_capacity=e-len(c),
                      continuing_aware_improves_support_minus_one=e-len(c)<len(s)-1)
            assert len(t)<=seat['continuing_aware_capacity']
            seats.append(seat);local_total+=capacity;shared+=len(t)>=2;maxterm=max(maxterm,len(t))
            depth_improvements+=seat['continuing_aware_improves_support_minus_one']
            if len(t)>=2:examples.setdefault('first_shared',seat)
            if n in [297,1031] and initial and side=='left':
                key=str(n)+'_largest_terminal'
                if key not in examples or len(t)>examples[key]['terminal_card']:examples[key]=seat
            if n==297 and initial and side=='left' and a==44:examples['297_branching']=seat
            if capacity>len(s)-1:counterexamples.setdefault('product_capacity_strictly_weaker',seat)
        sumterm=sum(len(term[a]) for a in D)
        assert sumterm==len(missing)==r[side]['unrepresented']
        assert sumterm+retained==r[side]['loss']
        existing_excess=sum(max(0,len(s)-1) for s in f.values())
        assert existing_excess<=local_total+retained and existing_excess<=len(D)*uniform+retained
        result[side]=dict(missing=len(missing),sum_terminal=sumterm,max_terminal=maxterm,
                          multi_source_seats=shared,deleted=len(D),retained_excess=retained,
                          local_product_loss_upper=local_total+retained,
                          uniform_product_loss_upper=len(D)*uniform+retained,
                          existing_loss=r[side]['loss'],existing_support_excess=existing_excess,
                          continuing_aware_local_improvements=depth_improvements,
                          exact_source_residual=sumterm-len(missing))
    result['better_loss']=r['better_loss']
    result['survivor_capacity']=r['survivor_capacity']
    result['product_better_loss_upper']=min(result[s]['local_product_loss_upper'] for s in ['left','right'])
    result['product_survivor_capacity']=result['product_better_loss_upper']+r['T']-r['A']<r['U']
    assert not result['product_survivor_capacity'] or result['survivor_capacity']
    rows.append(result)
seat_file=base/'logs/deleted-seats-024.csv'
with seat_file.open('w',newline='') as stream:
    writer=csv.DictWriter(stream,fieldnames=list(seats[0]))
    writer.writeheader()
    for seat in seats:
        writer.writerow({k:';'.join(map(str,v)) if isinstance(v,list) else v for k,v in seat.items()})
out=dict(rows=rows,seats_file=seat_file.name,examples=examples,counterexamples=counterexamples,
         counts=dict(worlds=len(rows),deleted_records=len(seats),
                     simple_local_improvements=sum(s['capacity_improves_support_minus_one'] for s in seats),
                     continuing_aware_improvements=sum(s['continuing_aware_improves_support_minus_one'] for s in seats),
                     product_capacity_worlds=sum(r['product_survivor_capacity'] for r in rows),
                     existing_capacity_worlds=sum(r['survivor_capacity'] for r in rows)))
(base/'logs/discovery-024.json').write_text(json.dumps(out,indent=2)+'\n')
print(out['counts'])
for key,seat in examples.items():print(key,seat)
for r in rows:
    if r['n'] in [29,297,1031] and r['initial_cutoff_valid']:print('anchor',r)
print('counterexamples',counterexamples)
