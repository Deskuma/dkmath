"""Bounded exact integer diagnostics. This script is not a Lean proof."""
from pathlib import Path
from math import gcd, prod, isqrt
from collections import Counter
import json
base=Path(__file__).resolve().parent.parent
N=2062
primes=[p for p in range(2,N+1) if all(p%d for d in range(2,isqrt(p)+1))]
def support(x,n):return [p for p in primes if p<=n and x%p==0]
fold_rows={r['n']:r for r in json.loads((base/'logs/discovery-018.json').read_text())['rows']}
rows=[]
for n in list(range(1,301))+[1031]:
 for kind in ['initial','odd']:
  S=[];M=1
  for p in primes:
   if p>n:break
   if kind=='odd' and p==2:continue
   if M*p>n:break
   S.append(p);M*=p
  shell_survivors=[r for r in range(1,2*n+1) if not support(n*n+r,n)]
  fold=fold_rows[n]
  old=[p for p in primes if p<=n];T=[p for p in old if p not in S]
  B=[r for r in range(1,M+1) if gcd(n*n+r,M)==1];shift=[M+r for r in B];town=B+shift
  supports={r:support(n*n+r,n) for r in town}
  occ=Counter((p,q) for r in B for p in supports[r] for q in supports[M+r])
  near=[(p,q) for p in T for q in T if p!=q and p*q<=M]
  far=[(p,q) for p in T for q in T if p!=q and M<p*q]
  used=set();family=[];coveredfamily=[]
  for r in sorted(town,key=lambda r:(not bool(supports[r]),len(supports[r]),r)):
   if not (set(supports[r]) & used):
    family.append(r);used.update(supports[r])
    if supports[r]:coveredfamily.append(r)
  repeats=[dict(p=p,seats=[r for r in town if p in supports[r]]) for p in T if sum(p in supports[r] for r in town)>1]
  original=[r for r in range(1,n+1) if gcd(n,r)==1]
  assert len(B)==sum(gcd(a,M)==1 for a in range(M))
  assert all(gcd(n*n+r,n*n+M+r)==1 for r in B)
  assert all(v<=1 for (p,q),v in occ.items() if p*q>M)
  rows.append(dict(n=n,shell_survivor_count=len(shell_survivors),shell_fully_covered=not shell_survivors,fold_stats={k:fold[k] for k in ['norm','norm_gap_gcd','nontrivial_pair_count','visible_old','visible_fresh','local_gcd_product_valuations']},world_kind=kind,S=S,cutoff=max(S,default=0),M=M,residue_card=len(B),base_card=len(B),shift_card=len(shift),T_card=len(T),town_card=len(town),actual_survivors=[r for r in town if not supports[r]],fully_covered_packets=[r for r in B if supports[r] and supports[M+r]],incidence=sum(occ.values()),near_ordered_pairs=len(near),far_ordered_pairs=len(far),near_incidence=sum(v for (p,q),v in occ.items() if p*q<=M),far_incidence=sum(v for (p,q),v in occ.items() if p*q>M),maximum_pair_occupancy=max(occ.values(),default=0),coprime_pair_count=len(B),greedy_disjoint_family=family,covered_disjoint_family=coveredfamily,old_prime_card=len(old),original_n_packet_count=len(original),capacity_slack=len(near)+len(far)-len(B),support_reuse=repeats,odd_gap_radical=prod(p for p in primes if p!=2 and p<2*n)))
reuse=next(r for r in rows if r['M']>1 and r['support_reuse'])
maxpressure=max((r for r in rows if r['M']>1),key=lambda r:r['incidence']/r['base_card'])
minslack=min((r for r in rows if r['M']>1),key=lambda r:r['capacity_slack'])
data=dict(range=[1,300],extra_anchors=[1031],worlds=['initial','odd'],rows=rows,first_support_reuse=reuse,maximum_incidence_pressure=maxpressure,minimum_direction_slack=minslack)
(base/'logs/discovery-019.json').write_text(json.dumps(data,indent=2)+'\n')
print('rows',len(rows),'first support reuse',reuse['n'],reuse['world_kind'],reuse['M'],reuse['support_reuse'])
print('max incidence pressure',maxpressure['n'],maxpressure['world_kind'],maxpressure['incidence'],maxpressure['base_card'])
print('min direction slack',minslack['n'],minslack['world_kind'],minslack['capacity_slack'])
for r in rows:
 if r['n'] in [5,6,8,11,19,29,297,1031]:
  print(r['n'],r['world_kind'],r['M'],r['base_card'],r['T_card'],r['incidence'],r['near_ordered_pairs'],r['far_ordered_pairs'],r['maximum_pair_occupancy'],len(r['greedy_disjoint_family']),r['old_prime_card'])
