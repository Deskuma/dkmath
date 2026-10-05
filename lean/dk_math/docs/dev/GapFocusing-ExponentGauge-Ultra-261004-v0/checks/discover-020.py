"""Exact finite full-period diagnostics. Computations are not Lean proofs."""
from pathlib import Path
from math import gcd,comb
import json
base=Path(__file__).resolve().parent.parent
prior=json.loads((base/'logs/discovery-019.json').read_text())
rows=[]
for oldrow in prior['rows']:
 n=oldrow['n'];S=oldrow['S'];M=oldrow['M'];K=2*n//M
 old=[q for q in range(2,n+1) if all(q%d for d in range(2,int(q**.5)+1))]
 T=[q for q in old if q not in S]
 B=[r for r in range(1,M+1) if gcd(n*n+r,M)==1]
 columns={r:[r+j*M for j in range(K)] for r in B}
 V=sorted(a for C in columns.values() for a in C)
 support={a:{q for q in old if (n*n+a)%q==0} for a in V}
 fibers={q:[a for a in V if q in support[a]] for q in T}
 edges=[(a,b) for i,a in enumerate(V) for b in V[i+1:] if support[a]&support[b]]
 deleted={a for a,b in edges};R=[a for a in V if a not in deleted]
 family=[];used=set()
 for a in sorted(V,key=lambda a:(bool(support[a]),len(support[a]),a)):
  if not used&support[a]:family.append(a);used|=support[a]
 ceil={q:(K+q-1)//q for q in T};cap=sum(ceil.values())
 max_column_occ=max((sum(q in support[a] for a in C) for q in T for C in columns.values()),default=0)
 norm=n*n+(n-1)*(n-1)
 norm_primes={q for q in old if norm%q==0}
 norm_seats=[a for a in V if support[a]&norm_primes]
 rows.append(dict(norm=norm,norm_old_primes=sorted(norm_primes),norm_supported_seats=len(norm_seats),norm_supported_edges=sum(bool(support[a]&support[b]&norm_primes) for a,b in edges),centered_odd_gap_modulus=oldrow['odd_gap_radical'],centered_odd_gap_fits=oldrow['odd_gap_radical']<=n,n=n,world_kind=oldrow['world_kind'],S=S,M=M,K=K,base_card=len(B),fullTown_card=len(V),tail_size=2*n-K*M,T_card=len(T),minimum_outside_prime=min(T,default=None),vertical_capacity=cap,uniform_sparse=all(K<=q for q in T),uniform_frontier_passes=K<=len(T),vertical_slack=cap-K,actual_support_incidence=sum(len(support[a]) for a in V),prime_fiber_cards={str(q):len(fibers[q]) for q in T},maximum_fiber_card=max(map(len,fibers.values()),default=0),maximum_column_occupancy=max_column_occ,collision_edges=len(edges),fiber_edge_upper=sum(comb(len(f),2) for f in fibers.values()),ceiling_edge_upper=sum(comb(len(B)*ceil[q],2) for q in T),weak_packing_lower=max(0,len(V)-len(edges)),endpoint_deleted_family=R,greedy_disjoint_family=family,old_prime_card=len(old),deletion_consumer_fires=len(old)<len(R),greedy_consumer_fires=len(old)<len(family),edge_slack=len(old)+len(edges)-len(V),two_street_assignment_slack=oldrow['near_incidence']+oldrow['far_ordered_pairs']-len(B),shell_survivor_count=oldrow['shell_survivor_count'],fold_stats=oldrow['fold_stats'],fullTown_survivors=[a for a in V if not support[a]]))
data=dict(range=prior['range'],extra_anchors=prior['extra_anchors'],worlds=prior['worlds'],rows=rows)
(base/'logs/discovery-020.json').write_text(json.dumps(data,indent=2)+'\n')
print('Rows:',len(rows))
print('Strict vertical deficits:',[(r['n'],r['world_kind']) for r in rows if r['vertical_slack']<0])
print('Strict improvement over passing two-street assignment:',[(r['n'],r['world_kind']) for r in rows if r['vertical_slack']<0<=r['two_street_assignment_slack']])
print('Strict edge deficits:',[(r['n'],r['world_kind']) for r in rows if r['edge_slack']<0])
print('n world M K base seats T minq cap incidence maxcol edges weak greedy pi vertical-slack edge-slack')
for r in rows:
 if r['n'] in [3,5,6,8,11,19,29,297,1031]:
  print(*(r[k] for k in ['n','world_kind','M','K','base_card','fullTown_card','T_card','minimum_outside_prime','vertical_capacity','actual_support_incidence','maximum_column_occupancy','collision_edges','weak_packing_lower']),len(r['greedy_disjoint_family']),r['old_prime_card'],r['vertical_slack'],r['edge_slack'])
