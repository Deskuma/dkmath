"""Deletion orientation and fiber structure diagnostics, never proof input."""
from pathlib import Path
from math import gcd,isqrt
import json
base=Path(__file__).resolve().parent.parent
old=json.loads((base/'logs/discovery-020.json').read_text())
rows=[];structure=None
for r in old['rows']:
 n=r['n'];M=r['M'];K=r['K'];S=r['S']
 primes=[q for q in range(2,n+1) if all(q%d for d in range(2,isqrt(q)+1))]
 B=[a for a in range(1,M+1) if gcd(n*n+a,M)==1]
 V={a+j*M for a in B for j in range(K)}
 fibers={q:{a for a in V if (n*n+a)%q==0} for q in primes}
 leftQ={q:F-{max(F)} if F else set() for q,F in fibers.items()}
 rightQ={q:F-{min(F)} if F else set() for q,F in fibers.items()}
 D=set().union(*leftQ.values());Dright=set().union(*rightQ.values())
 R=V-D;Rright=V-Dright
 assert R==set(r['endpoint_deleted_family'])
 def cert(R):
  return all(1<=a<=2*n for a in R) and all(len(R&F)<=1 for F in fibers.values()) and len(primes)<len(R)
 assert all(len(R&F)<=1 and len(Rright&F)<=1 for F in fibers.values())
 raw=sum(max(0,len(F)-1) for F in fibers.values())
 row=dict(n=n,world_kind=r['world_kind'],S=S,M=M,K=K,town_card=len(V),old_prime_card=len(primes),edge_card=r['collision_edges'],left_deletion_card=len(D),right_deletion_card=len(Dright),left_remainder_card=len(R),right_remainder_card=len(Rright),greedy_card=len(r['greedy_disjoint_family']),left_fires=cert(R),right_fires=cert(Rright),greedy_fires=cert(set(r['greedy_disjoint_family'])),edge_fires=r['edge_slack']<0,raw_prime_fiber_deletion_bound=raw,best_endpoint_fires=cert(R) or cert(Rright))
 rows.append(row)
 if n==1031 and r['world_kind']=='initial':
  columns=[dict(r=a,retained=sorted(R&{a+j*M for j in range(K)}),deleted=sorted(D&{a+j*M for j in range(K)}),retained_count=len(R&{a+j*M for j in range(K)})) for a in B]
  structure=dict(columns=columns,most_deleted_columns=sorted(columns,key=lambda c:(c['retained_count'],c['r']))[:8],deleting_primes=[dict(q=q,fiber_card=len(fibers[q]),max_seat=max(fibers[q]),deleted_first_endpoint_count=len(F)) for q,F in leftQ.items() if F],empty_support_seats=sorted(V-set().union(*fibers.values())),retained_supported_seats=sorted(R&set().union(*fibers.values())),remainder=sorted(R),deletion=sorted(D),right_remainder=sorted(Rright),greedy=sorted(r['greedy_disjoint_family']),raw_deletion_sum=raw)
counts={k:sum(r[k] for r in rows) for k in ['left_fires','right_fires','best_endpoint_fires','greedy_fires','edge_fires']}
first_strict=next(r for r in rows if r['left_fires'] and not r['edge_fires'])
result=dict(range=old['range'],extra_anchors=old['extra_anchors'],rows=rows,counts=counts,first_strict_deletion_improvement=first_strict,structure1031=structure)
(base/'logs/discovery-021.json').write_text(json.dumps(result,indent=2)+'\n')
print('Rows:',len(rows),'threshold counts:',counts)
print('First strict deletion improvement:',first_strict)
print('1031 column retained-card histogram:',{i:sum(c['retained_count']==i for c in structure['columns']) for i in range(10)})
print('1031 empty supports:',len(structure['empty_support_seats']),'retained supported seats:',len(structure['retained_supported_seats']))
print('1031 largest deletion fibers:',sorted(structure['deleting_primes'],key=lambda x:-x['deleted_first_endpoint_count'])[:8])
print('n world V E leftD rightD leftR rightR greedy pi rawFiberDeletion')
for r in rows:
 if r['n'] in [3,5,8,11,19,29,297,1031]:
  print(*(r[k] for k in ['n','world_kind','town_card','edge_card','left_deletion_card','right_deletion_card','left_remainder_card','right_remainder_card','greedy_card','old_prime_card','raw_prime_fiber_deletion_bound']))
