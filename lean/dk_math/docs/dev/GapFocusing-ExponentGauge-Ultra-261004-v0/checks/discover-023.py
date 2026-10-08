"""Recompute retained-direction and extremal handoff diagnostics."""
from pathlib import Path
from math import gcd,isqrt
from collections import Counter
import json
base=Path(__file__).resolve().parent.parent
rows=[];counterexamples={};details={}
for r in json.loads((base/'logs/discovery-020.json').read_text())['rows']:
 n,S,M,K=r['n'],set(r['S']),r['M'],r['K']
 T=[q for q in range(2,n+1) if q not in S and all(q%d for d in range(2,isqrt(q)+1))]
 V={a+j*M for a in range(1,M+1) if gcd(n*n+a,M)==1 for j in range(K)}
 F={q:{a for a in V if (n*n+a)%q==0} for q in T}
 A={q for q in T if F[q]};support={a:{q for q in A if a in F[q]} for a in V}
 U={a for a in V if not support[a]};X=sum(max(0,len(f)-1) for f in support.values())
 orient=[]
 for side,extreme in [('left',max),('right',min)]:
  end={q:extreme(F[q]) for q in A}
  charges=Counter(a for q in A for a in F[q]-{end[q]})
  D=set(charges);R=V-D;rep={q for a in R for q in support[a]};lost=A-rep
  excess=sum(max(0,len(support[a])-1) for a in R);O=sum(c-1 for c in charges.values());L=X-O
  E={(q,p) for q in A for p in support[end[q]] if end[p]!=end[q]}
  assert all((end[q]<end[p]) if side=='left' else (end[p]<end[q]) for q,p in E)
  assert lost=={q for q,p in E}
  depth={}
  for q in sorted(A,key=end.get,reverse=side=='left'):
   depth[q]=max([1+depth[p] for x,p in E if x==q]+[0])
  residual=L-len(lost)-excess
  assert residual==0 and len(R)+L==len(U)+len(A) and len(R)+X==len(U)+len(A)+O
  data=dict(represented=len(rep),unrepresented=len(lost),retained_excess=excess,loss=L,R=len(R),D=len(D),O=O,mass=sum(charges.values()),master_residual=len(R)+X-len(U)-len(A)-O,handoff_edges=len(E),chain_depth=max(depth.values(),default=0),residual=residual)
  orient.append(data)
  if n in [29,297,1031] and r['world_kind']=='initial':
   details.setdefault(str(n),{})[side]=dict(remainder=sorted(R),represented=sorted(rep),unrepresented=sorted(lost),edges=sorted(E))
  indeg=Counter(p for q,p in E);outdeg=Counter(q for q,p in E)
  for label,pred in [('acyclic_implies_loss_zero',L>0),('bounded_out_degree_one',any(c>1 for c in outdeg.values())),('unique_terminal_seat',len({end[q] for q in rep})<len(rep))]:
   if pred and label not in counterexamples:counterexamples[label]=dict(n=n,world=r['world_kind'],S=sorted(S),side=side,values=data,edges=sorted(E))
  for q,p in E:
   for b in F[p]:
    if (b>end[q] if side=='left' else b<end[q]) and (b-end[q])%(p*q):
     counterexamples.setdefault('pq_dvd_continuation_gap',dict(n=n,world=r['world_kind'],S=sorted(S),side=side,q=q,p=p,a=end[q],b=b))
 row=dict(n=n,world_kind=r['world_kind'],S=sorted(S),V=len(V),T=len(T),A=len(A),U=len(U),X=X,I=sum(map(len,F.values())),left=orient[0],right=orient[1],better_R=max(o['R'] for o in orient),better_loss=min(o['loss'] for o in orient))
 row['survivor_capacity']=len(T)<row['better_R']
 assert row['survivor_capacity']==(row['better_loss']+len(T)-len(A)<len(U))
 rows.append(row)
out=dict(rows=rows,details=details,counterexamples=counterexamples,counts=dict(better=sum(r['survivor_capacity'] for r in rows),left=sum(r['T']<r['left']['R'] for r in rows),right=sum(r['T']<r['right']['R'] for r in rows)))
(base/'logs/discovery-023.json').write_text(json.dumps(out,indent=2)+chr(10))
print('Rows:',len(rows),'capacity counts:',out['counts'])
for r in rows:
 if r['n'] in [29,297,1031]: print(r)
print('False conjectures:',counterexamples)
