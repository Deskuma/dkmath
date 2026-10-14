"""Recompute finite conservation diagnostics; no Lean proof premises."""
from pathlib import Path
from math import gcd,isqrt
from collections import Counter
import json
base=Path(__file__).resolve().parent.parent
rows=[]
for r in json.loads((base/'logs/discovery-020.json').read_text())['rows']:
 n,S,M,K=r['n'],set(r['S']),r['M'],r['K']
 T=[q for q in range(2,n+1) if q not in S and all(q%d for d in range(2,isqrt(q)+1))]
 V={a+j*M for a in range(1,M+1) if gcd(n*n+a,M)==1 for j in range(K)}
 F={q:{a for a in V if (n*n+a)%q==0} for q in T}
 L={q:f-{max(f)} if f else set() for q,f in F.items()}
 H={q:f-{min(f)} if f else set() for q,f in F.items()}
 m=Counter(a for f in L.values() for a in f)
 h=Counter(a for f in H.values() for a in f)
 support=Counter(a for f in F.values() for a in f)
 U=len(V-set(support));A=sum(bool(f) for f in F.values());I=sum(map(len,F.values()))
 X=sum(c-1 for c in support.values());mass=sum(m.values());O=sum(c-1 for c in m.values())
 D=len(m);R=len(V)-D;Or=sum(c-1 for c in h.values());Dr=len(h);Rr=len(V)-Dr
 assert R+X==U+A+O and D+O==mass and mass+A==I
 assert Rr+X==U+A+Or
 row=dict(n=n,world_kind=r['world_kind'],S=sorted(S),V=len(V),T=len(T),A=A,U=U,I=I,X=X,Dleft=D,Rleft=R,deletion_mass=mass,O=O,inactive=len(T)-A,overlap_minus_excess=O-X,residual=R+X-U-A-O,Dright=Dr,Rright=Rr,Oright=Or,direct_left=len(T)<R,direct_right=len(T)<Rr,conservation_left=len(T)+X<A+O,greedy=len(r['greedy_disjoint_family']))
 rows.append(row)
assert len(rows)==602
out=dict(rows=rows,counts={k:sum(r[k] for r in rows) for k in ['direct_left','direct_right','conservation_left']},first_false_equivalence=next(r for r in rows if r['direct_left'] and not r['conservation_left']))
(base/'logs/discovery-022.json').write_text(json.dumps(out,indent=2)+chr(10))
print('Rows:',len(rows),'counts:',out['counts'])
print('Smallest scanned false equivalence:',out['first_false_equivalence'])
for r in rows:
 if r['n'] in [5,11,19,29,297,1031]: print(r)
