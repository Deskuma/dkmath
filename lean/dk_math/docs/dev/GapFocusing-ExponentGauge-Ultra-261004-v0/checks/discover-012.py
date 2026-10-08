"""Independent finite head/tail/rough diagnostics. Output is not a proof."""
from pathlib import Path
from math import gcd,isqrt
import json
base=Path(__file__).resolve().parent.parent

def prime(n): return n>=2 and all(n%d for d in range(2,isqrt(n)+1))
def row(n):
    ps=[p for p in range(3,n) if prime(p)]
    delta=lambda m: ((n*n+2*n)//m-n*n//m)-((n*n+2*n)//(2*m)-n*n//(2*m))
    W=lambda m: delta(m)-delta(n*m)
    F=lambda m: W(m)+W(15*m)+W(21*m)+W(35*m)-(W(3*m)+W(5*m)+W(7*m)+W(105*m))
    cs=[sum(W(3*q) for q in ps if q>3),sum(W(5*q)-W(15*q) for q in ps if q>5),
        sum(W(7*q)+W(105*q)-W(21*q)-W(35*q) for q in ps if q>7),
        sum(F(11*q) for q in ps if q>11)]
    union11=sum(max(0,W(11*q)-W(33*q)-W(55*q)-W(77*q)) for q in ps if q>11)
    A=n-1; B=sum(W(q) for q in ps); D=B-A+1
    cumulative=[sum(cs[:i]) for i in range(1,5)]
    support={r:[q for q in ps if (n*n+r)%q==0] for r in range(1,2*n+1)
        if gcd(n,r)==1 and (n*n+r)%2}
    E=sum(max(0,len(s)-1) for s in support.values())
    diags=[]
    for P,L in [(3,5),(5,7),(7,11),(11,13)]:
        rough=[r for r,s in support.items() if all(q>P for q in s)]
        roughI=sum(len(support[r]) for r in rough)
        tail=sum(max(0,len(support[r])-1) for r in rough)
        head=sum(max(0,len(s)-1) for s in support.values() if s and s[0]<=P)
        assert head==cumulative[[3,5,7,11].index(P)] and head+tail==E
        assert B-head==(A-len(rough))+roughI
        rough_formula=(A-W(3) if P==3 else A+W(15)-W(3)-W(5) if P==5 else F(1) if P==7 else F(1)-F(11))
        roughI_formula=sum(W(q)-W(3*q) if P==3 else W(q)+W(15*q)-W(3*q)-W(5*q) if P==5
            else F(q) if P==7 else F(q)-F(11*q) for q in ps if q>P)
        assert rough_formula==len(rough) and roughI_formula==roughI
        K=0
        while L**(K+1)<=n*n+2*n: K+=1
        diags.append(dict(P=P,L=L,head=head,remaining=B-head,demand_remaining=max(0,D-head),
            rough_seats=len(rough),rough_incidence=roughI,tail=tail,uncovered_rough=sum(not support[r] for r in rough),
            max_actual_support=max(map(lambda r:len(support[r]),rough),default=0),K=K,
            tail_multiplicity_bound=len(rough)*max(0,K-1)))
    return dict(n=n,A=A,B2=B,D=D,charges=cs,cumulative=cumulative,
        cutoff=next((p for p,c in zip([3,5,7,11],cumulative) if c>=D),None),
        union11=union11,credit11=cs[3]-union11,E_diagnostic=E,active=ps,diagnostics=diags)
rows=[row(n) for n in [47,97,127,211,503,1009,1013]]
(base/'logs/root-tail-diagnostics-012.json').write_text(json.dumps(rows,indent=2)+'\n')
for row in rows:
    print({k:v for k,v in row.items() if k not in ['active','diagnostics']})
    for d in row['diagnostics']:print(' ',d)
