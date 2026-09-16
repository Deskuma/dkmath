"""ASTRA-000 exact finite reconnaissance; Python 3 and SymPy 1.12.
The bounded searches are experiments, not uniform density proofs.
Run from any directory with: python /path/to/numeric-000.py
"""
import math, json
from sympy import factorint

def gn(a,b): return a*a+3*a*b+3*b*b
def row(a,b):
    fs=[{int(p):int(k) for p,k in factorint(gn(x,y)).items()} for x,y in [(a,b),(b,a)]]
    rs=[{p:k for p,k in f.items() if k>=2} for f in fs]
    return dict(a=a,b=b,c=a+b,coprime=math.gcd(a,b)==1,F=gn(a,b),G=gn(b,a),factors=fs,repeated=rs,moduli=[math.prod(p**k for p,k in r.items()) for r in rs],gcd=math.gcd(gn(a,b),gn(b,a)))
print('mandatory',json.dumps(row(605,370688)))
first=None; large=None; checked=0; bad=[]
for c in range(2,1001):
 for a in range(1,(c+1)//2):
    b=c-a
    if math.gcd(a,b)!=1: continue
    checked+=1
    d=math.gcd(gn(a,b),gn(b,a))
    if 14%d or any(e>=2 for e in factorint(d).values()): bad.append((a,b,d))
    if first is None or large is None:
      r=row(a,b)
      if all(r['repeated']) and first is None: first=r
      if all(m>c+1 for m in r['moduli']) and large is None: large=r
print('first_both',json.dumps(first))
print('first_both_moduli_gt_c_plus_one',json.dumps(large))
print('scan',json.dumps(dict(c_max=1000,positive_pairs_a_lt_b=checked,gcd_or_disjointness_counterexamples=bad)))
from sympy.ntheory.modular import crt
# Fixed-sum paired profile: a is the shared moving coordinate, b=c-a.
c=115; m1=13**2; m2=151**2
roots1=[a for a in range(m1) if (a*a-3*c*a+3*c*c)%m1==0]
roots2=[a for a in range(m2) if (a*a+c*a+c*c)%m2==0]
addresses=sorted(int(crt([m1,m2],[r,s])[0]) for r in roots1 for s in roots2)
points=[a for a in range(1,c) if (a*a-3*c*a+3*c*c)%m1==0 and (a*a+c*a+c*c)%m2==0]
print('paired_fixed_sum',json.dumps(dict(c=c,moduli=[m1,m2],product=m1*m2,roots1=roots1,roots2=roots2,addresses=addresses,positive_interval_points=points,pure_density_bound_fails=len(points)*m1*m2>4*(c-1))))
# Finite depth certificates only: b=1 gives automatic coprimality.
def lift(q,k,f,df):
    x=next(x for x in range(q) if f(x)%q==0)
    mod=q
    for depth in range(1,k):
        assert f(x)%mod==0
        digit=(-(f(x)//mod)*pow(df(x),-1,q))%q
        x+=mod*digit
        mod*=q
    assert f(x)%mod==0
    return x
for k in [2,4,8,16]:
    r=lift(7,k,lambda a:gn(a,1),lambda a:2*a+3)
    s=lift(13,k,lambda a:gn(1,a),lambda a:6*a+3)
    a=int(crt([7**k,13**k],[r,s])[0])
    assert gn(a,1)%(7**k)==0 and gn(1,a)%(13**k)==0
    print('paired_finite_depth',json.dumps(dict(k=k,a=a,b=1,divisors=[7**k,13**k],verified=True)))
