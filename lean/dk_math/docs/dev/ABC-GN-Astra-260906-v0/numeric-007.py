"""ASTRA-007. Exact polynomial factor sieve; floats ONLY describe fractional moments.
Run: python3 numeric-007.py --limit 200000
Requires sympy (tested 1.12). No statistical result here is a proof.
"""
import argparse, collections, json, math, itertools, random
from sympy.ntheory.modular import crt
import sympy

def sieve(limit):
    vals = [a*a+3*a+3 for a in range(limit+1)]
    fac = [[] for _ in vals]
    for p in sympy.primerange(2, limit+3):
        if p == 3: roots = [0]
        elif p % 3 != 1: continue
        else:
            roots = sorted({int((r-3)*pow(2,-1,p)%p) for r in sympy.sqrt_mod(-3,p,all_roots=True)})
        for r in roots:
            for a in range(r,limit+1,p):
                k=0
                while vals[a]%p == 0:
                    vals[a]//=p; k+=1
                if k: fac[a].append((int(p),k))
    for a,n in enumerate(vals):
        if n>1: fac[a].append((n,1))
    return fac

def main(limit):
    fac=sieve(limit)
    rng=random.Random(7007)
    sampled=sorted(set(range(min(limit+1,100))) | {rng.randrange(limit+1) for _ in range(128)})
    for a in sampled:
        assert dict(fac[a]) == dict(sympy.factorint(a*a+3*a+3))
    print('INDEPENDENT factorint cross-check count',len(sampled),'seed',7007)
    rows=[]
    for a,fs in enumerate(fac):
        F=a*a+3*a+3
        M=math.prod(p**k for p,k in fs if k>=2 and p!=3)
        S=F//M
        assert math.prod(p**k for p,k in fs)==F
        assert all(p!=3 or k==1 for p,k in fs)
        assert math.gcd(M,S)==1
        assert all(p%3==1 for p,k in fs if p!=3)
        rows.append((M,S))
    print('EXACT sieve invariants verified, endpoints 0..',limit)
    groups=collections.defaultdict(list)
    for a,(M,S) in enumerate(rows):
        if 1<=a and a+1<M: groups[M].append(a)
    collisions=sorted((aa[1],M,aa[:10]) for M,aa in groups.items() if len(aa)>1 and aa[1]+1<M)
    print('FIRST LARGE COLLISIONS',json.dumps(collisions[:12]))
    for X in [x for x in [10,30,100,300,1000,3000,6105,10000,30000,100000,limit] if x<=limit]:
        g=collections.defaultdict(list)
        for a in range(1,X+1):
            M,S=rows[a]
            if M>X+1: g[M].append(a)
        total=sum(M**.375 for M in g)
        # Rational certificates: eighth root of M^3, rounded down at 32 bits.
        scale=1<<32
        low=sum(math.isqrt(math.isqrt(math.isqrt(M**3 * scale**8))) for M in g)
        print('CERTIFIED moment/X interval numerators, common denominator',
              low, low+len(g), scale*X)
        actual=sum((M/math.prod(p for p,k in fac[a] if k>=2))**.375
                   for M,aa in g.items() for a in aa)
        ratios=sorted(M/X for M in g)
        comp=sorted(rows[a][1] for aa in g.values() for a in aa)
        print('WINDOW',json.dumps(dict(X=X,distinct=len(g),points=sum(map(len,g.values())),
             max_multiplicity=max(map(len,g.values()),default=0),moment_float=total,
             moment_over_X_float=total/X,actual_large_over_X_float=actual/X,
             M_over_X_quantiles=[ratios[int((len(ratios)-1)*t)] if ratios else None for t in [0,.5,.9,1]],
             S_quantiles=[comp[int((len(comp)-1)*t)] if comp else None for t in [0,.5,.9,1]])))
        if g:
            m=max(g,key=lambda m:len(g[m])); print('MAX MULTIPLICITY',m,g[m], 'factor',sympy.factorint(m))
    byS=collections.defaultdict(list)
    for a,(M,S) in enumerate(rows):
        if a>=1 and M>a+1: byS[S].append((a,M))
    print('COMPLEMENT COLLISIONS', sorted((aa[1][0],S,aa[:6]) for S,aa in byS.items() if len(aa)>1)[:12])
    # CRT mixed roots: more than two roots of a composite squareful modulus.
    m=49*169
    roots=[a for a in range(m) if (a*a+3*a+3)%m==0]
    print('COMPOSITE ROOTS',m,roots,[(a,dict(sympy.factorint(a*a+3*a+3))) for a in roots])
    print('TOP WEIGHTS',sorted(((M,a,S,fac[a]) for a,(M,S) in enumerate(rows) if a>0),reverse=True)[:12])
    # Exact normalized eighth-power checks for individual counterexamples.
    for X in [10,100,1000,10000,limit]:
        if X>limit: continue
        eligible=[(M,a,S) for a,(M,S) in enumerate(rows[:X+1]) if a and M>X+1]
        if eligible: print('MAX MODULUS',X,max(eligible))
    paired=[]
    for a in range(1,limit+1):
        M,S=rows[a]
        if M<=a+1: continue
        gs=sympy.factorint(3*a*a+3*a+1)
        N=math.prod(int(p)**int(k) for p,k in gs.items() if k>=2 and p!=3)
        if N>a+1: paired.append((a,M,N,S,(3*a*a+3*a+1)//N))
    print('PAIR SCAN limit',limit,'eligible F-large witnesses',sum(1 for a,(M,S) in enumerate(rows) if a and M>a+1))
    print('BOTH ABOVE INTERVAL',paired[:15])
    print('PAIR PRODUCT ABOVE INTERVAL SQUARED',[(a,M,N) for a,M,N,_,_ in paired if M*N>(a+1)**2][:10])
    for ps in [[7,13,19],[7,13,19,31]]:
        ms=[p*p for p in ps]; m=math.prod(ms)
        rr=[[int((r-3)*pow(2,-1,d)%d) for r in sympy.sqrt_mod(-3,d,all_roots=True)] for d in ms]
        out=[]
        for rs in itertools.product(*rr):
            a=int(crt(ms,rs)[0]); fs=sympy.factorint(a*a+3*a+3)
            rep=math.prod(int(p)**int(k) for p,k in fs.items() if k>=2 and p!=3)
            if rep==m and a+1<m:
                out.append((a, int((a*a+3*a+3)//m), {int(p):int(k) for p,k in fs.items()}))
        print('MIXED CRT full-part collisions',m,'count',len(out),'certificates',sorted(out))
    a,d=0,1
    for n in range(8):
        assert a*a+3*a+3==3*d*d and a%3==0 and d%3==1
        print('PELL complement=3',n,a,d,'repeated',d*d)
        a,d=7*a+12*d+9,4*a+7*d+6
    from fractions import Fraction as Q
    print('EXACT exponent ledger',{'height_only':str(2*(Q(1,2)+Q(3,8))),
      'density_shell':str(Q(1,2)+Q(3,8)-1),
      'necessary_squarefull_count_exponent':str(1-2*Q(3,8)),
      'largest_admissible_boundary_count_exponent':str((1-2*Q(3,8))/2)})

if __name__=='__main__':
    ap=argparse.ArgumentParser(); ap.add_argument('--limit',type=int,default=200000)
    main(ap.parse_args().limit)
