"""Exact finite arithmetic diagnostics; logarithmic readouts are labeled approximate."""
from pathlib import Path
from math import comb, gcd, log, fsum, prod
from functools import reduce
from fractions import Fraction
import json
base=Path(__file__).resolve().parent.parent
limit=1031**2+2*1031
sieve=bytearray(b'\x01')*(limit+1)
sieve[0:2]=b'\x00\x00'
for p in range(2,int(limit**0.5)+1):
    if sieve[p]:
        start=p*p
        sieve[start::p]=b'\x00'*((limit-start)//p+1)
primes=[p for p in range(limit+1) if sieve[p]]
def power_data(N):
    for p in primes:
        if p>N: break
        t=N; a=0
        while t%p==0: t//=p; a+=1
        if t==1: return p,a
    return None,None
def vp(x,p):
    h=0
    while x and x%p==0: x//=p; h+=1
    return h
def defects(d,p):
    row=[comb(d,k)%p for k in range(d+1)]
    adj=[(row[k]+row[k+1])%p for k in range(d)]
    raw=[sum(x!=0 for x in adj),sum(x!=pow(-1,k,p) for k,x in enumerate(row)),sum(min(x,p-x) for x in adj)]
    return raw+[str(Fraction(raw[0],d)),str(Fraction(raw[1],d+1)),str(Fraction(raw[2],d))]
rows=[]
for N in [2,3,4,5,6,7,8,9,10,12,15,25,27]:
    p,a=power_data(N)
    common=reduce(gcd,(comb(N,k) for k in range(1,N)),0)
    modulus=p or next(q for q in primes if N%q==0)
    all_inner=all(comb(N,k)%modulus==0 for k in range(1,N))
    pre=all(comb(N-1,k)%modulus==pow(-1,k,modulus) for k in range(N))
    ks=sorted({1,N//2,N-1,*([modulus] if modulus<N else [])})
    rows.append(dict(N=N,gcd=common,prime=bool(sieve[N]),prime_power=bool(p),base=p,exponent=a,selected_modulus=modulus,prebirth=pre,common_next=all_inner,dials={str(k):vp(comb(N,k),modulus) for k in ks}))
names=['nonzero_adjacent','phase_mismatch','centered_adjacent','nonzero_adjacent_per_d','phase_mismatch_per_d_plus_one','centered_adjacent_per_d']
scans={}
for mode in ['prime','prime_power']:
    first={name:None for name in names}; transitions=0; targets=[]
    for p in primes:
        if p>31: break
        for a in range(1,8):
            N=p**a
            if N>128: break
            if mode=='prime' and a!=1: continue
            if mode=='prime_power' and a<2: continue
            targets.append([p,a,N])
            for d in range(1,N-1):
                left=defects(d,p);right=defects(d+1,p);transitions+=1
                for j,name in enumerate(names):
                    L=Fraction(left[j]);R=Fraction(right[j])
                    if R>L and first[name] is None:
                        first[name]=dict(p=p,a=a,N=N,row=d,next_row=d+1,before=left[j],after=right[j])
            assert defects(N-1,p)[:3]==[0,0,0]
    scans[mode]=dict(order='p ascending, a ascending, row ascending; rows start at one',targets=targets,transitions=transitions,first_increase=first)
def vf(n,p):
    h=0
    while n: n//=p;h+=n
    return h
anchors=[]
for n in [5,11,19,29,297,1031]:
    top=n*n+2*n;k=2*n
    support=[(p,vf(top,p)-vf(k,p)-vf(n*n,p)) for p in primes if p<=top]
    support=[(p,h) for p,h in support if h]
    fresh=[p for p in primes if n*n<p<=top]
    assert prod(p**h for p,h in support)==comb(top,k)
    assert Fraction(k,top)==Fraction(2,n+2)
    assert [p for p,h in support if p>n*n]==fresh
    assert all(h==1 for p,h in support if p>n*n)
    anchors.append(dict(full_factorization_checked=True,n=n,top=top,index=k,ratio=str(Fraction(k,top)),support_card=len(support),old_support_card=sum(p<=n*n for p,h in support),max_height=max(h for p,h in support),fresh_count=len(fresh),fresh_primes=fresh,selected_heights={str(p):h for p,h in support if p<=19},log_cell_approx=fsum(h*log(p) for p,h in support),old_log_approx=fsum(h*log(p) for p,h in support if p<=n*n),shell_birth_log_approx=fsum(log(p) for p in fresh)))
preflight=[dict(n=297,r=350,point=88559,factors=[19,59,79]),dict(n=1031,r=90,point=1063051,factors=[11,241,401])]
for row in preflight:
    assert row['n']**2+row['r']==row['point']
    assert all(sieve[p] for p in row['factors'])
    assert prod(row['factors'])==row['point']
result=dict(rows=rows,monotonicity=scans,anchors=anchors,preflight=preflight)
(base/'logs/pascal-diagnostics-025.json').write_text(json.dumps(result,indent=2)+'\n')
lines=['Exact finite Pascal diagnostics.','Log values only are approximate; all supports, heights, ratios and counts are exact.','']
lines+=['ROW '+json.dumps(row,sort_keys=True) for row in rows]
for mode,scan in scans.items():
    lines+=['SCAN '+mode+' '+str(scan['transitions'])+' transitions '+scan['order']]
    lines+=[name+' '+json.dumps(scan['first_increase'][name]) for name in names]
lines+=['ANCHOR '+json.dumps({**{k:v for k,v in row.items() if k!='fresh_primes'},'fresh_first':row['fresh_primes'][0],'fresh_last':row['fresh_primes'][-1]},sort_keys=True) for row in anchors]
(base/'logs/pascal-diagnostics-025.txt').write_text('\n'.join(lines)+'\n')
print('\n'.join(lines))
