"""Global prefix correction compression, independent of shell prime inventory."""
from pathlib import Path
import math,json,hashlib,time
base=Path(__file__).resolve().parent.parent;start=time.monotonic()
source=base/'logs/diagnostics-031.json';old={r['n']:r for r in json.loads(source.read_text())['rows']}
ns=list(range(3,301))+[1031,5000];limit=2*max(ns)+2
prime=bytearray([1])*(limit+1);prime[:2]=bytes(2)
for p in range(2,math.isqrt(limit)+1):
    if prime[p]:prime[p*p:limit+1:p]=bytes((limit-p*p)//p+1)
primes=[p for p in range(2,limit+1) if prime[p]]
rows=[]
for n in ns:
    N=n*n;top=N+2*n;small=[];repeated=[];higher=[];psi=[];theta=[];globalpowers=[]
    for p in primes:
        lp=math.log(p)
        if p<=2*n:theta.append(lp)
        if p>2*n and p>n+1:continue
        d=p;a=1
        while d<=top:
            if d<=2*n:psi.append(lp)
            if a>=2 and d<=N:globalpowers.append(lp)
            if d<=N and top//d-N//d-(2*n)//d==1:
                if d<=2*n:small.append(lp)
                elif a>=2:repeated.append(lp)
            if a>=2 and N<d<=top:higher.append(lp)
            d*=p;a+=1
    S=math.fsum(small);R=math.fsum(repeated);H=math.fsum(higher)
    theta2=math.fsum(theta);psi2=math.fsum(psi);G=math.fsum(globalpowers)
    cutoff=((n+1)**2).bit_length()-1
    reciprocal=math.log(top)*math.fsum(1/a for a in range(3,cutoff+1,2))
    B=theta2+G+reciprocal;C=S+R+H
    explicit=math.log(4)*2*n+(math.log(4)+4)*(n+N**(1/3)+N**(1/5))+reciprocal
    r=old[n];Q=r['singleton_mass_approx'];logcell=r['log_cell_approx']
    assert S<=psi2+1e-7 and R<=G+1e-7 and S+R<=theta2+G+1e-7
    assert H<=reciprocal+1e-7 and C<=B+1e-7 and B<=explicit+1e-7
    assert abs(Q+C-r['old_budget_approx'])<1e-6
    rows.append(dict(n=n,small_approx=S,repeated_approx=R,higher_approx=H,correction_approx=C,
        psi_width_approx=psi2,theta_width_approx=theta2,global_nonprime_prefix_approx=G,
        higher_reciprocal_approx=reciprocal,budget_approx=B,explicit_scale_approx=explicit,
        compression_over_naive_psi_approx=psi2-theta2,slack_approx=B-C,
        singleton_approx=Q,log_cell_approx=logcell,old_margin_approx=logcell-Q-C,
        reduced_margin_approx=logcell-Q-B,Q_over_B_approx=Q/B))
summary=dict(sample_count=len(rows),range=[3,300],additional_anchors=[1031,5000],
    source_sha256=hashlib.sha256(source.read_bytes()).hexdigest(),elapsed_seconds=round(time.monotonic()-start,3),
    sampled_reduced_failures=[r['n'] for r in rows if r['reduced_margin_approx']<=0],
    scope='Global prefix enumeration; floating diagnostics only. Singleton and cell values reused from 031. No diagnostic is a Lean premise.')
(base/'logs/diagnostics-036.json').write_text(json.dumps(dict(summary=summary,rows=rows),indent=2)+chr(10))
print(json.dumps(summary,indent=2))
