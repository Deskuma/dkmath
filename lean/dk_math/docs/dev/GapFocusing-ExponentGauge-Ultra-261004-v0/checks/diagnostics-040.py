"""First eligible repeated-power gate: exact integers, floating weights only."""
from pathlib import Path
import math,json,hashlib,time
base=Path(__file__).resolve().parent.parent;start=time.monotonic()
source=base/'logs/diagnostics-036.json'
old={r['n']:r for r in json.loads(source.read_text())['rows']}
ns=list(range(3,301))+[1031,2896,5000]
limit=(2896**2+2*2896)//2
sieve=bytearray([1])*(limit+1);sieve[:2]=bytes(2)
for p in range(2,math.isqrt(limit)+1):
    if sieve[p]:sieve[p*p:limit+1:p]=bytes((limit-p*p)//p+1)
primes=[p for p in range(2,10001) if sieve[p]]
rows=[];anchors=[]
for n in ns:
    N=n*n;w=2*n;top=N+w
    band=[];kept=[];exact=[];blocks=[];small=[];excluded=[];psi=[];higher=[]
    for p in primes:
        if p>w:break
        d=p;a=1;lp=math.log(p)
        while d<=top:
            if d<=w:
                psi.append(lp);r=n%d
                if N%d+w%d>=d:small.append(lp)
                if (r<=4*math.isqrt(d) and r*r%d+(2*r)%d<d) or r==d-1:
                    excluded.append(lp)
            if a>=2 and N<d<=top:higher.append(lp)
            a+=1;d*=p
        if p>n:continue
        a=2;d=p*p
        while d<=w:a+=1;d*=p
        first_a=a;first_d=d;gap=d-N%d;active=gap<=w
        labels=[]
        while d<=N:
            carry=d-N%d<=w
            band.append(lp)
            if active:kept.append(lp)
            if carry:
                assert active
                exact.append(lp)
            labels.append(dict(exponent=a,label=d,actual_carry=carry))
            a+=1;d*=p
        if labels:
            blocks.append(dict(base=p,first_exponent=first_a,first_power=first_d,
                first_gap=gap,base_active=active,exponent_count=len(labels),
                weight_approx=len(labels)*lp,labels=labels))
    R=math.fsum(exact);RP=math.fsum(kept);RB=math.fsum(band)
    S=math.fsum(small);E=math.fsum(excluded);PS=math.fsum(psi);H=math.fsum(higher)
    cutoff=((n+1)**2).bit_length()-1
    reciprocal=math.log(top)*math.fsum(1/a for a in range(3,cutoff+1,2))
    B037=PS-E+RB+reciprocal;B040=PS-E+RP+reciprocal
    if n in old:
        r=old[n];Q=r['singleton_approx'];cell=r['log_cell_approx']
        assert abs(R-r['repeated_approx'])<1e-7
        assert abs(S-r['small_approx'])<1e-7
    else:
        # Exact Q windows, only for the newly added anchor 2896.
        qs=[p for k in range(2,n) for p in range(max(N//k,w)+1,top//k+1) if sieve[p]]
        assert len(qs)==len(set(qs))
        Q=math.fsum(math.log(p) for p in qs)
        # Log product avoids subtracting very large lgamma values.
        cell=math.fsum(math.log(N+i)-math.log(i) for i in range(1,w+1))
    assert R<=RP+1e-7 and RP<=RB+1e-7
    assert S+R+H<=B040+1e-7 and B040<=B037+1e-7
    row=dict(n=n,repeated_exact_approx=R,repeated_band_approx=RB,
        repeated_phase_approx=RP,repeated_saving_approx=RB-RP,
        exact_repeated_count=len(exact),envelope_prime_power_count=len(kept),
        excluded_prime_power_count=len(band)-len(kept),small_phase_bound_approx=PS-E,
        higher_reciprocal_approx=reciprocal,correction_exact_approx=S+R+H,
        budget037_approx=B037,budget040_approx=B040,singleton_approx=Q,
        log_cell_approx=cell,margin037_approx=cell-Q-B037,margin040_approx=cell-Q-B040)
    rows.append(row)
    if n in {3,32,69,297,1031,2896,5000}:anchors.append(dict(row,base_blocks=blocks))
summary=dict(sample_count=len(rows),range=[3,300],additional_anchors=[1031,2896,5000],
    source_sha256=hashlib.sha256(source.read_bytes()).hexdigest(),
    recovered_sample_failures=[r['n'] for r in rows if r['margin037_approx']<=0<r['margin040_approx']],
    remaining_sample_failures=[r['n'] for r in rows if r['margin040_approx']<=0],
    strict_repeated_saving_count=sum(r['repeated_saving_approx']>1e-7 for r in rows),
    elapsed_seconds=round(time.monotonic()-start,3),
    scope='Exact integer labels and gates; floating logs and consumer margins are diagnostics, never Lean premises. Q and cell reused from 036 except directly computed 2896. No central-binomial conjecture assumed.')
(base/'logs/diagnostics-040.json').write_text(json.dumps(dict(summary=summary,rows=rows,anchors=anchors),indent=2)+'\n')
print(json.dumps(summary,indent=2))
for r in rows:
    if r['n'] in {3,32,69,297,1031,2896,5000}:print(json.dumps(r))
