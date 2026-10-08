"""Bounded zero-phase exclusion diagnostics; central-binomial target is tested only."""
from pathlib import Path
import math,json,hashlib,time
base=Path(__file__).resolve().parent.parent;start=time.monotonic()
source=base/'logs/diagnostics-036.json';old={r['n']:r for r in json.loads(source.read_text())['rows']}
limit=20000;prime=bytearray([1])*(limit+1);prime[:2]=bytes(2)
for p in range(2,math.isqrt(limit)+1):
    if prime[p]:prime[p*p:limit+1:p]=bytes((limit-p*p)//p+1)
primes=[p for p in range(2,limit+1) if prime[p]]
rows=[];largest=dict(n=None,ratio=0);counterexamples=[]
for n in range(3,10001):
    small=[];excluded=[];excluded_labels=[];lowpowers=[]
    for p in primes:
        if p>2*n:break
        d=p;lp=math.log(p)
        while d<=2*n:
            r=n%d
            carry=n*n%d+(2*n)%d>=d
            zone=(r<=4*math.isqrt(d) and (r*r)%d+(2*r)%d<d) or r==d-1
            if carry:small.append(lp)
            if zone:
                assert not carry
                excluded.append(lp);excluded_labels.append(d)
            if d!=p:lowpowers.append(lp)
            d*=p
    S=math.fsum(small);E=math.fsum(excluded)
    central=math.log(math.comb(2*n,n));ratio=S/central
    if ratio>largest['ratio']:largest=dict(n=n,ratio=ratio,small_approx=S,central_approx=central)
    if S>central+1e-7:counterexamples.append(n)
    if n in old:
        r=old[n];band=r['global_nonprime_prefix_approx']-math.fsum(lowpowers)
        B=r['budget_approx']-E
        alternative=r['psi_width_approx']-E+band+r['higher_reciprocal_approx']
        assert abs(B-alternative)<1e-7 and abs(S-r['small_approx'])<1e-7
        assert r['repeated_approx']<=band+1e-7
        assert r['correction_approx']<=B+1e-7
        rows.append(dict(n=n,small_approx=S,central_approx=central,central_ratio_approx=ratio,
            excluded_mass_approx=E,excluded_labels=sorted(excluded_labels),
            phase_small_bound_approx=r['psi_width_approx']-E,repeated_band_approx=band,
            correction_approx=r['correction_approx'],previous_budget_approx=r['budget_approx'],
            phase_budget_approx=B,previous_margin_approx=r['reduced_margin_approx'],
            phase_margin_approx=r['reduced_margin_approx']+E,
            hypothetical_central_budget_approx=central+band+r['higher_reciprocal_approx'],
            singleton_approx=r['singleton_approx']))
summary=dict(sample_count=len(rows),phase_range=[3,300],additional_phase_anchors=[1031,5000],
    central_conjecture_range=[3,10000],largest_sampled_central_ratio=largest,
    sampled_central_counterexamples=counterexamples,source_sha256=hashlib.sha256(source.read_bytes()).hexdigest(),
    elapsed_seconds=round(time.monotonic()-start,3),
    scope='All logs and inequalities are floating diagnostics; central-binomial bound is unproved. The proved alternative is zero-phase exclusion plus a global nonprime band.')
(base/'logs/diagnostics-037.json').write_text(json.dumps(dict(summary=summary,rows=rows),indent=2)+chr(10))
print(json.dumps(summary,indent=2))
