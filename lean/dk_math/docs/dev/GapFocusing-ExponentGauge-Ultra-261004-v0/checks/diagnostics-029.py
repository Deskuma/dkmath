"""Reconstruct same-base exponent fibers from the exact 028 label inventory."""
from pathlib import Path
from collections import Counter
import hashlib,json,math,time
base=Path(__file__).resolve().parent.parent
source=base/'logs/diagnostics-028.jsonl'
oldsummary=json.loads((base/'logs/diagnostics-summary-028.json').read_text())
assert hashlib.sha256(source.read_bytes()).hexdigest()==oldsummary['data_sha256']
def ilog(p,x):
    a=0;q=1
    while q*p<=x:q*=p;a+=1
    return a
def valuation(p,y):
    a=0
    while y%p==0:y//=p;a+=1
    return a
rows=[];anchors=[];first_mixed=None;first_collision=None;first_slack=None
maximum=(0,0,0,0);worst=(0,0);failures=[];start=time.monotonic()
for line in source.open():
    r=json.loads(line);n=r['n'];b=n*n;w=2*n;events={};q=0
    for delta in r['prime_label_deltas']:q+=delta;events[q]=(q,1)
    for q,p,a in r['higher_labels']:events[q]=(p,a)
    allimages={};fibers={}
    for q,(p,a) in events.items():
        y=q*(b//q+1)
        allimages.setdefault(y,[]).append([q,p,a])
        if q>w:fibers.setdefault((p,y),[]).append(a)
    if first_mixed is None:
        mixed=[(y,es) for y,es in allimages.items() if len({e[1] for e in es})>1]
        if mixed:
            y,es=min(mixed);first_mixed=dict(n=n,y=y,labels=sorted(es))
    if n<3:continue
    bytarget={};packets=[];slack=Counter();mass=[];capmass=[];collapsed=[]
    for (p,y),exps in sorted(fibers.items()):
        assert y not in bytarget or bytarget[y]==p
        bytarget[y]=p
        exps.sort();L=ilog(p,w);U=ilog(p,b);v=valuation(p,y)
        exact=list(range(L+1,min(U,v)+1))
        # Direct divisibility scan is independent of the label-group membership.
        scan=[a for a in range(1,U+1) if p**a>w and y%(p**a)==0]
        assert exps==exact==scan,(n,p,y,exps,exact)
        C=U-L;F=max(min(U,v)-L,0)
        assert F==len(exps) and 0<F<=C
        assert all(b<p**a*(b//(p**a)+1)<=b+w and p**a*(b//(p**a)+1)==y for a in exps)
        mass.append(F*math.log(p));capmass.append(C*math.log(p));collapsed.append(math.log(p))
        slack[p]+=C-F
        packets.append(dict(p=p,y=y,lower=L,old_upper=U,valuation=v,
            exponents=exps,card=F,cutoff_card=C,slack_card=C-F))
        if F>maximum[0]:maximum=(F,n,p,y)
        if first_collision is None and F>1:first_collision=dict(n=n,p=p,y=y,exponents=exps)
        if first_slack is None and F<C:first_slack=dict(n=n,p=p,y=y,exponents=exps,cutoff_card=C,valuation=v)
    exactmass=math.fsum(mass);cap=math.fsum(capmass);gap=math.fsum(a*math.log(p) for p,a in slack.items())
    assert abs(exactmass-r['large_mass_approx'])<1e-8
    assert abs(cap-exactmass-gap)<1e-8
    envelope=r['higher_correction_approx']+r['small_mass_approx']+cap
    assert abs(envelope-r['old_Pascal_budget_approx']-gap)<1e-8
    ratio=cap/exactmass
    if ratio>worst[0]:worst=(ratio,n)
    provider=r['small_mass_approx']+cap+r['log_log_budget_approx']<r['log_cell_approx']
    if not provider:failures.append(n)
    row=dict(n=n,labels=r['large_count'],targets=len(fibers),
        fiber_histogram=sorted(Counter(len(es) for es in fibers.values()).items()),
        exact_weight_approx=exactmass,cutoff_budget_approx=cap,cap_over_exact_approx=ratio,
        one_per_target_weight_approx=math.fsum(collapsed),slack_prime_heights=sorted((p,a) for p,a in slack.items() if a),
        slack_mass_approx=gap,old_budget_approx=r['old_Pascal_budget_approx'],
        old_envelope_approx=envelope,provider_pass_approx=provider,
        all_exponent_intervals_equal=True,independent_divisibility_equal=True)
    prime_mass=math.fsum(math.log(p) for q,(p,a) in events.items() if q>w and a==1)
    row.update(singleton_prime_mass_approx=prime_mass,
        singleton_prime_fraction_approx=prime_mass/exactmass,
        repeated_power_mass_approx=exactmass-prime_mass)
    rows.append(row)
    if n in [3,5,6,7,11,12,19,29,297,1031,2896,5000]:anchors.append(dict(row,fibers=packets))
data=dict(summary=dict(range=[3,5000],source='diagnostics-028.jsonl',source_sha256=oldsummary['data_sha256'],
    integer_scope='Every fiber reconstructed by grouped labels, consecutive cutoff/valuation interval, and direct prime-power divisibility scan.',
    floating_scope='Logarithmic weights, ratios and strict conditions are floating diagnostics only.',
    first_mixed_base_without_large_hypothesis=first_mixed,first_large_collision=first_collision,
    first_cutoff_slack=first_slack,maximum_fiber=dict(zip(('card','n','p','y'),maximum)),
    maximum_cap_ratio=dict(ratio=worst[0],n=worst[1]),provider_failures_approx=failures,
    elapsed_seconds=round(time.monotonic()-start,3)),rows=rows,anchors=anchors)
(base/'logs/diagnostics-029.json').write_text(json.dumps(data,separators=(',',':'))+'\n')
print(json.dumps(data['summary'],indent=2))
