"""Exact integer compensation checks; finite searches never imply a universal theorem."""
from pathlib import Path
from collections import Counter
import math,json,hashlib,time
base=Path(__file__).resolve().parent.parent;start=time.monotonic()
source=base/'logs/diagnostics-037.json';old={r['n']:r for r in json.loads(source.read_text())['rows']}
limit=20000;prime=bytearray([1])*(limit+1);prime[:2]=bytes(2)
for p in range(2,math.isqrt(limit)+1):
    if prime[p]:prime[p*p:limit+1:p]=bytes((limit-p*p)//p+1)
primes=[p for p in range(2,limit+1) if prime[p]];lp={p:math.log(p) for p in primes}
rows=[];anchors=[];counterexamples=[];first_base=None;first_label=None;first_rank=None
for n in range(3,10001):
    common=[];smallonly=[];centralonly=[]
    for p in primes:
        if p>2*n:break
        d=p
        while d<=2*n:
            small=n*n%d+(2*n)%d>=d;central=2*(n%d)>=d
            if small and central:common.append((d,p))
            elif small:smallonly.append((d,p))
            elif central:centralonly.append((d,p))
            d*=p
    sp=math.prod(p for d,p in smallonly);cp=math.prod(p for d,p in centralonly)
    if sp>cp:counterexamples.append(n)
    sb=Counter(p for d,p in smallonly);cb=Counter(p for d,p in centralonly)
    if first_base is None:
        bad=sorted(p for p,c in sb.items() if c>cb[p])
        if bad:first_base=dict(n=n,p=bad[0],small_count=sb[bad[0]],central_count=cb[bad[0]])
    sbase=sorted((p for d,p in smallonly),reverse=True);cbase=sorted((p for d,p in centralonly),reverse=True)
    rankok=len(sbase)<=len(cbase) and all(s<=c for s,c in zip(sbase,cbase))
    if not rankok and first_rank is None:first_rank=dict(n=n,small_bases=sbase,central_bases=cbase)
    slabel=sorted((d for d,p in smallonly),reverse=True);clabel=sorted((d for d,p in centralonly),reverse=True)
    labelok=len(slabel)<=len(clabel) and all(s<=c for s,c in zip(slabel,clabel))
    if not labelok and first_label is None:first_label=dict(n=n,small_labels=slabel,central_labels=clabel)
    if n in old or n==4:
        sm=math.fsum(lp[p] for d,p in smallonly);cm=math.fsum(lp[p] for d,p in centralonly)
        commonmass=math.fsum(lp[p] for d,p in common)
        centralproduct=cp*math.prod(p for d,p in common)
        assert centralproduct==math.comb(2*n,n)
        row=dict(n=n,common_count=len(common),small_only_count=len(smallonly),central_only_count=len(centralonly),
            common_mass_approx=commonmass,small_only_mass_approx=sm,central_only_mass_approx=cm,
            compensation_margin_approx=cm-sm,exact_product_inequality=sp<=cp,
            same_base_domination=all(c<=cb[p] for p,c in sb.items()),rank_base_matching=rankok,label_matching=labelok)
        if n in old:
            r=old[n];central=math.log(math.comb(2*n,n))
            assert abs(sm+commonmass-r['small_approx'])<1e-7
            assert abs(cm+commonmass-central)<1e-7
            cbudget=central+r['repeated_band_approx']+(r['phase_budget_approx']-r['phase_small_bound_approx']-r['repeated_band_approx'])
            row.update(phase_budget_approx=r['phase_budget_approx'],hypothetical_central_budget_approx=cbudget,
                hypothetical_central_margin_approx=r['phase_margin_approx']+r['phase_budget_approx']-cbudget,
                phase_margin_approx=r['phase_margin_approx'])
        rows.append(row)
        if n in [4,27,32,69,210,297,1031,5000]:
            anchors.append(dict(row,common=common,small_only=smallonly,central_only=centralonly,
                small_only_product=str(sp),central_only_product=str(cp)))
summary=dict(compensation_search_range=[3,10000],exact_integer_counterexamples=counterexamples,
    first_same_base_failure=first_base,first_label_matching_failure=first_label,first_rank_base_failure=first_rank,
    recorded_sample_count=len(rows),source_sha256=hashlib.sha256(source.read_bytes()).hexdigest(),
    elapsed_seconds=round(time.monotonic()-start,3),
    scope='Exact integer products in the bounded search; logs and margins are floating diagnostics. No finite search is a Lean premise or a universal comparison theorem.')
(base/'logs/diagnostics-038.json').write_text(json.dumps(dict(summary=summary,rows=rows,anchors=anchors),indent=2)+chr(10))
print(json.dumps(summary,indent=2))
