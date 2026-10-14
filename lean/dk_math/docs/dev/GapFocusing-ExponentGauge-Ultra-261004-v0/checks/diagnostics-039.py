"""One canonical pooled principle: every prime-base threshold tail product."""
from pathlib import Path
from collections import Counter
import math,json,hashlib,time
base=Path(__file__).resolve().parent.parent;start=time.monotonic()
source=base/'logs/diagnostics-038.json';old={r['n']:r for r in json.loads(source.read_text())['rows']}
ns=list(range(3,301))+[1031,5000];limit=2*max(ns)
prime=bytearray([1])*(limit+1);prime[:2]=bytes(2)
for p in range(2,math.isqrt(limit)+1):
    if prime[p]:prime[p*p:limit+1:p]=bytes((limit-p*p)//p+1)
primes=[p for p in range(2,limit+1) if prime[p]]
rows=[];anchors=[]
for n in ns:
    small=[];central=[]
    for p in primes:
        if p>2*n:break
        d=p
        while d<=2*n:
            s=n*n%d+(2*n)%d>=d;c=2*(n%d)>=d
            if s and not c:small.append((d,p))
            if c and not s:central.append((d,p))
            d*=p
    sc=Counter(p for d,p in small);cc=Counter(p for d,p in central)
    totalL=math.prod(p for d,p in small);totalR=math.prod(p for d,p in central)
    assert totalL<=totalR
    L=totalL;R=totalR;failures=[];first=None
    for t in range(2,2*n+1):
        if t>2:
            L//=(t-1)**sc[t-1];R//=(t-1)**cc[t-1]
        if L>R:
            failures.append(t)
            if first is None:
                first=dict(threshold=t,left_above=str(L),right_above=str(R),
                    left_below=str(totalL//L),right_below=str(totalR//R),
                    weighted_tail_defect_approx=math.log(L)-math.log(R))
    r=old[n]
    row=dict(n=n,threshold_principle_holds=first is None,failed_threshold_count=len(failures),
        first_threshold_failure=first,exact_total_product_inequality=True,
        phase_margin_approx=r['phase_margin_approx'],
        hypothetical_central_margin_approx=r['hypothetical_central_margin_approx'])
    rows.append(row)
    if n in [4,27,32,69,210,297,1031,5000]:
        anchors.append(dict(row,small_only=small,central_only=central,
            total_left=str(totalL),total_right=str(totalR),failed_thresholds=failures))
summary=dict(sample_count=len(rows),range=[3,300],additional_anchors=[1031,5000],
    first_sampled_threshold_failure=next(r for r in rows if not r['threshold_principle_holds']),
    failing_sample_count=sum(not r['threshold_principle_holds'] for r in rows),
    source_sha256=hashlib.sha256(source.read_bytes()).hexdigest(),elapsed_seconds=round(time.monotonic()-start,3),
    scope='Exact integer threshold-tail and total-product diagnostics. Threshold grouping depends only on base size, never on comparison success. Floating signs and inherited budget margins are not proof premises.')
(base/'logs/diagnostics-039.json').write_text(json.dumps(dict(summary=summary,rows=rows,anchors=anchors),indent=2)+chr(10))
print(json.dumps(summary,indent=2))
