"""Independent endpoint factor-pair cover, canonical fibers and square deletion."""
from pathlib import Path
from collections import Counter
import math,json,hashlib,time
base=Path(__file__).resolve().parent.parent
source=base/'logs/diagnostics-031.json';prior=json.loads(source.read_text())
old={r['n']:r for r in prior['rows']}
start=time.monotonic();ns=list(range(3,301))+[1031,5000]
limit=(max(ns)**2+2*max(ns))//2
prime=bytearray(b'\x01')*(limit+1);prime[0:2]=b'\x00\x00'
for p in range(2,math.isqrt(limit)+1):
    if prime[p]:prime[p*p:limit+1:p]=b'\x00'*((limit-p*p)//p+1)
small=[p for p in range(2,math.isqrt(limit)+1) if prime[p]]
rows=[];anchors=[];first_duplicate=None
for n in ns:
    b=n*n;t=b+2*n;packets=[];errors=[];covers=[];squares=[];pair_count=0;composite_count=0
    for k in range(2,min(n-1,t//(2*n+1))+1):
        A=max(b//k,2*n);B=t//k
        pairs=[(r,m) for r in small if r*r<=B and math.gcd(r,30)==1
            for m in range(max(r,A//r+1),B//r+1) if math.gcd(m,30)==1]
        products=Counter(r*m for r,m in pairs)
        comps=[q for q in range(A+1,B+1) if math.gcd(q,30)==1 and not prime[q]]
        assert set(products)==set(comps)
        canonical=[(q,next(p for p in small if q%p==0)) for q in comps]
        for q,r in canonical:assert (r,q//r) in pairs
        sqs=[r*m for r,m in pairs if r==m]
        assert len(sqs)==len(set(sqs)) and set(sqs)<=set(comps)
        E=math.fsum(math.log(q) for q in comps);F=math.fsum(math.log(r*m) for r,m in pairs);L=math.fsum(math.log(q) for q in sqs)
        assert F>=E-1e-8 and L<=E+1e-8
        errors.append(E);covers.append(F);squares.append(L);pair_count+=len(pairs);composite_count+=len(comps)
        dup=[q for q,c in products.items() if c>1]
        if dup and first_duplicate is None:first_duplicate=dict(n=n,k=k,q=min(dup),pairs=[list(p) for p in pairs if math.prod(p)==min(dup)])
        if n in [3,7,9,12,29,31,32,33,34,35,297,1031,5000]:
            packets.append(dict(k=k,A=A,B=B,canonical=[[q,r,q//r] for q,r in canonical],pairs=[list(p) for p in pairs],squares=sqs))
    E=math.fsum(errors);F=math.fsum(covers);L=math.fsum(squares);r=old[n]
    assert abs(E-r['raw_composite_error_approx'])<1e-6
    U=min(r['sieve_budget_approx'],r['raw_sieve_mass_approx']-L)
    margin=r['log_cell_approx']-r['old_budget_approx']-(U-r['singleton_mass_approx'])
    row=dict(n=n,composite_count=composite_count,pair_count=pair_count,error_approx=E,factor_pair_budget_approx=F,square_lower_mass_approx=L,cover_excess_approx=F-E,remaining_error_approx=E-L,corrected_budget_approx=U,improvement_over031_approx=r['sieve_budget_approx']-U,consumer_margin_approx=margin,old_margin_approx=r['log_cell_approx']-r['old_budget_approx'])
    rows.append(row)
    if packets:anchors.append(dict(row,windows=packets))
summary=dict(range=[3,300],additional_anchors=[1031,5000],source_sha256=hashlib.sha256(source.read_bytes()).hexdigest(),basis=[2,3,5],modulus=30,first_duplicate=first_duplicate,first_corrected_consumer_failure_approx=next((r['n'] for r in rows if r['consumer_margin_approx']<=0),None),passing_anchors_approx=[r['n'] for r in rows if r['consumer_margin_approx']>0],strict_improvement_anchors_approx=[r['n'] for r in rows if r['improvement_over031_approx']>1e-6],elapsed_seconds=round(time.monotonic()-start,3),scope='Integer factor pairs reconstructed independently; weights and margins are floating diagnostics only.')
(base/'logs/diagnostics-032.json').write_text(json.dumps(dict(summary=summary,rows=rows,anchors=anchors),separators=(',',':'))+'\n')
print(json.dumps(summary,indent=2))
