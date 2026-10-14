"""Independent adaptive endpoint carriers; floating weights are diagnostics only."""
from pathlib import Path
import math,json,hashlib,time
base=Path(__file__).resolve().parent.parent
source=base/'logs/diagnostics-034.json'
prior=json.loads(source.read_text());old={r['n']:r for r in prior['rows']}
ns=list(range(3,301))+[1031,5000];start=time.monotonic()
limit=(max(ns)**2+2*max(ns))//2
prime=bytearray([1])*(limit+1);prime[:2]=bytes(2)
for p in range(2,math.isqrt(limit)+1):
    if prime[p]:prime[p*p:limit+1:p]=bytes((limit-p*p)//p+1)
small=[p for p in range(2,math.isqrt(limit)+1) if prime[p]]
rows=[]
for n in ns:
    c=math.isqrt(n);basis=[p for p in small if p<=c];M=math.prod(basis)
    assert all(p<=2*n for p in basis) and n*n+2*n<(c+1)**4
    errors=[];semis=[];triples=[];count=0;scount=0;tcount=0;primeweights=[]
    for k in range(2,min(n-1,(n*n+2*n)//(2*n+1))+1):
        A=max(n*n//k,2*n);B=(n*n+2*n)//k
        comps={q for q in range(A+1,B+1) if math.gcd(q,M)==1 and not prime[q]}
        pairproducts=[r*s for r in small if r>c and r*r<=B
            for s in range(max(r,A//r+1),B//r+1) if prime[s] and s>c]
        tripleproducts=[r*s*t for r in small if r>c and r**3<=B
            for s in small if r<=s and s*s<=B//r
            for t in range(max(s,A//(r*s)+1),B//(r*s)+1) if prime[t]]
        assert len(pairproducts)==len(set(pairproducts))
        assert len(tripleproducts)==len(set(tripleproducts))
        assert not set(pairproducts)&set(tripleproducts)
        assert comps==set(pairproducts)|set(tripleproducts)
        errors.extend(math.log(q) for q in comps)
        semis.extend(math.log(q) for q in pairproducts)
        triples.extend(math.log(q) for q in tripleproducts)
        primeweights.extend(math.log(q) for q in range(A+1,B+1) if prime[q])
        count+=len(comps);scount+=len(pairproducts);tcount+=len(tripleproducts)
    E=math.fsum(errors);D3=math.fsum(semis+triples);Q=math.fsum(primeweights)
    assert abs(E-D3)<1e-7
    rows.append(dict(n=n,cutoff=c,basis=basis,composite_count=count,semiprime_count=scount,
        triple_count=tcount,error_approx=E,combined_mass_approx=D3,remaining_error_approx=E-D3,
        singleton_mass_approx=Q,corrected_budget_approx=Q,
        old_margin_approx=old[n]['old_margin_approx'],
        fixed_wheel_remaining_error_approx=old[n]['remaining_error_approx']))
summary=dict(range=[3,300],additional_anchors=[1031,5000],sample_count=len(rows),
    source_sha256=hashlib.sha256(source.read_bytes()).hexdigest(),
    exhaustive_carrier_checks=True,elapsed_seconds=round(time.monotonic()-start,3),
    scope='Independent endpoint pair/triple enumeration. Floating weights and inherited exact-ledger margins are diagnostics, not Lean premises.')
(base/'logs/diagnostics-035.json').write_text(json.dumps(dict(summary=summary,rows=rows),indent=2)+chr(10))
print(json.dumps(summary,indent=2))
