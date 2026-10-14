"""Finite wheel weight and accumulated error, independent of carry membership."""
from pathlib import Path
from array import array
import json, math, hashlib, time

base = Path(__file__).resolve().parent.parent
source = base / 'logs/diagnostics-030.json'
old = json.loads(source.read_text())
start = time.monotonic()
limit = (5000**2+10000)//2
counts = array('I', [0])*(limit+1)
weights = array('d', [0.0])*(limit+1)
corrections = array('d', [0.0])*(limit+1)
count, total, correction = 0, 0.0, 0.0
for q in range(1,limit+1):
    if math.gcd(q,30)==1:
        count += 1
        weight = math.log(q)-correction
        updated = total+weight
        correction = (updated-total)-weight
        total = updated
    counts[q], weights[q], corrections[q] = count,total,correction

rows, anchors, passes, clipped = [], [], [], []
first_composite = None
anchor_set = {3,4,5,6,7,8,9,11,12,19,29,297,1031,5000}
for r in old['rows']:
    n=r['n'];b=n*n;w=2*n;t=b+w
    mass, survivors, packets = [], 0, []
    active=min(n-1,t//(w+1))
    for k in range(2,active+1):
        A,B=max(b//k,w),t//k
        survivors += counts[B]-counts[A]
        value=(weights[B]-weights[A])-(corrections[B]-corrections[A])
        mass.append(value)
        if n in anchor_set:
            qs=[q for q in range(A+1,B+1) if math.gcd(q,30)==1]
            direct=math.fsum(math.log(q) for q in qs)
            assert abs(value-direct)<1e-7
            assert len(qs)==counts[B]-counts[A]
            composites=[]
            for q in qs:
                divisor=next((d for d in range(2,math.isqrt(q)+1) if q%d==0),None)
                if divisor:
                    composites.append([q,divisor])
                    if first_composite is None:
                        first_composite=dict(n=n,k=k,q=q,least_divisor=divisor)
            alternatives={}
            for modulus in [6,30,210,2310]:
                # Basis primes must be below the window-prime cutoff.
                largest={6:3,30:5,210:7,2310:11}[modulus]
                if largest<=w:
                    alternatives[str(modulus)]=dict(
                        count=sum(math.gcd(q,modulus)==1 for q in range(A+1,B+1)),
                        weight_approx=math.fsum(math.log(q) for q in range(A+1,B+1) if math.gcd(q,modulus)==1))
            packets.append(dict(k=k,A=A,B=B,survivors=qs,composites=composites,
                direct_weight_approx=direct,alternatives=alternatives))
    raw=math.fsum(mass);Q=r['singleton_mass_approx'];G=r['geometric_budget_approx']
    W=min(G,raw);error=raw-Q;excess=W-Q
    assert survivors>=r['singleton_count'] and error>=-1e-6
    remainder=r['small_mass_approx']+r['repeated_mass_approx']+r['higher_mass_approx']
    margin=r['log_cell_approx']-remainder-W
    if margin>0:passes.append(n)
    if raw>G+1e-6:clipped.append(n)
    row=dict(n=n,basis=[2,3,5],modulus=30,survivor_count=survivors,
        prime_count=r['singleton_count'],composite_count=survivors-r['singleton_count'],
        singleton_mass_approx=Q,raw_sieve_mass_approx=raw,geometric_budget_approx=G,
        sieve_budget_approx=W,raw_composite_error_approx=error,capped_excess_approx=excess,
        gain_over_030_approx=G-W,consumer_margin_approx=margin,
        old_budget_approx=r['exact_old_budget_approx'],log_cell_approx=r['log_cell_approx'])
    rows.append(row)
    if packets:
        alternative_rows={}
        for modulus in [6,30,210,2310]:
            if all(str(modulus) in x['alternatives'] for x in packets):
                amass=math.fsum(x['alternatives'][str(modulus)]['weight_approx'] for x in packets)
                alternative_rows[str(modulus)]=dict(raw_mass_approx=amass,
                    composite_error_approx=amass-Q,capped_margin_approx=r['log_cell_approx']-remainder-min(G,amass))
        anchors.append(dict(row,windows=packets,alternative_wheels=alternative_rows))
summary=dict(range=[3,5000],source_sha256=hashlib.sha256(source.read_bytes()).hexdigest(),
    basis=[2,3,5],modulus=30,integer_scope='All survivor counts use exact prefix counts; anchor windows reconstructed by gcd and factored directly.',
    floating_scope='Kahan prefix differences and direct anchor fsum weights are diagnostics, never proof premises; tolerance 1e-6.',
    first_surviving_composite=first_composite,
    first_consumer_failure_approx=next((r for r in rows if r['consumer_margin_approx']<=0),None),
    passing_anchors_approx=passes,passing_count=len(passes),failure_count=len(rows)-len(passes),
    raw_above_geometric_anchors_approx=clipped,
    minimum_gain_over_030_approx=min(r['gain_over_030_approx'] for r in rows),
    minimum_gain_after3_approx=min(r['gain_over_030_approx'] for r in rows if r['n']>3),
    elapsed_seconds=round(time.monotonic()-start,3))
(base/'logs/diagnostics-031.json').write_text(json.dumps(dict(summary=summary,rows=rows,anchors=anchors),separators=(',',':'))+'\n')
print(json.dumps(summary,indent=2))
