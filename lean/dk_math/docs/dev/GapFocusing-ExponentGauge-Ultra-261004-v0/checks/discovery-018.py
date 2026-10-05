"""Exact finite gcd/valuation diagnostics; never construct or store enormous products."""
from pathlib import Path
from math import gcd, isqrt
from collections import Counter
import json

base = Path(__file__).resolve().parent.parent
old = json.loads((base/'logs/discovery-017.json').read_text())
old_rows = {r['n']:r for r in old['rows']}
primes = [p for p in range(2,2101) if all(p % q for q in range(2,isqrt(p)+1))]

def factors(x):
    result = {}
    for p in primes:
        if p*p > x: break
        while x % p == 0:
            result[p] = result.get(p,0) + 1
            x //= p
    if x > 1: result[x] = result.get(x,0) + 1
    return result

rows = []
first_repeated = first_aggregate_difference = first_large_old_gcd = first_covered_coprime = None
for n in [0]+list(range(1,301))+[1031]:
    norm = n*n+(n+1)**2
    nf = factors(norm)
    gap_v = Counter()
    product_v = Counter()
    gcd_events = []
    covered_coprime = []
    both_colors = {} if n == 0 else {j: c == 3 for j,a,b,c in old_rows[n]['coloring']}
    local_values = []
    for j in range(n):
        left=n*n+n-j; right=n*n+n+1+j; gap=2*j+1
        g=gcd(left,right)
        assert g == gcd(norm,gap)
        local_values.append(g)
        gf=factors(g); gapf=factors(gap)
        gap_v.update(gapf)
        product_v.update(gf)
        assert gf == {p:min(v,gapf.get(p,0)) for p,v in nf.items() if min(v,gapf.get(p,0))}
        if g > 1:
            event=dict(n=n,j=j,gcd=g,gap=gap,factors=gf,covered_both=both_colors[j],
                       old=[p for p in gf if p<=n],fresh=[p for p in gf if p>n])
            gcd_events.append(event)
            assert all(p%4==1 and p<2*n for p in gf)
            if any(v>1 for v in gf.values()) and first_repeated is None: first_repeated=event
            if g>n and any(p<=n for p in gf) and first_large_old_gcd is None:first_large_old_gcd=event
        if g == 1 and both_colors[j]:
            covered_coprime.append(j)
            if first_covered_coprime is None:
                first_covered_coprime=dict(n=n,j=j,left=left,right=right,gcd=1,norm=norm)
    visible_v={p:min(v,gap_v[p]) for p,v in nf.items() if gap_v[p]}
    assert set(gap_v)=={p for p in primes if p!=2 and p<2*n}
    assert set(visible_v)==set(product_v)
    assert all(product_v[p]==sum(min(v,factors(2*j+1).get(p,0)) for j in range(n)) for p,v in nf.items())
    aggregate=1
    for p,v in visible_v.items():aggregate*=p**v
    norm_prime=len(nf)==1 and next(iter(nf.values()))==1
    if n>0: assert norm_prime==(aggregate==1)==all(g==1 for g in local_values)
    if visible_v!=dict(product_v) and first_aggregate_difference is None:
        first_aggregate_difference=dict(n=n,aggregate=aggregate,aggregate_factors=visible_v,local_product_factors=dict(product_v))
    row=dict(n=n,norm=norm,norm_factors=nf,norm_prime=norm_prime,
             odd_gap_prime_support=sorted(gap_v),odd_gap_valuations=dict(sorted(gap_v.items())),
             norm_gap_gcd=aggregate,aggregate_valuations=visible_v,
             local_gcd_product_valuations=dict(sorted(product_v.items())),nontrivial_pair_count=len(gcd_events),
             common_gcd_events=gcd_events,covered_coprime_pairs=covered_coprime,
             visible_old=[p for p in visible_v if p<=n],visible_fresh=[p for p in visible_v if p>n],
             invisible_norm_primes=[p for p in nf if p>=2*n],
             U=None if n<2 else old_rows[n]['one_covered'],
             escaping_seat_count=0 if n==0 else old_rows[n]['one_covered']+2*old_rows[n]['neither_covered'],
             covered_pair_count=0 if n==0 else old_rows[n]['different_owner_covered'],
             full_cover=n==0,positive_full_cover_observed=False)
    # The next two facts are arithmetic, not claims about hypothetical full cover.
    assert gcd(norm,(n+1)**2+(n+2)**2)==1
    if rows and rows[-1]['n']+1==n:
        assert gcd(rows[-1]['norm_gap_gcd'],aggregate)==1
        assert not set(rows[-1]['local_gcd_product_valuations'])&set(product_v)
    rows.append(row)
assert first_repeated['n']==21 and first_repeated['j']==12 and first_repeated['gcd']==25
assert first_aggregate_difference['n']==8
assert first_large_old_gcd['n']==21 and first_large_old_gcd['gcd']==25
assert first_covered_coprime==dict(n=4,j=0,left=20,right=21,gcd=1,norm=41)
selected=[r for r in rows if r['n'] in [1,2,3,5,6,8,11,19,21,29,297,1031]]
result=dict(range=[0,300],extra_anchors=[1031],rows=rows,selected=selected,
            smallest_repeated_prime_gcd=first_repeated,smallest_aggregate_difference=first_aggregate_difference,
            smallest_large_gcd_with_old_support=first_large_old_gcd,
            smallest_covered_coprime_pair=first_covered_coprime,
            full_cover_scope='No positive full-cover shell was observed. Conditional implications from full cover are not refuted by this scan.')
(base/'logs/discovery-018.json').write_text(json.dumps(result,indent=2)+'\n')
for r in selected:
    print(json.dumps({k:r[k] for k in ['n','norm','norm_factors','norm_gap_gcd','nontrivial_pair_count','visible_old','visible_fresh','local_gcd_product_valuations','U']}))
for key in ['smallest_repeated_prime_gcd','smallest_aggregate_difference','smallest_large_gcd_with_old_support','smallest_covered_coprime_pair']:
    print(key+': '+json.dumps(result[key]))
print(result['full_cover_scope'])
