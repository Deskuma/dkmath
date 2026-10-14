"""Finite residue/owner/census diagnostics, all natural anchors 1..300 plus 1031.
Python output is exploratory evidence; selected regressions are checked in Lean.
"""
from pathlib import Path
from math import gcd, isqrt, prod
from collections import Counter
import json

base = Path(__file__).resolve().parent.parent
limit = 1033
primes = [p for p in range(2, limit + 1) if all(p % q for q in range(2, isqrt(p) + 1))]

def factors(x):
    out = []
    for p in primes:
        if p*p > x:
            break
        if x % p == 0:
            k = 0
            while x % p == 0:
                x //= p
                k += 1
            out.append((p, k))
    if x > 1:
        out.append((x, 1))
    return out

def row(n):
    basis = [p for p in primes if p <= n]
    period = prod(basis)
    anchor = n*n
    images, survivors, escapes = set(), set(), []
    owner_fibers, overlaps = Counter(), Counter()
    census = Counter()
    transitions = dict(lower_common=Counter(), upper_common=Counter(), lower_owner_persist=0,
                       upper_owner_persist=0, three_lower_owner_persist=0)
    for r in range(1, 2*n+1):
        x = anchor+r
        fs = factors(x)
        support = [p for p,k in fs if p <= n]
        overlaps[len(support)] += 1
        coord = x % period
        images.add(coord)
        if support:
            owner_fibers[support[0]] += 1
        else:
            escapes.append(r)
            if 0 < coord < period:
                survivors.add(coord)
        if gcd(2*n, x) == 1 and all(p > isqrt(n) for p,k in fs):
            census['R'] += 1
            if not support:
                census['U'] += 1
            elif len(support) == 1:
                if len(fs) == 1 and fs[0][1] == 3:
                    census['Cube'] += 1
                else:
                    assert len(fs) == 2 and all(k == 1 for p,k in fs), (n,x,fs)
                    census['Cross'] += 1
            elif len(support) == 2:
                assert len(fs) == 2 and sorted(k for p,k in fs) == [1,2], (n,x,fs)
                census['Repeated'] += 1
            else:
                assert len(support) == 3 and all(k == 1 for p,k in fs), (n,x,fs)
                census['Triple'] += 1
        rr = r if r < n+1 else r+1
        new = (n+1)**2 + rr
        newsup = [p for p,k in factors(new) if p <= n+1]
        common = set(support) & set(newsup)
        channel = 'lower' if r < n+1 else 'upper'
        transitions[channel+'_common'][len(common)] += 1
        for p in common:
            assert ((2*n+1) if channel == 'lower' else 2*(n+1)) % p == 0
            if channel == 'upper' and n+1 in primes:
                assert p == 2
        if support and newsup and support[0] == newsup[0]:
            transitions[channel+'_owner_persist'] += 1
            if channel == 'lower':
                nextsup = [p for p,k in factors((n+2)**2+r) if p <= n+2]
                if nextsup and nextsup[0] == support[0]:
                    transitions['three_lower_owner_persist'] += 1
    raw, rejected = 0, 0
    rough_owners = [p for p in basis if p > isqrt(n) and p != 2 and n % p]
    for p in rough_owners:
        for q in range(anchor//p+1, (anchor+2*n)//p+1):
            if gcd(2*n, q) == 1:
                raw += 1
                if any(u <= isqrt(n) for u,k in factors(q)):
                    rejected += 1
    counts = {k: census[k] for k in ['R','U','Cube','Cross','Repeated','Triple']}
    counts.update(Rejected=rejected, Qtotal=raw)
    assert counts['R'] == counts['U']+counts['Cube']+counts['Cross']+counts['Repeated']+counts['Triple']
    assert raw == counts['Cross']+counts['Cube']+2*counts['Repeated']+3*counts['Triple']+rejected
    assert raw+counts['U'] == counts['R']+counts['Repeated']+2*counts['Triple']+rejected
    assert transitions['three_lower_owner_persist'] == 0
    assert sum(owner_fibers.values())+len(escapes) == 2*n
    assert (len(images) == 2*n) == (n == 3 or n >= 5)
    if n >= 5:
        assert 2*n+4 < period and len(survivors) == len(escapes)
    return dict(n=n, basis=basis, square_anchor=anchor % period, period=period, width=2*n,
                image_card=len(images), projected_survivors=len(survivors), escaping_card=len(escapes),
                full_cover=not escapes, owner_fibers=dict(sorted(owner_fibers.items())),
                support_overlap=dict(sorted(overlaps.items())), first_escape=escapes[0] if escapes else None,
                counts=counts, transition=transitions)

rows = [row(n) for n in range(1,301)]
near = sorted((r for r in rows if r['n'] >= 5), key=lambda r:(r['projected_survivors'], r['n']))[:12]
# A separate finite stress ranking; no asymptotic conclusion.
relative = sorted((r for r in rows if r['n'] >= 30), key=lambda r:(r['escaping_card']/r['width'], r['n']))[:12]
false_rule = []
for n in range(1,301):
    for r in range(1,2*n+1):
        fs = factors(n*n+r)
        if gcd(2*n,n*n+r) == 1 and all(p>isqrt(n) for p,k in fs) and len(fs)==2 and sorted(k for p,k in fs)==[1,2] and fs[1][0]<=n:
            repeated = next(p for p,k in fs if k == 2)
            if fs[0][0] != repeated:
                false_rule.append(dict(n=n,r=r,point=n*n+r,owner=fs[0][0],repeated_prime=repeated))
assert false_rule[0] == dict(n=8,r=11,point=75,owner=3,repeated_prime=5)
prime_false = next(r for r in false_rule if r['n'] in primes)
assert prime_false == dict(n=29,r=6,point=847,owner=7,repeated_prime=11)
result = dict(range=[1,300], anchor_count=len(rows), rows=rows, calibration1031=row(1031),
              near_misses=near, relative_stress=relative, smallest_false_owner_rule=false_rule[0],
              smallest_prime_false_owner_rule=prime_false)
(base/'logs/discovery-016.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(dict(anchor_count=len(rows), near_misses=[(r['n'],r['projected_survivors']) for r in near],
                     relative_stress=[(r['n'],r['projected_survivors'],r['width']) for r in relative],
                     calibration1031=result['calibration1031']['counts']),indent=2))
