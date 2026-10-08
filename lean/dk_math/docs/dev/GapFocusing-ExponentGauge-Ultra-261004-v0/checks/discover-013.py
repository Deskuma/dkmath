"""Bounded independent discovery; these outputs are not Lean proofs."""
from pathlib import Path
from math import gcd, isqrt, comb
import json

base = Path(__file__).resolve().parent.parent
limit = 3000
sieve = bytearray([1]) * (limit + 1)
sieve[:2] = b'\0\0'
for p in range(2, isqrt(limit) + 1):
    if sieve[p]:
        sieve[p*p:limit+1:p] = b'\0' * len(range(p*p, limit+1, p))
primes = [p for p in range(2, limit+1) if sieve[p]]

def row(n):
    cutoff = isqrt(n)
    small = [p for p in primes if p <= cutoff]
    active = [p for p in primes if cutoff < p < n and p != 2]
    seats = [r for r in range(1, 2*n+1)
             if gcd(n, r) == 1 and (n*n+r) % 2 == 1
             and all((n*n+r) % p for p in small)]
    sizes = [sum((n*n+r) % p == 0 for p in active) for r in seats]
    incidence = sum(sizes)
    pair = sum(comb(k, 2) for k in sizes)
    triple = sum(comb(k, 3) for k in sizes)
    uncovered = sizes.count(0)
    assert max(sizes, default=0) <= 3
    assert len(seats) + pair == uncovered + incidence + triple
    return dict(n=n, P=cutoff, R=len(seats), I=incidence, M2=pair, M3=triple,
                U=uncovered, direct_margin=max(0, len(seats)-incidence),
                moment_margin=len(seats)+pair-incidence-triple,
                classes=[sizes.count(k) for k in range(4)])

calibration = [row(n) for n in [211, 503, 1009, 1013, 1019]]
scan = []
first = None
for n in primes:
    result = row(n)
    scan.append(result)
    if result['I'] >= result['R'] and result['U'] > 0:
        first = result
        break
result = dict(calibration=calibration, scan_upper=limit, scan_count=len(scan),
              scan_last=scan[-1]['n'], first=first, scan=scan)
(base / 'logs/discovery-013.json').write_text(json.dumps(result, indent=2) + '\n')
print(json.dumps({k: v for k, v in result.items() if k != 'scan'}, indent=2))
