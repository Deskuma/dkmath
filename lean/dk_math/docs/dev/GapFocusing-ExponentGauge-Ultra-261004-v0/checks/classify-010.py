"""Bounded CRT family discovery, with Lean checking all emitted certificates.

Basis7 is fixed first. Basis10 adds23,29,31 at five scaling checkpoints only.
Only pair/triple subsets, positive CRT lifts in1..2n, and actual candidates
are emitted. No whole-shell incidence or whole-shell excess is evaluated.
"""
from pathlib import Path
from itertools import combinations
from math import gcd, isqrt, prod
import json

base = Path(__file__).resolve().parent.parent
root = base.parents[2]
old = json.loads((base/'logs/classification-009.json').read_text())
survivors = [r for r in old if not r['solved']]
caps = {r['n']: (r['upper'], r['candidate']) for r in old}

# The extra caps use the existing prime-anchor endpoint/one-divisor formula,
# not actual incidence. Lean independently checks these cap values.
def prime_cap(n):
    assert all(n % d for d in range(2, isqrt(n)+1))
    total = 0
    for q in range(3, n):
        if any(q % d == 0 for d in range(2, isqrt(q)+1)):
            continue
        lo, hi = n*n//q, (n*n+2*n)//q
        raw = (hi+1)//2 - (lo+1)//2
        excluded = (hi//n+1)//2 - (lo//n+1)//2
        total += min((n-1)//q+1, raw-excluded)
    return total, n-1

for n in (107, 127, 211, 503):
    caps[n] = prime_cap(n)

basis7 = [3, 5, 7, 11, 13, 17, 19]
bases = {7: basis7, 10: basis7+[23, 29, 31]}
checkpoints = [(7, r['n']) for r in survivors] + [(7, n) for n in (107, 127, 211, 503)]
checkpoints += [(10, n) for n in (97, 107, 127, 211, 503)]
rows = []
for tag, n in checkpoints:
    active = [q for q in bases[tag] if q <= n and n % q]
    pool = [Q for k in (2, 3) for Q in combinations(active, k)]
    witnesses = []
    merged = {}
    short = {}
    floor_merged = {}
    floor_index = 0
    for Q in pool:
        m = prod(Q)
        # Integer modular arithmetic in discovery; Lean verifies point congruences.
        first = (m-n*n) % (2*m) or 2*m
        for r in range(first, 2*n+1, 2*m):
            if gcd(n, r) != 1:
                continue
            witnesses.append({'seat': r, 'primes': list(Q)})
            merged.setdefault(r, set()).update(Q)
            if m < n:
                short.setdefault(r, set()).update(Q)
            if r <= 2*m*((n-1)//m):
                floor_merged.setdefault(r, set()).update(Q)
                floor_index += len(Q)-1
    B, A = caps[n]
    C = sum(len(Q)-1 for Q in merged.values())
    raw = sum(len(w['primes'])-1 for w in witnesses)
    Cshort = sum(len(Q)-1 for Q in short.values())
    D = B-A+1
    rows.append({'basis_size': tag, 'n': n, 'upper': B, 'candidate': A,
                 'required': D, 'merged_charge': C, 'index_charge': raw,
                 'short_product_charge': Cshort, 'margin': C-D, 'solved': C >= D,
                 'seats': len(merged), 'family_records': len(witnesses),
                 'prime_floor_index_sum': sum((n-1)//prod(Q)*(len(Q)-1) for Q in pool),
                 'floor_pool_index_charge': floor_index,
                 'floor_pool_merged_charge': sum(len(Q)-1 for Q in floor_merged.values()),
                 'anchor_prime': all(n%d for d in range(2,isqrt(n)+1)),
                 'witnesses': witnesses})

mixed = [(58,1,29,1), (62,1,31,1), (68,2,17,1), (74,1,37,1),
         (76,2,19,1), (80,4,5,1), (82,1,41,1), (86,1,43,1),
         (88,3,11,1), (92,2,23,1), (94,1,47,1), (98,1,7,2), (100,2,5,2)]

header = '''/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

'''
def finite(items):
    items = list(items)
    return '{'+(',\n    ' if len(items)>3 else ', ').join(items)+'}'

source = header+'''import DkMath.NumberTheory.Legendre.ParitySafeMixedCRT
import DkMathTest.NumberTheory.LegendreAdaptiveClassification

#print "file: DkMathTest.NumberTheory.LegendreMergedCRTData"

namespace DkMathTest.LegendreMergedCRT

def controlledBasis (tag : ℕ) : Finset ℕ :=
  if tag = 7 then {3, 5, 7, 11, 13, 17, 19} else {3, 5, 7, 11, 13, 17, 19, 23, 29, 31}

-- tag,n,B2,A,merged charge; discovery is not a proof.
def checkpointData : Finset (ℕ × ℕ × ℕ × ℕ × ℕ) :=
  '''+finite(f"({r['basis_size']}, {r['n']}, {r['upper']}, {r['candidate']}, {r['merged_charge']})" for r in rows)+'''

-- tag,n,index charge,short-product merged charge.
def comparisonData : Finset (ℕ × ℕ × ℕ × ℕ) :=
  '''+finite(f"({r['basis_size']}, {r['n']}, {r['index_charge']}, {r['short_product_charge']})" for r in rows)+'''

def extraCapData : Finset (ℕ × ℕ × ℕ) :=
  '''+finite(f'({n}, {caps[n][0]}, {caps[n][1]})' for n in (107,127,211,503))+'''

-- tag,n,raw floor index sum,merged charge of the first floor-many lifts.
def floorComparisonData : Finset (ℕ × ℕ × ℕ × ℕ) :=
  '''+finite(f"({r['basis_size']}, {r['n']}, {r['prime_floor_index_sum']}, {r['floor_pool_merged_charge']})"
             for r in rows if r['anchor_prime'])+'''

def mixedAnchorData : Finset (ℕ × ℕ × ℕ × ℕ) :=
  '''+finite(f'({n}, {a}, {p}, {k})' for n,a,p,k in mixed)+'''

-- Every pair/triple CRT family is represented by its actual seat and prime labels.
set_option maxRecDepth 100000 in
def familyData (tag n : ℕ) : Finset (ℕ × Finset ℕ) :=
  match tag, n with
'''
for row in rows:
    source += f"  | {row['basis_size']}, {row['n']} => "+finite(
        f"({w['seat']}, {finite(map(str,w['primes']))})" for w in row['witnesses'])+'\n'
source += '''  | _, _ => ∅

end DkMathTest.LegendreMergedCRT
'''
(root/'DkMathTest/NumberTheory/LegendreMergedCRTData.lean').write_text(source)
(base/'logs/classification-010.json').write_text(json.dumps(rows, indent=2)+'\n')
summary = '\n'.join(f"basis{r['basis_size']} n={r['n']}: A={r['candidate']} B2={r['upper']} "
                    f"D={r['required']} C={r['merged_charge']} C-D={r['margin']} "
                    f"index={r['index_charge']} short={r['short_product_charge']}" for r in rows)+'\n'
(base/'logs/classification-summary-010.txt').write_text(summary)
print(summary, end='')
