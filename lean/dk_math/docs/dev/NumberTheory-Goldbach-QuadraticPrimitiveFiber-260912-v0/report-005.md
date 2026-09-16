# QP-005 — information-gain verdict and closeout

Date: 2026-09-12. **Primary outcome: Outcome B — structural normalization only.**
The qualified primitive/parity/gcd/support facts are correct. This investigation
found no strict capacity improvement or new independent short-fiber escape
estimate. Strong Goldbach remains unproved.

This conclusion concerns the candidates actually audited here; it is not an
impossibility theorem about future uses of these coordinates.

## Incremental evidence trail

| Phase | Pre-existing committed report | Result |
|---|---|---|
| QP-000 | [report-000](report-000.md), `7014733c2` | Source and Mathlib inventory; original HEAD `b723621ed9a6d9a33fd36ed20e4c2cdfbe933123` |
| QP-001 | [report-001](report-001.md), `fb098d0b3` | Canonical quadratic boundary, exact parity equivalence, positive-pair normalization, diagonal exception |
| QP-002 | [report-002](report-002.md), `f931c16cf` | Left/right proper supports, center/two removal, exact reduced-world survival, first numerical scan |
| QP-003 | [report-003](report-003.md), `57d72d21d` | Exact LL/LR/RR and reconciliation with the original full ledger |
| QP-004 | [report-004](report-004.md), `7d31cf2a2` | Oriented CRT, actual interval spacing, sharpness and false cardinality shortcut |

All previous reports remain unchanged. The present report records the final
comparison and later findings rather than replacing the earlier record.

## Exact formal comparison

All scratch names are in namespace
`DkMathTest.GoldbachQuadraticPrimitiveAstra` in
[GoldbachQuadraticPrimitiveAstra.lean](../../../DkMathTest/NumberTheory/GoldbachQuadraticPrimitiveAstra.lean).

Write A for the production admissible offsets, P for primitive positive
parity-compatible offsets, C for production covered seats, C' for normalized
covered seats, S for production survivors, and S' for normalized survivors.
`normalizedCovered` and `normalizedSurvivors` use the **reduced** world, with
proper endpoint exceptions. They are not raw CRT survivors.

The new kernel-checked statements are:

- `normalized_survivors_eq_positive`: S' is exactly the positive-offset
  filter of S, even though the obstruction world was reduced.
- `zero_survivor_iff`: zero belongs to S iff the center n is prime.
- `survivors_exact_split`: S = S' ∪ diagonalSeats(n), disjointly.
- `survivor_card_exact`: |S| = |S'| + δ, where δ is 1 for prime n and 0 otherwise.
- `normalized_conservation`: |S'| + |C'| = |P|.
- `capacity_balance`: (n-1) + |C'| = |P| + |C| + δ. This additive form avoids
  any hidden assumptions about truncated natural subtraction. Equivalently,
  candidate removal minus covered-seat removal is exactly the lost diagonal.
- `pair_iff_normalized_capacity`: GoldbachPairAt(n) iff
  Prime(n) or |C'| < |P|.
- `strongGoldbach_iff_normalized_capacity` and
  `capacityEscape_iff_normalized_capacity`: the restored-diagonal universal
  condition is equivalent both to StrongGoldbach and to the **existing**
  GoldbachCapacityEscape.

Thus reduced obstruction directions exactly compensate for filtering already
blocked candidates, with the one explicit diagonal correction. A relative
survivor density can increase because its denominator shrinks; the number of
positive solutions is unchanged. The strict capacity inequality has not been
proved uniformly. At nonprime centers its margin is exactly the original
margin; at prime centers the omitted diagonal accounts for one unit.

## Quantitative audit: centers 0..500

[Numeric script](numeric/goldbach_quadratic_primitive.py),
[summary JSON](numeric/qp-005-summary.json), [center CSV](numeric/qp-005-centers.csv),
and [console snapshot](numeric/qp-005-summary.txt) are reproducible with only
standard Python. The earlier snapshots retain detailed seat and wave evidence.

For n≥2 the script additionally checks exact candidate formulas
`|primitiveOffsets| = phi(n)-1` and `|P| = phi(2*n)/2-1` against enumeration.
These totient formulas and the full-period phi count in QP-004 are numerical
checks plus arithmetic explanations, **not universal Lean cardinality theorems
added by this investigation**. The kernel-checked comparison is the set and
capacity identity above and does not rely on those formulas.

Each removed prime direction (two or a center divisor within the cutoff)
removes exactly one merged raw forbidden residue class; the remaining primes
each have two classes. Summing local class counts is not a union capacity.
The script records both the number of removed directions and these class
counts, separately from actual proper coverage.

| Observation | Finite result |
|---|---|
| Correctly qualified invariant checks | No failures; the script asserts the ten checks listed in its JSON summary |
| Original survivor count vs normalized | Equal at composite centers; one fewer after normalization at prime centers |
| Primitive-only density | Improved at 404 comparable centers, worsened at 94; undefined at n=2 |
| Primitive-parity density | Improved at all 497 comparable centers n=4..500; undefined at n=2,3 |
| Worst normalized density in this range | n=496: 13/239; next n=439: 13/218 |
| Least candidate removal, n≥2 | n=2 removes 1; n=3 and n=4 remove 2 |
| Most candidate removal | n=495 removes 375; n=480 removes 352; n=483 removes 351 |
| Oriented CRT interval checks | 21,192 orientations through center 500 |
| Full normalization-period checks | 120 orientations, restricted to centers ≤40 |

The density statements are bounded observations, not uniform lower bounds.
Undefined densities use a null value, never a fabricated zero denominator.
Even the unnormalized primitive density can worsen because the diagonal is
removed: center 3 is the first example. Parity subsequently discards many
composite seats, which explains the observed relative density improvement.

## Rejected stronger candidates

The scratch file encodes the important counterexamples with kernel `decide`:

- Dropping the subtraction bound: smallest scanned `(0,1)`.
- Primitive without parity: reflected gcd two at `(3,1)` and shared proper
  two at `(5,1)`.
- Parity without primitive: shared odd proper factor at `(9,0)`; the smallest
  positive version found by the final scan is `(12,3)`.
- Deleting the diagonal branch: center 2 has GoldbachPairAt but empty P.
- Vanishing higher overlap: `(31,4)` retains support {3,5,7} and residual 1.
- Strict incidence bound even on P: `normalized_incidence_counterexample`
  at n=19 has |P|=8, |C'|=7, |S'|=1, incidence=8.
- Stronger universal oriented spacing: `sharp_spacing_regression` at n=47
  realizes two proper LR seats separated by exactly 2*p*q.
- Substituting candidate cardinality for interval width: n=50 gives two raw
  seats with 19 candidates < modulus 21. The final scan also finds a **proper**
  version: `proper_cardinality_not_width_regression` at n=162 has 53 candidates
  < modulus 65 and offsets 7,137. Endpoints are (155,169) and (25,299); each
  seat has proper left divisor 5 and proper right divisor 13.

Minima refer to exhaustive scans within the stated range, not a separately
formalized universal minimality theorem. The two proper seats at n=162 show
that the cardinality failure is not merely caused by endpoint equality.
These rejected strengthenings do not invalidate the correctly qualified
normalization chain, so the primary verdict remains Outcome B.

## Why the product wave is not strict information gain

The oriented wave supplies a useful decomposition, a modular injection and
spacing. But these are derived directly from Mathlib CRT and the production
raw coordinate theorems; the existing production full-world proof already
contains the same coordinate bijection and bounded injectivity. The number
alone does not determine spatial placement; the underlying CRT bijection
does. Adding parity is simply adjoining its existing modulus two.

No new monotone quantity or independent collision constraint was found beyond
these derived exact identities. Proper exceptions remain nonperiodic. Neither
one-residue existence over a full period, nor at-most-one occupancy in a short
interval, proves that some short-interval candidate survives all obstructions.
The unconditional uniform step remains open.

## Final verification and artifacts

Executed from `lean/dk_math`, all with exit 0:

```bash
lake build DkMathTest.NumberTheory.GoldbachQuadraticPrimitiveAstra
lake build DkMath.NumberTheory.Goldbach DkMathTest.NumberTheory.GoldbachGNFiber
lake env lean docs/dev/NumberTheory-Goldbach-QuadraticPrimitiveFiber-260912-v0/AxiomAudit.lean
python3 docs/dev/NumberTheory-Goldbach-QuadraticPrimitiveFiber-260912-v0/numeric/goldbach_quadratic_primitive.py --max-center 500 --summary-json docs/dev/NumberTheory-Goldbach-QuadraticPrimitiveFiber-260912-v0/numeric/qp-005-summary.json --csv docs/dev/NumberTheory-Goldbach-QuadraticPrimitiveFiber-260912-v0/numeric/qp-005-centers.csv
git diff --check
```

The script's stdout is saved as `numeric/qp-005-summary.txt`. A second run to
`/tmp` reproduced JSON, CSV and stdout byte-for-byte (`cmp`, all exit 0).
Both builds report 8692 jobs; final scratch build took 8.6 seconds.
[AxiomAudit.lean](AxiomAudit.lean) queries all 59 named definitions/theorems.
Dependencies are confined to `propext`, `Classical.choice`, `Quot.sound`.
All three final verification logs have no errors or warnings; the scratch
contains none of `sorry`, `admit`, user `axiom`, `unsafe`, `native_decide`.
See [verification summary](verification/audit-summary.txt) and its sibling logs.

Early QP-005 elaboration failures came from broad simplification of the
zero-seat proposition, a redundant argument to a Finset cardinality theorem,
and branch simplification in the capacity equivalence. Explicit local facts
and case splits repaired them; the final proofs require no increased limits.

The source diff is confined to the authorized scratch target and this research
document directory. Production Goldbach/Lib files are unchanged, and the
production facade does not import scratch. The six committed phase reports,
scratch Lean, audit, Python and snapshots close the requested research pass.

Final staging check caught the CSV writer default CRLF line endings as trailing
whitespace under this repository configuration. The writer now explicitly uses
LF; CSV was regenerated and the byte-for-byte reproduction checks were repeated.
