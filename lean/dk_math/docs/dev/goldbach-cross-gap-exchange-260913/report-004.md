# CGE-004 report

## Scope

Implemented the balanced-window capacity and first-overlap ledger requested by
`instruction-004.md`.  The module evaluates obstruction waves using the actual
window width `w`, separates repeated incidences from covered seats, and keeps
survivor existence conditional.

## Files

- Added `DkMath/NumberTheory/Goldbach/BalancedCapacity.lean`.
- Updated `DkMath/NumberTheory/Goldbach.lean` to export the module.
- Extended `DkMathTest/NumberTheory/GoldbachBalancedReflectionAudit.lean` with
  capacity, overlap, conservation, and target-30 regressions.

## Production theorem list

- `goldbachWindowIncidence`
- `goldbachWindow_covered_le_incidence`
- `goldbachWindow_blocked_card_le_residue_capacity`
- `goldbachWindow_incidence_le_residue_capacity`
- `goldbachObstructionSupportIn`
- `goldbachWindowLocalOverlapExcess`
- `goldbachWindowOverlapExcess`
- `goldbachWindowIncidence_eq_covered_add_overlapExcess`
- `goldbachWindowIncidenceConservation`
- `goldbachWindowSurvivors_nonempty_iff_incidence_lt`
- `goldbachWindowSurvivor_of_incidence_le_of_overlap_le`
- `goldbachWindowSurvivor_of_residue_capacity_of_overlap_lower`
- `goldbachPairAt_of_goldbachWindow_residue_capacity_of_overlap_lower`

## Width-local capacity

`goldbachWindowIncidence n w S` is

```text
∑ r ∈ S, (goldbachWindowBlockedSeats n w r).card
```

and the cover is bounded by this incidence.  For every `n`, `w`, and `r`, the
per-prime theorem is

```text
card (goldbachWindowBlockedSeats n w r)
  ≤ (if r ∣ 2*n then 1 else 2) * (w / r + 1)
```

The proof injects a blocked seat `t` into
`((t : ZMod r), t / r)`.  The residue coordinate lies in the existing
`goldbachForbiddenResidues`, while the quotient lies below `w / r + 1`.
Thus the theorem has the required width-local arithmetic and does not reuse
the full-fiber `n-2` bound.

Summing the per-prime result gives

```text
goldbachWindowIncidence n w S ≤
  ∑ r ∈ S, (if r ∣ 2*n then 1 else 2) * (w / r + 1)
```

for every finite world `S`.

## Generic support and overlap ledger

`goldbachObstructionSupportIn n t S` is the existing proper-obstruction
predicate restricted to an arbitrary finite world `S`.  The local excess is
the support cardinality minus one, and `goldbachWindowOverlapExcess` sums this
over the balanced window.  It records repeated obstruction mass: one covered
seat pays for the first obstruction, and every further incidence is overlap
payment.  It never negates an obstruction.

The exact first-overlap identity is

```text
goldbachWindowIncidence =
  card goldbachWindowCoveredSeats + goldbachWindowOverlapExcess
```

Combining it with CGE-003 gives

```text
card goldbachWindowSurvivors + goldbachWindowIncidence =
  card goldbachBalancedOffsets + goldbachWindowOverlapExcess
```

and the exact normal form

```text
window survivor exists ↔
window incidence < window card + window overlap excess
```

## Conditional provider interface

The generic theorem accepts an incidence upper bound `I ≤ C`, an overlap lower
bound `e ≤ E`, and the strict budget `C < card(window) + e`; it returns a
window survivor.  A residue-capacity corollary supplies `C` from the width-
local sum.  The anchor-local corollary then uses CGE-003's hypotheses
`w ≤ n`, `P < n-w`, and `n+w ≤ squareBody P` to return `GoldbachPairAt n`.

No universal cover inequality, universal survivor existence, or Strong
Goldbach theorem is supplied.

## Target-30 audit

For `n=15`, `w=8`, and `S=primeScalesUpTo 5 = {2,3,5}`, the kernel-checked
values are:

```text
card Window   = 9
card Covered  = 6
Incidence     = 9
Overlap       = 3
Capacity sum  = 10
```

The incidence-only inequality `10 < 9` fails, while the overlap-paid budget
`10 < 9 + 3` holds.  This demonstrates that localization alone is not the
same as a provider: overlap accounting is an independent ledger input.

## Reuse and firewalls

`BalancedReflection.lean` supplies the window and reflection API.  `Capacity`
supplies the original blocked/covered/survivor definitions, and
`Overlap.lean` / `PairOverlap.lean` are not copied or window-expanded.  The
implementation does not use AKS, RH, CFBRC, analytic density, or coprimality
as a primality substitute.

## Verification

Focused build command:

```text
lake build DkMath.NumberTheory.Goldbach DkMathTest.NumberTheory.GoldbachBalancedReflectionAudit
```

The focused build completed successfully with 8730 jobs.  The audit
`#print axioms` output contains only the repository's standard
`propext`, `Classical.choice`, and `Quot.sound`; no `sorryAx` or newly
introduced axiom is present.

Facade build:

```text
lake build DkMath
```

The facade build completed successfully with 9853 jobs.  A fresh warning
filter found no warnings other than the repository's excluded
`declaration uses \`sorry\`` category.

The forbidden-construct grep over the added implementation and extended audit
found no `sorry`, `admit`, `native_decide`, `unsafe`, or new `axiom`
declaration.  `git diff --check` also passed.

## Outcome

**Outcome A — WIDTH-LOCAL CAPACITY + EXACT OVERLAP LEDGER.**

The `w / r + 1` local capacity, exact window incidence/cover/overlap
conservation, and conditional survivor interface are production theorems.
The next stage needs one nontrivial lower bound for
`goldbachWindowOverlapExcess`, or a theorem supplying that payment from
prime-pair overlap or CRT structure.
