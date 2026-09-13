# CGE-003 report

## Scope

Implemented the localized balanced-reflection survivor-provider interface
requested by `instruction-003.md`.  The implementation restricts the existing
Goldbach offset fiber to a finite central window, canonicalizes Cross-Gap
outputs by orientation-free reflection, and keeps survivor existence
conditional.

## Files

- Added `DkMath/NumberTheory/Goldbach/BalancedReflection.lean`.
- Added `DkMathTest/NumberTheory/GoldbachBalancedReflectionAudit.lean`.
- Updated `DkMath/NumberTheory/Goldbach.lean` to export the module.

## Balanced window and reflection API

`goldbachBalancedOffsets n w` is exactly

```text
(goldbachOffsets n).filter (fun t => t ≤ w)
```

with membership, subset, range, and exact card theorems.  Its cardinality is
`min (n - 1) (w + 1)`.

The wrappers
`reflectionLeft n t = n - t` and `reflectionRight n t = n + t` preserve
`2*n` under `t ≤ n`.  Balanced membership supplies the endpoint bounds
`n-w ≤ n-t ≤ n+t ≤ n+w` when `w ≤ n`.

## Cross-Gap canonicalization

`crossGapReflectionOffset` is defined as

```text
n - min CrossLeft CrossRight
```

under the existing `CrossGapEvenFiberAt` conservation law.  The production
theorems identify `min CrossLeft CrossRight` with `n-t` and `max CrossLeft
CrossRight` with `n+t`, without imposing a permanent `CrossLeft ≤ CrossRight`
orientation.  A fiber with eligible endpoints has an admissible canonical
offset, and an offset bound places it in the balanced window.

## Window blocked / covered / survivors

The window APIs are restrictions of the existing APIs:

- `goldbachWindowBlockedSeats n w r` is `goldbachBlockedSeats n r` intersected
  with the balanced window.
- `goldbachWindowCoveredSeats n w S` is the existing cover intersected with the
  balanced window.
- `goldbachWindowSurvivors n w S` filters the balanced window by the existing
  `GoldbachSurvives n S` predicate.

The cover is proved equal both to the bi-union of restricted blocks and to the
complementary survivor filter.  The exact conservation theorem is

```text
card windowSurvivors + card windowCovered = card window
```

for every finite obstruction world `S`.  Consequently, window survivor
nonemptiness is equivalent to strict cover shortfall.

## Anchor-local SquareBody bridge

For `S = primeScalesUpTo P`, a window survivor yields support disjointness for
both reflection endpoints.  With `w ≤ n`, `P < n-w`, and
`n+w ≤ squareBody P`, the existing
`FixedBigGauge.prime_iff_supportDisjointFrom_in_squareShell` theorem certifies
both endpoints as prime.  This yields `GoldbachPairAt n` conditionally.

The strict window-cover theorem has the same hypotheses and accepts only the
finite inequality

```text
card windowCovered < card window
```

as its provider-facing input.  No universal inequality or universal survivor
existence theorem is supplied.

## Capacity / Overlap reuse

`Capacity.lean` supplies the original blocked, covered, survivor, and card
conservation APIs; the new module uses them by restriction.  `Overlap.lean`
and `PairOverlap.lean` are not duplicated or reimplemented.  No window-wide
incidence hierarchy is introduced.

## Primorial / reflection audit

The audit replays the target-30 reflections `13+17`, `11+19`, and `7+23`, and
checks the endpoint-one reflection `1+29` as non-prime.  It also checks the
fixed point `1+1=2`.  These are conceptual regressions only and are not proof
dependencies of the production provider interface.

## Verification

Focused build command:

```text
lake build DkMath.NumberTheory.Goldbach DkMathTest.NumberTheory.GoldbachBalancedReflectionAudit
```

The focused build completed successfully with 8729 jobs, and the audit
`#print axioms` checks passed.  The axiom output contains no `sorryAx` and no
newly introduced axiom.

Facade build:

```text
lake build DkMath
```

The facade build completed successfully with 9852 jobs.  A fresh warning
filter found no warnings other than the repository's excluded
`declaration uses \`sorry\`` category.

The forbidden-construct grep over the added implementation and audit files
found no `sorry`, `admit`, `native_decide`, `unsafe`, or new `axiom`
declaration.

## Outcome

**Outcome A — LOCALIZED SURVIVOR PROVIDER INTERFACE.**

Balanced reflection windows, Cross-Gap canonical offsets, exact local cover
conservation, and anchor-local SquareBody certification are now connected in
one API.  The next exact provider problem is:

```text
prove a strict obstruction-cover shortfall for the balanced window,
under explicit hypotheses, without assuming universal survivor existence.
```
