# report-petal-148

Date: 2026-07-04

## Checkpoint

Implemented checkpoint 148 from `__next_implementation.md`.

This checkpoint moves `PressureAccounting` from theorem-only single-address
accounting to a reusable accounted interval carrier and an explicit finite-list
budget theorem.

No maximality, uniqueness, coverage, prefix behavior, disjointness conclusion,
union accounting, or Collatz convergence was introduced.

## Code Changes

Updated:

- `lean/dk_math/DkMath/Collatz/PetalBridge/PressureAccounting.lean`

No new Lean file was needed.

## Interval Net-Drop Abbreviation

Added:

```lean
noncomputable def SourcePressureIntervalNetDrop
    (n : OddNat) (k r start len : Nat) : Int :=
  (Finset.range len).sum (fun i =>
    SourcePressureNetDropInt n k r (start + i))
```

It had to be `noncomputable` because it depends on
`SourcePressureNetDropInt`, which is already noncomputable.

Address-level wrappers were added:

- `sourcePressureIntervalPulseAddress_intervalNetDrop_eq_after_sub_start`
- `sourcePressureIntervalPulseAddress_intervalNetDrop_le_neg_start_margin`
- `sourcePressureIntervalPulseAddress_intervalNetDrop_le_neg_one`
- `sourcePressureIntervalPulseAddress_intervalNetDrop_neg`

No aggressive `[simp]` attributes were added.  The abbreviation is unfolded
only where the wrapper theorem needs it.

## Accounted Interval Carrier

Added:

```lean
structure SourcePressureAccountedInterval
    (n : OddNat) (k r : Nat) where
  start : Nat
  len : Nat
  hlen : 0 < len
  startMarginPos :
    0 < SourcePressureMarginInt n k (r + start)
  afterMarginNonpos :
    SourcePressureMarginInt n k (r + (start + len)) <= 0
  accounting :
    SourcePressureMarginInt n k (r + (start + len)) =
      SourcePressureMarginInt n k (r + start) +
        SourcePressureIntervalNetDrop n k r start len
```

Carrier-level accounting theorems:

- `sourcePressureAccountedInterval_intervalNetDrop_neg`
- `sourcePressureAccountedInterval_intervalNetDrop_le_neg_one`
- `sourcePressureAccountedInterval_intervalNetDrop_le_neg_start_margin`

The important budget form is:

```lean
SourcePressureIntervalNetDrop n k r A.start A.len <=
  -SourcePressureMarginInt n k (r + A.start)
```

## Address to Carrier

Added:

```lean
def sourcePressureAccountedInterval_of_intervalPulseAddress
    {n : OddNat} {k r : Nat}
    (A : SourcePressureIntervalPulseAddress n k r) :
    SourcePressureAccountedInterval n k r
```

This uses the existing interval-pulse address facts:

- positive length,
- positive start margin,
- nonpositive after-margin,
- finite interval accounting identity.

## Finite-List Budget

Proved:

```lean
theorem sourcePressureAccountedInterval_list_sum_le_neg_length
    {n : OddNat} {k r : Nat}
    (L : List (SourcePressureAccountedInterval n k r)) :
    (L.map (fun A =>
      SourcePressureIntervalNetDrop n k r A.start A.len)).sum <=
        -((L.length : Nat) : Int)
```

This is the checkpoint's main finite-family experiment.

Meaning:

```text
each explicit accounted interval contributes at most -1
therefore a list of m explicit accounted intervals contributes at most -m
```

This theorem does not require disjointness and does not state a pressure budget
over a union of intervals.

## Optional Nonempty Negativity

Proved:

```lean
theorem sourcePressureAccountedInterval_list_sum_neg_of_nonempty
    {n : OddNat} {k r : Nat}
    {L : List (SourcePressureAccountedInterval n k r)}
    (hL : L != []) :
    (L.map (fun A =>
      SourcePressureIntervalNetDrop n k r A.start A.len)).sum < 0
```

This follows from the list budget and `0 < L.length`.

## Optional Disjointness Vocabulary

Added vocabulary only:

```lean
def NatIntervalsDisjoint (a len b len' : Nat) : Prop :=
  a + len <= b || b + len' <= a
```

and:

```lean
def SourcePressureAccountedIntervalsDisjoint
    {n : OddNat} {k r : Nat}
    (A B : SourcePressureAccountedInterval n k r) : Prop :=
  NatIntervalsDisjoint A.start A.len B.start B.len
```

Symmetry theorems:

- `NatIntervalsDisjoint.symm`
- `SourcePressureAccountedIntervalsDisjoint.symm`

This is only assumption-level vocabulary.  No disjointness conclusion is
derived from accounted intervals.

## Verification

Passed:

- `lake build DkMath.Collatz.PetalBridge.PressureAccounting`
- `lake build DkMath.Collatz.PetalBridge`
- `rg -n "\bsorry\b" lean/dk_math/DkMath/Collatz/PetalBridge/PressureAccounting.lean`
- `git diff --check`

The `rg` command returned no matches.  The aggregate build still reports the
pre-existing unrelated warning that
`DkMath.NumberTheory.ZsigmondyCyclotomicResearch` contains a declaration using
`sorry`.

## Next Implementation Candidates

The next natural step is to move from list budget to list structure while still
avoiding union claims.

Possible thin next steps:

- define a `List` predicate asserting pairwise disjoint accounted intervals,
- prove that pairwise disjointness is stable under list cons when the head is
  disjoint from every tail element,
- add a theorem that the budget theorem still holds under any extra predicate,
  making clear that disjointness is not used for the budget,
- or define a future-facing `SourcePressureAccountedIntervalFamily` wrapper
  with fields `items : List ...` and optional `pairwiseDisjoint`.

The next proof should still avoid coverage/decomposition.  The safe line is:
explicit intervals first, disjointness as an optional hypothesis, union
accounting only after a separate theorem justifies it.
