# report-petal-149

Date: 2026-07-04

## Checkpoint

Implemented checkpoint 149 from `__next_implementation.md`.

This checkpoint adds pairwise-disjoint list structure and a thin family carrier
around explicitly provided accounted intervals.

No maximality, uniqueness, coverage, prefix behavior, union accounting, or
Collatz convergence was introduced.  Disjointness remains an explicit
hypothesis/field; it is not inferred from accounted intervals.

## Code Changes

Updated:

- `lean/dk_math/DkMath/Collatz/PetalBridge/PressureAccounting.lean`

No new Lean file was created.

## Pairwise Predicate

Used `List.Pairwise` directly through a project-facing wrapper:

```lean
def SourcePressureAccountedIntervalListPairwiseDisjoint
    {n : OddNat} {k r : Nat}
    (L : List (SourcePressureAccountedInterval n k r)) : Prop :=
  L.Pairwise SourcePressureAccountedIntervalsDisjoint
```

Constructor/projection helpers added:

- `sourcePressureAccountedIntervalListPairwiseDisjoint_nil`
- `sourcePressureAccountedIntervalListPairwiseDisjoint_singleton`
- `sourcePressureAccountedIntervalListPairwiseDisjoint_cons`

The cons theorem has the accepted shape:

```lean
theorem sourcePressureAccountedIntervalListPairwiseDisjoint_cons
    {n : OddNat} {k r : Nat}
    {A : SourcePressureAccountedInterval n k r}
    {L : List (SourcePressureAccountedInterval n k r)}
    (hhead : forall B in L, SourcePressureAccountedIntervalsDisjoint A B)
    (htail : SourcePressureAccountedIntervalListPairwiseDisjoint L) :
    SourcePressureAccountedIntervalListPairwiseDisjoint (A :: L)
```

## Symmetry

Added:

- `sourcePressureAccountedIntervalsDisjoint_comm`
- `sourcePressureAccountedIntervalListPairwiseDisjoint_reverse`

The reverse theorem was added as an extra useful lemma.  It uses symmetry of
`SourcePressureAccountedIntervalsDisjoint` and does not add any coverage or
union interpretation.

## Family Carrier

Added:

```lean
structure SourcePressureAccountedIntervalFamily
    (n : OddNat) (k r : Nat) where
  items : List (SourcePressureAccountedInterval n k r)
  pairwiseDisjoint :
    SourcePressureAccountedIntervalListPairwiseDisjoint items
```

This is only a carrier.  The `pairwiseDisjoint` field is stored for future
union/decomposition work, but the budget theorem below does not use it.

## Family Budget

Proved:

```lean
theorem sourcePressureAccountedIntervalFamily_sum_le_neg_length
    {n : OddNat} {k r : Nat}
    (F : SourcePressureAccountedIntervalFamily n k r) :
    (F.items.map (fun A =>
      SourcePressureIntervalNetDrop n k r A.start A.len)).sum <=
        -((F.items.length : Nat) : Int)
```

This is just the existing list budget applied to the family items.
Disjointness is intentionally unused.

## Nonempty Family Negativity

Proved:

```lean
theorem sourcePressureAccountedIntervalFamily_sum_neg_of_nonempty
    {n : OddNat} {k r : Nat}
    (F : SourcePressureAccountedIntervalFamily n k r)
    (hF : F.items != []) :
    (F.items.map (fun A =>
      SourcePressureIntervalNetDrop n k r A.start A.len)).sum < 0
```

## Ordered Interval Vocabulary

Added optional ordered non-overlap vocabulary:

```lean
def NatIntervalBefore (a len b _len' : Nat) : Prop :=
  a + len <= b
```

and:

```lean
def SourcePressureAccountedIntervalBefore
    {n : OddNat} {k r : Nat}
    (A B : SourcePressureAccountedInterval n k r) : Prop :=
  NatIntervalBefore A.start A.len B.start B.len
```

Helper theorems:

- `NatIntervalsDisjoint.of_before`
- `SourcePressureAccountedIntervalsDisjoint.of_before`

This prepares sorted-family work.  It does not claim coverage or decomposition.

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

The next safe step is to add family construction helpers while keeping union
claims out of scope.

Possible next moves:

- family constructors for `nil`, singleton, and cons,
- prove the family budget for singleton and cons as named corollaries,
- define a sorted-family predicate using `SourcePressureAccountedIntervalBefore`,
- prove sorted-before implies pairwise-disjoint for very small shapes first
  such as two-element lists.

The boundary remains clear: explicit family/list structure is fine; union
accounting and coverage require separate future theorems.
