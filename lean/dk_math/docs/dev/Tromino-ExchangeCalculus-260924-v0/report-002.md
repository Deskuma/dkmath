# TRM-003 report: certified geometric restoration

Date: 2026-09-24
Branch: `research/Tromino-ExchangeCalculus-260924-v0`

## Scope

The geometric restoration bridge is complete. The implementation reuses the
existing BookOfMagic restoration infrastructure and does not modify
BookOfMagic. No MacroCell, recursive substitution, BoundaryIR, rescue, graph,
optimization, or Four Color layer was added.

## Generic restoration relation

The Tromino-owned relation is:

```lean
shapeRestoreRel target core gap : Prop :=
  Disjoint core gap ∧ restoreShape core gap = target
```

The target is fixed explicitly. `core` is the retained shape, `gap` is the
removed shape, disjointness prevents overlap, and the union equality is the
restoration certificate.

The thin operation

```lean
restoreShape core gap := core ∪ gap
```

was added because it makes the restoration theorem readable without adding a
second abstraction layer.

## GapCrystal / GapFiber adapters

The production module is
`DkMath/Tromino/Restoration.lean`, with dependency direction
`DkMath.Tromino -> DkMath.BookOfMagic`.

It defines only aliases, not duplicate structures:

```lean
shapeGapFiber target core
  := DkMath.BookOfMagic.GapFiber (shapeRestoreRel target) core

shapeGapCrystal target
  := DkMath.BookOfMagic.GapCrystal
       Shape (fun _ : Shape => Shape) (shapeRestoreRel target)
```

The atomic certified values are `atomicGapFiber` and `atomicGapCrystal`.
They retain `L_tromino`, carry `hole2`, and use the existing restoration
certificate.

## Atomic certificate

`atomic_shapeRestoreRel` uses exactly:

- `DkMath.Polyomino.Tromino.disjoint_L_hole`;
- `DkMath.Polyomino.Tromino.block2_eq_L_union_hole`.

The user-facing equality is:

```lean
restoreShape L_tromino hole2 = block2
```

via `atomic_restoreShape`. No finite-set enumeration or recomputed certificate
was introduced.

## Generic uniqueness and UniqueGap

`shapeRestoreRel_gap_unique` proves, for any fixed target and core, that two
disjoint restoring gaps are equal. The proof is generic over `Shape`: a point
of one gap lies in the target, hence in the other gap or in the common core;
the latter is excluded by disjointness.

`uniqueGap_of_shapeRestoreRel` converts any certified relation witness into the
existing `DkMath.BookOfMagic.UniqueGap (shapeRestoreRel target) core`
contract. The atomic specialization is `atomic_uniqueGap`.

The optional complement characterization `gap = target \ core` was deferred.
The current generic uniqueness theorem already establishes the required
restoration uniqueness without extending the API with a difference/subset
lemma.

## Interpretation boundary

This checkpoint types only geometric restoration. The gap does not yet carry a
color state, macro-cell payload, orientation, boundary signature, or recursive
scale level. Those remain future dependent payload choices.

The restoration bridge is separate from the TRM-002 numeric `4 = 3 + 1`
calibration and does not import `CosmicBridge`.

## Validation

Focused build:

```text
lake build DkMath.Tromino.Restoration DkMathTest.Tromino.RestorationAxiomAudit
```

Result: successful (`Build completed successfully (8929 jobs)`). The audit
module checks the atomic relation, restore operation, both BookOfMagic adapter
types, generic gap uniqueness, and the atomic `UniqueGap` contract.

The substantive `#print axioms` output was:

```text
atomic_shapeRestoreRel       [propext, Classical.choice, Quot.sound]
shapeRestoreRel_gap_unique   [propext, Classical.choice, Quot.sound]
uniqueGap_of_shapeRestoreRel [propext, Classical.choice, Quot.sound]
atomic_uniqueGap             [propext, Classical.choice, Quot.sound]
```

These are standard Lean/Mathlib dependencies. No `sorryAx`, `admitAx`, or
new user axiom was introduced, and no unsafe declaration was added.

## Stop boundary

TRM-003 stops at the certified unique atomic geometric gap. Macro-cell,
FourColorCell, rescue, BoundaryIR, graph, and optimization work remains out of
scope pending review.
