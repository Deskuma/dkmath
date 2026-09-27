# TRM-008 report: MacroTromino frame / typed macro gap

Date: 2026-09-25
Branch: `research/Tromino-ExchangeCalculus-260924-v0`

## Scope

The first macro-coordinate Tromino frame is complete. It has three retained
macro payload positions and one typed macro gap position. The coordinates reuse
the existing finite `Shape` carrier only as a coordinate pattern; they are not
atomic lattice cells and are not flattened to a physical 4x4 geometry.

No arbitrary recursive level, BoundaryIR, graph traversal, residual
optimization, or Four Color claim was introduced.

## MacroShape and restriction

`MacroShape` is:

```lean
structure MacroShape where
  shape : Shape
  payload : Cell → FourColorMacroCell
```

The payload outside the finite macro footprint is semantically irrelevant.
`restrictMacroShape P S` retains the payload map and restricts the footprint
to `P.shape ∩ S`. The canonical body is obtained by restricting the canonical
2x2 frame to `L_tromino`.

## Typed gap and restoration relation

`MacroGapSlot` stores:

```lean
structure MacroGapSlot where
  footprint : Shape
  expected : FourColorMacroCell
```

`macroRestoreRel target body gap` records four facts:

1. body and gap footprints are disjoint;
2. their union is the target footprint;
3. retained body payloads agree with the target payload;
4. the expected gap payload agrees with the target payload on the gap.

The shape-only projection `macroRestoreRel_shape_part` reuses the existing
`shapeRestoreRel` interface. Consequently,
`macroRestoreRel_gap_footprint_unique` reuses
`shapeRestoreRel_gap_unique` for footprint uniqueness. For a nonempty fixed
gap footprint, `macroRestoreRel_expected_unique` proves uniqueness of the
expected `FourColorMacroCell` payload. No uniqueness statement for arbitrary
multi-cell missing regions is claimed.

## Canonical frame, body, and gap

The canonical frame has footprint `block2` and carries
`atomicFourColorMacroCell` at every occupied macro position. Its body is the
restriction to `L_tromino`; its typed gap has footprint `hole2` and expected
payload `atomicFourColorMacroCell`.

The canonical restoration proof reuses `disjoint_L_hole` and
`block2_eq_L_union_hole`; it does not re-enumerate coordinates. The resulting
macro-position counts are:

```text
body = 3
gap  = 1
total = 4
```

## Atomic payload counts

`atomicPayloadMass` is the `Finset.sum` of `atomicCellCount` over occupied
macro coordinates. The constant-payload calibration proves:

```text
body atomic count = 12
gap expected count = 4
frame atomic count = 16
12 + 4 = 16
16 = 4 * 4
```

The optional CosmicFormula `BodyGapSplit` bridge was not added; the local
finite count API is sufficient and avoids unnecessary coupling.

## Restoration reconnaissance and next boundary

`DkMath.Tromino.Restoration` remains shape-only: `restoreShape`,
`shapeRestoreRel`, `shapeGapFiber`, and `shapeGapCrystal` carry footprint
information but no colored macro payload. It was read and not modified.

For the next bridge, a lightweight certified slot record carrying a
`FourColorMacroCell` remains preferable at this stage. A dependent
`Gap : Core → Type` should be introduced only once recursive levels or a real
core-dependent interface makes the payload type depend on the retained core.

## Computability

No new declaration is marked `noncomputable`. The macro-coordinate and count
definitions use direct finite data and `Finset.sum`; certification fields are
propositions. The `#print axioms` output contains only standard Lean/Mathlib
dependencies (`propext`, `Classical.choice`, and/or `Quot.sound`) inherited
from the certified payload and restoration proofs. No new axiom declaration
was added.

## Regression audit

`DkMathTest/Tromino/MacroTrominoAxiomAudit.lean` checks:

1. canonical frame footprint `block2` and macro count `4`;
2. canonical body footprint `L_tromino` and count `3`;
3. canonical gap footprint `hole2`, count `1`, and expected payload;
4. canonical typed restoration certificate;
5. footprint uniqueness and nonempty-gap payload uniqueness;
6. body atomic count `12`;
7. gap atomic count `4`;
8. total atomic count `16` and the `12 + 4 = 16` split;
9. the `16 = 4 * 4` scale calibration.

## Validation

Focused build:

```text
lake build DkMath.Tromino.MacroCell DkMath.Tromino.Restoration \
  DkMath.Tromino.MacroTromino \
  DkMathTest.Tromino.MacroTrominoAxiomAudit
```

Result: successful (`Build completed successfully (8936 jobs)`). No
`sorryAx`, `admitAx`, unsafe declaration, or new axiom declaration was
introduced.

## Stop boundary

TRM-008 stops at one macro-coordinate 3+1 frame with an exact typed-gap
restoration certificate and the count laws `3 + 1 = 4` and `12 + 4 = 16`.
Arbitrary recursive levels, physical flattening, BoundaryIR, graph search,
residual optimization, and Four Color claims remain deferred.
