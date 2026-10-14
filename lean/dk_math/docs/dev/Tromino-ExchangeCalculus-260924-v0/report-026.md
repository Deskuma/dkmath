# TRM-027 — Port Rotation System / Unlabeled Face-Step Migration

## Implemented

Added `DkMath/Tromino/PortRotationSystem.lean` with label-free structural
permutation data:

- `PortLocalRotation P` stores a port equivalence preserving the region;
- `PortRegionRotationCyclic` and `PortRotationSystem P` express cyclicity
  inside each region;
- `portFaceStep R C := R.rotate ∘ C.cross`;
- `portFaceEquiv R C` uses `C.cross ∘ R.rotate.symm` as inverse; and
- `portEdgeSource`, `portEdgeTarget`, and the structural source theorem expose
  the crossing endpoint relation without flow labels.

The module also provides the finite permutation-order periodicity API:
`portFaceStep_periodic`, `PortFaceReturn`, `firstPortFaceReturn`, its
specification/minimality theorems, and `PortFacePrimitiveReturn`.

## Flow adapters and assignment lift

Existing `FlowLocalRotation` and `FlowRotationSystem` data erase to
`PortLocalRotation` and `PortRotationSystem` with the same rotate function and
cyclicity proof.  Conversely, a `PortLocalRotation` lifts through any
`V4FlowAssignment` to a `FlowLocalRotation`, and a `PortRotationSystem` lifts
to a `FlowRotationSystem`.

The audit kernel-checks exact face-step equalities for both adapters,
including the round trip through an existing Flow fixture.  It also proves
that two assignments on the same structural crossing give the same Flow
face-step because both reduce to `portFaceStep`.

FlowPairing and FlowTransition remain on the Flow side; no label-aware
transition layer was migrated.

## Pure structural fixtures

`DkMathTest/Tromino/PortRotationSystemAxiomAudit.lean` defines fixtures
directly as `PortNetwork` data:

- 2 regions × 2 ports, with region-swapping crossing and index-swapping
  rotation.  It has two face-step 2-cycles and first return `2`;
- 2 regions × 3 ports, with region-swapping crossing and a 3-cycle rotation.
  Its explicit face-step chain has first return `6`.

The same 2×2 structural carrier is lifted with all-`deltaA` and all-`deltaB`
assignments, and the resulting Flow face dynamics are proven identical.

## Boundary and verification

The existing Flow rotation API remains unchanged.  Face-orbit counting, Euler
characteristic, genus, planarity, topological realization, and Four-Color flow
existence are outside this checkpoint and were not migrated.

The requested production/audit build and RotationSystem/CombinatorialMap
regressions completed successfully.  The audited declarations were checked
with `#print axioms`; no new axiom, `sorry`, `admit`, `unsafe`, or
`noncomputable` production declaration was introduced.
