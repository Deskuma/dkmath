# TRM-027 — Port rotation system / unlabeled face-step migration

## Goal

Migrate the purely structural rotation-system / face-step layer from
FlowNetwork onto the unlabeled PortNetwork carrier introduced in TRM-026.

This checkpoint should make the combinatorial-map permutation kernel fully
independent of V4 labels.

Do not migrate face-orbit counting, Euler characteristic, genus, planarity,
or Four-Color flow existence yet.

The existing Flow rotation API must remain unchanged.

## Production

Create:

DkMath/Tromino/PortRotationSystem.lean

Import PortNetwork and the existing RotationSystem for adapter theorems.

## A. Unlabeled local rotation

Define:

```lean
structure PortLocalRotation (P : PortNetwork) where
  rotate : PortNetworkPort P ≃ PortNetworkPort P
  preservesRegion : ∀ p, (rotate p).1 = p.1
```

Provide unlabeled analogues of:

- symm_preservesRegion;
- iterate_preservesRegion;
- symm_iterate_preservesRegion.

Keep definitions computable.

## B. Unlabeled cyclic rotation system

Define:

```lean
def PortRegionRotationCyclic
    (R : PortLocalRotation P)
    (r : Fin P.regionCount) : Prop :=
  ∀ i j : Fin (P.arity r),
    ∃ n : Nat, (R.rotate^[n]) ⟨r,i⟩ = ⟨r,j⟩
```

and:

```lean
structure PortRotationSystem (P : PortNetwork)
    extends PortLocalRotation P where
  cyclic : ∀ r, PortRegionRotationCyclic toPortLocalRotation r
```

Expose a reachability theorem matching the existing FlowRotationSystem API.

No labels may appear in these definitions.

## C. Crossing permutation

PortCrossing.crossEquiv already exists from TRM-026.

Reuse it rather than duplicating a second wrapper.

Add any simp/readability theorem needed for composition with rotation.

## D. Unlabeled face-step

Fix the same convention as TRM-022:

    alpha := crossing
    rho   := local rotation
    phi   := rho ∘ alpha

Define:

```lean
def portFaceStep
    (R : PortLocalRotation P)
    (C : PortCrossing P) :
    PortNetworkPort P -> PortNetworkPort P :=
  fun p => R.rotate (C.cross p)
```

and:

```lean
def portFaceEquiv ...
```

with inverse:

    alpha ∘ rho⁻¹.

Prove:

- forward formula;
- inverse formula;
- left/right inverse;
- source-region theorem:
  source(portFaceStep p) = target of crossing p.

If useful define lightweight structural observers:

```text
portEdgeSource p := p.1
portEdgeTarget C p := (C.cross p).1
```

Do not depend on flowEdgeLabel.

## E. Finite periodicity / first return

Migrate the structural periodicity API:

- portFaceStep_periodic;
- PortFaceReturn;
- firstPortFaceReturn;
- firstPortFaceReturn_spec;
- firstPortFaceReturn_min;
- PortFacePrimitiveReturn;
- firstPortFaceReturn_primitive.

Use the finite permutation order strategy from RotationSystem.

These theorems must not mention V4 labels.

## F. Existing Flow -> Port erasure adapter

For N : FlowNetwork and R : FlowLocalRotation N define:

```lean
R.toPortLocalRotation :
  PortLocalRotation N.toPortNetwork
```

using exactly the same rotate function.

For R : FlowRotationSystem N define:

```lean
R.toPortRotationSystem :
  PortRotationSystem N.toPortNetwork
```

Prove:

- rotate pointwise equality;
- cyclicity transfers exactly;
- face-step equality under erasure:
  ```text
  portFaceStep R.toPortLocalRotation C.toPortCrossing p
    = faceStep R C p
  ```
  preferably rfl;
- first return equality if definitionally straightforward.

This proves TRM-022's structural dynamics factor through label erasure.

## G. Port + assignment -> Flow lift

For:

- P : PortNetwork;
- C : PortCrossing P;
- A : V4FlowAssignment C;
- R : PortLocalRotation P;

define:

```lean
R.toFlowLocalRotation (A) :
  FlowLocalRotation A.toFlowNetwork
```

with the same rotate function.

Likewise for:

```lean
PortRotationSystem.toFlowRotationSystem
```

Prove:

```text
faceStep (R.toFlowLocalRotation A) A.toFlowCrossing p
=
portFaceStep R C p
```

and, if cheap, equality of first-return values.

The structural face dynamics must be independent of which assignment A is
chosen.

## H. Assignment-independence theorem

This is a central calibration.

Given two assignments A B : V4FlowAssignment C and one structural rotation R,
prove:

```text
faceStep (R.toFlowLocalRotation A) A.toFlowCrossing p
=
faceStep (R.toFlowLocalRotation B) B.toFlowCrossing p
```

after identifying the definitionally equal port carriers.

If dependent typing makes a direct cross-assignment equality awkward, prove
both sides equal to portFaceStep R C p.

Likewise expose first-return equality across assignments if clean.

Interpretation:

    same structural map
    + different V4 labels
    -> same face permutation.

This theorem is important.

## I. Round-trip calibration

For existing Flow rotation data:

1. erase N,C,R to Port data;
2. use C.toV4FlowAssignment to rebuild Flow data;
3. lift the erased Port rotation;

prove pointwise equality with the original:

- rotate;
- crossing;
- faceStep.

Full structure equality is optional.

## J. Pure unlabeled fixtures

Create an audit fixture directly as PortNetwork data, not by erasing a
FlowNetwork.

### 2 regions × 2 ports

- crossing swaps regions at equal index;
- local rotation swaps the two indices;
- cyclic in each region;
- portFaceStep has two 2-cycles.

Audit:

- port count = 4;
- cyclicity;
- first return 2 for representative ports.

### 2 regions × 3 ports

- crossing swaps regions at equal index;
- local rotation is the 3-cycle;
- portFaceStep has the same 6-cycle as the old Flow fixture.

Audit first return 6.

Then place both deltaA and deltaB assignments on the same 2×2 structure and
confirm the lifted Flow faceStep remains identical.

## K. FlowTransition calibration boundary

Do not migrate FlowPairing / FlowTransition onto PortNetwork.

Pairing is label-aware and belongs to the flow layer.

Keep the existing special theorem:

    rotate = localMate -> faceStep = flowTransitionStep

on the Flow side.

PortRotationSystem is structural and should not depend on FlowPairing.

## L. Dependency boundary

PortRotationSystem.lean may import the existing RotationSystem for adapters,
but the core Port definitions should not use FlowSignature labels.

If a cleaner split is easy:

- PortRotationSystemCore.lean for pure structural definitions;
- PortRotationSystem.lean for Flow adapters.

This split is optional.

Avoid import cycles.

## M. Computability / axioms

All new definitions must be computable.

No:

- sorry;
- admit;
- unsafe;
- new axiom;
- noncomputable production declaration.

## N. Audit

Create:

DkMathTest/Tromino/PortRotationSystemAxiomAudit.lean

Audit at least:

1. PortLocalRotation Equiv laws;
2. region preservation;
3. PortRotationSystem cyclicity;
4. portFaceStep / portFaceEquiv inverse;
5. structural source/target theorem;
6. positive periodicity;
7. 2×2 first return 2;
8. 2×3 first return 6;
9. Flow -> Port faceStep exact calibration;
10. Port + assignment -> Flow exact calibration;
11. deltaA vs deltaB assignments yield identical face dynamics.

## O. Validation

Build:

- DkMath.Tromino.PortNetwork
- DkMath.Tromino.PortRotationSystem
- DkMathTest/Tromino.PortRotationSystemAxiomAudit

Regression-build:

- DkMath.Tromino.RotationSystem
- DkMathTest/Tromino.RotationSystemAxiomAudit
- DkMath.Tromino.CombinatorialMap
- DkMathTest/Tromino.CombinatorialMapAxiomAudit

Run git diff --check, forbidden-construct scan, and #print axioms.

## P. Report

Create:

docs/dev/Tromino-ExchangeCalculus-260924-v0/report-026.md

Record:

- PortLocalRotation / PortRotationSystem definitions;
- portFaceStep convention;
- periodicity / first return;
- Flow erasure adapter;
- assignment lift;
- assignment-independence theorem;
- 2×2 and 2×3 pure structural fixtures;
- dependency decision;
- exact stop boundary before face-orbit/Euler/genus migration.

## Stop condition

Stop once local rotation and face-step permutation dynamics are fully
label-free on PortNetwork and the existing Flow rotation system is proven to
factor through this structural layer.

Do not migrate face-orbit counting, Euler characteristic, genus, planarity,
topological realization, or Four-Color flow existence without review.
