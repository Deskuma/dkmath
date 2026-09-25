# TRM-022 — Rotation-system kernel / combinatorial face step

## Goal

Introduce the minimal combinatorial-map layer above FlowNetwork/FlowCrossing.

TRM-021 landed the region graph in Mathlib SimpleGraph/Dart, but SimpleGraph
forgets parallel-edge multiplicity. Therefore the primary carrier for planar
combinatorics remains FlowNetworkPort.

TRM-022 should add a local rotation permutation on FlowNetworkPort and combine
it with the existing crossing involution to obtain the standard face-step
permutation.

This checkpoint must **not** claim planarity, genus zero, face extraction as a
topological embedding theorem, non-crossing pairing existence, or the
Four-Color theorem.

## Conceptual convention

Let:

- alpha = crossing reversal;
- rho = local rotation around the source region.

Use the convention

    faceStep p := rho (alpha p)

that is:

    phi = rho ∘ alpha.

Document this exact convention because the opposite composition is also common
in the literature.

## Production

Create:

DkMath/Tromino/RotationSystem.lean

Import GraphColoringBridge only if the Dart bridge is used; otherwise depend
on the smaller FlowTransition / FlowNetwork layer as appropriate.

## A. Local rotation carrier

Define a weak local rotation certificate:

```lean
structure FlowLocalRotation (N : FlowNetwork) where
  rotate : FlowNetworkPort N ≃ FlowNetworkPort N
  preservesRegion : ∀ p, (rotate p).1 = p.1
```

This is a permutation of all ports that acts independently inside each region.

Required theorems:

- rotate preserves source region;
- rotate.symm also preserves source region;
- all iterates preserve source region.

Keep the definition computable.

## B. Cyclic rotation-system condition

Define a stronger property saying every pair of ports in one region lies in
the same orbit of rotate.

Suggested:

```lean
def RegionRotationCyclic (R : FlowLocalRotation N)
    (r : Fin N.regionCount) : Prop :=
  ∀ i j : Fin (N.signature r).arity,
    ∃ n : Nat,
      (R.rotate^[n]) ⟨r,i⟩ = ⟨r,j⟩
```

Adjust dependent-pair syntax as needed.

Then define:

```lean
structure FlowRotationSystem (N : FlowNetwork)
    extends FlowLocalRotation N where
  cyclic : ∀ r, RegionRotationCyclic toFlowLocalRotation r
```

Interpretation:

- FlowLocalRotation allows multiple rotation orbits in one region;
- FlowRotationSystem asserts one cyclic order of incident ports per region.

This explicitly scopes the first planar-combinatorics kernel to one cyclic
boundary order per region.

Do not silently assume this for arbitrary planar maps with multiple boundary
components.

## C. Crossing as a permutation

Package FlowCrossing.cross as:

```lean
def flowCrossEquiv (C : FlowCrossing N) :
  FlowNetworkPort N ≃ FlowNetworkPort N
```

using C.cross as both forward and inverse functions.

Prove:

- apply = C.cross;
- symm = itself;
- involutive.

This should be a thin wrapper around the existing crossing certificate.

## D. Face-step permutation

For R : FlowLocalRotation N and C : FlowCrossing N define:

```lean
def faceStep (R : FlowLocalRotation N) (C : FlowCrossing N) :
  FlowNetworkPort N → FlowNetworkPort N :=
  fun p => R.rotate (C.cross p)
```

and package:

```lean
def faceEquiv (R : FlowLocalRotation N) (C : FlowCrossing N) :
  FlowNetworkPort N ≃ FlowNetworkPort N
```

with inverse mathematically:

    alpha ∘ rho⁻¹.

Prove exact left/right inverse formulas.

Do not claim faceStep is involutive.

## E. Face-step source/target observation

For p, define or prove readable formulas for:

- after alpha, source becomes the neighboring region;
- rho then stays in that neighboring region;
- therefore the source region of faceStep p is the target region of p.

Target after faceStep is determined by the next crossing and need not equal a
simple local expression.

Expose:

```text
(flowEdgeSource C (faceStep R C p))
=
flowEdgeTarget C p.
```

or the equivalent region equality.

This is the key "turn around the next region after crossing" interpretation.

## F. Finite periodicity

Because faceEquiv is a permutation on a finite port type, prove:

```text
∀ p, ∃ n > 0, (faceStep R C)^[n] p = p.
```

Use the same finite-permutation order strategy already used for transitionStep.

Introduce, if useful:

- FaceReturn
- firstFaceReturn
- firstFaceReturn_spec
- firstFaceReturn_min
- firstFaceReturn_primitive

These are recommended because the next checkpoint will materialize face
orbits.

Do not define a quotient of faces yet if that would require a broad orbit API.

## G. Rotation orbit sanity theorems

For R : FlowRotationSystem N prove:

- every port in the same region is reached by some rotate iterate;
- rotate never leaves the region;
- the local cyclic order contains exactly the region's port multiplicity,
  at least as a reachability statement.

Do not attempt a numeric orbit-cardinality theorem unless Mathlib makes it
straightforward.

## H. Relation to Mathlib Dart

Reuse TRM-021's:

```text
flowPortToDart C
```

and prove only the safe endpoint-level facts.

For example:

- rotate changes the outgoing Dart while preserving its fst/source region;
- crossing reversal still maps to Dart.symm.

Do not define the rotation system on SimpleGraph.Dart as primary data, because
parallel FlowNetworkPorts may collapse to one Dart.

Record this information boundary explicitly.

## I. Relation to FlowTransition — calibration only

The face rotation and local pairing are distinct concepts.

Do **not** identify:

- R.rotate;
- FlowPairing.mate.

However, prove a calibration theorem:

If N : ClosedFlowNetwork and a local rotation R satisfies pointwise

    R.rotate p = flowLocalMatePort N p

for every p, then

    faceStep R N.crossing p = flowTransitionStep N p.

This theorem should make the relation explicit without conflating the two
structures.

A small two-port fixture may satisfy this accidentally; document that it is a
special calibration, not the general meaning.

## J. Pure rotation-system fixture

Create an audit fixture that does not depend on FlowPairing.

Recommended:

- two regions;
- each region has three ports;
- all labels may be deltaA for simplicity;
- crossing pairs corresponding port indices across regions;
- local rotation cycles 0 -> 1 -> 2 -> 0 in each region.

Audit:

1. rotate preserves region;
2. the three local ports form one cyclic orbit;
3. crossing is involutive;
4. faceStep = rotate after crossing;
5. faceStep has a positive period;
6. faceStep is not incorrectly asserted involutive;
7. port-to-Dart may still collapse multiplicity where endpoints agree.

If the above crossing plus 3-cycle rotation gives faceStep period 6, kernel
check that calibration.

## K. Combinatorial-map interpretation boundary

Record clearly:

The pair

    (alpha = crossing involution, rho = local rotation)

is the combinatorial permutation data commonly used to generate face orbits.

TRM-022 only formalizes these permutations and periodic face steps.

It does **not** yet prove:

- that the system comes from an embedding in the sphere;
- that every faceStep orbit is a geometric face of a planar embedding;
- Euler characteristic / genus;
- non-crossing local pairing;
- arbitrary planar-map extraction.

Those require later certificates/theorems.

## L. Mathlib API boundary

Record the survey result:

- Mathlib SimpleGraph.Dart supplies oriented simple-graph edges;
- parallel FlowNetworkPort multiplicity is not represented injectively;
- no general planar embedding / rotation-system object was identified in the
  current Mathlib repository survey.

Therefore DkMath keeps rotation data on FlowNetworkPort.

## M. Computability / axioms

All data definitions must remain computable.

No:

- sorry;
- admit;
- unsafe;
- new axiom;
- noncomputable production definition.

Nat.find may be used for first-return theorem data only if consistent with the
existing pattern and no noncomputable declaration is needed.

## N. Audit

Create:

DkMathTest/Tromino/RotationSystemAxiomAudit.lean

Audit at least:

1. local rotation Equiv laws;
2. region preservation for rotate and rotate.symm;
3. cyclicity in the 3-port fixture;
4. crossing Equiv self-inverse;
5. faceStep and inverse formulas;
6. face source = previous edge target;
7. positive face period;
8. explicit expected period in the 2-region / 3-port fixture if cheap;
9. Dart endpoint calibration;
10. FlowTransition equality under an explicit rotate=mate hypothesis.

## O. Validation

Build:

- DkMath.Tromino.GraphColoringBridge
- DkMath.Tromino.RotationSystem
- DkMathTest/Tromino.RotationSystemAxiomAudit

Regression-build:

- DkMathTest/Tromino.GraphColoringBridgeAxiomAudit
- DkMathTest/Tromino.RegionPotentialAxiomAudit

Run git diff --check, forbidden-construct scan, and #print axioms.

## P. Report

Create:

docs/dev/Tromino-ExchangeCalculus-260924-v0/report-021.md

Record:

- FlowLocalRotation representation;
- FlowRotationSystem cyclicity condition;
- alpha / rho / faceStep convention;
- faceEquiv inverse;
- periodicity / first-return API;
- pure 3-port fixture;
- Dart information-loss boundary;
- calibration with FlowTransition;
- exact non-planarity claim boundary;
- recommended next face-orbit / Euler-certificate checkpoint.

## Stop condition

Stop once FlowNetworkPort carries a certified local cyclic rotation and the
crossing/rotation permutations generate a finite periodic face-step system.

Do not proceed to face quotient/cardinality, Euler characteristic, genus-zero
certificate, non-crossing pairing, planar extraction, ghost completion,
BoundaryIR, optimization, or Four-Color claims without review.
