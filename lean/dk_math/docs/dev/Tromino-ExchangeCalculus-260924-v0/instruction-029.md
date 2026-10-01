# TRM-030 — Strong Port combinatorial map / unlabeled arithmetic genus

## Goal

Migrate the strong connected combinatorial-map and arithmetic genus layer from
FlowNetwork onto the unlabeled PortNetwork carrier.

After TRM-029, all structural ingredients are label-free:

- PortNetwork / PortCrossing;
- PortRotationSystem;
- Port face orbits and Euler counts;
- PortRegionConnected.

TRM-030 should package these into the canonical **unlabeled strong
combinatorial-map type** and define its arithmetic genus / genus-zero
certificate without any V4FlowAssignment.

The existing FlowCombinatorialMap API must remain unchanged.

Do not prove topological realization, planarity, sphere embedding, universal
V4-flow existence, or the Four-Color theorem.

## Production

Create:

DkMath/Tromino/PortCombinatorialMap.lean

Import:

- PortEulerCount;
- PortRegionWalk;
- existing CombinatorialMap only for adapter/calibration theorems.

## A. Strong unlabeled map wrapper

Define:

```lean
structure PortCombinatorialMap (P : PortNetwork) where
  crossing : PortCrossing P
  rotation : PortRotationSystem P
  nonemptyRegions : 0 < P.regionCount
  connected : PortRegionConnected crossing
```

This is the structural owner of the map.

No TrominoState / FlowSignature / V4FlowAssignment field may appear.

## B. Readability / observer API

Expose:

```lean
def PortCombinatorialMap.localRotation ...
def PortCombinatorialMap.vertexCount ...
def PortCombinatorialMap.edgeCount ...
def PortCombinatorialMap.faceCount ...
def PortCombinatorialMap.portCount ...
def PortCombinatorialMap.eulerCharacteristic ...
```

forwarding exactly to PortEulerCount.

Recommended meanings:

- V = P.regionCount;
- E = portCrossingEdgeCount M.crossing;
- F = portFaceCount M.localRotation M.crossing;
- D = P.portCount;
- chi = portCombinatorialEulerCharacteristic ...

Keep all observers computable.

## C. Rotation-orbit calibration

Define, if useful:

```lean
def SamePortVertexRotationOrbit
  (M : PortCombinatorialMap P)
  (p q : PortNetworkPort P) : Prop :=
  p.1 = q.1 ∧
    ∃ n, (M.localRotation.rotate^[n]) p = q
```

Prove:

same region ->
same Port rotation orbit.

This is the Port analogue of the existing Flow theorem and confirms that V is
the intended local rotation-cycle count.

Do not create a second vertex-orbit partition unless needed.

## D. Connectedness readability

Expose:

```lean
theorem PortCombinatorialMap.connected_regions ...
```

returning PortRegionReachable for arbitrary region pairs.

If useful, expose rooted connectedness at any chosen base.

No Flow reachability should be needed in the core theorem.

## E. Arithmetic genus relation

Define:

```lean
def PortHasCombinatorialGenus
    (M : PortCombinatorialMap P) (g : Nat) : Prop :=
  M.eulerCharacteristic = (2 : Int) - 2 * (g : Int)
```

Prove the exact Port analogues:

- genus uniqueness;
- genus zero iff chi = 2;
- genus one iff chi = 0;
- any witnessed genus gives chi <= 2;
- any witnessed genus gives Even chi.

Do not prove every PortCombinatorialMap has a genus witness.

Do not define genus by Nat division.

## F. Sphere-characteristic predicate

Define:

```lean
def PortHasSphereCharacteristic
    (M : PortCombinatorialMap P) : Prop :=
  M.eulerCharacteristic = 2
```

Prove:

```text
PortHasSphereCharacteristic M
iff
PortHasCombinatorialGenus M 0.
```

Use "sphere characteristic" only in the arithmetic/combinatorial sense.

## G. Canonical genus-zero wrapper

Create a small type suitable as the later Four-Color input:

```lean
structure PortGenusZeroCombinatorialMap (P : PortNetwork) where
  map : PortCombinatorialMap P
  genusZero : PortHasCombinatorialGenus map 0
```

or an equivalent subtype.

Expose:

- sphere characteristic follows;
- underlying crossing / rotation / connectedness / counts via map.

This type is the intended unlabeled structural input for the later V4-flow
existence problem.

Do **not** name it PlanarMap or SphereEmbedding.

## H. FlowCombinatorialMap -> Port erasure

For N : FlowNetwork and M : FlowCombinatorialMap N define:

```lean
def FlowCombinatorialMap.toPortCombinatorialMap :
  PortCombinatorialMap N.toPortNetwork
```

using:

- M.crossing.toPortCrossing;
- M.rotation.toPortRotationSystem;
- same nonemptyRegions;
- M.connected transported through Flow -> Port reachability.

Prove exact observer calibration:

```text
M.toPortCombinatorialMap.vertexCount = M.vertexCount
M.toPortCombinatorialMap.edgeCount = M.edgeCount
M.toPortCombinatorialMap.faceCount = M.faceCount
M.toPortCombinatorialMap.portCount = M.portCount
M.toPortCombinatorialMap.eulerCharacteristic = M.eulerCharacteristic
```

Use TRM-028/029 adapter theorems.

## I. Port map + assignment -> Flow lift

For:

- M : PortCombinatorialMap P;
- A : V4FlowAssignment M.crossing;

define:

```lean
def PortCombinatorialMap.toFlowCombinatorialMap
    (M : PortCombinatorialMap P)
    (A : V4FlowAssignment M.crossing) :
    FlowCombinatorialMap A.toFlowNetwork
```

using:

- A.toFlowCrossing;
- M.rotation.toFlowRotationSystem A;
- same nonemptyRegions;
- M.connected transported through Port <-> Flow reachability equivalence.

Prove the same observer equalities back to M.

This should show the Flow strong map is merely a labeled lift of the structural
Port map.

## J. Genus / sphere-characteristic calibration

For existing Flow M prove:

```text
HasCombinatorialGenus M g
iff
PortHasCombinatorialGenus M.toPortCombinatorialMap g
```

and:

```text
HasSphereCharacteristic M
iff
PortHasSphereCharacteristic M.toPortCombinatorialMap.
```

For Port M and assignment A prove the reverse lift equivalences.

These are central migration theorems.

## K. Assignment-independence at strong-map level

Given M : PortCombinatorialMap P and two assignments

```text
A B : V4FlowAssignment M.crossing
```

prove:

- lifted Flow maps have equal V/E/F/D/chi;
- HasCombinatorialGenus for the A-lift iff for the B-lift;
- HasSphereCharacteristic for A-lift iff for B-lift.

This packages all previous assignment-independence into the strong map layer.

## L. Pure Port positive fixtures

Reuse the pure Port fixtures.

### 2 × 2

Package:

```lean
portTwoMap : PortCombinatorialMap portTwoNetwork
```

using:

- portTwoCrossing;
- portTwoRotationSystem;
- portTwo_region_connected.

Kernel-check:

- V = 2;
- E = 2;
- F = 2;
- D = 4;
- chi = 2;
- PortHasSphereCharacteristic;
- PortHasCombinatorialGenus 0;
- PortGenusZeroCombinatorialMap can be built.

### 2 × 3

Package:

```lean
portThreeMap : PortCombinatorialMap portThreeNetwork
```

and kernel-check:

- V = 2;
- E = 3;
- F = 1;
- D = 6;
- chi = 0;
- PortHasCombinatorialGenus 1;
- not PortHasSphereCharacteristic.

These fixtures must require no V4 assignment.

## M. Disconnected non-example

Use TRM-029's disconnected 4-region fixture.

If a cyclic rotation can be supplied cheaply, demonstrate that it still cannot
be packaged as PortCombinatorialMap because PortRegionConnected fails.

At minimum audit:

```text
¬ PortRegionConnected disconnectedCrossing.
```

Do not force an impossible structure construction.

## N. Old weak chi=2 non-example

The old identity-rotation 2×4 Flow fixture remains a useful historical
negative calibration, but TRM-030 should primarily use Port fixtures.

If a pure Port identity-rotation 2×4 fixture already exists or is cheap,
prove:

- weak Port Euler chi = 2;
- rotation cyclicity fails;
- hence it cannot become PortCombinatorialMap with that rotation.

This is optional if already well documented by the Flow audit.

## O. Round-trip calibration

For existing FlowCombinatorialMap M:

1. erase to PortCombinatorialMap;
2. use M.crossing.toV4FlowAssignment;
3. lift back to FlowCombinatorialMap;

prove pointwise equality/calibration of:

- crossing function;
- rotation function;
- V/E/F/D/chi.

Full structure equality is optional.

Conversely, for Port map M and assignment A:

1. lift to Flow;
2. erase back;

prove the structural observers and crossing/rotation functions return M.

## P. The exact Four-Color-side boundary

The report must state the now-clean architecture:

```text
PortGenusZeroCombinatorialMap
        |
        |  [OPEN EXISTENCE GAP]
        v
exists V4FlowAssignment with appropriate zero-holonomy property
        |
        v
RegionPotential
        |
        v
Mathlib SimpleGraph.Colorable 4
```

TRM-030 does not prove the open existence arrow.

Also note:

- PortHasSphereCharacteristic is still arithmetic/combinatorial;
- topological realization as an embedding in S^2 is not formalized.

## Q. Dependency boundary

PortCombinatorialMap core definitions must be label-free.

Importing existing CombinatorialMap is allowed only for adapter/calibration
theorems.

If necessary split:

- PortCombinatorialMapCore.lean
- PortCombinatorialMap.lean

but this is optional.

Avoid import cycles.

## R. Computability / axioms

All structural definitions and observers must be computable.

No:

- sorry;
- admit;
- unsafe;
- new axiom;
- noncomputable production declaration.

Arithmetic genus proofs should remain elementary.

## S. Audit

Create:

- DkMathTest/Tromino/PortCombinatorialMapAxiomAudit.lean
- DkMathTest/Tromino/PortCombinatorialMapGenusAxiomAudit.lean

Audit at least:

1. strong Port wrapper fields;
2. 2×2 Port map V/E/F/D/chi;
3. 2×2 genus 0 / sphere characteristic;
4. PortGenusZeroCombinatorialMap construction;
5. 2×3 Port map V/E/F/D/chi;
6. 2×3 genus 1 and not sphere characteristic;
7. genus uniqueness;
8. genus-zero iff chi=2;
9. disconnected non-example;
10. Flow -> Port observer calibration;
11. Port + assignment -> Flow observer calibration;
12. genus/sphere predicate calibration;
13. deltaA/deltaB assignment strong-map independence;
14. round-trip crossing/rotation function calibration.

## T. Validation

Build:

- DkMath.Tromino.PortCombinatorialMap
- DkMathTest/Tromino.PortCombinatorialMapAxiomAudit
- DkMathTest/Tromino.PortCombinatorialMapGenusAxiomAudit

Regression-build:

- DkMathTest/Tromino.PortEulerCountAxiomAudit
- DkMathTest/Tromino.PortRegionWalkAxiomAudit
- DkMathTest/Tromino.CombinatorialMapAxiomAudit
- DkMathTest/Tromino.CombinatorialMapGenusAxiomAudit

Run git diff --check, forbidden-construct scan, label-free core scan, and
#print axioms.

## U. Report

Create:

docs/dev/Tromino-ExchangeCalculus-260924-v0/report-029.md

Record:

- PortCombinatorialMap definition;
- label-free observer API;
- Port arithmetic genus / sphere characteristic;
- PortGenusZeroCombinatorialMap;
- 2×2 / 2×3 fixtures;
- Flow erasure / assignment lift;
- genus/sphere calibration;
- assignment-independence at strong-map level;
- exact topological-realization boundary;
- exact remaining Four-Color flow-existence gap.

## Stop condition

Stop once the strong connected cyclic combinatorial-map and arithmetic
genus-zero input type are completely label-free on PortNetwork, and the old
FlowCombinatorialMap/genus API is proven to factor through this structural
layer.

Do not prove topological realization, planarity equivalence, universal
zero-holonomy V4 flow existence, or Four-Color theorem results without review.
