# TRM-028 — Port face-orbit and Euler-count migration

## Goal

Migrate the finite face-orbit partition and combinatorial V/E/F counting layer
from FlowNetwork onto the unlabeled PortNetwork carrier.

TRM-027 already established that face-step dynamics depend only on:

- PortNetwork;
- PortCrossing;
- PortLocalRotation.

TRM-028 should therefore make the following fully label-free:

- face orbits;
- edge orbits;
- face partition;
- V / E / F / D counts;
- combinatorial Euler characteristic.

The existing Flow FaceOrbit/EulerCount APIs must remain unchanged.

Do not migrate the strong connected genus wrapper yet.
Do not claim planarity, sphere realization, or Four-Color flow existence.

## Production files

Create:

- DkMath/Tromino/PortFaceOrbit.lean
- DkMath/Tromino/PortEulerCount.lean

## A. Port face orbit

In PortFaceOrbit.lean define the exact unlabeled analogue of TRM-023:

```lean
def portFaceOrbit
  (R : PortLocalRotation P)
  (C : PortCrossing P)
  (p : PortNetworkPort P) :
  Finset (PortNetworkPort P)
```

using:

```text
Finset.range (firstPortFaceReturn R C p)
```

and iterates of portFaceStep.

Required theorems:

- self-membership;
- arbitrary iterate membership;
- membership iff some iterate;
- distinctness of iterates before first return;
- orbit card = firstPortFaceReturn;
- orbit reverse membership;
- subset/equality from membership;
- SamePortFaceOrbit;
- Setoid;
- equal-or-disjoint;
- coverage;
- firstPortFaceReturn invariant on one orbit.

Keep names clearly distinct from the existing Flow API.

## B. Port face orbit / Flow face orbit calibration

For existing Flow data N,R,C prove:

```text
portFaceOrbit R.toPortLocalRotation C.toPortCrossing p
=
faceOrbit R C p.
```

Prefer rfl only if the definitions genuinely reduce; otherwise prove via
membership characterization and the portFaceStep erasure theorem.

Also prove:

```text
firstPortFaceReturn R.toPortLocalRotation C.toPortCrossing p
=
firstFaceReturn R C p.
```

This equality should follow from exact face-step identity and the same Nat.find
predicate. If rfl is not available, prove extensional equality of the periodic
existence predicates carefully.

## C. Assignment-independence of face orbit

For structural P,C,R and any two assignments A B : V4FlowAssignment C prove
that the lifted Flow face orbits are the same.

Preferred form:

```text
faceOrbit (R.toFlowLocalRotation A) A.toFlowCrossing p
=
portFaceOrbit R C p
```

and therefore the A/B face orbits are equal.

This is the set-level strengthening of TRM-027 face-step independence.

## D. Unlabeled edge-pair layer

In PortEulerCount.lean define:

```lean
def portCrossingEdgePair (C : PortCrossing P)
    (p : PortNetworkPort P) : Finset (PortNetworkPort P) :=
  {p, C.cross p}
```

and migrate the edge-orbit theorems:

- card = 2;
- invariant under crossing;
- equality from membership;
- equal-or-disjoint.

Define:

```lean
def portCrossingEdgeOrbits ...
def portCrossingEdgeCount ...
```

and prove:

- coverage;
- pairwise disjoint;
- biUnion = univ;
- sum of cards = P.portCount;
- 2 * edgeCount = P.portCount.

## E. Unlabeled face-orbit family

Define:

```lean
def portFaceOrbits
  (R : PortLocalRotation P)
  (C : PortCrossing P) :
  Finset (Finset (PortNetworkPort P)) :=
  Finset.univ.image (portFaceOrbit R C)
```

and:

```lean
def portFaceCount ...
```

Prove:

- orbit member characterization;
- coverage;
- pairwise disjoint;
- biUnion = univ;
- sum of face-orbit cards = P.portCount.

If the generic helper

```text
sum_card_eq_card_univ_of_pairwise_disjoint_cover
```

from EulerCount is reusable without import cycles, reuse it.

Preferred dependency direction:

- PortEulerCount may import EulerCount for this generic theorem and adapter
  calibration;
- do not move the generic helper unless that is cleaner.

Avoid duplicate generic finite-partition lemmas if possible.

## F. Unlabeled V/E/F/D/chi

Define:

```lean
def portRegionVertexCount (P : PortNetwork) : Nat := P.regionCount

def portCombinatorialEulerCharacteristic
    (R : PortLocalRotation P)
    (C : PortCrossing P) : Int :=
  (portRegionVertexCount P : Int)
    - (portCrossingEdgeCount C : Int)
    + (portFaceCount R C : Int)
```

Expose the readability theorem:

```text
chi = V - E + F.
```

All counts must depend only on structural map data.

## G. Exact calibration with Flow EulerCount

For N : FlowNetwork, R : FlowLocalRotation N, C : FlowCrossing N prove:

- PortNetwork.portCount after erasure = totalPortCount N;
- port edge-pair = crossingEdgePair pointwise;
- port edge-orbit count = crossingEdgeCount;
- port face-orbit family/count = faceOrbits/faceCount;
- port Euler characteristic =
  combinatorialEulerCharacteristic R C.

This is the central factorization theorem:

```text
TRM-023/TRM-024 structural counting
factors through label erasure.
```

Pointwise/calculated equality is sufficient; full structure equality is not
required.

## H. Assignment-independence of Euler data

For P,C,R and any A B : V4FlowAssignment C prove:

```text
combinatorialEulerCharacteristic
  (R.toFlowLocalRotation A) A.toFlowCrossing
=
portCombinatorialEulerCharacteristic R C
```

and the same with B.

Then derive A/B equality.

If cheap, also expose individual V/E/F/D count equalities across assignments.

This theorem is important: labels cannot affect the combinatorial surface
counts.

## I. Pure Port fixtures

Reuse TRM-027 pure fixtures.

### 2 × 2 cyclic fixture

Kernel-check:

- D = 4;
- E = 2;
- each face orbit has length 2;
- F = 2;
- V = 2;
- chi = 2.

All calculations must use only Port types.

### 2 × 3 cyclic fixture

Kernel-check:

- D = 6;
- E = 3;
- one face orbit length 6;
- F = 1;
- V = 2;
- chi = 0.

Again no V4 assignment required.

## J. Multiple-face structural fixture

The 2×2 fixture already has two face orbits; use it to audit disjointness and
coverage.

If desired, add a 2×4 identity PortLocalRotation fixture, but do not require a
PortRotationSystem for this weak Euler-count layer.

If added, it should reproduce:

- D = 8;
- E = 4;
- F = 4;
- chi = 2.

Keep the same warning as TRM-024: weak chi = 2 alone has no sphere meaning.

## K. Existing Flow API preservation

Do not rewrite:

- FaceOrbit.lean;
- EulerCount.lean.

They stay CI-stable.

TRM-028 is additive and proves they are label-decorated facades over the new
Port structural layer.

A future refactor may make Flow modules thin wrappers, but not in this
checkpoint.

## L. Interpretation boundary

Record explicitly:

After TRM-028,

```text
PortNetwork
+ PortCrossing
+ PortLocalRotation
  -> face partition / V/E/F/chi
```

without any V4 labels.

The V4FlowAssignment is logically orthogonal to these counts.

Do not infer:

- genus;
- sphere;
- planarity;
- topological realization;
- zero-holonomy assignment existence.

## M. Computability / axioms

All new finite-orbit/count definitions must be computable.

No:

- sorry;
- admit;
- unsafe;
- new axiom;
- noncomputable production declaration.

## N. Audit

Create:

- DkMathTest/Tromino/PortFaceOrbitAxiomAudit.lean
- DkMathTest/Tromino/PortEulerCountAxiomAudit.lean

Audit at least:

1. Port face self-membership;
2. membership iff iterate;
3. orbit card = firstPortFaceReturn;
4. equal-or-disjoint;
5. first-return invariance in orbit;
6. 2×2 two face-orbit decomposition;
7. 2×3 six-port single orbit;
8. edge-orbit card 2;
9. D = 2E;
10. D = sum face lengths;
11. pure Port 2×2 V/E/F/chi;
12. pure Port 2×3 V/E/F/chi;
13. Flow erasure exact face-orbit/count calibration;
14. deltaA/deltaB assignment Euler data equality.

## O. Validation

Build:

- DkMath.Tromino.PortRotationSystem
- DkMath.Tromino.PortFaceOrbit
- DkMath.Tromino.PortEulerCount
- DkMathTest/Tromino/PortFaceOrbitAxiomAudit
- DkMathTest/Tromino/PortEulerCountAxiomAudit

Regression-build:

- DkMathTest/Tromino.FaceOrbitAxiomAudit
- DkMathTest/Tromino.EulerCountAxiomAudit
- DkMathTest/Tromino.CombinatorialMapAxiomAudit

Run git diff --check, forbidden-construct scan, and #print axioms.

## P. Report

Create:

docs/dev/Tromino-ExchangeCalculus-260924-v0/report-027.md

Record:

- Port face-orbit representation;
- exact Flow face-orbit calibration;
- assignment-independence;
- Port edge/face partitions;
- D=2E;
- D=sum face lengths;
- Port V/E/F/chi;
- exact 2×2 and 2×3 values;
- Flow Euler factorization through label erasure;
- stop boundary before strong Port combinatorial-map/genus migration.

## Stop condition

Stop once face-orbit partition and V/E/F/chi counting are completely
label-free on PortNetwork and the existing Flow FaceOrbit/EulerCount APIs are
proved to factor through the new Port layer.

Do not migrate genus/strong combinatorial-map wrappers yet, and do not claim
planarity, topological realization, sphere embedding, universal V4 flow
existence, or Four-Color theorem results.
