# TRM-029 — Port region-walk / structural connectivity migration

## Goal

Migrate the purely structural region-walk and reachability layer from
FlowNetwork/FlowCrossing onto PortNetwork/PortCrossing.

TRM-028 already made face partition and Euler counting label-free.
The remaining obstacle to a fully unlabeled strong combinatorial-map wrapper
is connectedness: the current FlowCombinatorialMap uses RegionReachable, which
is defined through FlowRegionWalk.

TRM-029 should make region paths and connectedness fully structural.

Do not migrate genus/strong PortCombinatorialMap yet.
Do not add holonomy, labels, potentials, planarity, or Four-Color claims.

## Production

Create:

DkMath/Tromino/PortRegionWalk.lean

Import PortNetwork and RegionWalk only for adapter/calibration theorems.

## A. Structural walk validity

Define the unlabeled analogue:

```lean
def PortRegionWalk.Valid {P : PortNetwork}
    (C : PortCrossing P)
    (r s : Fin P.regionCount) :
    List (PortNetworkPort P) -> Prop
  | [] => r = s
  | p :: ps =>
      p.1 = r ∧ PortRegionWalk.Valid C (C.cross p).1 s ps
```

and:

```lean
structure PortRegionWalk {P : PortNetwork}
    (C : PortCrossing P)
    (r s : Fin P.regionCount) where
  edges : List (PortNetworkPort P)
  valid : PortRegionWalk.Valid C r s edges
```

No TrominoState label may occur in these definitions.

## B. Basic structural walk algebra

Migrate the structural subset of FlowRegionWalk:

- ext by edge-list equality;
- nil;
- length;
- singleton;
- append;
- append_nil_left/right;
- append_assoc;
- reverseEdges;
- reverse;
- reverse_nil;
- reverse_append;
- reverse_reverse.

The semantics must be identical to FlowRegionWalk, but label-free.

Keep everything computable.

## C. Structural edge observers

Reuse from PortRotationSystem if already available:

- portEdgeSource;
- portEdgeTarget.

If importing PortRotationSystem would create an undesirable dependency, keep
PortRegionWalk dependent only on PortNetwork and refer directly to p.1 /
(C.cross p).1.

Do not introduce duplicate label observers.

## D. PortRegionReachable

Define:

```lean
def PortRegionReachable {P : PortNetwork}
    (C : PortCrossing P)
    (r s : Fin P.regionCount) : Prop :=
  Nonempty (PortRegionWalk C r s)
```

Prove:

- refl;
- symm;
- trans.

Then define:

```lean
def PortRootedRegionConnected
    (C : PortCrossing P)
    (base : Fin P.regionCount) : Prop :=
  ∀ s, PortRegionReachable C base s
```

and optionally:

```lean
def PortRegionConnected (C : PortCrossing P) : Prop :=
  ∀ r s, PortRegionReachable C r s
```

This global form is recommended because the next strong Port map wrapper will
use it directly.

Prove:

- PortRegionConnected -> rooted connected at every base;
- if P.regionCount > 0 and rooted connected at one base, then global connected,
  using symmetry/transitivity.

The second theorem is useful but not mandatory if dependent Fin details become
noisy.

## E. Flow -> Port walk erasure

For N : FlowNetwork and C : FlowCrossing N define:

```lean
def FlowRegionWalk.toPortRegionWalk
  (W : FlowRegionWalk C r s) :
  PortRegionWalk C.toPortCrossing r s
```

with the exact same edge list.

Prove:

- edges are definitionally equal;
- length is equal;
- nil/singleton/append/reverse commute with erasure where clean.

Main reachability theorem:

```text
RegionReachable C r s
->
PortRegionReachable C.toPortCrossing r s.
```

Prefer an iff after also implementing the lift below.

## F. Port + assignment -> Flow walk lift

For:

- P : PortNetwork;
- C : PortCrossing P;
- A : V4FlowAssignment C;

define:

```lean
def PortRegionWalk.toFlowRegionWalk
  (W : PortRegionWalk C r s) :
  FlowRegionWalk A.toFlowCrossing r s
```

again preserving the exact edge list.

Prove basic operations commute with lift where cheap.

Then prove the exact reachability equivalence:

```text
PortRegionReachable C r s
↔
RegionReachable A.toFlowCrossing r s.
```

This should show that Flow reachability is assignment-independent.

## G. Assignment-independence of reachability

For A B : V4FlowAssignment C prove:

```text
RegionReachable A.toFlowCrossing r s
↔
RegionReachable B.toFlowCrossing r s.
```

Prefer deriving both sides from PortRegionReachable.

Likewise for rooted/global connectedness if wrappers are convenient.

This theorem is central: map connectedness cannot depend on V4 labels.

## H. Round-trip calibration

For existing FlowRegionWalk W:

1. erase to PortRegionWalk;
2. rebuild using C.toV4FlowAssignment;

prove:

- edge list is unchanged;
- the rebuilt Flow walk equals W if proof irrelevance/extensionality makes this
  cheap.

At minimum provide pointwise/list equality.

Conversely for Port walk W and assignment A:

- lift to Flow;
- erase back;
- recover the same Port walk.

Full structure equality is preferred but not required.

## I. Optional SimpleGraph connectivity bridge

TRM-021 defined regionSimpleGraph on Flow data.

Do not extend that in this checkpoint unless cheap.

A future unlabeled SimpleGraph bridge can be added later if needed.

The key connectedness owner should be PortRegionReachable.

## J. Pure structural fixtures

Reuse TRM-027 Port fixtures.

### 2 × 2

Prove:

- region 0 reaches region 1 via singleton crossing;
- region 1 reaches region 0;
- PortRegionConnected portTwoCrossing.

### 2 × 3

Likewise prove global connectedness.

### disconnected fixture

Add a pure PortNetwork fixture with at least two disconnected components if
possible.

Because PortCrossing.changesRegion requires every port to cross to another
region, a clean fixture could use 4 regions split into pairs:

- 0 <-> 1;
- 2 <-> 3.

Give each region one port.

Prove:

- 0 reaches 1;
- 2 reaches 3;
- not PortRegionReachable 0 2;
- therefore not PortRegionConnected.

This negative fixture is strongly recommended so the connectivity predicate is
not vacuous.

## K. Flow fixture calibration

Take an existing connected Flow fixture, erase it, and prove Port connectedness.

Take any two assignments on the same connected Port fixture and prove both
lifted Flow crossings have the same connectivity.

## L. Dependency boundary

PortRegionWalk core definitions must not depend on:

- FlowSignature labels;
- FlowPairing;
- FlowTransition;
- holonomy;
- RegionPotential.

RegionWalk import is allowed only for adapters.

If necessary split:

- PortRegionWalkCore.lean
- PortRegionWalk.lean

but this is optional.

## M. Computability / axioms

All walk constructors and transformations must be computable.

No:

- sorry;
- admit;
- unsafe;
- new axiom;
- noncomputable production declaration.

## N. Audit

Create:

DkMathTest/Tromino/PortRegionWalkAxiomAudit.lean

Audit at least:

1. nil/singleton validity;
2. append;
3. reverse;
4. reverse_reverse;
5. PortRegionReachable refl/symm/trans;
6. 2×2 connectedness;
7. 2×3 connectedness;
8. disconnected 4-region fixture;
9. Flow -> Port walk erasure;
10. Port + assignment -> Flow walk lift;
11. reachability iff under assignment lift;
12. deltaA/deltaB assignment connectivity independence;
13. round-trip edge-list preservation.

## O. Validation

Build:

- DkMath.Tromino.PortNetwork
- DkMath.Tromino.PortRegionWalk
- DkMathTest/Tromino.PortRegionWalkAxiomAudit

Regression-build:

- DkMath.Tromino.PortEulerCount
- DkMathTest/Tromino.PortEulerCountAxiomAudit
- DkMath.Tromino.RegionWalk
- DkMathTest/Tromino.RegionWalkAxiomAudit
- DkMath.Tromino.CombinatorialMap
- DkMathTest/Tromino.CombinatorialMapAxiomAudit

Run git diff --check, forbidden-construct scan, and #print axioms.

## P. Report

Create:

docs/dev/Tromino-ExchangeCalculus-260924-v0/report-028.md

Record:

- PortRegionWalk representation;
- structural walk algebra;
- PortRegionReachable / connectedness;
- Flow erasure and assignment lift;
- exact reachability equivalence;
- assignment-independence;
- connected and disconnected fixtures;
- exact stop boundary before strong PortCombinatorialMap/genus migration.

## Stop condition

Stop once region walks and connectedness are completely label-free on
PortNetwork and existing Flow reachability is proved to factor through this
structural layer.

Do not migrate genus/strong combinatorial-map wrappers yet, and do not claim
planarity, topological realization, sphere embedding, universal V4 flow
existence, or Four-Color theorem results.
