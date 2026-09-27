# TRM-026 — Unlabeled port network / V4 flow-assignment split

## Goal

Separate the combinatorial carrier of the map from the supplied nonzero
TrominoState labels.

Current FlowNetwork stores, per region, a FlowSignature, hence every port
already carries a nonzero V4 label. This was useful for the flow theory, but
it is too strong as the carrier for the eventual Four-Color existence
statement.

TRM-026 should factor:

    structural port network
      +
    nowhere-zero V4 flow assignment
      =
    current FlowNetwork/FlowCrossing data.

This checkpoint is additive. Do not rewrite the completed Flow* stack.

Do not implement planarity, genus realization, flow existence for arbitrary
sphere maps, or Four-Color claims.

## Production

Create:

DkMath/Tromino/PortNetwork.lean

## A. Unlabeled carrier

Define:

```lean
structure PortNetwork where
  regionCount : Nat
  arity : Fin regionCount -> Nat
```

and:

```lean
abbrev PortNetworkPort (P : PortNetwork) :=
  Sigma (fun r : Fin P.regionCount => Fin (P.arity r))
```

This carrier contains:

- regions;
- multiplicity-preserving ports;

and contains no TrominoState labels.

## B. Unlabeled crossing

Define:

```lean
structure PortCrossing (P : PortNetwork) where
  cross : PortNetworkPort P -> PortNetworkPort P
  involutive : Function.Involutive cross
  changesRegion : forall p, (cross p).1 != p.1
```

No label-preservation field belongs here.

Provide:

- cross is fixed-point-free;
- crossing as an Equiv;
- reverse twice = identity.

## C. V4 flow assignment

For P : PortNetwork and C : PortCrossing P define:

```lean
structure V4FlowAssignment where
  label : PortNetworkPort P -> TrominoState
  nonzero : forall p, label p != 0
  cross_sameLabel : forall p, label (C.cross p) = label p
```

This is the exact relative-state / nowhere-zero edge-label data.

Do not add holonomy to the structure. Holonomy is a theorem/property of an
assignment, not primitive data.

## D. Build the current FlowNetwork stack from an assignment

Given A : V4FlowAssignment C, define:

```lean
A.toFlowNetwork : FlowNetwork
A.toFlowCrossing : FlowCrossing A.toFlowNetwork
```

with:

- same regionCount;
- same arity;
- signature labels induced by A.label;
- crossing function definitionally the same where possible.

Required calibration:

- PortNetworkPort P and FlowNetworkPort A.toFlowNetwork should reduce to the
  same Sigma type if possible;
- toFlowCrossing.cross = C.cross;
- toFlowNetwork labels = A.label;
- nonzero and cross_sameLabel fields are transported directly.

## E. Erase labels from the existing Flow stack

Define:

```lean
FlowNetwork.toPortNetwork : PortNetwork
FlowCrossing.toPortCrossing : PortCrossing N.toPortNetwork
```

For C : FlowCrossing N define the extracted assignment:

```lean
C.toV4FlowAssignment :
  V4FlowAssignment C.toPortCrossing
```

using the existing FlowSignature labels.

Required exact theorems:

- erased regionCount = original regionCount;
- erased arity = original signature arity;
- erased crossing = original crossing;
- extracted label = original FlowSignature label.

## F. Round-trip calibration

Prove that erasing and rebuilding preserves the existing data.

Preferred pointwise theorems:

For N : FlowNetwork and C : FlowCrossing N,

```text
(C.toV4FlowAssignment.toFlowNetwork).regionCount = N.regionCount
```

and arities/labels agree pointwise.

Likewise:

```text
C.toV4FlowAssignment.toFlowCrossing.cross p = C.cross p.
```

If full structure equality is cheap via extensionality/proof irrelevance,
expose it; pointwise exactness is sufficient.

Conversely, for A : V4FlowAssignment C:

- erase A.toFlowNetwork = P pointwise;
- erase A.toFlowCrossing = C pointwise;
- re-extracted assignment label = A.label.

The important result is a faithful factorization, not a category-theory API.

## G. Structural meaning theorem

Document and, where clean, theoremize:

The current FlowNetwork/FlowCrossing data are equivalent in information
content to:

    PortNetwork
    + PortCrossing
    + V4FlowAssignment.

In particular:

- Euler/rotation/map structure should ultimately live on PortNetwork;
- holonomy/potential/coloring should live on V4FlowAssignment.

Do not migrate those modules in this checkpoint.

## H. Assignment-to-existing-theory wrappers

Provide small wrappers so the existing completed theory can be reused without
migration.

For A : V4FlowAssignment C, expose definitions/properties such as:

```lean
def V4FlowAssignment.ZeroHolonomy (A) : Prop :=
  RegionZeroHolonomy A.toFlowCrossing
```

Only do this if imports remain acyclic and the dependency is clean.

If importing RegionPotential/RegionWalk would make PortNetwork.lean too high
in the dependency graph, place these wrappers in a separate module:

DkMath/Tromino/PortNetworkFlowBridge.lean

Preferred dependency hygiene:

- PortNetwork.lean: structural carrier + assignment + FlowNetwork round trip;
- PortNetworkFlowBridge.lean: wrappers into holonomy/potential/coloring.

Do not create an import cycle.

## I. Negative type calibration

Construct two different V4FlowAssignment values on the same PortNetwork /
PortCrossing when possible.

This should demonstrate that:

```text
same combinatorial map carrier
does not determine
the V4 labels.
```

For example, on the 2-region × 2-port structural fixture, use:

- all deltaA;
- all deltaB.

Both satisfy nonzero/cross_sameLabel but are different assignments.

This is central to the separation.

## J. Positive round-trip fixture

Take an existing FlowNetwork/FlowCrossing fixture, erase it, extract the
assignment, rebuild it, and audit:

- same arity;
- same labels;
- same crossing function.

## K. No rotation/genus migration yet

Do not yet rewrite:

- FlowLocalRotation;
- FlowRotationSystem;
- FlowCombinatorialMap;
- EulerCount;
- FaceOrbit.

They remain on FlowNetwork for CI stability.

The next reviewed checkpoint should migrate the purely structural map layer
onto PortNetwork and prove counts/face dynamics factor through label erasure.

## L. Computability / axioms

All new data definitions must be computable.

No:

- sorry;
- admit;
- unsafe;
- new axiom;
- noncomputable production declaration.

## M. Audit

Create:

DkMathTest/Tromino/PortNetworkAxiomAudit.lean

Audit at least:

1. unlabeled port count/arity behavior;
2. PortCrossing involution and no fixed point;
3. two distinct V4FlowAssignment values on one structural carrier;
4. assignment -> FlowNetwork labels;
5. assignment -> FlowCrossing crossing equality;
6. FlowNetwork -> PortNetwork erasure;
7. extracted assignment reproduces original labels;
8. erase/extract/rebuild pointwise round trip;
9. rebuild/erase assignment round trip.

## N. Validation

Build:

- DkMath.Tromino.PortNetwork
- DkMathTest/Tromino/PortNetworkAxiomAudit

Regression-build:

- DkMath.Tromino.CombinatorialMap
- DkMathTest/Tromino.CombinatorialMapAxiomAudit
- DkMath.Tromino.RegionPotential
- DkMathTest/Tromino.GraphColoringBridgeAxiomAudit

Run git diff --check, forbidden-construct scan, and #print axioms.

## O. Report

Create:

docs/dev/Tromino-ExchangeCalculus-260924-v0/report-025.md

Record:

- PortNetwork representation;
- PortCrossing;
- V4FlowAssignment;
- exact FlowNetwork reconstruction;
- exact label-erasure adapters;
- round-trip calibration;
- two different assignments on one map carrier;
- dependency decision for optional flow-theory wrappers;
- explicit statement of the remaining Four-Color existence problem.

## Stop condition

Stop once unlabeled structural map data and nowhere-zero V4 flow labels are
separate types, and the current FlowNetwork/FlowCrossing stack is proven to
factor through their combination.

Do not migrate rotation/Euler/genus yet, and do not claim planarity,
topological realization, universal zero-holonomy flow existence, or the
Four-Color theorem.
