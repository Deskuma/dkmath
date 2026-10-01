# TRM-017 — FlowTransition migration / label-only closed network

## Goal

Migrate the TRM-013 closed transition layer from contact-based
BoundarySignature/BoundaryPairing onto label-only FlowSignature/FlowPairing.

This checkpoint is additive. Existing BoundaryNetwork, ClosedBoundaryNetwork,
TransitionGraph, and TransitionXor APIs must remain unchanged.

Do not migrate TransitionXor yet. Do not implement color recovery, open
residual paths, ghost completion, planarity, BoundaryIR, optimization, or
Four-Color claims.

## Production

Create:

DkMath/Tromino/FlowTransition.lean

Reuse FlowSignature and FlowPairing.

Define a finite region family:

```lean
structure FlowNetwork where
  regionCount : Nat
  signature : Fin regionCount → FlowSignature
```

and global ports:

```lean
abbrev FlowNetworkPort (N : FlowNetwork) :=
  Sigma (fun r : Fin N.regionCount => Fin (N.signature r).arity)
```

## Crossing

Define:

```lean
structure FlowCrossing (N : FlowNetwork) where
  cross : FlowNetworkPort N → FlowNetworkPort N
  involutive : Function.Involutive cross
  changesRegion : ∀ p, (cross p).1 ≠ p.1
  sameLabel : ∀ p,
    (N.signature (cross p).1).label (cross p).2 =
      (N.signature p.1).label p.2
```

Keep the same first-kernel scope as TRM-013: crossing always changes region,
so self-adjacent region edges remain deferred.

Define:

```lean
structure ClosedFlowNetwork extends FlowNetwork where
  crossing : FlowCrossing toFlowNetwork
  pairing : ∀ r, FlowPairing (toFlowNetwork.signature r)
  perfect : ∀ r, flowResidualPorts (pairing r) = ∅
```

Do not force canonicalFlowPairing as the only pairing.

## Global local-mate and crossing API

Define Flow-specific analogues of:

- flowCrossPort
- flowLocalMatePort

Prove:

- both involutive;
- crossing changes region and is non-self;
- local mate preserves region and is non-self under perfectness;
- both preserve labels;
- crossing and local mate are distinct at every port.

## Two-neighbor transition kernel

Define:

- flowTransitionNeighbors
- FlowTransitionAdj

Prove:

- neighbor card = 2;
- adjacency symmetric;
- adjacency irreflexive;
- every port has exactly two distinct transition neighbors.

Do not require Mathlib SimpleGraph packaging.

## Alternating transition permutation

Use the same convention as TRM-013:

```text
flowTransitionStep p :=
  flowLocalMatePort (flowCrossPort p)
```

and inverse:

```text
flowTransitionStepInv p :=
  flowCrossPort (flowLocalMatePort p)
```

Prove left/right inverse, injective, surjective, and expose:

```lean
flowTransitionEquiv
```

as an Equiv / permutation when clean.

## Label preservation and periodicity

Prove:

- one step preserves FlowSignature label;
- every iterate preserves label;
- every port has a positive periodic return.

Reuse the finite permutation order strategy from TransitionGraph.

Do not yet define XOR accumulation.

## Boundary-network erasure

Define additive adapters:

```lean
BoundaryNetwork.toFlowNetwork
BoundaryCrossing.toFlowCrossing
ClosedBoundaryNetwork.toClosedFlowNetwork
```

using BoundarySignature.toFlowSignature and
BoundaryPairing.toFlowPairing.

Preserve the same crossing and mate functions.

Because erasure preserves arity definitionally, prefer definitions that make
port types and transition functions definitionally equal where possible.

## Exact calibration with TRM-013

For every contact-based closed network N, prove the erased flow network agrees
with TRM-013 on the transition dynamics.

Target bridge theorems:

- flowCrossPort on N.toClosedFlowNetwork = crossPort N;
- flowLocalMatePort = localMatePort;
- flowTransitionStep = transitionStep;
- flow transition labels = boundaryDelta labels;
- positive periodicity is the same dynamic statement.

Pointwise function equality is sufficient. If the relevant types reduce
definitionally, exploit rfl rather than adding transport machinery.

This is the key factorization theorem:

TRM-013 transition dynamics depend only on erased nonzero labels plus the
crossing/pairing certificates, not on absolute inside/outside states.

## Canonical two-region regression

Create a pure label-only fixture:

- two regions;
- each FlowSignature is A A;
- canonicalFlowPairing at each region;
- crossing swaps regions and preserves local index.

Audit:

- total port count 4;
- crossing/local mate involutive;
- two neighbors;
- transition adjacency symmetric/irreflexive;
- positive periodic orbit;
- label preservation.

## Contact-erasure regression

Construct or reuse a contact-based two-region fixture and erase it.

Verify pointwise:

- same ports;
- same crossing;
- same local mate;
- same transitionStep.

Do not depend on TransitionXor in the production module.

## Computability

All data definitions must be computable.

No sorry, admit, unsafe, new axiom, or noncomputable production declaration.

## Validation

Create:

DkMathTest/Tromino/FlowTransitionAxiomAudit.lean

Build:

- DkMath.Tromino.FlowPairing
- DkMath.Tromino.TransitionGraph
- DkMath.Tromino.FlowTransition
- DkMathTest/Tromino/FlowTransitionAxiomAudit

Regression-build TransitionXor unchanged.

Run git diff --check, forbidden-construct scan, and #print axioms.

## Report

Create:

docs/dev/Tromino-ExchangeCalculus-260924-v0/report-016.md

Record:

- FlowNetwork/FlowCrossing/ClosedFlowNetwork representations;
- transition-neighbor API;
- permutation/periodicity theorems;
- label preservation;
- erasure adapters;
- exact transition calibration with TRM-013;
- computability;
- TransitionXor regression status;
- recommended next step for label-only XOR/holonomy migration.

## Stop condition

Stop once the complete closed transition dynamics of TRM-013 exist on
FlowSignature/FlowPairing and the contact-based closed network is proved to
erase to the same transition step.

Do not migrate TransitionXor yet and do not proceed to color recovery, open
paths, ghost completion, planarity, BoundaryIR, optimization, or Four-Color
claims.
