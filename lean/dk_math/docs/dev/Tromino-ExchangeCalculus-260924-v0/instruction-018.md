# TRM-019 — General region walk / crossing holonomy

## Goal

Generalize the label-only holonomy theory from the special alternating
transition orbits of TRM-018 to arbitrary region walks determined only by
FlowSignature + FlowCrossing.

This checkpoint should identify the true graph-level obstruction needed before
state-potential reconstruction.

Important structural point:

- FlowPairing chooses local routing;
- FlowTransition follows one particular routed system;
- a region potential depends only on crossing labels on the underlying
  region multigraph.

Therefore the general walk API should be parameterized by:

- N : FlowNetwork
- C : FlowCrossing N

and should not require ClosedFlowNetwork or FlowPairing.

Do not yet prove existence of a global potential/coloring from zero holonomy.
That is the next checkpoint.

Do not implement open residual paths, ghost completion, planarity,
BoundaryIR, optimization, or Four-Color claims.

## Production

Create:

DkMath/Tromino/RegionWalk.lean

## A. Oriented region edge

A FlowNetworkPort already determines one oriented crossing:

source(p) := p.1

target(p) := (C.cross p).1

label(p) := (N.signature p.1).label p.2.

Define readable observers, e.g.:

- flowEdgeSource
- flowEdgeTarget
- flowEdgeLabel

for C : FlowCrossing N.

Define reverse orientation:

```text
reverseEdge p := C.cross p.
```

Prove:

- source(reverseEdge p) = target p;
- target(reverseEdge p) = source p;
- reverseEdge(reverseEdge p) = p;
- label(reverseEdge p) = label p;
- source p != target p.

The last follows from changesRegion.

Because the state group has characteristic two, orientation reversal keeps
the same delta label; do not introduce signed labels.

## B. Indexed region walk

Introduce a path/walk representation that preserves parallel edges.

Preferred semantic type:

```lean
FlowRegionWalk (C : FlowCrossing N) (r s : Fin N.regionCount)
```

whose elements are finite sequences of oriented NetworkPorts forming a
continuous chain from r to s.

An indexed inductive representation is preferred if ergonomic, e.g.
nil at r and cons/snoc of a crossing edge with endpoint compatibility.

Alternative list + validity certificate is acceptable if append/reverse are
clean.

Requirements:

- preserve the exact port used for every crossing;
- allow multiple edges between the same two regions;
- empty walk r -> r;
- computable data;
- no SimpleGraph representation that collapses parallel ports.

## C. Core walk algebra

Define/prove:

- walk length;
- append:
  walk r s -> walk s t -> walk r t;
- reverse:
  walk r s -> walk s r;
- reverse_reverse;
- append associativity, at least propositionally;
- nil left/right laws where useful.

Keep proofs structural.

## D. Region-walk XOR

Define:

```text
regionWalkXor W
```

as the sum of the crossing labels of all oriented edges in W.

Prove:

- xor(nil) = 0;
- xor(single edge p) = label p;
- xor(W1 ++ W2) = xor(W1) + xor(W2);
- xor(reverse W) = xor(W).

The reverse equality uses crossing label preservation and characteristic-two
orientation semantics; no negation is required because every state is
self-inverse.

## E. Closed walks and zero holonomy

Define:

```lean
def ClosedRegionWalk (C : FlowCrossing N) (r : Fin N.regionCount) :=
  FlowRegionWalk C r r
```

or an equivalent predicate.

Define network-level graph holonomy:

```lean
def RegionZeroHolonomy (C : FlowCrossing N) : Prop :=
  ∀ r (W : FlowRegionWalk C r r), regionWalkXor W = 0
```

This is the general cycle condition needed for future path independence.

Do not define it only on primitive/simple cycles; all closed walks are fine
for the first API.

## F. Path comparison theorem

For two walks W1 W2 : r -> s prove:

```text
RegionZeroHolonomy C
->
regionWalkXor W1 = regionWalkXor W2.
```

Proof strategy:

W1 ++ reverse W2 is a closed walk at r.

Since xor(reverse W2) = xor W2 and the group is exponent two,

xor(W1) + xor(W2) = 0

implies xor(W1) = xor(W2).

This is the key path-independence theorem, but only for XOR values; do not yet
construct a potential function.

Also expose the converse in local form if cheap:

all same-endpoint walk XORs equal
-> every closed walk has XOR 0

using comparison with nil.

## G. Reachability

Define:

```text
RegionReachable C r s := Nonempty (FlowRegionWalk C r s)
```

or Prop-existence equivalent.

Prove reflexive and symmetric; transitive via append.

This prepares the next checkpoint for connected-component potential
reconstruction.

Do not force global connectedness into FlowNetwork.

## H. Transition-orbit to region-walk bridge

For N : ClosedFlowNetwork, each flowTransitionStep contributes exactly one
crossing edge; local mate only selects the next port in the arrival region.

Construct an induced region walk:

```text
transitionRegionWalk N p n
```

from:

source region p.1

to:

region of (flowTransitionStep N)^[n] p

with n crossing edges corresponding to the n transition steps.

The exact endpoint may need to account for the post-cross local mate, but
local mate preserves the destination region, so it should match the iterate
region.

Prove:

```text
regionWalkXor (transitionRegionWalk N p n)
=
flowTransitionXor N p n.
```

This theorem is central: TRM-018 transition holonomy becomes a special case of
general crossing holonomy.

## I. Transition return gives closed region walk

If:

```text
FlowTransitionReturn N p n
```

then transitionRegionWalk N p n is a closed region walk at p.1.

Consequently prove:

```text
RegionZeroHolonomy N.crossing
->
flowTransitionXor N p n = 0
```

for every transition return.

Then derive:

```text
RegionZeroHolonomy
->
every primitive transition return has even period.
```

using TRM-018's parity theorem.

This is an implication only.

Do not claim the converse. Transition orbits inspect only the routed
same-label subsystem and may not generate all region cycles.

## J. Counterexample boundary

Keep the TRM-018 period-3 fixture as a negative calibration:

its primitive transition return yields a closed region walk with XOR deltaA,
so RegionZeroHolonomy fails.

Audit this explicitly using the new bridge.

This confirms the abstract odd-cycle obstruction survives at the general
region-walk level.

## K. No potential construction yet

Do not define a global region-state function by path choice in this
checkpoint.

The next checkpoint should use:

- RegionReachable;
- RegionZeroHolonomy;
- path-XOR independence

to prove existence/uniqueness-up-to-base-state of a potential.

Keeping that theorem separate will make its assumptions clear.

## L. Computability

Walk data, append, reverse, XOR, and induced transition walks must be
computable.

No sorry, admit, unsafe, new axiom, or noncomputable production declaration.

Proofs may inherit the existing foundational axioms from finite structures.

## M. Audit

Create:

DkMathTest/Tromino/RegionWalkAxiomAudit.lean

Audit at least:

1. one crossing edge and its reverse;
2. reverse preserves label;
3. append XOR law;
4. reverse XOR law;
5. small two-region walks;
6. path-comparison theorem under an explicit zero-holonomy toy network;
7. transitionRegionWalk XOR = flowTransitionXor;
8. period-2 transition gives a closed region walk with XOR 0;
9. period-3 fixture gives a closed region walk with XOR deltaA != 0;
10. RegionZeroHolonomy implies transition primitive periods even.

## N. Validation

Build:

- DkMath.Tromino.FlowTransition
- DkMath.Tromino.FlowTransitionXor
- DkMath.Tromino.RegionWalk
- DkMathTest/Tromino.RegionWalkAxiomAudit

Regression-build FlowTransitionXor audit.

Run git diff --check, forbidden-construct scan, and #print axioms.

## O. Report

Create:

docs/dev/Tromino-ExchangeCalculus-260924-v0/report-018.md

Record:

- region-edge orientation convention;
- walk representation;
- append/reverse algebra;
- regionWalkXor;
- RegionZeroHolonomy;
- path-XOR independence;
- reachability;
- transitionRegionWalk bridge;
- period-2/period-3 calibration;
- proof that transition holonomy is only a special case;
- exact stop boundary before potential reconstruction.

## Stop condition

Stop once arbitrary crossing walks have a certified XOR calculus and
RegionZeroHolonomy implies path-XOR independence, with TRM-018 transition
holonomy embedded as a special case.

Do not construct the global state potential yet, and do not proceed to open
paths, ghost completion, planarity, BoundaryIR, optimization, or Four-Color
claims.
