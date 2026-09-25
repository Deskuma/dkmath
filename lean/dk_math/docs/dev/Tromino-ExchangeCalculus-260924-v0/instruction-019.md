# TRM-020 — Region potential reconstruction / label-only ColorRecovery kernel

## Goal

Construct an actual region-state potential from the label-only crossing flow.

TRM-019 established:

- arbitrary region walks;
- walk XOR;
- RegionZeroHolonomy;
- zero holonomy => same-endpoint path-XOR independence.

TRM-020 should use exactly that theorem to reconstruct states.

This is the first genuine recovery direction:

label-only crossing flow
  -> zero holonomy
  -> region potential.

The core result should be independent of BoundaryContact and independent of
FlowPairing / FlowTransition routing.

Do not yet introduce planar-map extraction, open residual paths, ghost
completion, BoundaryIR, optimization, or a Four-Color theorem.

## Existing owners

Reuse:

- DkMath.Tromino.RegionWalk
- FlowNetwork
- FlowCrossing
- flowEdgeSource / flowEdgeTarget / flowEdgeLabel
- FlowRegionWalk
- regionWalkXor
- RegionZeroHolonomy
- regionWalkXor_eq_of_zeroHolonomy
- RegionReachable
- regionReachable_refl/symm/trans

## Production

Create:

DkMath/Tromino/RegionPotential.lean

## A. RegionPotential certificate

Define:

```lean
structure RegionPotential {N : FlowNetwork} (C : FlowCrossing N) where
  state : Fin N.regionCount -> TrominoState
  edgeLaw : forall p : FlowNetworkPort N,
    state (flowEdgeTarget C p) =
      state (flowEdgeSource C p) + flowEdgeLabel C p
```

This is the state/color potential reconstructed from relative labels.

Do not store any original BoundaryContact.

## B. Potential integrates every walk

For P : RegionPotential C prove, for every W : FlowRegionWalk C r s:

```text
P.state s
=
P.state r + regionWalkXor W.
```

Prove structurally by induction on W.edges / validity.

Useful corollaries:

- nil walk;
- singleton edge recovers edgeLaw;
- closed walk under any potential has XOR 0.

The latter gives the necessary direction:

```text
RegionPotential C -> RegionZeroHolonomy C.
```

This is important: zero holonomy is not merely sufficient later; it is
necessary for any potential.

## C. Rooted reachability

Define:

```lean
def RootedRegionConnected {N : FlowNetwork}
    (C : FlowCrossing N) (base : Fin N.regionCount) : Prop :=
  forall s, RegionReachable C base s
```

This avoids assuming regionCount > 0 or selecting a global root
nonconstructively.

Provide the obvious theorem that a globally connected relation implies this
if a global connectedness predicate is added, but a global predicate is
optional.

## D. Existence from zero holonomy

Main existence theorem:

Given:

- base : Fin N.regionCount;
- baseState : TrominoState;
- hreach : RootedRegionConnected C base;
- hzero : RegionZeroHolonomy C;

prove:

```text
exists P : RegionPotential C,
  P.state base = baseState.
```

Construction:

For every region s choose one walk W_s : base -> s from hreach, and set

```text
state(s) := baseState + regionWalkXor W_s.
```

Use TRM-019 path-XOR independence to prove edgeLaw by comparing:

- chosen walk W_target;
- append W_source (singleton crossing edge p).

Important:

The theorem may use Classical.choice / Classical.choose internally.
Do not introduce a solver-facing noncomputable production definition if not
needed. An existential theorem with a proof witness is preferred.

## E. Based uniqueness

Prove:

If P Q : RegionPotential C,
hreach : RootedRegionConnected C base,
and

```text
P.state base = Q.state base
```

then:

```text
forall s, P.state s = Q.state s.
```

Use any walk base -> s and the integration theorem.

Expose structure equality if cheap via extensionality, but pointwise equality
is sufficient.

Thus, under rooted connectivity and fixed base state, the reconstructed
potential is unique.

## F. Gauge translation

Define a computable action:

```lean
translateRegionPotential
  (gamma : TrominoState)
  (P : RegionPotential C) : RegionPotential C
```

with:

```text
state'(r) = P.state r + gamma.
```

Prove edgeLaw is preserved.

Then, under rooted connectivity, prove any two potentials differ by a single
global translation.

A clean statement is:

For P Q : RegionPotential C and base,

let gamma := P.state base + Q.state base.

Then for every reachable s:

```text
Q.state s = P.state s + gamma
```

(or the equivalent orientation).

This is the exact gauge freedom anticipated by TRM-015.

Check orientation carefully in characteristic two.

## G. Edge-label recovery

From edgeLaw prove the symmetric-difference formula:

```text
P.state (flowEdgeSource C p) +
P.state (flowEdgeTarget C p)
=
flowEdgeLabel C p.
```

Because x + (x + delta) = delta in TrominoState.

This theorem says the reconstructed absolute states erase back to the original
relative edge label.

It is the core round-trip calibration.

## H. Proper-state / four-state separation

Since every FlowSignature label is nonzero, prove for every crossing p:

```text
P.state (flowEdgeSource C p)
!=
P.state (flowEdgeTarget C p).
```

Thus any RegionPotential gives adjacent-distinct TrominoState values on all
crossings.

Use only:

- edgeLaw;
- label nonzero.

Do not call this a Four-Color theorem. It is a proper four-state coloring
certificate for the supplied FlowNetwork/FlowCrossing.

Suggested theorem naming may use:

- regionPotential_adjacent_ne
- regionPotential_proper_on_crossing

## I. Exact equivalence on rooted connected networks

Package the main mathematical equivalence.

For fixed C with rooted connectivity from base:

```text
RegionZeroHolonomy C
iff
exists P : RegionPotential C, P.state base = baseState
```

for any baseState.

The reverse direction uses "potential integrates closed walk".

The forward direction uses the construction theorem.

If quantifying baseState makes the theorem clumsy, provide:

1. zero holonomy -> existence for every baseState;
2. potential existence -> zero holonomy.

That is sufficient.

## J. Pure-flow positive fixture

Use a small pure Flow network where RegionZeroHolonomy can actually be
proved.

The two-region single undirected edge represented by two reverse half-ports is
ideal if it satisfies the current arity/nonzero setup.

Audit:

- choose base state 0;
- reconstruct or exhibit a RegionPotential;
- target region state = deltaA;
- edge-label round trip returns deltaA;
- adjacent regions differ.

If the existing two-region A A fixture has parallel edges and creates an
additional closed walk, verify zero holonomy explicitly before using it.

Do not assume it.

## K. Negative fixture

Reuse the TRM-019 / TRM-018 three-region odd cycle.

From its known nonzero closed-walk XOR prove:

```text
not exists P : RegionPotential C
```

or equivalently derive contradiction from any proposed potential.

This gives the exact negative side:

nonzero holonomy -> no global state potential.

## L. Relation to FlowTransition

Record that FlowPairing and FlowTransition are no longer required for the
potential theorem.

They remain useful as:

- a routing/search certificate;
- a way to expose particular closed walks/obstructions.

But the state-reconstruction theorem belongs to FlowNetwork + FlowCrossing.

Do not delete the transition stack.

## M. Optional contact round-trip calibration

If small, for a contact-based BoundaryNetwork erased to FlowNetwork, and a
RegionPotential reconstructed from its labels, show that its crossing
differences agree with the original boundaryDelta labels.

Do not claim recovered absolute states equal the original contact states
without a chosen base/gauge alignment.

If base alignment is supplied, equality on a connected component may be a
later theorem.

## N. Computability and axioms

Definitions:

- RegionPotential
- translateRegionPotential

must be computable.

Existence theorem may depend on Classical.choice because a path is selected
from RegionReachable.

No:

- sorry;
- admit;
- unsafe;
- new axiom;
- solver-facing noncomputable definition.

Record Classical.choice honestly in the axiom audit.

## O. Audit

Create:

DkMathTest/Tromino/RegionPotentialAxiomAudit.lean

Audit at least:

1. potential integrates a singleton edge;
2. potential integrates appended walks;
3. potential => zero holonomy;
4. zero holonomy + rooted reachability => potential existence;
5. based uniqueness;
6. gauge translation preserves edgeLaw;
7. any two potentials differ by a global gamma on a rooted component;
8. edge-label round trip;
9. crossing endpoints get distinct states;
10. positive two-region fixture;
11. negative odd-cycle fixture has no potential.

## P. Validation

Build:

- DkMath.Tromino.RegionWalk
- DkMath.Tromino.RegionPotential
- DkMathTest/Tromino/RegionPotentialAxiomAudit

Regression-build:

- DkMath.Tromino.FlowTransitionXor
- DkMathTest/Tromino.RegionWalkAxiomAudit

Run git diff --check, forbidden-construct scan, and #print axioms.

## Q. Report

Create:

docs/dev/Tromino-ExchangeCalculus-260924-v0/report-019.md

Record:

- RegionPotential definition;
- walk integration theorem;
- necessary zero-holonomy theorem;
- rooted-connectivity definition;
- existence construction;
- uniqueness at fixed base;
- gauge freedom;
- edge-label round trip;
- adjacent-distinct theorem;
- positive/negative fixtures;
- exact scope boundary before planar-map extraction.

## Stop condition

Stop once zero holonomy plus rooted reachability reconstructs a unique
(up to global TrominoState translation) region potential whose edge
differences are exactly the supplied flow labels.

Do not proceed to planar-map extraction, open residual paths, ghost completion,
BoundaryIR, optimization, or Four-Color theorem claims without review.
