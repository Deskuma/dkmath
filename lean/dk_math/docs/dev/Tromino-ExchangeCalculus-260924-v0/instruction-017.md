# TRM-018 — FlowTransitionXor migration / label-only holonomy

## Goal

Migrate the TRM-014 transition-XOR / primitive-cycle obstruction layer from
contact-based ClosedBoundaryNetwork onto label-only ClosedFlowNetwork.

This checkpoint must preserve the existing TransitionXor API unchanged.

Do not implement general region-path potential reconstruction, color recovery,
open residual paths, ghost completion, planarity, BoundaryIR, optimization,
or Four-Color claims.

## Existing owners

Reuse:

- DkMath.Tromino.FlowTransition
- DkMath.Tromino.TransitionXor
- flowTransitionStep
- flowTransitionStep_iterate_sameLabel
- flowTransitionStep_periodic
- nsmul_state_eq_mod_two
- nsmul_state_eq_zero_iff
- ClosedBoundaryNetwork.toClosedFlowNetwork

Do not duplicate the generic characteristic-two repeated-addition lemmas from
TransitionXor.

## Production

Create:

DkMath/Tromino/FlowTransitionXor.lean

Define:

```lean
flowTransitionXor
  (N : ClosedFlowNetwork)
  (p : FlowNetworkPort N.toFlowNetwork)
  (n : Nat) : TrominoState
```

using the same convention as transitionXor:

- j = 0 contributes the starting port label;
- n steps contribute n labels;
- local mate contributes no extra state difference.

## Main repeated-label theorem

Prove:

```text
flowTransitionXor N p n
  = n • (N.signature p.1).label p.2.
```

Then reuse the characteristic-two theorem to obtain, since every FlowSignature
label is nonzero:

```text
flowTransitionXor N p n = 0
  iff
n % 2 = 0.
```

This theorem should hold for every n, not only primitive returns.

## Additivity

Prove the flow analogue of transitionXor_add:

```text
flowTransitionXor N p (n+m)
=
flowTransitionXor N p n
+
flowTransitionXor N ((flowTransitionStep N)^[n] p) m.
```

Keep it executable.

## Return / primitive return

Introduce Flow-specific propositions:

```lean
FlowTransitionReturn
FlowPrimitiveTransitionReturn
```

with the same semantics as TRM-014.

Define a first/minimal positive return:

```lean
firstFlowTransitionReturn
```

using Nat.find over flowTransitionStep_periodic, and prove:

- specification;
- minimality;
- primitive first return;
- existence of a primitive return.

Do not define a noncomputable solver-facing orbit object.

## Primitive compatibility

Define:

```lean
FlowPrimitiveCycleCompatible
```

or equivalent.

Prove the central label-only theorem:

```text
FlowPrimitiveTransitionReturn N p n
  ->
(flowTransitionXor N p n = 0
  iff
 n % 2 = 0).
```

and the compatibility iff even corollary.

This is the exact label-only form of TRM-014's global transition-orbit
obstruction.

## Prefix transport

Define:

```lean
flowTransportState
  (base : TrominoState)
  (N : ClosedFlowNetwork)
  (p : FlowNetworkPort N.toFlowNetwork)
  (n : Nat)
```

as base + flowTransitionXor.

Prove:

- zero-step;
- concatenation;
- return-to-base iff accumulated XOR = 0;
- primitive return-to-base iff primitive period is even.

Interpret this only as transport along one transition orbit prefix.

Do not claim global region coloring or arbitrary path independence.

## Pure Flow fixtures

Recreate the TRM-014 positive and negative examples without BoundaryContact.

### Even fixture

Two regions, each FlowSignature A A.

Use canonicalFlowPairing and region-swap crossing.

Audit:

- primitive period 2;
- flowTransitionXor = 0;
- flowTransportState returns to base.

### Odd fixture

Three regions, each FlowSignature A A.

Use the same 6-half-port crossing pattern as TRM-014 so that flowTransitionStep
has primitive period 3.

Audit:

- first iterate is not the start;
- second iterate is not the start;
- third iterate returns;
- primitive period 3;
- flowTransitionXor at 3 = deltaA != 0;
- flowTransportState does not return to base.

These fixtures must use only FlowSignature/FlowPairing/FlowTransition data.

## Erasure adapter / exact calibration

For every contact-based N : ClosedBoundaryNetwork, prove that after erasure:

```text
flowTransitionXor N.toClosedFlowNetwork p n
=
transitionXor N p n.
```

Also calibrate:

- flowTransportState = transportState;
- FlowTransitionReturn corresponds to TransitionReturn;
- FlowPrimitiveTransitionReturn corresponds to PrimitiveTransitionReturn;
- first-return values agree if this is definitionally easy;
- primitive compatibility agrees.

Prefer rfl / Iff.rfl where the definitions reduce exactly.

The key factorization result is:

TRM-014's odd-cycle obstruction depends only on erased labels plus the
transition certificates, not on absolute inside/outside states.

## Network-level optional wrapper

If small, define:

```lean
FlowCycleXorCompatible (N : ClosedFlowNetwork) : Prop :=
  ∀ p n, FlowPrimitiveTransitionReturn N p n ->
    flowTransitionXor N p n = 0
```

and prove it is equivalent to every primitive transition return having even
length.

This wrapper is optional; do not expand scope to general graph cycles.

## Interpretation boundary

Record explicitly:

This checkpoint proves zero/nonzero holonomy only for the homogeneous
alternating transition orbits generated by flow crossing + same-label local
pairing.

It does **not** yet prove that zero holonomy on these orbits is sufficient for
a global state potential on the region graph.

General region-path integration and its full cycle obstruction remain a later
checkpoint.

This boundary is important.

## Audit

Create:

DkMathTest/Tromino/FlowTransitionXorAxiomAudit.lean

Check:

1. repeated-label theorem;
2. XOR zero iff even;
3. two-region primitive period 2 and XOR 0;
4. three-region primitive period 3 and XOR deltaA != 0;
5. transport success/failure;
6. primitive compatibility iff even;
7. erased contact-based transitionXor agrees pointwise;
8. erased transport agrees.

## Computability / validation

All production observers and explicit fixtures must be computable.

No sorry, admit, unsafe, new axiom, or noncomputable production declaration.

Build:

- DkMath.Tromino.FlowTransition
- DkMath.Tromino.TransitionXor
- DkMath.Tromino.FlowTransitionXor
- DkMathTest/Tromino/FlowTransitionXorAxiomAudit

Regression-build the existing contact-based TransitionXor audit if practical.

Run git diff --check, forbidden-construct scan, and #print axioms.

## Report

Create:

docs/dev/Tromino-ExchangeCalculus-260924-v0/report-017.md

Record:

- flowTransitionXor convention;
- repeated-label/parity theorem;
- primitive return API;
- pure Flow even/odd fixtures;
- transport results;
- erasure calibration with TRM-014;
- exact interpretation boundary;
- computability / axiom audit;
- recommendation for the later general region-potential checkpoint.

## Stop condition

Stop when TRM-014's complete transition-orbit XOR/holonomy theorem family has
an independent label-only realization and the contact-based theorem family is
proved to factor through ClosedBoundaryNetwork.toClosedFlowNetwork.

Do not proceed to general path-potential/color recovery, open paths, ghost
completion, planarity, BoundaryIR, optimization, or Four-Color claims.
