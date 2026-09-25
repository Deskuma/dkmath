# TRM-016 — FlowPairing migration / label-only residual normal form

## Goal

Move the TRM-012 pairing/residual layer from contact-based BoundarySignature
onto TRM-015 FlowSignature, without changing existing BoundaryPairing,
TransitionGraph, or TransitionXor APIs.

This checkpoint is additive. Do not implement FlowNetwork, color recovery,
open paths, ghost completion, planarity, BoundaryIR, optimization, or a
Four-Color theorem.

## Existing reusable machinery

Reuse FlowSignature, flowLabelCount, FlowConserved,
flowConserved_even_or_odd, and the contact-independent ordered-pairing helpers
already in BoundaryPairing:

- adjacentMate
- adjacentMate_involutive
- adjacentMate_card_residual
- fiberPairing
- fiberPairing_involutive

Do not duplicate these helpers. A tiny shared-helper refactor is allowed only
if it preserves current theorem names and imports.

## Production

Create DkMath/Tromino/FlowPairing.lean.

Define:

```lean
structure FlowPairing (F : FlowSignature) where
  mate : Fin F.arity → Fin F.arity
  involutive : Function.Involutive mate
  sameLabel : ∀ i, F.label (mate i) = F.label i
```

Fixed points are residual ports; non-fixed 2-cycles are paired ports.

Add:

- flowResidualPorts
- flowPairedPorts
- membership lemmas
- non-residual transition-readiness:
  mate i ≠ i,
  F.label (mate i) = F.label i,
  mate (mate i) = i.

## Canonical computable pairing

Define label fibers

```text
flowPortsWithLabel F delta
```

and construct canonicalFlowMate / canonicalFlowPairing by the same deterministic
ordered policy as TRM-012:

- order each equal-label fiber by Fin index;
- pair ranks 0↔1, 2↔3, ...;
- if odd, leave the final rank fixed.

No Classical.choice-selected production pairing and no noncomputable
declaration.

## Main normal-form theorems

For arbitrary F and delta prove

```text
card(residual ports with label delta)
  = flowLabelCount F delta % 2.
```

Then derive total residual card as the sum of the A/B/C parities.

For conserved flows:

- all-even → residual set empty;
- all-odd → residual card 3;
- in the odd case exactly one residual A, one B, one C.

Package the conserved decomposition as empty-or-card-3.

Also retain nonconserved diagnostics:
A A B C leaves exactly one B and one C residual.

Duplicate A A must pair the two distinct Fin indices with no residual.

## BoundaryPairing adapter

Add a compatibility adapter

```lean
BoundaryPairing.toFlowPairing
  {S : BoundarySignature}
  (P : BoundaryPairing S) :
  FlowPairing S.toFlowSignature
```

with the same mate function.

Prove:

- adapted mate = original mate;
- residual membership/cardinality agrees.

Then prove the canonical constructions agree under erasure:

```text
(canonicalBoundaryPairing S).mate i
=
(canonicalFlowPairing S.toFlowSignature).mate i.
```

Derive equality of the canonical residual sets.

This is the key factorization theorem: TRM-012 depends only on erased labels.

## Scope / compatibility

Do not migrate TransitionGraph or TransitionXor yet.
Regression-build them unchanged.

Do not rewrite BoundaryPairing wholesale. If FlowPairing imports
BoundaryPairing temporarily to reuse generic helpers, record that dependency
choice in the report.

## Audit

Create DkMathTest/Tromino/FlowPairingAxiomAudit.lean.

Check:

1. empty flow → no residual;
2. A A B B C C → perfect;
3. A A A B B B C C C → 3 residuals, one A/B/C;
4. A A B C → 2 residuals, one B/C;
5. A A duplicate indices pair together;
6. contact-based signature erasure gives pointwise-equal canonical mates;
7. canonical residual sets agree under erasure;
8. transition-readiness on an arbitrary non-residual flow port.

Run focused builds for FlowSignature, BoundaryPairing, FlowPairing and its
audit, plus regression builds of TransitionGraph and TransitionXor.

Run git diff --check, forbidden-construct scan, and #print axioms.

No sorry/admit/unsafe/new axiom/noncomputable production declaration.

## Report

Create
docs/dev/Tromino-ExchangeCalculus-260924-v0/report-015.md

Record representation, helper reuse/refactor, canonical construction,
residual-parity theorem, conserved decomposition, erasure adapter/calibration,
computability, and regression status.

## Stop condition

Stop when the complete TRM-012 pairing/residual theorem family exists on
FlowSignature and the existing canonical BoundaryPairing is proved to factor
through BoundarySignature.toFlowSignature.
