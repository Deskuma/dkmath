# Codex Instruction: BMV-002

## Generic Collision Certificate

Repository:

```text
Deskuma/dkmath
```

Branch:

```text
hackathon/breaking-math-jacobian-counterexample
```

Base:

```text
develop
```

## Goal

Add the smallest reusable Lean API for certifying that a function has an explicit two-point collision.

This checkpoint is implementation work.

## Restrictions

- Do not modify the Jacobian modules.
- Do not create JAC-012.
- Do not add provenance metadata structures.
- Do not integrate with `DkMath.BookOfMagic`.
- Do not create a pull request.
- Do not merge.
- Do not inspect large raw conversation, Codex-session, or `ALL AGENT LOG` files.

## Target files

```text
lean/dk_math/DkMath/Verification/Collision.lean
lean/dk_math/DkMath/Verification.lean
lean/dk_math/DkMathTest/Verification/Collision.lean
```

## Namespace

```lean
namespace DkMath.Verification
```

## Implementation

Implement the following structure.

```lean
structure CollisionCertificate
    {α : Type u}
    {β : Type v}
    (f : α → β) where
  left : α
  right : α
  left_ne_right : left ≠ right
  map_eq : f left = f right
```

Prove the following theorem.

```lean
theorem CollisionCertificate.notInjective
    {α : Type u}
    {β : Type v}
    {f : α → β}
    (c : CollisionCertificate f) :
    ¬ Function.Injective f
```

Prove the following theorem.

```lean
theorem CollisionCertificate.noLeftInverse
    {α : Type u}
    {β : Type v}
    {f : α → β}
    (c : CollisionCertificate f) :
    ¬ ∃ g : β → α, Function.LeftInverse g f
```

The proofs must derive the contradiction directly from:

```text
c.left_ne_right
c.map_eq
```

Prefer the existing `Function.LeftInverse` and `Function.Injective` APIs when useful.

## Tests

In:

```text
lean/dk_math/DkMathTest/Verification/Collision.lean
```

provide at least:

1. A concrete noninjective function with an explicit certificate.
2. A check that `.notInjective` proves noninjectivity.
3. A check that `.noLeftInverse` proves absence of a left inverse.
4. `#print axioms` for both public consequence theorems.

## Public module

The file:

```text
lean/dk_math/DkMath/Verification.lean
```

must import:

```lean
import DkMath.Verification.Collision
```

Do not yet import `DkMath.Verification` from root `DkMath.lean`.
That public-root decision is deferred to BMV-006.

## Do not add

- `BreakingMathClaim`
- `FiniteCertificate`
- `VerificationBundle`
- `RefutationCertificate`
- `ProvenanceRecord`
- `TrustAudit`

## Do not modify

- `DkMath.Hackathon.JacobianCounterexample3.*`
- `DkMath.BookOfMagic.*`
- existing Petal obstruction APIs

## Documentation

Add a short module-level doc comment explaining that a `CollisionCertificate` records two distinct inputs with the same image and provides generic consequences independent of any domain-specific counterexample.

## Build

Build the new source module and its focused test.

## Report

Return a Markdown report titled:

```text
BMV-002 Generic Collision Certificate
```

Required sections:

```text
Summary
Files Added
Public API
Proof Strategy
Tests
Axiom Audit
Non-Goals Preserved
Build Result
Changed Files
Outcome
```

Use one of the following outcomes.

### Outcome A

The generic certificate and both consequence theorems are complete.

### Outcome B

The structure is complete, but one consequence theorem requires API adjustment.

### Outcome C

An existing DkMath or Mathlib abstraction makes this new structure unnecessary.

Stop after the report.
