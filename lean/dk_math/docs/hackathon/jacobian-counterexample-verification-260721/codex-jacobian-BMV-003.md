# BMV-003 — Jacobian Adapter Validation

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

Connect the completed normalized Jacobian collision witnesses to the new generic
`DkMath.Verification.CollisionCertificate` API through one thin adapter module.

This checkpoint validates that the generic API works naturally on a real
DkMath verification project without replacing the existing Jacobian theorems.

Do not create JAC-012.
Do not create a pull request.
Do not merge.
Do not modify root `DkMath.lean`.
Do not inspect large raw conversation, Codex-session, TTS-workspace, or
ALL AGENT LOG files.

## Existing API to reuse

The generic API already exists in:

```text
DkMath/Verification/Collision.lean
```

with:

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

and:

```lean
theorem CollisionCertificate.notInjective
    (c : CollisionCertificate f) :
    ¬ Function.Injective f

theorem CollisionCertificate.noLeftInverse
    (c : CollisionCertificate f) :
    ¬ ∃ g : β → α, Function.LeftInverse g f
```

The normalized Jacobian implementation already exposes:

```lean
p0C
p1C
p0C_ne_p1C
normalized_eval_p0C
normalized_eval_p1C
evalNormalizedCounterexampleC
evalNormalizedCounterexampleC_notInjective
evalNormalizedCounterexampleC_noLeftInverse
```

Do not re-prove polynomial evaluation, collision coordinates, determinant
identities, complex transport, or normalization algebra.

## Target source file

Add:

```text
lean/dk_math/DkMath/Hackathon/JacobianCounterexample3/VerificationBridge.lean
```

Use namespace:

```lean
namespace DkMath.Hackathon.JacobianCounterexample3
```

Import only the required modules. The bridge may import:

```lean
import DkMath.Hackathon.JacobianCounterexample3.Normalized
import DkMath.Verification.Collision
```

## Required adapter

Define an explicit certificate using `p0C` and `p1C`:

```lean
def normalizedCollisionCertificateC :
    DkMath.Verification.CollisionCertificate
      evalNormalizedCounterexampleC where
  left := p0C
  right := p1C
  left_ne_right := p0C_ne_p1C
  map_eq := by
    calc
      evalNormalizedCounterexampleC p0C = normalizedTargetC := normalized_eval_p0C
      _ = evalNormalizedCounterexampleC p1C := normalized_eval_p1C.symm
```

The exact proof syntax may be adjusted if elaboration requires it, but the
certificate must be assembled only from existing normalized witnesses.

## Required consequence theorems

Expose thin domain-facing theorems derived from the generic certificate:

```lean
theorem normalizedCollisionCertificateC_notInjective :
    ¬ Function.Injective evalNormalizedCounterexampleC :=
  normalizedCollisionCertificateC.notInjective
```

and:

```lean
theorem normalizedCollisionCertificateC_noLeftInverse :
    ¬ ∃ G : Point3C → Point3C,
      Function.LeftInverse G evalNormalizedCounterexampleC :=
  normalizedCollisionCertificateC.noLeftInverse
```

These are compatibility-facing adapter theorems.

Do not delete, rename, or rewrite the existing theorems:

```lean
evalNormalizedCounterexampleC_notInjective
evalNormalizedCounterexampleC_noLeftInverse
```

The old direct proofs and the new generic derivations should coexist.

## Project aggregator

Update:

```text
lean/dk_math/DkMath/Hackathon/JacobianCounterexample3.lean
```

so the project aggregator publicly imports the new bridge as well as the
existing Demo module.

Keep the dependency one-way:

```text
DkMath.Verification
  ↓
JacobianCounterexample3.VerificationBridge
```

The following reverse dependency is forbidden:

```text
DkMath.Verification
  ─X→ JacobianCounterexample3
```

Do not add `DkMath.Verification` to root `DkMath.lean` in this checkpoint.

## Axiom audit

Update the existing focused audit:

```text
lean/dk_math/DkMathTest/Hackathon/JacobianCounterexample3/CheckAxioms.lean
```

Add:

```lean
#print axioms DkMath.Hackathon.JacobianCounterexample3.normalizedCollisionCertificateC_notInjective
#print axioms DkMath.Hackathon.JacobianCounterexample3.normalizedCollisionCertificateC_noLeftInverse
```

Record the exact output in the report.

The expected trust boundary is the same as the existing normalized Jacobian
witness chain. Do not introduce project-specific axioms, `sorry`, `axiom`, or
`native_decide`.

## Validation

Build at least:

```text
lake build DkMath.Hackathon.JacobianCounterexample3.VerificationBridge
lake build DkMath.Hackathon.JacobianCounterexample3
lake build DkMathTest.Hackathon.JacobianCounterexample3.CheckAxioms
```

Confirm that the adapter consequence theorem propositions match the existing
public consequences:

```lean
example : ¬ Function.Injective evalNormalizedCounterexampleC :=
  normalizedCollisionCertificateC_notInjective

example :
    ¬ ∃ G : Point3C → Point3C,
      Function.LeftInverse G evalNormalizedCounterexampleC :=
  normalizedCollisionCertificateC_noLeftInverse
```

These examples may be placed in the focused test/audit file when useful.

## Non-goals

Do not:

- alter the normalized polynomial map;
- alter collision points or targets;
- alter determinant proofs;
- replace the three-point collision theorem;
- replace the existing direct noninjectivity proofs;
- modify `DkMath.BookOfMagic`;
- merge `CollisionCertificate` with `UniqueGap` or `GapCrystal`;
- rename the existing Demo API;
- add a universal verification bundle;
- add provenance metadata to Lean;
- import the framework from root `DkMath.lean`;
- create BMV-004 work in this checkpoint.

## Changed-file discipline

Expected changed files:

```text
lean/dk_math/DkMath/Hackathon/JacobianCounterexample3/VerificationBridge.lean
lean/dk_math/DkMath/Hackathon/JacobianCounterexample3.lean
lean/dk_math/DkMathTest/Hackathon/JacobianCounterexample3/CheckAxioms.lean
```

Do not modify unrelated files.

## Report

Return a Markdown report titled:

```text
BMV-003 Jacobian Adapter Validation
```

Required sections:

```text
Summary
Files Changed
Adapter Definition
Generic Consequences
Compatibility with Existing Theorems
Dependency Direction
Axiom Audit
Non-Goals Preserved
Build Result
Outcome
```

Use one of these outcomes:

```text
Outcome A:
  The normalized Jacobian collision is connected cleanly to the generic
  CollisionCertificate API, with both generic consequences complete.

Outcome B:
  The certificate is complete, but one domain-facing consequence requires an
  API or type-signature adjustment.

Outcome C:
  The generic API does not fit the normalized Jacobian witness without an
  undesirable dependency or abstraction change.
```

Stop after the report.
