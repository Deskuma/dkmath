# Breaking Math Verification

## Jacobian counterexample case study

[Watch the 2:56 demo](https://youtu.be/IGNKJBknzrQ)

Breaking Math Verification is a reusable Lean 4 workflow for turning a newly
reported mathematical claim into an independently reconstructed, auditable
verification package.

This case study formalizes the displayed three-variable polynomial map over
`ℚ` and `ℂ`, computes its formal Jacobian, normalizes its determinant to `1`,
and verifies an explicit three-point collision.

The project separates four questions that are often mixed together:

1. What formulas were reported?
2. What exact statement was independently encoded in Lean?
3. Which finite witnesses establish the formal consequence?
4. Which axioms does the final certificate depend on?

## Verified result

For the normalized polynomial map `F̃ : ℂ³ → ℂ³`, Lean verifies:

```text
det J(F̃) = 1
```

and three pairwise-distinct inputs map to the same exact target:

```text
(0, 0, -1/4)
(1, -3/2, 13/2)
(-1, 3/2, 13/2)

F̃(p₀) = F̃(p₁) = F̃(p₂) = (1/8, 0, 0)
```

Therefore the formalized map is not injective and has no set-theoretic left
inverse.

## Public Lean surface

```text
jacobianCounterexampleCertificateQ
jacobianCounterexampleCertificateC
normalizedJacobianCounterexampleCertificateC
normalized_three_point_collision_C
evalNormalizedCounterexampleC_noLeftInverse
normalizedCollisionCertificateC
normalizedCollisionCertificateC_notInjective
normalizedCollisionCertificateC_noLeftInverse
```

The generic collision API is available through:

```text
DkMath.Verification.CollisionCertificate
DkMath.Verification.CollisionCertificate.notInjective
DkMath.Verification.CollisionCertificate.noLeftInverse
```

## Fast judge path

No account or hosted service is required.

1. Watch the public demo: <https://youtu.be/IGNKJBknzrQ>
2. Inspect this directory and the focused audit module:
   [`DkMathTest/Hackathon/JacobianCounterexample3/CheckAxioms.lean`](../../../DkMathTest/Hackathon/JacobianCounterexample3/CheckAxioms.lean)
3. Read the full verification record:
   [`docs/hackathon/jacobian-counterexample-verification-260721`](../../../docs/hackathon/jacobian-counterexample-verification-260721/README.md)

## Build and test

Supported project environment: Lean 4 + Mathlib through the DkMath Lake
workspace. The project was built and rendered on Linux; the Lean modules are
portable to platforms supported by the repository toolchain.

From `lean/dk_math`:

```sh
lake build DkMath.Hackathon.JacobianCounterexample3
lake build DkMathTest.Hackathon.JacobianCounterexample3.CheckAxioms
lake build DkMathTest.Verification.CheckAxioms
```

The second command checks the rational, complex, normalized, collision, Demo,
and verification-bridge certificates. The generic collision consequences are
also audited separately and depend on no axioms.

## Project structure

```text
Basic.lean                 exact points, targets, and coordinate data
PolynomialMap.lean         polynomial map definitions
Collision.lean             explicit evaluation and collision witnesses
Jacobian.lean              formal partial derivatives
Determinant.lean            determinant computation
Counterexample.lean        rational summit certificate
ComplexLift.lean           transport to ℂ
Normalized.lean            determinant-one presentation map
VerificationBridge.lean    adapter to the reusable collision API
Demo.lean                  stable presentation theorems
```

The project aggregator is
[`DkMath.Hackathon.JacobianCounterexample3`](../JacobianCounterexample3.lean).

## GPT-5.6 and Codex collaboration

GPT-5.6 was used for mathematical decomposition, theorem-boundary design,
architecture review, scope control, and checkpoint evaluation.

Codex inspected the live repository, implemented the Lean modules, reused
existing APIs instead of duplicating proofs, ran focused builds and axiom
audits, generated structured handoff reports, and produced the reproducible
video pipeline.

A key workflow innovation was using committed repository reports as an
auditable handoff channel between GPT-5.6 review and Codex implementation. The
resulting BMV-001 through BMV-006 checkpoints extracted:

```text
reported claim
  → independent reconstruction
  → explicit witness
  → summit theorem
  → axiom audit
  → provenance record
  → stable Demo surface
```

## Trust boundary

Lean verifies the exact formalized polynomial identities, determinant, explicit
collision, and their logical consequences.

It does not certify historical priority, authorship, publication status, peer
review, community acceptance, or the correctness of claims that were not
encoded. The candidate is new and broader mathematical review may continue;
this project supplies a fast, reproducible first verification layer for the
exact formulas under discussion.

## Further documentation

- [Full case README](../../../docs/hackathon/jacobian-counterexample-verification-260721/README.md)
- [Verification contracts](../../../docs/verification/README.md)
- [Video production package](../../../docs/hackathon/jacobian-counterexample-verification-260721/video/README.md)
- [Provenance record](../../../docs/hackathon/jacobian-counterexample-verification-260721/PROVENANCE.md)

Released under the repository MIT license.
