# BMV-006 — Public Framework Integration

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

Complete the BMV framework by publishing the already validated generic
`DkMath.Verification` API through the root `DkMath` import.

This is a small public-integration checkpoint. The generic collision certificate
has already been validated independently and against the normalized Jacobian
case. The verification workflow has also been validated on the unrelated GN5
finite arithmetic obstruction case.

Do not create a universal verification bundle.
Do not migrate existing counterexample projects.
Do not modify Jacobian mathematics or GN5 arithmetic.
Do not create JAC-012.
Do not create a pull request.
Do not merge.
Do not inspect large raw conversation, Codex-session, TTS-workspace, or
ALL AGENT LOG files.

## Current validated API

The aggregator already exists:

```text
DkMath/Verification.lean
```

It currently exports:

```lean
DkMath.Verification.CollisionCertificate
DkMath.Verification.CollisionCertificate.notInjective
DkMath.Verification.CollisionCertificate.noLeftInverse
```

The implementation module remains:

```text
DkMath/Verification/Collision.lean
```

Do not change the structure fields or theorem statements unless a genuine public
integration problem is discovered.

## Required changes

### 1. Root public import

Update:

```text
DkMath.lean
```

Add:

```lean
import DkMath.Verification
```

Place it with the generic reusable infrastructure near `DkMath.Lib`, before
project/domain imports. Add a short comment identifying it as the reusable
verification certificate layer if that improves the local import map.

Do not import Jacobian or GN5 modules through `DkMath.Verification`.
The dependency direction must remain:

```text
DkMath.Verification
  ↓
domain-specific adapters and cases
```

Never the reverse.

### 2. Root public-surface test

Create:

```text
DkMathTest/Verification/CheckAxioms.lean
```

It must import only:

```lean
import DkMath
```

Then check the public API through the root import:

```lean
#check DkMath.Verification.CollisionCertificate
#check DkMath.Verification.CollisionCertificate.notInjective
#check DkMath.Verification.CollisionCertificate.noLeftInverse
```

Also audit the two generic consequence theorems:

```lean
#print axioms DkMath.Verification.CollisionCertificate.notInjective
#print axioms DkMath.Verification.CollisionCertificate.noLeftInverse
```

The expected result from the already completed focused test is that both generic
theorems depend on no axioms. Record the exact output in the report.

Do not duplicate the `Bool` example from
`DkMathTest/Verification/Collision.lean`. This new test exists specifically to
validate root-import visibility and the final public trust boundary.

### 3. Verification documentation status

Update:

```text
docs/verification/README.md
```

Add a compact status section recording that:

- `DkMath.Verification` is public through root `DkMath`;
- the generic collision certificate was validated on an explicit Jacobian
  collision case;
- the broader verification project contracts were separately validated on a
  finite GN5 arithmetic obstruction case;
- the GN5 case is a cross-domain engineering validation, not a universal proof
  bundle and not a dependency of `DkMath.Verification`.

Keep this factual and brief. Do not turn the documentation into a new project
landing page.

### 4. BMV roadmap completion status

Update the Jacobian verification project README only as needed to mark BMV-001
through BMV-006 complete and to point to the reusable verification contracts.
Do not rewrite the Jacobian submission narrative around GN5.

Candidate file:

```text
docs/hackathon/jacobian-counterexample-verification-260721/README.md
```

The public Jacobian story remains focused on rapid independent verification of
the explicit Jacobian counterexample. GN5 remains a framework validation example.

## Required dependency audit

Confirm the final graph is effectively:

```text
Mathlib
  ↓
DkMath.Verification.Collision
  ↓
DkMath.Verification
  ↓
DkMath root public import

DkMath.Verification
  ↓
Jacobian VerificationBridge

existing GN5 arithmetic
  ↓
GN5 summit certificate and Demo
```

Confirm there is no edge from `DkMath.Verification` to:

```text
DkMath.Hackathon.JacobianCounterexample3
DkMath.Hackathon.FinitePrimeEscapeGN5
DkMath.BookOfMagic
DkMath.FLT
```

## Required validation

Run focused builds from `lean/dk_math`:

```sh
lake build DkMath.Verification
lake build DkMathTest.Verification.CheckAxioms
```

Also run the root build target needed to confirm the new root import is valid:

```sh
lake build DkMath
```

The supplied checkpoint is treated as build-validated after Codex reports it.
Do not spend report space on unrelated pre-existing warnings.

## Non-goals

Do not add:

- `VerificationBundle`;
- `BreakingMathClaim`;
- `FiniteCertificate`;
- `RefutationCertificate`;
- provenance or audit structures in Lean;
- generic arithmetic obstruction structures;
- automatic source or URL verification;
- migration of existing DkMath counterexamples;
- Jacobian or GN5 imports inside `DkMath.Verification`;
- new Jacobian or GN5 mathematics;
- root imports for the BMV-005 certificate or Demo;
- video, TTS, Devpost submission, PR, or merge work.

## Repository handoff protocol

Do not paste a long completion report into the chat.

Create and commit:

```text
docs/hackathon/jacobian-counterexample-verification-260721/report-jacobian-BMV-006.md
```

The report must contain:

1. Summary
2. Files Changed
3. Root Public Import
4. Public API Checks
5. Generic Axiom Audit with exact output
6. Dependency Direction
7. Documentation Status
8. Non-Goals Preserved
9. Build Result
10. Changed Files
11. Outcome

Commit and push all BMV-006 changes to the current branch.

Return in chat only:

```text
commit SHA
short changed-files summary
Outcome A/B/C
report path
```

## Outcome classification

- **Outcome A** — root import, public checks, generic audit, and documentation are
  complete with dependency direction preserved.
- **Outcome B** — API is public, but import placement, test surface, or
  documentation needs a small adjustment.
- **Outcome C** — root publication exposes a genuine dependency or naming problem
  requiring redesign.

Stop after BMV-006. Do not start another checkpoint.
