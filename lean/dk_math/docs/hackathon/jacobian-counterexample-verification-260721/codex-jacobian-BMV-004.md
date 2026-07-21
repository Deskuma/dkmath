# BMV-004 — Verification Project Contract Templates

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

Extract the successful Jacobian verification workflow into a small set of reusable Markdown contract templates for future independently verified mathematical claims.

This checkpoint is documentation-only.

Do not modify Lean source files.
Do not modify tests.
Do not create BMV-005.
Do not create JAC-012.
Do not create a pull request.
Do not merge.
Do not modify root `DkMath.lean`.
Do not inspect large raw conversation, Codex-session, TTS-workspace, or ALL AGENT LOG files.

## Background

BMV-001 concluded that the reusable framework has two distinct layers:

1. Small Lean APIs for genuinely shared logic, such as `CollisionCertificate`.
2. Project contracts governing theorem layering, provenance, scope, trust audit, and public Demo presentation.

BMV-002 and BMV-003 completed the Lean collision layer and validated it against the normalized Jacobian counterexample.

BMV-004 must now extract only the documentation and review conventions.

Do not encode provenance, URLs, publication state, audit output, or project status as Lean structures.

## Existing Jacobian documents to inspect

Use the completed Jacobian verification documents as the principal example:

```text
lean/dk_math/docs/hackathon/jacobian-counterexample-verification-260721/README.md
lean/dk_math/docs/hackathon/jacobian-counterexample-verification-260721/PROVENANCE.md
lean/dk_math/docs/hackathon/jacobian-counterexample-verification-260721/DEMO_CONTRACT.md
lean/dk_math/docs/hackathon/jacobian-counterexample-verification-260721/jacobian-counterexample-roadmap-260721.md
```

Inspect only the parts needed to identify reusable fields and workflow rules.

Do not copy Jacobian-specific formulas, theorem names, points, determinant values, or Book of Magic interpretations into the generic templates.

## Target files

Create exactly these four files:

```text
lean/dk_math/docs/verification/README.md
lean/dk_math/docs/verification/BREAKING_MATH_CASE_TEMPLATE.md
lean/dk_math/docs/verification/PROVENANCE_TEMPLATE.md
lean/dk_math/docs/verification/DEMO_CONTRACT_TEMPLATE.md
```

Do not create additional files unless a hard repository convention requires one.

## 1. Verification README

The file:

```text
lean/dk_math/docs/verification/README.md
```

must explain the purpose of the template directory and the separation among:

```text
mathematical source claim
independent DkMath formalization
finite or explicit witnesses
summit theorem
axiom audit
provenance metadata
scope and non-goals
public Demo surface
```

It must state clearly:

- Lean verifies theorem terms, not external publication history.
- Provenance records where the claim and formulas came from.
- Axiom audit records the trust boundary of selected summit theorems.
- Demo modules should expose direct aliases of already-proved theorems rather than recompute proofs.
- A project may use a domain-specific certificate shape; no universal `VerificationBundle` is required.
- Optional interpretation layers, including Book of Magic bridges, must remain separate from the core verification certificate.

Include a compact recommended directory layout for a future case.

Use placeholders such as `<CaseName>` and `<date>` rather than any one concrete project name.

## 2. Breaking Math case template

The file:

```text
lean/dk_math/docs/verification/BREAKING_MATH_CASE_TEMPLATE.md
```

must be a reusable project landing-page template.

Required sections:

```text
Title and Status
Reported Claim
Exact Formalization Target
Source Formula or Data
Independent Formalization Boundary
Mathematical Objects
Local Identities
Explicit or Finite Witnesses
Global Consequence
Summit Theorem
Module Map
Build Commands
Axiom Audit Target
Trust Boundary
Provenance Link
Demo Contract Link
Scope and Non-Goals
Deferred Work
Checkpoint Status
```

The template must distinguish at least these statuses:

```text
reported
under reconstruction
candidate formalization
verified
refuted
inconclusive
```

Do not imply that every case is a counterexample or refutation.
The template must also support positive identity verification and finite arithmetic obstruction projects.

For each theorem-facing field, request exact Lean identifiers rather than prose-only descriptions.

The summit theorem section must allow a domain-specific theorem or conjunction theorem instead of requiring a structure.

## 3. Provenance template

The file:

```text
lean/dk_math/docs/verification/PROVENANCE_TEMPLATE.md
```

must separate the following layers:

```text
external reported source
formula transcription
DkMath-independent reconstruction
DkMath-specific formalization choices
later interpretation layers
```

Required fields:

```text
Source title or description
Author or account, when known
Publication or post location, when known
First observed date
Accessed date
Source status
Exact formulas transcribed
Missing information
Normalization or coordinate changes
Independent calculations performed
Lean encoding choices
Material not taken from the source
DkMath interpretation added later
Known uncertainties
```

The missing-information policy must permit values such as:

```text
unknown
not published
not independently confirmed
not applicable
```

Do not fabricate unavailable metadata.
Do not require a URL when no stable URL exists.
Do not treat social-media publication, peer review, independent verification, and Lean verification as equivalent statuses.

Include a small status vocabulary that keeps those distinctions explicit.

## 4. Demo contract template

The file:

```text
lean/dk_math/docs/verification/DEMO_CONTRACT_TEMPLATE.md
```

must define a stable presentation surface for videos, talks, README examples, and external reviewers.

Required sections:

```text
Demo Goal
Audience
Public Import
Ordered Theorem Surface
What Each Theorem Establishes
Trust and Axiom Statement
Presentation Sequence
Claims Allowed
Claims Not Allowed
Fallback if a theorem name changes
Build or Check Commands
```

The ordered theorem surface should use placeholder entries such as:

```lean
#check DkMath.Hackathon.<CaseName>.<demoTheoremOne>
#check DkMath.Hackathon.<CaseName>.<demoTheoremTwo>
```

Explain that Demo theorems should normally be direct aliases or thin compositions of completed theorems.
They must not conceal new heavy proof work inside the presentation layer.

The claims-allowed and claims-not-allowed sections must force the project to distinguish:

```text
what Lean proved
what external sources reported
what remains interpretation
what remains deferred
```

## Style requirements

- Write in clear English.
- Keep the templates operational rather than essay-like.
- Use checklists and placeholder fields where they improve reuse.
- Avoid mandatory fields that cannot apply to every mathematical case.
- Avoid universal proof-bundle abstractions.
- Avoid Jacobian-specific terminology except in a brief note that the templates were extracted from a completed verification case.
- Do not mention internal conversation history.
- Do not mention Codex credit usage.
- Do not add raw external URLs unless already necessary for an example; generic placeholders are preferred.

## Validation

Check that:

1. All four files exist at the exact target paths.
2. Links among the four templates are relative and valid.
3. No Lean source or test file changed.
4. No Jacobian-specific theorem identifier appears in the generic template bodies.
5. No `BreakingMathClaim`, `FiniteCertificate`, `VerificationBundle`, `ProvenanceRecord`, or `TrustAudit` Lean structure is proposed.
6. The templates support:
   - explicit collision counterexamples;
   - finite arithmetic obstructions;
   - concrete identity verification;
   - future externally reported mathematical claims.

## Required report

Return a Markdown report titled:

```text
BMV-004 Verification Project Contract Templates
```

Required sections:

```text
Summary
Files Added
Template Roles
Reusable Contract Fields
Status and Missing-Information Policy
Separation of Lean Proof and Metadata
Cross-Template Links
Validation
Non-Goals Preserved
Changed Files
Outcome
```

Report one outcome:

```text
Outcome A:
  All four reusable templates are complete and remain independent of any one mathematical domain.

Outcome B:
  The templates are usable, but one contract boundary requires revision.

Outcome C:
  Existing repository documentation already provides equivalent generic templates, so no new files were needed.
```

Stop after the report.
