# Instructions

## JAC-011

Implement the final checkpoint JAC-011 Demo and Submission Package for the
DkMath Jacobian counterexample verification project.

Repository:
Deskuma/dkmath

Branch:
hackathon/breaking-math-jacobian-counterexample

Completed checkpoints:

- JAC-001 through JAC-010
- rational counterexample certificate
- complex counterexample certificate
- determinant-one Keller normalization
- public DkMath import
- axiom audit
- Book of Magic UniqueGap / GapCrystal API
- Jacobian GapCrystal bridge
- general polynomial GN finite-difference theorem

This is the final planned checkpoint.

Do not add new mathematical claims.
Do not begin higher-dimensional padding or PrincipalPartCompletion.

## Main goal

Create a small presentation surface that shows, in this order:

1. the explicit normalized polynomial map;
2. its formal Jacobian determinant is `1`;
3. three distinct complex points share one image;
4. therefore the map is not injective and has no left inverse;
5. the collision is interpreted as non-unique restoring Gaps;
6. the Lean certificates have no `sorryAx` or project-specific axioms.

The Demo layer must reuse the completed theorems.
It must not recompute the determinant or point evaluations.

## 1. Create Demo.lean

Create:

```text
lean/dk_math/DkMath/Hackathon/JacobianCounterexample3/Demo.lean
```

Import:

```lean
import DkMath.Hackathon.JacobianCounterexample3.GapCrystalBridge
```

Use:

```lean
namespace DkMath.Hackathon.JacobianCounterexample3
```

Add concise presentation aliases.

Required:

```lean
/-- Demo certificate: the normalized formal Jacobian determinant is one. -/
theorem jacobianDemo_det_eq_one :
    normalizedJacobianMatrixC.det =
      MvPolynomial.C (1 : ℂ) :=
  normalizedJacobianMatrixC_det_eq_one
```

```lean
/-- Demo certificate: three distinct points lie in one normalized fiber. -/
theorem jacobianDemo_three_point_collision :
    p0C ≠ p1C ∧ p0C ≠ p2C ∧ p1C ≠ p2C ∧
      evalNormalizedCounterexampleC p0C = normalizedTargetC ∧
      evalNormalizedCounterexampleC p1C = normalizedTargetC ∧
      evalNormalizedCounterexampleC p2C = normalizedTargetC :=
  normalized_three_point_collision_C
```

```lean
/-- Demo certificate: the normalized polynomial map is not injective. -/
theorem jacobianDemo_notInjective :
    ¬ Function.Injective evalNormalizedCounterexampleC :=
  evalNormalizedCounterexampleC_notInjective
```

```lean
/-- Demo certificate: the normalized map has no set-theoretic left inverse. -/
theorem jacobianDemo_noLeftInverse :
    ¬ ∃ G : Point3C → Point3C,
      Function.LeftInverse G evalNormalizedCounterexampleC :=
  evalNormalizedCounterexampleC_noLeftInverse
```

```lean
/-- Demo certificate: the common output has no unique restoring input Gap. -/
theorem jacobianDemo_target_notUniqueGap :
    ¬ DkMath.BookOfMagic.UniqueGap
      normalizedRestoreRelC
      normalizedTargetC :=
  normalizedTargetC_not_uniqueGap
```

Add the compact summit alias:

```lean
/--
Presentation surface for a complex polynomial map whose formal Jacobian
determinant is one but which is not injective.
-/
theorem jacobianDemoCertificateC :
    normalizedJacobianMatrixC.det =
        MvPolynomial.C (1 : ℂ) ∧
    normalizedJacobianMatrixC.det ≠ 0 ∧
    ¬ Function.Injective evalNormalizedCounterexampleC :=
  normalizedJacobianCounterexampleCertificateC
```

Do not duplicate proofs.
Each theorem should be a direct reuse of an existing theorem.

Add the standard build marker:

```lean
#print "file: DkMath.Hackathon.JacobianCounterexample3.Demo"
```

Do not add permanent `#check` commands.

## 2. Update the public aggregator

Modify:

```text
lean/dk_math/DkMath/Hackathon/JacobianCounterexample3.lean
```

Change its import to:

```lean
import DkMath.Hackathon.JacobianCounterexample3.Demo
```

`Demo` imports `GapCrystalBridge`, so the complete existing theorem surface
must remain publicly available.

Do not alter `DkMath.lean`; it already imports the project aggregator.

## 3. Extend the axiom audit

Modify:

```text
lean/dk_math/DkMathTest/Hackathon/JacobianCounterexample3/CheckAxioms.lean
```

Keep the existing three certificate audits.

Add:

```lean
#print axioms DkMath.Hackathon.JacobianCounterexample3.jacobianDemoCertificateC
```

Expected acceptable foundations are the same standard Lean/Mathlib axioms
already observed:

```text
propext
Classical.choice
Quot.sound
```

Failure signals:

```text
sorryAx
DkMath-specific axiom
unexpected theorem assumption
```

Report the exact output.

## 4. Update the project README

Update:

```text
lean/dk_math/docs/hackathon/jacobian-counterexample-verification-260721/README.md
```

Convert it from a planning document into a completed verification landing page.

Required sections:

```text
Status
Verified map
Normalized map
Main Lean certificates
Three-point collision
Module map
Build
Axiom audit
Book of Magic interpretation
GN finite-difference recovery
Scope and non-goals
Provenance
```

### Status

State that JAC-001 through JAC-011 are complete after this checkpoint.

### Main theorem surface

List the exact current names:

```lean
jacobianCounterexampleCertificateQ
jacobianCounterexampleCertificateC
normalizedJacobianCounterexampleCertificateC
jacobianDemoCertificateC
normalized_three_point_collision_C
evalNormalizedCounterexampleC_noLeftInverse
normalizedTargetC_not_uniqueGap
normalizedForgetGap_notInjective
eval_add_sub_eval_eq_mul_GNFiniteDifference
differenceQuotient_eq_GNFiniteDifference
```

### Normalized map

Explain that the first output coordinate is multiplied by `-1/2`.

State the normalized common target exactly:

```text
(1/8, 0, 0)
```

Derive it from `normalizeOutputC targetC`; do not introduce a new Lean
definition solely for the documentation.

### Actual module map

Reflect the implemented files:

```text
DkMath/Hackathon/JacobianCounterexample3/
├── Basic.lean
├── PolynomialMap.lean
├── Collision.lean
├── Jacobian.lean
├── Determinant.lean
├── Counterexample.lean
├── ComplexLift.lean
├── Normalized.lean
├── GapCrystalBridge.lean
└── Demo.lean

DkMath/Hackathon/JacobianCounterexample3.lean

DkMath/BookOfMagic/
├── UniqueGapContract.lean
├── GapCrystal.lean
└── GNFiniteDifference.lean

DkMath/BookOfMagic.lean
```

### Build commands

Include commands for:

```text
lake build DkMath.Hackathon.JacobianCounterexample3
lake build DkMath.BookOfMagic
lake build DkMathTest.Hackathon.JacobianCounterexample3.CheckAxioms
lake build DkMath
```

Do not claim a clean root warning set if unrelated existing warnings are
outside this project.

### Trust statement

Clearly distinguish:

```text
Lean kernel-checked algebraic certificate
```

from:

```text
historical priority, authorship, publication status, and external review
```

The README may say that DkMath independently formalizes and verifies the
stated formulas. It must not claim that DkMath discovered the counterexample.

## 5. Create DEMO_CONTRACT.md

Create:

```text
lean/dk_math/docs/hackathon/jacobian-counterexample-verification-260721/DEMO_CONTRACT.md
```

Specify a three-part demonstration.

### Part A — Polynomial map

Show:

```text
the normalized complex polynomial map
the fact that its Jacobian is generated by MvPolynomial.pderiv
```

Do not display all nine expanded derivative entries unless needed as a
brief proof-chain screenshot.

### Part B — Local certificate

Show:

```lean
#check jacobianDemo_det_eq_one
#print axioms jacobianDemoCertificateC
```

Narrative:

```text
Lean computes the formal Jacobian from the polynomial definition and proves
that its determinant is exactly one.
```

### Part C — Global collision

Show:

```lean
#check jacobianDemo_three_point_collision
#check jacobianDemo_notInjective
#check jacobianDemo_noLeftInverse
```

Narrative:

```text
The local Jacobian is everywhere nondegenerate, but three distinct input
addresses share one output.
```

End with the Book of Magic interpretation:

```lean
#check jacobianDemo_target_notUniqueGap
```

Provide a compact timing plan suitable for a video under three minutes, but
do not add or upload any video in this checkpoint.

## 6. Create PROVENANCE.md

Create:

```text
lean/dk_math/docs/hackathon/jacobian-counterexample-verification-260721/PROVENANCE.md
```

The document must distinguish three layers.

### A. Mathematical source

Record the exact original source information already available in repository
notes and project materials:

```text
author or account name
title or post description
publication date
exact URL
date accessed
```

Search the existing repository documents before writing this section.

Do not invent missing metadata.

If an exact primary-source field cannot be located, explicitly mark that
single field as:

```text
Not yet fixed in repository records
```

rather than guessing.

### B. DkMath formal verification

State that DkMath independently formalizes:

```text
the polynomial definitions
the three explicit evaluations
the formal partial derivatives
the 3×3 determinant
the rational-to-complex coefficient transport
the determinant-one output normalization
noninjectivity and no-left-inverse consequences
```

State that the proofs are checked by Lean 4 + Mathlib.

### C. Interpretation added by DkMath

Identify these as DkMath interpretation layers, not part of the source claim:

```text
UniqueGap
GapCrystal
forgetGap
GNFiniteDifference
```

Also record that scaling the first output coordinate by `-1/2` is a
presentation normalization used to obtain determinant `1`.

Do not make claims about historical priority beyond the available source
record.

## 7. Update the roadmap

Modify:

```text
lean/dk_math/docs/hackathon/jacobian-counterexample-verification-260721/
  jacobian-counterexample-roadmap-260721.md
```

Mark JAC-001 through JAC-010 complete.

After all JAC-011 work builds, mark JAC-011 complete and add a final status:

```text
Mathematical summit: complete
Public import: complete
Axiom audit: complete
Book of Magic extraction: complete
Demo package: complete
```

Do not add new checkpoints to this roadmap.

List higher-dimensional padding and PrincipalPartCompletion under deferred
future work only.

## 8. Public checks

Using a temporary file importing only:

```lean
import DkMath
```

verify:

```lean
#check DkMath.Hackathon.JacobianCounterexample3.jacobianDemo_det_eq_one
#check DkMath.Hackathon.JacobianCounterexample3.jacobianDemo_three_point_collision
#check DkMath.Hackathon.JacobianCounterexample3.jacobianDemo_notInjective
#check DkMath.Hackathon.JacobianCounterexample3.jacobianDemo_noLeftInverse
#check DkMath.Hackathon.JacobianCounterexample3.jacobianDemo_target_notUniqueGap
#check DkMath.Hackathon.JacobianCounterexample3.jacobianDemoCertificateC
```

Remove the temporary file afterward.

## 9. Verification

Build:

```text
DkMath.BookOfMagic.GNFiniteDifference
DkMath.BookOfMagic
DkMath.Hackathon.JacobianCounterexample3.Demo
DkMath.Hackathon.JacobianCounterexample3
DkMathTest.Hackathon.JacobianCounterexample3.CheckAxioms
DkMath
```

Run:

```text
git diff --check
```

## Restrictions

Do not:

- alter any polynomial formula;
- alter any collision point;
- alter Jacobian or determinant proofs;
- recompute any completed certificate;
- introduce a new mathematical theorem beyond direct presentation aliases;
- use `sorry`;
- introduce axioms;
- use `native_decide`;
- begin higher-dimensional padding;
- begin PrincipalPartCompletion;
- create or upload a video;
- submit to Devpost;
- open or merge a pull request;
- guess provenance metadata.

## Report

Report:

1. files created and modified;
2. exact Demo theorem names;
3. confirmation that every Demo theorem is a direct alias/reuse;
4. aggregator change;
5. exact axiom output for `jacobianDemoCertificateC`;
6. README sections updated;
7. DEMO_CONTRACT timing and theorem flow;
8. provenance sources found and any explicitly missing field;
9. roadmap completion status;
10. public `#check` results;
11. build results and warnings;
12. `git diff --check` result;
13. confirmation that no later mathematical work was started.

Stop after JAC-011 and wait for final review.
