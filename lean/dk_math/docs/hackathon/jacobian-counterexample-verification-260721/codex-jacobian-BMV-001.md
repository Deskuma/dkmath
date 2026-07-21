# Instructions

## BMV-001

```txt
BMV-001 — Breaking Math Verification Architecture Reconnaissance

Repository:
  Deskuma/dkmath

Branch:
  hackathon/breaking-math-jacobian-counterexample

Base:
  develop

This is a read-only reconnaissance checkpoint.

Do not modify source files.
Do not create commits.
Do not push.
Do not create a pull request.
Do not add JAC-012.

IMPORTANT:
Do not open, search, grep, summarize, or inspect any large raw conversation,
Codex session, or ALL AGENT LOG dump under logs.

Background:

JAC-001 through JAC-011 are complete and merged into develop.

The Jacobian project already provides:

- explicit polynomial definitions;
- exact determinant certificates;
- explicit collision witnesses;
- non-injectivity and no-left-inverse theorems;
- normalized certificates;
- reusable BookOfMagic UniqueGap / GapCrystal APIs;
- finite-difference GN bridges;
- dedicated axiom audit;
- Demo aliases;
- README, provenance, and demo-contract documents.

The next project phase is not another Jacobian checkpoint.

The goal is to determine which parts of this workflow can become a reusable
DkMath Breaking Math Verification framework for rapidly verifying newly
reported mathematical results.

Tasks:

1. Inspect the completed Jacobian implementation.

Focus on:

  DkMath/Hackathon/JacobianCounterexample3/
  DkMath/BookOfMagic/
  the Jacobian axiom audit
  the Jacobian documentation directory
  the public aggregators

Identify the exact dependency chain from raw formulas to final public demo
certificate.

2. Extract the workflow layers.

Classify every important definition and theorem into:

  A. mathematical object definition
  B. local symbolic identity
  C. finite witness certificate
  D. global property refutation
  E. normalization / transport
  F. reusable abstract API
  G. trust / axiom audit
  H. provenance and scope documentation
  I. public Demo surface

3. Search for existing reusable structures.

Before proposing new abstractions, inspect DkMath for existing APIs related to:

  certificate
  counterexample
  witness
  finite verification
  injectivity / left inverse
  UniqueGap / GapFiber / GapCrystal
  theorem bundles
  axiom auditing
  provenance or verification contracts

Avoid duplicating an existing abstraction.

4. Determine the minimal reusable framework.

Evaluate whether a general framework should contain structures such as:

  BreakingMathClaim
  FiniteCertificate
  VerificationBundle
  RefutationCertificate
  ProvenanceRecord
  TrustAudit

These names are only candidates.

Do not assume all of them are needed.

Prefer the smallest abstraction that can support at least:

  - an explicit collision counterexample;
  - a finite arithmetic obstruction;
  - a concrete identity verification;
  - a future externally reported mathematical result.

5. Determine what must remain domain-specific.

Explicitly separate:

  reusable framework material

from:

  Jacobian-specific polynomial algebra
  Jacobian determinant machinery
  Point3Q / Point3C witnesses
  normalized Jacobian details
  BookOfMagic interpretation

Do not force domain-specific mathematics into a universal structure.

6. Propose module placement.

Compare at least these possibilities:

  DkMath/BreakingMath/
  DkMath/Verification/
  DkMath/Research/Verification/
  DkMath/Hackathon/BreakingMath/

Recommend one canonical home and explain the dependency direction.

The reusable framework must not import the Jacobian implementation.

7. Propose the next implementation checkpoints.

Produce a short roadmap beginning with BMV-002.

Each checkpoint must have:

  - one primary goal;
  - exact candidate file paths;
  - exact candidate definitions or theorem shapes;
  - explicit non-goals;
  - expected implementation difficulty;
  - estimated Codex credit cost category:
      low / medium / high.

Keep the first implementation checkpoint small enough to be completed and
reviewed independently.

8. Report one of three outcomes.

Outcome A:
  A clear reusable framework can be extracted immediately.

Outcome B:
  Some reuse is clear, but one more domain example is needed before abstraction.

Outcome C:
  The Jacobian pipeline is too domain-specific; retain only documentation and
  audit conventions for now.

Return a Markdown report titled:

  BMV-001 Breaking Math Verification Architecture Reconnaissance

Required sections:

  Conclusion
  Current Jacobian Verification Pipeline
  Existing Reusable APIs
  Reusable vs Domain-Specific Boundary
  Minimal Framework Proposal
  Module Placement
  Dependency Graph
  BMV-002 and Later Roadmap
  Credit Cost Estimate
  Outcome

Stop after the report.
```
