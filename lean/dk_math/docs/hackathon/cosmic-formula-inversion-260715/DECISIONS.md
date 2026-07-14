# Decisions

## DkMath — Cosmic Formula Inversion

This document records binding architectural, mathematical, workflow, visualization, and submission decisions for the hackathon project.

Its purposes are:

- to prevent repeated reconsideration of already-settled questions;
- to keep Codex sessions aligned;
- to make later changes explicit and reviewable;
- to preserve the reasoning behind the project structure;
- to distinguish accepted decisions from open questions.

When a later document conflicts with an accepted decision here, the accepted decision governs unless a newer decision explicitly supersedes it.

---

## 1. Decision Status Vocabulary

Each decision has one status.

```text
ACCEPTED:
  currently binding

PROPOSED:
  under consideration but not yet binding

DEFERRED:
  intentionally postponed

REJECTED:
  considered and not adopted

SUPERSEDED:
  replaced by a later decision
```

Accepted decisions may be changed only through a new decision record.

Existing decision identifiers must never be reused.

---

## 2. Decision Record Format

Every decision should follow this structure.

```text
Identifier
Title
Status
Date
Context
Decision
Rationale
Consequences
Affected files
Supersedes
Superseded by
```

Dates use:

```text
YYYY-MM-DD
```

---

## ADR-001 — Project Identity

### Status

```text
ACCEPTED
```

### Date

```text
2026-07-15
```

### Context

The hackathon project requires one stable public identity across:

- repository documentation;
- Lean modules;
- Manim scenes;
- demo video;
- submission materials.

### Decision

The project name is:

```text
DkMath — Cosmic Formula Inversion
```

The project is described as:

```text
a verifiable AI-assisted mathematical research workflow
```

### Rationale

The name connects:

- the existing DkMath library;
- the Cosmic Formula;
- the forward and inverse projection program;
- the formal-verification workflow.

### Consequences

All public documents should use the same project name.

### Affected Files

```text
README.md
PROJECT.md
ROADMAP.md
ARCHITECTURE.md
MATHEMATICAL_CONTRACT.md
VISUAL_STORYBOARD.md
DEMO_CONTRACT.md
submission materials
```

### Supersedes

```text
none
```

---

## ADR-002 — Repository and Branch

### Status

```text
ACCEPTED
```

### Date

```text
2026-07-15
```

### Context

The hackathon work must remain isolated from unrelated active DkMath research.

### Decision

Use:

```text
repository:
  Deskuma/dkmath

base branch:
  nightly

working branch:
  hackathon/cosmic-formula-inversion
```

### Rationale

The `nightly` branch contains the current DkMath development state.

A separate hackathon branch protects the existing research line and allows a stable submission history.

### Consequences

All hackathon commits, reports, Lean modules, and visual work belong on the working branch unless explicitly stated otherwise.

### Affected Files

```text
entire hackathon branch
```

---

## ADR-003 — Primary Submission Category

### Status

```text
ACCEPTED
```

### Date

```text
2026-07-15
```

### Context

The project combines mathematics, formal verification, agent execution, and visualization.

### Decision

The primary project category is:

```text
Developer Tools
```

### Rationale

The principal innovation is the workflow:

```text
mathematical dialogue
→ repository-aware agent implementation
→ Lean verification
→ visual explanation
```

The project is not primarily a standalone educational animation or a new mathematical theorem submission.

### Consequences

Submission language should emphasize:

- repository-aware Codex behavior;
- theorem contracts;
- build-gated claims;
- reproducible checkpoints;
- formal verification.

---

## ADR-004 — Public Documentation Language

### Status

```text
ACCEPTED
```

### Date

```text
2026-07-15
```

### Context

The documentation may become part of the public hackathon submission.

### Decision

All primary project documents are written in English.

### Rationale

English maximizes accessibility for:

- hackathon judges;
- international developers;
- Lean users;
- public repository readers.

### Consequences

The following documents should remain English-first:

```text
README.md
PROJECT.md
MATHEMATICAL_CONTRACT.md
ROADMAP.md
ARCHITECTURE.md
GLOSSARY.md
DECISIONS.md
RISKS_AND_STOPPING_RULES.md
EXISTING_DKMATH_MAP.md
VISUAL_STORYBOARD.md
DEMO_CONTRACT.md
CHECKPOINTS.md
CODEX_PLAN.md
```

Historical Japanese discussion files may remain unchanged.

---

## ADR-005 — Main Mathematical Path

### Status

```text
ACCEPTED
```

### Date

```text
2026-07-15
```

### Context

The project requires one short mathematical story that can be implemented, verified, and visualized.

### Decision

The main path is:

```text
finite prime universe
→ known-prime product
→ coprime offset
→ Cosmic Formula completion
→ completed boundary
→ fresh prime factors
→ bounded projection
→ inverse reconstruction
```

The minimum viable formal path ends after the fresh-prime and Cosmic Formula stages.

### Rationale

This route is:

- finite;
- exact;
- visually understandable;
- connected to existing DkMath theory;
- extensible toward inverse projection.

### Consequences

Codex must not replace the path with an unrelated number-theory example.

---

## ADR-006 — Fixed Demonstration Data

### Status

```text
ACCEPTED
```

### Date

```text
2026-07-15
```

### Context

The Lean code, visual animation, documentation, and narration must use the same example.

### Decision

The fixed public demo data is:

$$
S=\{2,3,5,7\}
$$

$$
P=210
$$

$$
u=11
$$

$$
P+u=221
$$

$$
221=13\cdot17
$$

The Cosmic Formula values are:

$$
210\cdot232=48720
$$

$$
11^2=121
$$

$$
221^2=48841
$$

$$
48720+121=48841
$$

### Rationale

The example has:

- a small finite prime set;
- a nontrivial offset;
- two distinct fresh prime factors;
- a visually meaningful Gap;
- arithmetic suitable for Lean and animation.

### Consequences

The fixed example must remain synchronized across all layers.

Changing it requires a new decision record.

---

## ADR-007 — Fresh Prime Terminology

### Status

```text
ACCEPTED
```

### Date

```text
2026-07-15
```

### Context

The project needs a term for a prime divisor outside the original finite prime set.

### Decision

Use:

```text
fresh prime factor
```

Do not use:

```text
primitive prime divisor
```

unless sequence-relative earlier-stage exclusion hypotheses are formally present.

### Rationale

Freshness is relative to the finite set `S`.

Primitiveness is normally relative to an ordered sequence or family.

### Consequences

Public theorem names, comments, documentation, and narration should prefer `fresh`.

---

## ADR-008 — Core Finite Prime Theorem

### Status

```text
ACCEPTED
```

### Date

```text
2026-07-15
```

### Context

The first formal theorem must be precise and finite.

### Decision

The core theorem is:

$$
P=\prod_{p\in S}p
$$

$$
\gcd(P,u)=1
$$

$$
q\mid P+u
$$

$$
\operatorname{Prime}(q)
$$

implies:

$$
q\notin S
$$

The preferred public existence theorem is:

$$
1<P+u\Longrightarrow\exists q,\ \operatorname{Prime}(q)\land q\mid P+u\land q\notin S
$$

### Rationale

This theorem directly supports the demo and separates:

- supplied-divisor exclusion;
- prime-divisor existence.

### Consequences

The Lean implementation should preserve these theorem layers.

---

## ADR-009 — General Offset Instead of Only `u = 1`

### Status

```text
ACCEPTED
```

### Date

```text
2026-07-15
```

### Context

The classical Euclid-style construction commonly uses `P + 1`.

### Decision

Formalize the general coprime offset `u`.

Use `u = 1` only as a special case.

### Rationale

General `u`:

- exposes the essential coprimality condition;
- supports the fixed demo `u = 11`;
- gives a visible square Gap `u²`;
- connects to the wider Cosmic Formula program.

### Consequences

The main theorem must not be reduced to `P + 1` unless a serious implementation obstruction is found and recorded.

---

## ADR-010 — Cosmic Formula Contract

### Status

```text
ACCEPTED
```

### Date

```text
2026-07-15
```

### Context

The arithmetic theorem and visual geometry need one exact shared identity.

### Decision

Use:

$$
P(P+2u)+u^2=(P+u)^2
$$

with the interpretation:

```text
Body:
  P(P + 2u)

Gap:
  u²

Big:
  (P + u)²
```

### Rationale

The identity is exact, elementary, visualizable, and already aligned with DkMath terminology.

### Consequences

No parallel Cosmic Formula hierarchy should be created in the hackathon layer.

---

## ADR-011 — Arithmetic and Geometry Remain Distinct

### Status

```text
ACCEPTED
```

### Date

```text
2026-07-15
```

### Context

The project connects an arithmetic factor theorem with a square-completion visualization.

### Decision

The formal connection is the shared boundary value:

$$
P+u
$$

The project may state:

```text
the completed boundary carries prime factors outside the original finite prime set
```

The project must not state:

```text
the geometry creates the prime factors
```

### Rationale

The arithmetic theorem follows from divisibility and coprimality.

The square identity provides structural visualization but does not cause primality.

### Consequences

Narration and Manim scenes must preserve this boundary.

---

## ADR-012 — Thin Hackathon Facade

### Status

```text
ACCEPTED
```

### Date

```text
2026-07-15
```

### Context

DkMath is already a large formal mathematics library.

### Decision

The hackathon Lean layer is a thin facade over existing DkMath and Mathlib APIs.

Initial modules:

```text
DkMath/Hackathon/FinitePrimeEscape.lean
DkMath/Hackathon/CosmicCompletion.lean
DkMath/Hackathon/Demo.lean
```

### Rationale

The goal is to expose a clear public route through DkMath, not to rebuild the library.

### Consequences

New declarations should be classified as:

```text
direct reuse
thin wrapper
specialized corollary
bridge lemma
genuinely missing theorem
demo-only fact
```

---

## ADR-013 — No Reverse Dependency into Core DkMath

### Status

```text
ACCEPTED
```

### Date

```text
2026-07-15
```

### Context

The hackathon facade is downstream of the research library.

### Decision

Core DkMath modules must never import:

```text
DkMath.Hackathon.*
```

### Rationale

The hackathon layer is a presentation and integration surface, not a foundational dependency.

### Consequences

Any implementation requiring reverse dependency must stop and report an architecture obstruction.

---

## ADR-014 — Existing API Audit Before Lean Implementation

### Status

```text
ACCEPTED
```

### Date

```text
2026-07-15
```

### Context

DkMath likely already contains relevant definitions and theorems.

### Decision

The first Codex session is repository-audit-only.

Codex must inspect reusable APIs before editing Lean source.

### Rationale

This reduces:

- duplicated definitions;
- unnecessary proof work;
- import expansion;
- credit consumption;
- semantic inconsistency.

### Consequences

The first Codex report must identify:

```text
directly reusable declarations
thin-wrapper candidates
missing lemmas
dependency risks
smallest viable implementation surface
```

---

## ADR-015 — Stable Codex Reading Order

### Status

```text
ACCEPTED
```

### Date

```text
2026-07-15
```

### Context

Codex sessions need a stable project interpretation.

### Decision

Codex reads documents in this order:

```text
1. README.md
2. PROJECT.md
3. MATHEMATICAL_CONTRACT.md
4. ROADMAP.md
5. ARCHITECTURE.md
6. GLOSSARY.md
7. DECISIONS.md
8. RISKS_AND_STOPPING_RULES.md
9. EXISTING_DKMATH_MAP.md
10. VISUAL_STORYBOARD.md
11. DEMO_CONTRACT.md
12. CHECKPOINTS.md
13. CODEX_PLAN.md
14. current checkpoint instruction
```

### Rationale

The order moves from:

```text
meaning
→ mathematical boundary
→ architecture
→ terminology
→ current repository state
→ current task
```

### Consequences

The order should remain stable unless a later decision changes it.

---

## ADR-016 — Tracking Anchor Files

### Status

```text
ACCEPTED
```

### Date

```text
2026-07-15
```

### Context

UUID-named empty files connect repository checkpoints to originating research conversations.

### Decision

Preserve UUID-named empty files as tracking anchors.

Example:

```text
6a54173a-e5f8-83ee-9983-6932a7be858c
```

Rules:

```text
do not delete
do not rename
do not add content
do not repeatedly inspect after confirming emptiness
```

### Rationale

The filename is the metadata.

The empty content minimizes token consumption and avoids unnecessary processing.

### Consequences

Codex must treat these files as intentional historical infrastructure.

---

## ADR-017 — Checkpoint-Based Codex Execution

### Status

```text
ACCEPTED
```

### Date

```text
2026-07-15
```

### Context

Unbounded Codex sessions consume credits and encourage scope drift.

### Decision

Every Codex implementation session must be checkpoint-based.

Each checkpoint requires:

```text
one primary goal
bounded file permissions
required theorem surface
verification gates
stopping conditions
report destination
```

### Rationale

This reproduces the successful DkMath Collatz review workflow while protecting the hackathon scope.

### Consequences

Codex must not automatically continue into the next phase.

---

## ADR-018 — Stop at the First Genuine Obstruction

### Status

```text
ACCEPTED
```

### Date

```text
2026-07-15
```

### Context

Some tasks may expose new mathematical or architecture requirements.

### Decision

Codex must stop at the first genuine obstruction listed in the current instruction.

It must report:

```text
the smallest missing theorem
the incompatible representation
the dependency problem
the first missing invariant
```

### Rationale

A precise obstruction is a useful research result.

Repeated speculative reformulation wastes credits and obscures the actual boundary.

### Consequences

A stopped checkpoint is not automatically a failed checkpoint.

---

## ADR-019 — Lean Is the Formal Verification Gate

### Status

```text
ACCEPTED
```

### Date

```text
2026-07-15
```

### Context

The project combines human interpretation, Codex implementation, and formal proof.

### Decision

A formal claim enters the public verified surface only after Lean accepts the relevant module.

### Rationale

Codex output, prose, numerical examples, and visual scenes are not substitutes for type checking.

### Consequences

Required gates include:

```text
focused module build
relevant aggregate build
no-sorry check
git diff --check
theorem-contract review
```

---

## ADR-020 — User Checkpoints Are Treated as Build-Verified

### Status

```text
ACCEPTED
```

### Date

```text
2026-07-15
```

### Context

The project review workflow receives checkpoints after the user has already run the stated Lean builds.

### Decision

When a checkpoint report states that the build gates passed, review treats those build results as established.

### Rationale

Review effort should focus on:

- theorem meaning;
- architecture;
- API quality;
- true mathematical progress;
- next obstruction.

### Consequences

Reviews should not repeatedly spend effort on unrelated existing warnings or already-passed build gates.

---

## ADR-021 — Minimum Viable Project Before Stretch Research

### Status

```text
ACCEPTED
```

### Date

```text
2026-07-15
```

### Context

The inverse-projection and DkReal program may expand into deeper research.

### Decision

Secure the MVP before stretch work.

The MVP includes:

```text
finite prime escape
Cosmic Formula completion
concrete Lean demo
Manim visualization
recorded Codex process
submission package
```

### Rationale

A complete verified submission must survive even if later research stalls.

### Consequences

After `Demo.lean` builds, preserve a known-good commit before beginning projection or DkReal work.

---

## ADR-022 — Projection Is a Preferred Milestone

### Status

```text
ACCEPTED
```

### Date

```text
2026-07-15
```

### Context

Cosmic Formula inversion is broader than the initial finite theorem.

### Decision

Bounded projection and exact inverse are preferred milestones, not MVP requirements.

### Rationale

They strengthen the project’s research narrative but must not endanger the required submission.

### Consequences

Projection work starts only after the core demo is secure.

---

## ADR-023 — Projection Convention

### Status

```text
DEFERRED
```

### Date

```text
2026-07-15
```

### Context

Two natural candidate projections exist.

Unsigned:

$$
\pi(P,u)=\frac{P}{P+u}
$$

Signed:

$$
\Pi(P,u)=-\frac{P}{P+u}
$$

### Decision

Do not choose the primary public convention until after the repository audit.

### Rationale

The choice should account for:

- existing DkMath projection APIs;
- DkReal interval conventions;
- inverse simplicity;
- visual meaning;
- coercion cost.

### Consequences

Codex must not implement both competing conventions simultaneously.

A later decision must select one.

---

## ADR-024 — Rational Domain First for Projection

### Status

```text
ACCEPTED
```

### Date

```text
2026-07-15
```

### Context

Projection and inverse formulas are exact rational identities.

### Decision

Begin projection formalization over `ℚ` unless existing DkMath APIs strongly require `ℝ`.

### Rationale

Rational arithmetic provides:

- exact values;
- simpler computation;
- easier demo verification;
- reduced analytic overhead.

### Consequences

Real or DkReal lifting occurs only after the rational theorem surface is stable.

---

## ADR-025 — DkReal Is a Stretch Milestone

### Status

```text
ACCEPTED
```

### Date

```text
2026-07-15
```

### Context

DkReal reconstruction may require several missing interval bridges.

### Decision

Treat DkReal nested-interval reconstruction as stretch work.

### Rationale

The DkReal phase is valuable but may exceed the hackathon implementation budget.

### Consequences

If the first genuine DkReal bridge is missing, stop, report it, and return to the secured MVP.

---

## ADR-026 — Width Less Than One Is the Reconstruction Criterion

### Status

```text
ACCEPTED
```

### Date

```text
2026-07-15
```

### Context

Inverse projection may reconstruct a macro-scale interval rather than an exact value.

### Decision

Use the finite uniqueness criterion:

$$
\operatorname{width}(I)<1
$$

to prove that an interval contains at most one integer candidate.

### Rationale

This is exact, finite, and compatible with nested-interval reconstruction.

### Consequences

Existence and uniqueness remain separate theorem obligations.

The project must not infer exactly one candidate from width alone.

---

## ADR-027 — Manim Is the Visual Layer

### Status

```text
ACCEPTED
```

### Date

```text
2026-07-15
```

### Context

The mathematical path requires an accessible visual explanation.

### Decision

Use Manim for the primary animation.

### Rationale

Manim supports:

- precise equation transitions;
- geometric square completion;
- factor highlighting;
- theorem overlays;
- reproducible rendering.

### Consequences

The visual implementation must follow the fixed mathematical contract.

---

## ADR-028 — No Formal Euclidean Dissection for the MVP

### Status

```text
ACCEPTED
```

### Date

```text
2026-07-15
```

### Context

The square-completion scene can be represented as moving planar pieces.

### Decision

The MVP formalizes the arithmetic area identity only.

It does not require a set-theoretic Euclidean dissection theorem.

### Rationale

Formal polygonal geometry would consume substantial implementation effort without improving the main verified claim.

### Consequences

Manim may visualize rearrangement.

Lean proves:

$$
P(P+2u)+u^2=(P+u)^2
$$

and does not need to prove planar congruence.

---

## ADR-029 — Fixed Visual Story

### Status

```text
ACCEPTED
```

### Date

```text
2026-07-15
```

### Context

The demo must communicate the theorem in under approximately one minute.

### Decision

The primary scene sequence is:

```text
finite primes {2, 3, 5, 7}
→ product P = 210
→ Body P(P + 2u)
→ Gap u²
→ completed square (P + u)²
→ boundary 221
→ factorization 13 × 17
→ fresh factors highlighted
→ Lean verification
```

### Rationale

The sequence preserves one continuous mathematical story.

### Consequences

Prime spirals, aperiodic tilings, circular sectors, and unrelated visual experiments remain outside the MVP scene.

---

## ADR-030 — Visual Colors Have Stable Semantics

### Status

```text
ACCEPTED
```

### Date

```text
2026-07-15
```

### Context

The animation uses multiple mathematical components.

### Decision

Assign stable visual semantics to:

```text
known-prime components
Body
Gap
Big boundary
fresh prime factors
Lean verification
```

Exact colors are selected in `VISUAL_STORYBOARD.md`.

### Rationale

Stable semantics reduce cognitive load and prevent scene-to-scene ambiguity.

### Consequences

Once the visual palette is fixed, it should remain stable across the video and screenshots.

---

## ADR-031 — Collatz Footage Is Supporting Evidence

### Status

```text
ACCEPTED
```

### Date

```text
2026-07-15
```

### Context

A substantial Codex implementation session from the DkMath Collatz branch has been recorded with OBS.

### Decision

The Collatz cp-320 footage may appear briefly as evidence of agent capability.

It is not the main theorem of the hackathon project.

### Rationale

The footage demonstrates:

```text
large-repository navigation
proof repair
substantial Lean implementation
build verification
genuine-obstruction isolation
```

### Consequences

The submission must not imply that the Collatz conjecture was solved.

---

## ADR-032 — No Open-Problem Claim

### Status

```text
ACCEPTED
```

### Date

```text
2026-07-15
```

### Context

DkMath contains research related to major open problems.

### Decision

The hackathon submission does not claim to solve:

```text
Collatz
RH
ABC
FLT
Erdős open problems
any other currently open conjecture
```

### Rationale

The project demonstrates a verified workflow and a finite theorem path.

### Consequences

Open-problem references may appear only as background or supporting footage with explicit limitation language.

---

## ADR-033 — Documentation Is Part of the Deliverable

### Status

```text
ACCEPTED
```

### Date

```text
2026-07-15
```

### Context

The project’s value includes the traceable path from idea to formal proof.

### Decision

Project documentation, checkpoint reports, decisions, and stopping rules are part of the public deliverable.

### Rationale

They show:

- how Codex was constrained;
- what was reused;
- what was proved;
- where the agent stopped;
- how formal and visual layers remained aligned.

### Consequences

Historical reports must not be deleted merely because they are not source code.

---

## ADR-034 — Historical Records Are Not Rewritten

### Status

```text
ACCEPTED
```

### Date

```text
2026-07-15
```

### Context

Earlier plans and reports may later be corrected.

### Decision

Preserve historical documents in their original state.

Record corrections in later documents or reports.

### Rationale

The development trace is part of the research record.

### Consequences

Do not rewrite old reports to make the process appear cleaner in retrospect.

---

## ADR-035 — Report and Review Are Separate

### Status

```text
ACCEPTED
```

### Date

```text
2026-07-15
```

### Context

Codex produces implementation reports, while Wise Wolf performs mathematical and architectural review.

### Decision

Maintain separate artifacts:

```text
Codex report:
  factual implementation record

Wise Wolf review:
  mathematical and structural evaluation
```

### Rationale

The separation prevents implementation output from self-certifying its broader meaning.

### Consequences

A report may state build facts.

The review determines acceptance and next direction.

---

## ADR-036 — Public Theorem Names Become Stable After Demo Completion

### Status

```text
ACCEPTED
```

### Date

```text
2026-07-15
```

### Context

Theorem names may appear in:

- screenshots;
- Manim overlays;
- narration;
- README excerpts;
- video recordings.

### Decision

Freeze public theorem names after the concrete demo checkpoint is accepted.

### Rationale

Late renaming causes unnecessary presentation churn.

### Consequences

Later work should add theorems rather than casually rename the stable demo surface.

---

## ADR-037 — Credits Are a Managed Project Resource

### Status

```text
ACCEPTED
```

### Date

```text
2026-07-15
```

### Context

Hackathon Codex credits are finite.

### Decision

Reserve Codex primarily for:

```text
repository audit
Lean implementation
proof repair
Manim source implementation
integration
```

Use human–Wise Wolf work for:

```text
planning
documentation
review
storyboarding
submission prose
```

### Rationale

This allocation maximizes verified implementation per credit.

### Consequences

Each Codex report records:

```text
starting credits
ending credits
credits consumed
elapsed time
model
reasoning level
```

---

## ADR-038 — Stable Context Before Current Instruction

### Status

```text
ACCEPTED
```

### Date

```text
2026-07-15
```

### Context

Codex should receive the same project interpretation before each major task.

### Decision

Use:

```text
stable documentation prefix
+
current repository state
+
current checkpoint instruction
```

### Rationale

This reduces:

- repeated interpretation;
- terminology drift;
- duplicate exploration;
- scope expansion.

### Consequences

Current checkpoint instructions should not restate the entire project unnecessarily.

---

## ADR-039 — First Codex Session Is Audit-Only

### Status

```text
ACCEPTED
```

### Date

```text
2026-07-15
```

### Context

The documentation and Lean scaffold are prepared, but the existing DkMath reuse map is not yet known.

### Decision

The first Codex session must:

```text
read the project documents
inspect the repository
classify reusable APIs
propose the smallest implementation surface
write an audit report
stop
```

It must not edit Lean source.

### Rationale

The implementation instruction should be based on actual repository knowledge.

### Consequences

`report-hack-001.md` becomes the basis for the first implementation checkpoint.

---

## ADR-040 — Lean Module Responsibilities

### Status

```text
ACCEPTED
```

### Date

```text
2026-07-15
```

### Context

The scaffold contains three initial modules.

### Decision

Responsibilities are:

```text
FinitePrimeEscape.lean:
  finite-prime product
  coprime offset
  fresh-prime theorem

CosmicCompletion.lean:
  Body / Gap / Big completion
  existing Cosmic Formula bridge

Demo.lean:
  fixed numerical example
  compact public theorem surface
```

### Rationale

This separation keeps arithmetic, algebraic interpretation, and concrete presentation distinct.

### Consequences

General definitions must not be placed in `Demo.lean`.

---

## ADR-041 — Optional Modules Are Created Only When Their Phase Begins

### Status

```text
ACCEPTED
```

### Date

```text
2026-07-15
```

### Context

Projection and DkReal modules may be needed later.

### Decision

Do not create speculative empty modules such as:

```text
Projection.lean
InverseProjection.lean
DkRealReconstruction.lean
```

until the corresponding phase begins.

### Rationale

Premature files create false architecture commitments and extra audit surface.

### Consequences

Optional module creation requires a checkpoint and recorded decision.

---

## ADR-042 — No Automatic Export Through Top-Level `DkMath`

### Status

```text
DEFERRED
```

### Date

```text
2026-07-15
```

### Context

The hackathon facade may eventually be exported through a top-level aggregate.

### Decision

Do not add the hackathon modules to the top-level `DkMath` import surface automatically.

### Rationale

The public submission may only need:

```text
DkMath.Hackathon.Demo
```

A top-level export should be justified by actual usage.

### Consequences

The export decision is revisited after the demo module is complete.

---

## ADR-043 — Aggregate Hackathon Module

### Status

```text
DEFERRED
```

### Date

```text
2026-07-15
```

### Context

An aggregate module may simplify builds and imports.

### Decision

Consider later:

```text
DkMath/Hackathon.lean
```

Do not create it during the initial audit.

### Rationale

Its usefulness depends on the final number of hackathon modules.

### Consequences

A later checkpoint may create it after the module graph stabilizes.

---

## ADR-044 — Visual Source Directory

### Status

```text
DEFERRED
```

### Date

```text
2026-07-15
```

### Context

The final Manim source location has not yet been selected.

### Candidate Locations

```text
python/hackathon/cosmic_formula_inversion/
```

or:

```text
docs/hackathon/cosmic-formula-inversion-260715/manim/
```

### Decision

Choose the final location during the visual architecture checkpoint.

### Rationale

The correct location should match existing repository conventions.

### Consequences

Do not create multiple visual roots.

---

## ADR-045 — Manim Data Uses One Configuration Source

### Status

```text
ACCEPTED
```

### Date

```text
2026-07-15
```

### Context

Demo constants may otherwise be duplicated inconsistently across scenes.

### Decision

Use one shared Manim data configuration for:

```text
primes
P
u
boundary
fresh factors
Body
Gap
Big
```

### Rationale

One source of visual constants reduces mismatch risk.

### Consequences

All scenes should consume the same configuration object or module.

---

## ADR-046 — No Automatic Lean-to-Manim Extraction Required for MVP

### Status

```text
ACCEPTED
```

### Date

```text
2026-07-15
```

### Context

The Lean and Manim layers use the same values.

### Decision

The MVP does not require automated extraction of Lean constants into Python.

Manual synchronization and integration checks are sufficient.

### Rationale

Automatic cross-language extraction would add complexity without materially improving the primary demonstration.

### Consequences

The integration phase must explicitly verify that Lean and Manim values match.

---

## ADR-047 — Build Commands Are Part of the Public Reproduction Path

### Status

```text
ACCEPTED
```

### Date

```text
2026-07-15
```

### Context

The project claims formal verifiability.

### Decision

Document exact commands for:

```text
focused Lean build
demo build
optional aggregate build
Manim render
```

### Rationale

A reproducible command path is necessary for a credible developer-tool submission.

### Consequences

The final README and submission package must include tested commands.

---

## ADR-048 — Numerical Proofs May Use Automation

### Status

```text
ACCEPTED
```

### Date

```text
2026-07-15
```

### Context

The demo contains explicit arithmetic equalities and membership facts.

### Decision

Use tactics such as:

```text
norm_num
decide
native_decide
ring
ring_nf
```

where appropriate for concrete or algebraic facts.

### Rationale

The project should not manually expand routine arithmetic.

### Consequences

General structural theorems must still reuse the intended general API rather than being replaced by numerical automation.

---

## ADR-049 — Classical Reasoning Is Permitted for General Existence

### Status

```text
ACCEPTED
```

### Date

```text
2026-07-15
```

### Context

Prime-divisor existence may use classical choice internally.

### Decision

Classical reasoning is acceptable when:

```text
computable witness extraction is not claimed
the theorem is proposition-valued
the use is documented
```

### Rationale

The hackathon theorem requires existence, not an executable factorization algorithm.

### Consequences

The concrete example should still use explicit factors `13` and `17`.

---

## ADR-050 — No Cryptographic Claim

### Status

```text
ACCEPTED
```

### Date

```text
2026-07-15
```

### Context

Prime-based visual or Gap-based transformations may resemble encryption.

### Decision

Do not claim cryptographic security, encryption strength, or resistance to attack.

### Rationale

No security proof or threat model is part of the formal project.

### Consequences

Any future “Prime Gap Cipher” visualization must be described as a reversible encoding experiment unless formally strengthened.

---

## ADR-051 — No Aperiodic-Tiling Claim

### Status

```text
ACCEPTED
```

### Date

```text
2026-07-15
```

### Context

Earlier visual research considered recursive Gap placement and tiling analogies.

### Decision

Aperiodic tiling is outside the main hackathon theorem and visual path.

### Rationale

Nonperiodicity requires independent translation-symmetry and coverage proofs.

### Consequences

Do not include aperiodicity claims in the MVP narrative.

---

## ADR-052 — No New Infinitude-of-Primes Claim

### Status

```text
ACCEPTED
```

### Date

```text
2026-07-15
```

### Context

Finite prime escape resembles Euclid’s classical argument.

### Decision

Do not present the finite escape theorem as a new proof that infinitely many primes exist.

### Rationale

The mathematical core is classical.

The project contribution is the formal, architectural, visual, and agent workflow.

### Consequences

Submission wording must state this boundary explicitly.

---

## ADR-053 — Public Contribution Claim

### Status

```text
ACCEPTED
```

### Date

```text
2026-07-15
```

### Context

The core arithmetic theorem is elementary.

### Decision

The project contribution is framed as:

```text
a verifiable AI-assisted mathematical research workflow
built on a large Lean library
with a thin theorem facade
and a synchronized visual explanation
```

### Rationale

This accurately identifies the novel project value without overstating the mathematics.

### Consequences

The submission should emphasize process integration rather than theorem novelty.

---

## ADR-054 — Current Project State

### Status

```text
ACCEPTED
```

### Date

```text
2026-07-15
```

### Context

The branch scaffold and primary documentation are being prepared.

### Decision

Current phase:

```text
Phase 0 — project documentation and fixed context
```

Current completed items:

```text
working branch created
Lean scaffold created
documentation directory created
README drafted
PROJECT.md drafted
MATHEMATICAL_CONTRACT.md drafted
ROADMAP.md drafted
ARCHITECTURE.md drafted
GLOSSARY.md drafted
DECISIONS.md drafted
tracking anchor preserved
```

### Consequences

Lean theorem implementation must not begin until:

```text
remaining project documents are complete
first audit instruction is reviewed
repository audit is performed
audit report is reviewed
```

---

## 3. Open Decisions

The following questions remain unresolved.

```text
OPEN-001:
  signed or unsigned primary projection

OPEN-002:
  exact visual source directory

OPEN-003:
  whether to create DkMath/Hackathon.lean

OPEN-004:
  whether to export hackathon modules through top-level DkMath

OPEN-005:
  exact existing DkMath theorem used for finite prime escape

OPEN-006:
  exact existing DkMath Big / Body / Gap API used by CosmicCompletion

OPEN-007:
  whether FreshPrimeFactor already exists

OPEN-008:
  exact DkReal bridge surface

OPEN-009:
  final Manim color palette

OPEN-010:
  final theorem names after repository audit
```

Open decisions must not be silently resolved by Codex.

Codex may recommend a choice in its report.

---

## 4. Rejected Alternatives

### REJ-001 — Use Only `P + 1`

### Status

```text
REJECTED
```

### Reason

It hides the role of coprimality and produces a visually trivial unit Gap.

---

### REJ-002 — Begin with DkReal

### Status

```text
REJECTED
```

### Reason

The project first needs a secure discrete theorem and concrete demo.

---

### REJ-003 — Formalize Full Euclidean Dissection First

### Status

```text
REJECTED
```

### Reason

It adds high implementation cost without strengthening the core arithmetic theorem.

---

### REJ-004 — Make Collatz the Main Hackathon Theorem

### Status

```text
REJECTED
```

### Reason

The Collatz branch is currently at a deep active research boundary and would consume the entire hackathon budget.

---

### REJ-005 — Let Codex Design the Project Scope During Execution

### Status

```text
REJECTED
```

### Reason

Scope, theorem strength, and public meaning must be fixed before implementation.

---

### REJ-006 — Build a Separate Hackathon Mathematics Library

### Status

```text
REJECTED
```

### Reason

The project should expose existing DkMath, not duplicate it.

---

### REJ-007 — Implement Both Projection Conventions

### Status

```text
REJECTED
```

### Reason

Competing public conventions would create unnecessary proof and presentation complexity.

---

### REJ-008 — Delete Empty UUID Files

### Status

```text
REJECTED
```

### Reason

They are intentional conversation-tracking anchors whose filenames carry metadata.

---

## 5. Future Decision Template

Use the following template for new decisions.

````md
## ADR-XXX — Title

### Status

```text
PROPOSED
```

### Date

```text
YYYY-MM-DD
```

### Context

Describe the problem requiring a decision.

### Decision

State the selected action or rule.

### Rationale

Explain why this option is preferred.

### Consequences

List required changes, restrictions, or follow-up work.

### Affected Files

```text
file or module list
```

### Supersedes

```text
ADR-XXX or none
```

### Superseded By

```text
ADR-XXX or none
```
````

---

## 6. Change Procedure

To change an accepted decision:

```text
1. create a new ADR identifier;
2. describe the old decision;
3. explain the reason for change;
4. list affected Lean modules;
5. list affected documentation;
6. list affected Manim scenes;
7. state whether the change strengthens or weakens the project;
8. mark the old ADR as SUPERSEDED;
9. link both records.
```

Historical decision text should not be deleted.

---

## 7. Decision Summary

The binding project shape is:

```text
Project:
  DkMath — Cosmic Formula Inversion

Repository:
  Deskuma/dkmath

Branch:
  hackathon/cosmic-formula-inversion

Primary category:
  Developer Tools

Public language:
  English

Main theorem:
  finite prime escape under coprime offset

Core identity:
  P(P + 2u) + u² = (P + u)²

Fixed demo:
  S = {2, 3, 5, 7}
  P = 210
  u = 11
  P + u = 221
  fresh factors = 13 and 17

Formal architecture:
  existing DkMath
  → thin hackathon facade
  → concrete demo

Agent workflow:
  documentation
  → audit
  → bounded implementation
  → Lean verification
  → review

Visualization:
  Manim after theorem contract stabilization

Stretch direction:
  rational projection
  → exact inverse
  → optional DkReal reconstruction

Supporting evidence:
  recorded Collatz cp-320 Codex session
```

The project must remain a short verified route through a deep library, not an attempt to formalize every surrounding DkMath research idea during the hackathon.
