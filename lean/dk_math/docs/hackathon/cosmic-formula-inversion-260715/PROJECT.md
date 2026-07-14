# Project

## DkMath — Cosmic Formula Inversion

A verifiable AI-assisted mathematical research project for the OpenAI Build Week Hackathon.

---

## 1. Project Summary

DkMath — Cosmic Formula Inversion demonstrates a complete research workflow:

```text
human mathematical exploration
→ repository-aware AI investigation
→ Lean 4 formalization
→ machine verification
→ visual mathematical explanation
```

The project begins with a finite set of known prime factors, constructs a completed Cosmic Formula boundary, and proves that a prime divisor appearing on the new boundary lies outside the original finite prime set.

The first milestone is intentionally elementary and finite.

Its purpose is not to present an isolated prime-factor argument as a major mathematical discovery. Its purpose is to demonstrate how an AI agent can navigate a large formal mathematics library, identify reusable theory, implement only the missing bridge, and expose the result through both Lean and visual media.

---

## 2. Project Thesis

The central project thesis is:

> A mathematical AI system becomes significantly more useful when its reasoning is connected to a formal library, constrained by explicit theorem contracts, verified by Lean, and translated into a visual explanation that humans can inspect.

The workflow is designed so that no single layer stands alone.

```text
Dialogue:
  develops the mathematical interpretation.

Codex:
  investigates the repository and implements the formal bridge.

Lean:
  decides whether the formal claim is valid.

DkMath:
  supplies the existing mathematical structure and reusable theorem surface.

Manim:
  exposes the structure as motion, boundary, completion, and reconstruction.

Human review:
  controls scope, terminology, theorem strength, and project direction.
```

---

## 3. Main Research Theme

The project studies the relation between:

```text
finite arithmetic structure
boundary completion
new factor channels
bounded projection
inverse reconstruction
```

The initial theorem uses a finite prime universe.

Let `S` be a finite set of primes and let:

$$
P=\prod_{p\in S}p
$$

Choose an offset `u` such that:

$$
\gcd(P,u)=1
$$

Then every prime divisor `q` of `P + u` is outside `S`.

The same arithmetic transition is placed inside the Cosmic Formula identity:

$$
P(P+2u)+u^2=(P+u)^2
$$

The project interprets this as:

```text
Body:
  P(P + 2u)

Gap:
  u²

Big:
  (P + u)²

Completed boundary:
  P + u

Fresh prime channel:
  a prime divisor of P + u that is not in S
```

The later phases study how this completed boundary can be normalized into a bounded interval representation and reconstructed through inverse projection.

---

## 4. Initial Demonstration

The first demonstration uses one fixed numerical example across all project layers.

$$
S=\{2,3,5,7\}
$$

$$
P=2\cdot3\cdot5\cdot7=210
$$

$$
u=11
$$

Then:

$$
P+u=221=13\cdot17
$$

Both `13` and `17` are outside the original finite set.

The square completion is:

$$
210\cdot232+11^2=221^2
$$

or:

$$
48720+121=48841
$$

The same values must appear in:

```text
Lean theorem examples
Manim animation
submission video
project screenshots
documentation
final demo narrative
```

This common example is a project invariant.

No layer may silently replace it with a more convenient example without recording a project decision.

---

## 5. Project Objectives

### 5.1. Primary Objective

Build a verified and visually understandable demonstration of the following path:

```text
known finite prime set
→ known-prime product P
→ coprime offset u
→ completed boundary P + u
→ prime divisor outside the original set
→ formal Lean verification
```

### 5.2. Formalization Objective

Expose a thin Lean-facing API that reuses existing DkMath theory.

The hackathon modules should:

- reuse existing definitions and theorems;
- avoid parallel mathematical hierarchies;
- contain only the bridge required by the demo;
- provide a clean public theorem surface;
- compile without `sorry`;
- preserve the existing DkMath dependency structure.

### 5.3. Visualization Objective

Create a short Manim animation showing:

- construction of the finite known-prime universe;
- formation of `P`;
- the Body rectangle;
- the missing Gap square;
- completion into `(P + u)²`;
- exposure of the boundary value `P + u`;
- factorization into fresh prime channels;
- the corresponding Lean verification.

### 5.4. AI Workflow Objective

Demonstrate that Codex can:

- read a stable project specification;
- inspect an unfamiliar large Lean repository;
- locate reusable APIs;
- distinguish missing mathematics from missing wrappers;
- implement within explicit file boundaries;
- repair Lean failures;
- stop at a genuine obstruction;
- report exactly what changed.

### 5.5. Submission Objective

Produce a project that can be understood at three levels.

```text
General audience:
  sees a visual boundary-completion story.

Programmer:
  sees repository-aware AI implementation.

Formal mathematician:
  sees exact theorem statements and Lean verification.
```

---

## 6. Target Audience

The project addresses several overlapping audiences.

### Hackathon Judges

They should be able to understand:

- what the project demonstrates;
- why formal verification matters;
- what Codex contributed;
- what the visual layer contributes;
- how the workflow differs from ordinary code generation.

### Software Engineers

They should see:

- controlled AI-agent execution;
- repository audit before implementation;
- stable project context;
- explicit stopping rules;
- build-gated claims;
- reproducible checkpoint reports.

### Mathematicians and Lean Users

They should see:

- theorem contracts before code;
- disciplined reuse of existing APIs;
- separation between finite theorems and larger conjectural programs;
- exact limits of each formal result;
- a public facade over a large research library.

### General Viewers

They should see:

- a finite world built from known primes;
- a missing piece completing a square;
- a new boundary value;
- new factors appearing outside the original world;
- Lean confirming the claim.

---

## 7. Project Deliverables

### 7.1. Lean Deliverables

```text
DkMath/Hackathon/FinitePrimeEscape.lean
DkMath/Hackathon/CosmicCompletion.lean
DkMath/Hackathon/Demo.lean
```

Expected responsibilities:

```text
FinitePrimeEscape.lean:
  finite prime set
  product construction
  coprime offset
  fresh prime-factor theorem

CosmicCompletion.lean:
  square-completion identity
  Big / Body / Gap bridge
  reuse of existing Cosmic Formula APIs

Demo.lean:
  P = 210
  u = 11
  P + u = 221
  221 = 13 × 17
  public end-to-end theorem surface
```

### 7.2. Documentation Deliverables

```text
README.md
PROJECT.md
ROADMAP.md
MATHEMATICAL_CONTRACT.md
ARCHITECTURE.md
EXISTING_DKMATH_MAP.md
VISUAL_STORYBOARD.md
DEMO_CONTRACT.md
CODEX_PLAN.md
CHECKPOINTS.md
DECISIONS.md
GLOSSARY.md
RISKS_AND_STOPPING_RULES.md
```

### 7.3. Visual Deliverables

```text
Manim source
rendered demonstration video
still images or diagrams
optional interactive demo surface
```

### 7.4. Process Deliverables

```text
Codex checkpoint instructions
Codex execution recording
Lean build recording
checkpoint reports
credit-consumption ledger
final session identifiers
```

### 7.5. Submission Deliverables

```text
project description
public repository branch
demo video
setup instructions
verified theorem summary
AI workflow explanation
limitations and non-goals
```

---

## 8. Repository Structure

The working repository is:

```text
Deskuma/dkmath
```

The hackathon branch is:

```text
hackathon/cosmic-formula-inversion
```

The branch is based on:

```text
nightly
```

The hackathon work must remain isolated from active unrelated research branches.

The hackathon facade may import existing DkMath modules.

Existing DkMath core modules must not depend on the hackathon facade.

```text
existing DkMath theory
          ↓
DkMath.Hackathon facade
          ↓
demo and visualization
```

The reverse dependency is prohibited.

---

## 9. Development Model

The project follows a checkpoint-based development process.

Each checkpoint contains:

```text
Goal
Known facts
Files permitted to change
Required definitions
Required theorems
Existing APIs to inspect
Verification gates
Stopping conditions
Report destination
```

The standard workflow is:

```text
1. Human and Wise Wolf define the theorem contract.
2. Stable project documents are updated.
3. Codex reads the documents in the prescribed order.
4. Codex audits the repository before editing.
5. The audit result is reviewed.
6. A bounded implementation instruction is issued.
7. Codex implements until completion or a genuine obstruction.
8. Lean verifies the result.
9. Wise Wolf reviews mathematical meaning and API boundaries.
10. The next checkpoint is designed.
```

---

## 10. Roles

### D

Responsibilities:

- mathematical direction;
- project ownership;
- acceptance of theorem meaning;
- repository and branch decisions;
- recording Codex execution;
- visual and narrative judgment;
- final submission.

### Wise Wolf

Responsibilities:

- structural mathematical analysis;
- theorem-contract design;
- Codex instruction design;
- checkpoint review;
- distinction between proved facts and open structure;
- translation between DkMath terminology and standard mathematical language;
- submission narrative support.

### Codex

Responsibilities:

- repository inspection;
- API discovery;
- Lean implementation;
- local proof repair;
- build execution;
- exact obstruction reporting;
- checkpoint report generation.

Codex is not authorized to redefine project scope.

### Lean

Responsibilities:

- formal type checking;
- proof validation;
- rejection of invalid theorem implementations.

Lean is the final authority for formal claims inside the project.

### Manim

Responsibilities:

- visualizing the already-fixed mathematical contract;
- showing structure, motion, completion, and projection.

Manim does not establish mathematical truth.

---

## 11. Project Principles

### 11.1. Formal Claims Must Be Build-Gated

A mathematical statement is part of the verified project surface only when its Lean implementation builds.

Numerical examples, diagrams, and prose do not replace proof.

### 11.2. Audit Before Definition

Codex must search the existing DkMath library before creating:

- new structures;
- new predicates;
- new Big / Body / Gap definitions;
- new prime-factor terminology;
- new projection APIs.

### 11.3. Thin Facade Over Deep Library

The hackathon layer should expose a short path through DkMath.

It should not reproduce the entire research library.

### 11.4. One Story Across All Layers

The proof, animation, demo, and documentation must describe the same transition.

```text
finite known world
→ completion
→ new boundary
→ fresh factor
```

### 11.5. Exact Scope Boundaries

Every report must state:

- what is now proved;
- what is only visual interpretation;
- what remains open;
- what was deliberately excluded.

### 11.6. Stop at Genuine Obstructions

Codex must not consume time by repeatedly reformulating the same missing theorem.

Once the first genuine invariant or API obstruction is isolated, it must stop and report it.

### 11.7. Preserve Research History

Checkpoint reports, tracking-anchor files, and conversation-linked metadata are part of the research record.

They must not be deleted merely because they are not executable source files.

---

## 12. Codex Context Strategy

The project uses a stable documentation prefix before each major Codex task.

The prescribed reading order is maintained so that the project meaning remains stable across sessions.

```text
stable project documents
→ repository-specific audit
→ current checkpoint instruction
```

The purpose is to reduce:

- repeated interpretation;
- unnecessary repository exploration;
- terminology drift;
- accidental scope expansion;
- duplicated abstractions.

UUID-named empty files are intentional conversation-tracking anchors.

Their filenames are metadata.

Their empty contents do not require inspection.

---

## 13. Formal Milestones

### Milestone A — Repository Audit

Codex identifies:

- existing finite-prime APIs;
- finite-product APIs;
- coprimality lemmas;
- prime-divisor existence lemmas;
- Cosmic Formula identities;
- Big / Body / Gap structures;
- DkReal interval and projection candidates.

No Lean source is edited.

### Milestone B — Finite Prime Escape

Lean proves the general fresh-prime theorem.

Target meaning:

> A prime divisor of `P + u` cannot be one of the primes used to construct `P`, provided `P` and `u` are coprime.

### Milestone C — Cosmic Completion

Lean exposes:

$$
P(P+2u)+u^2=(P+u)^2
$$

through existing DkMath structure.

### Milestone D — Unified Demo

Lean proves the concrete `210`, `11`, `221`, `13`, `17` example.

### Milestone E — Inverse Projection

A normalized bounded projection is selected and formally connected to the arithmetic boundary.

### Milestone F — DkReal Reconstruction

Nested intervals or related DkReal machinery recover a unique macro-scale candidate.

### Milestone G — Visual Completion

Manim displays the theorem path without introducing unverified claims.

### Milestone H — Submission

The project is packaged, recorded, documented, and submitted.

---

## 14. Success Criteria

The minimum viable project succeeds when all of the following are true.

```text
1. The finite prime escape theorem is implemented in Lean.
2. The Cosmic Formula completion identity is connected to it.
3. The concrete example builds through a compact demo module.
4. The Manim animation follows the same mathematical contract.
5. Codex repository investigation and implementation are recorded.
6. The final report distinguishes theorem, interpretation, and future work.
7. A reviewer can reproduce the Lean build.
```

The stronger project succeeds when:

```text
1. A bounded inverse-projection layer is formalized.
2. DkReal reconstruction is included.
3. The visual demo shows forward projection and inverse recovery.
4. The final presentation connects finite prime escape to the broader DkMath program.
```

---

## 15. Quality Standards

### Lean Quality

- no `sorry` in new hackathon modules;
- no unnecessary axioms;
- no duplicated core definitions;
- minimal imports;
- stable theorem names;
- public comments explaining theorem meaning;
- full relevant build gates;
- `git diff --check` passing.

### Documentation Quality

- English throughout public project documents;
- explicit theorem assumptions;
- no unsupported novelty claims;
- stable terminology;
- links between roadmap, checkpoints, and reports;
- current status clearly visible.

### Visual Quality

- one mathematical story;
- readable equations;
- limited visual clutter;
- consistent color semantics;
- no graphical implication stronger than the Lean theorem;
- approximately sixty seconds for the first main sequence.

### Agent Quality

- repository audit before implementation;
- bounded file changes;
- explicit completion criteria;
- explicit stopping rules;
- exact report of remaining obstruction;
- recorded credit usage and elapsed time.

---

## 16. Risks

Primary project risks include:

```text
existing DkMath APIs are difficult to locate;
a thin wrapper expands into a large refactor;
DkReal reconstruction is too large for the hackathon window;
the visualization diverges from the Lean theorem;
Codex continues into unrelated research;
formal Euclidean geometry becomes unnecessarily expensive;
the project narrative overstates an elementary theorem;
credit consumption exceeds the available budget.
```

These risks are handled in detail by:

```text
RISKS_AND_STOPPING_RULES.md
```

---

## 17. Non-Goals

The project does not attempt to prove:

- the Collatz conjecture;
- the Riemann hypothesis;
- the ABC conjecture;
- Fermat's Last Theorem;
- a new theorem on the infinitude of primes;
- a general primitive-prime-divisor theorem;
- cryptographic security;
- a full theory of aperiodic tilings;
- a complete formal theory of Euclidean area;
- a complete inversion theory for all DkMath structures.

The project also does not present the finite prime escape argument itself as a new mathematical discovery.

The innovation target is the combined workflow and structural presentation.

---

## 18. Supporting Collatz Demonstration

A recorded DkMath Collatz checkpoint may appear briefly in the submission video.

The footage demonstrates that Codex can:

```text
read a large formal theory;
correct an earlier obstruction diagnosis;
implement a substantial new Lean module;
repair proof failures;
pass full builds;
stop at a newly isolated mathematical obstruction.
```

The footage is evidence of agent capability.

It is not part of the main theorem and does not claim Collatz convergence.

---

## 19. Current Status

Completed:

```text
hackathon branch created
initial Lean module scaffold created
documentation directory created
first project plan recorded
README drafted
PROJECT.md drafted
tracking anchor preserved
```

Next:

```text
ROADMAP.md
MATHEMATICAL_CONTRACT.md
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

After the documentation surface is stable, the first Codex session will be repository-audit-only.

No theorem implementation should begin before that audit is reviewed.

---

## 20. Project Identity

```text
Project:
  DkMath — Cosmic Formula Inversion

Repository:
  Deskuma/dkmath

Branch:
  hackathon/cosmic-formula-inversion

Primary category:
  Developer Tools

Core technologies:
  Lean 4
  Mathlib
  DkMath
  Codex
  Manim

Authors:
  D. and Wise Wolf
```

The project presents formal mathematics not as a static finished artifact, but as a traceable research process in which human interpretation, AI implementation, formal verification, and visual explanation remain connected from beginning to end.
