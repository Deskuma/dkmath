# Hackathon: OpenAI Build Week - 260715 @ devpost

Date: 2026/07/18  1:19
Author: Deskuma (D.) and AI GPT@OpenAI (Wise Wolf)

## DkMath — Cosmic Formula Inversion

A verifiable AI-assisted mathematical research project for the OpenAI Build Week Hackathon.

This project demonstrates a workflow in which:

1. a mathematical structure is proposed and refined through human–AI dialogue;
2. Codex investigates and implements the structure inside an existing Lean 4 library;
3. Lean verifies the resulting theorem surface;
4. the verified mathematics is transformed into an accessible visual demonstration.

The main theme is the transition from a finite universe of known prime factors to a provably new prime factor, expressed through the DkMath Cosmic Formula, finite-prime escape, and the new GN5 extension.

---

## Project Goal

The first public demonstration follows one short mathematical path:

```text
finite prime universe
→ product of known primes
→ coprime offset
→ completed square
→ factorization outside the known universe
→ Lean verification
→ visual explanation
```

The project is not intended to create an isolated theorem file.

Its purpose is to expose a clear, verifiable path through the existing DkMath library and show how an AI coding agent can:

- inspect a large formal mathematics codebase;
- reuse existing abstractions;
- isolate genuinely missing lemmas;
- implement only the necessary bridge layer;
- verify the result with Lean;
- report the exact remaining mathematical obstruction.

---

## Core Mathematical Contract

Let `S` be a finite set of prime numbers and define:

$$
P=\prod_{p\in S}p
$$

Choose a positive integer `u` satisfying:

$$
\gcd(P,u)=1
$$

Assume:

$$
1<P+u
$$

If a prime `q` divides `P + u`, then `q` cannot belong to the original finite prime set:

$$
q\mid P+u\Longrightarrow q\notin S
$$

The geometric completion identity is:

$$
P(P+2u)+u^2=(P+u)^2
$$

DkMath interprets this as:

```text
Big  = (P + u)²
Body = P(P + 2u)
Gap  = u²
```

with:

$$
\mathrm{Big}=\mathrm{Body}+\mathrm{Gap}
$$

The prime factors of `P + u` therefore appear on the completed boundary, while the Body is generated from the finite known-prime universe.

---

## Demonstration Example

The initial demonstration uses:

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

Both `13` and `17` lie outside the original set `S`.

The Cosmic Formula completion is:

$$
210\cdot232+11^2=221^2
$$

or numerically:

$$
48720+121=48841
$$

This single example will be shared by:

- the Lean theorem demonstration;
- the Manim animation;
- the submission video;
- the project documentation;
- the final interactive or scripted demo.

Using one common example prevents the formal proof, visual explanation, and submission narrative from drifting into separate mathematical stories.

---

## Why This Matters

The elementary prime-factor argument is not the final research goal.

It is the smallest verifiable example of a broader DkMath program:

```text
finite arithmetic world
→ boundary completion
→ new factor channel
→ normalized projection
→ bounded inverse representation
→ reconstruction of an integer-scale structure
```

The larger project studies how apparently unbounded arithmetic structures can be projected into bounded interval representations and later reconstructed through formally verified inverse maps.

The hackathon version deliberately begins with a theorem that is:

- finite;
- exact;
- visually understandable;
- inexpensive to verify;
- connected to deeper existing DkMath infrastructure.

---

## Repository Branch

```text
repository: Deskuma/dkmath
base branch: nightly
working branch: hackathon/cosmic-formula-inversion
```

---

## Lean Module Layout

The hackathon-facing Lean surface is intentionally thin.

```text
DkMath/Hackathon/
├── FinitePrimeEscape.lean
├── CosmicCompletion.lean
└── Demo.lean
```

### `FinitePrimeEscape.lean`

Responsibilities:

- finite sets of known primes;
- their product `P`;
- coprimality with the offset `u`;
- existence of a prime divisor of `P + u`;
- proof that such a divisor is outside the original finite set.

### `CosmicCompletion.lean`

Responsibilities:

- the identity

$$
P(P+2u)+u^2=(P+u)^2
$$

- connection to existing Big / Body / Gap APIs;
- reusable wrappers around existing DkMath Cosmic Formula theorems;
- no duplicate parallel theory.

### `Demo.lean`

Responsibilities:

- the concrete example `P = 210`, `u = 11`;
- factorization `221 = 13 × 17`;
- final public theorem surface;
- a compact import path for the recorded demonstration.

These modules must depend on existing DkMath infrastructure.

Existing DkMath modules must never import the hackathon facade.

---

## Documentation Layout

[docs/hackathon/cosmic-formula-inversion-260715/](./)

```text
docs/hackathon/cosmic-formula-inversion-260715/
├── README.md
├── PROJECT.md
├── ROADMAP.md
├── MATHEMATICAL_CONTRACT.md
├── ARCHITECTURE.md
├── EXISTING_DKMATH_MAP.md
├── VISUAL_STORYBOARD.md
├── DEMO_CONTRACT.md
├── CODEX_PLAN.md
├── CHECKPOINTS.md
├── DECISIONS.md
├── GLOSSARY.md
└── RISKS_AND_STOPPING_RULES.md
```

The documentation is part of the project deliverable.

It records not only the final theorem, but also:

- why the theorem surface was selected;
- how the existing library was audited;
- which definitions were reused;
- which missing lemmas were discovered;
- where Codex was instructed to stop;
- how the verified theorem was converted into a visual explanation.

---

## Required Reading Order for Codex

Before modifying source code, Codex must read the project documents in this order:

1. [README.md](./README.md)
2. [PROJECT.md](./PROJECT.md)
3. [MATHEMATICAL_CONTRACT.md](./MATHEMATICAL_CONTRACT.md)
4. [ROADMAP.md](./ROADMAP.md)
5. [ARCHITECTURE.md](./ARCHITECTURE.md)
6. [GLOSSARY.md](./GLOSSARY.md)
7. [DECISIONS.md](./DECISIONS.md)
8. [RISKS_AND_STOPPING_RULES.md](./RISKS_AND_STOPPING_RULES.md)
9. [EXISTING_DKMATH_MAP.md](./EXISTING_DKMATH_MAP.md)
10. [VISUAL_STORYBOARD.md](./VISUAL_STORYBOARD.md)
11. [DEMO_CONTRACT.md](./DEMO_CONTRACT.md)
12. [CHECKPOINTS.md](./CHECKPOINTS.md)
13. [CODEX_PLAN.md](./CODEX_PLAN.md)
14. the current checkpoint instruction

This order should remain stable across sessions.

The stable prefix exists to preserve a consistent project interpretation and reduce repeated repository exploration.

---

## Tracking Anchor Files

UUID-named empty files inside the hackathon documentation directory are intentional tracking anchors.

Example form:

```text
6a54173a-e5f8-83ee-9983-6932a7be858c
```

They connect repository checkpoints to their originating research conversation.

Rules:

- do not delete them;
- do not rename them;
- do not add content to them;
- do not inspect them after confirming that they are empty;
- do not treat them as implementation inputs.

Their filenames are metadata. Their contents are intentionally empty.

---

## Codex Operating Principles

Codex must act as a repository-aware mathematical implementation agent, not as a code transcription tool.

### Required behavior

- inspect existing DkMath APIs before defining new ones;
- prefer theorem wrappers and bridge lemmas over parallel abstractions;
- preserve existing dependency directions;
- verify every implementation checkpoint with Lean;
- distinguish mathematical obstruction from API inconvenience;
- stop at the first genuine missing invariant;
- record exact theorem names and file locations;
- report what was proved and what remains unproved.

### Prohibited behavior

- do not expand into unrelated DkMath research branches;
- do not continue into Collatz, FLT, RH, ABC, or Erdős problems unless a direct reusable API is required;
- do not create a second Big / Body / Gap hierarchy;
- do not create new prime-factor terminology when an existing predicate is sufficient;
- do not claim cryptographic security;
- do not claim a new prime-number theorem;
- do not infer an infinite theorem from a finite construction;
- do not replace a formal proof obligation with numerical testing;
- do not continue beyond the checkpoint stopping rule.

---

## Terminology Boundary

The project distinguishes several related terms.

### Fresh prime factor

A prime divisor of `P + u` that is not contained in the original finite prime set.

This is the preferred term for the initial demonstration.

### Primitive prime divisor

A sequence-relative concept stating that a prime appears at one stage and not at specified earlier stages.

This stronger term must not be used unless the theorem actually includes the required sequence-relative hypotheses.

### Finite prime universe

The finite arithmetic world generated by the selected prime set `S`, its product `P`, and the associated residue information.

This is project terminology, not a replacement for standard algebraic definitions.

### Inverse projection

A later project phase in which unbounded arithmetic data is normalized into a bounded interval representation and reconstructed through a verified inverse or uniqueness theorem.

The initial finite-prime theorem is an entry point to this phase, not the entire inverse-projection result.

---

## Development Roadmap

The intended phase structure is:

```text
Phase 0 — Project documentation and repository scaffold
Phase 1 — Existing DkMath API audit
Phase 2 — Finite prime escape theorem
Phase 3 — Cosmic Formula completion bridge
Phase 4 — Inverse projection surface
Phase 5 — DkReal interval and reconstruction bridge
Phase 6 — Manim visual implementation
Phase 7 — Unified Lean and visual demo
Phase 8 — Submission packaging
```

Each phase must have:

- a precise theorem or artifact target;
- an explicit file boundary;
- a completion condition;
- a stopping condition;
- a report identifying the next genuine obstruction.

---

## Visual Demonstration

The first animation should remain under approximately sixty seconds.

Planned sequence:

```text
1. Display the finite prime set {2, 3, 5, 7}.
2. Combine the primes into P = 210.
3. Construct the rectangular Body P(P + 2u).
4. Display the missing square Gap u².
5. Insert the Gap and complete the square (P + u)².
6. Reveal the completed side length P + u = 221.
7. Factor 221 into 13 × 17.
8. Highlight that 13 and 17 are outside the original prime set.
9. Show the corresponding Lean theorem and successful verification.
```

The animation explains the structure.

Lean establishes the theorem.

Neither layer substitutes for the other.

---

## Supporting Research Footage

The project may include short recorded footage from the DkMath Collatz formalization branch.

That footage demonstrates the same development workflow at a much larger scale:

```text
repository audit
→ theorem design
→ Lean implementation
→ error correction
→ verification
→ isolation of a genuine mathematical obstruction
```

The Collatz work is supporting evidence of the workflow.

It is not the main theorem of this hackathon submission and no Collatz convergence claim is made.

---

## Current Status

The hackathon implementation and submission package are complete.

Accepted Lean modules:

```text
DkMath/Hackathon/FinitePrimeEscape.lean
DkMath/Hackathon/CosmicCompletion.lean
DkMath/Hackathon/Demo.lean
```

Final submission package:

```text
submission/output/DkMathCosmicPromoFinal.mp4
submission/README.md
submission/narration.srt
submission/build_submission.sh
```

Formal MVP, visual prototype, promo integration, and submission packaging have
all passed their accepted checkpoints. Only external human publication tasks
remain: optional narration and authentic footage, upload, and platform form
completion. See `FINAL_HANDOFF.md` for the final artifact provenance, commands,
checksums, and the exact future inverse-projection resume point.

---

## First Codex Audit Session

The first Codex session is investigation-only.

Its target is:

```text
Read the complete hackathon documentation in the prescribed order.

Do not edit Lean source files.

Audit the existing DkMath repository for reusable definitions and theorems
required by the mathematical contract.

Identify:
- APIs reusable without modification;
- theorems requiring thin wrappers;
- genuinely missing lemmas;
- dangerous dependency directions;
- the smallest viable implementation surface.

Propose updates to EXISTING_DKMATH_MAP.md.

Stop after producing the audit report.
```

The implementation checkpoint will be written only after this report has been reviewed.

---

## Verification Policy

Every implementation checkpoint must record:

```text
checkpoint identifier
goal
model and reasoning level
elapsed time
credits consumed
files changed
definitions added
theorems added
build targets
no-sorry status
git diff status
genuine obstruction
next permitted action
session identifier
```

Lean build success is the verification gate for formal claims.

Numerical examples and visual output are supplementary evidence only.

---

## Non-Goals

The first hackathon milestone does not claim:

- a proof of the Collatz conjecture;
- a new proof of the infinitude of primes;
- a new primitive-prime-divisor theorem;
- a general theory of aperiodic tilings;
- cryptographic security;
- a complete formalization of Euclidean area;
- a complete DkReal inversion theorem;
- a solution to any currently open mathematical problem.

The project demonstrates a verifiable research workflow and a reusable structural bridge inside DkMath.

---

## Authors

D. and Wise Wolf

The Lean source code is released under the MIT license used by the DkMath project.

The project documentation records a human–AI collaborative mathematical research process.
