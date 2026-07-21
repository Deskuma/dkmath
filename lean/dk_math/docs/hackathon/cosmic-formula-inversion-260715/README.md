# DkMath — Verifiable AI Mathematical Research

OpenAI Build Week Hackathon project record
Started: 2026-07-15
Authors: Deskuma (D.) and AI GPT@OpenAI (Wise Wolf)

> [!IMPORTANT]
> This repository records a human-directed, AI-assisted mathematical research
> workflow. GPT-5.6 and Codex helped reason, investigate, implement, review, and
> publish the work. Lean is the verification gate for the accepted theorem
> declarations.

## Project Status

The Build Week project now has two connected tracks.

```text
Track 1 — recorded demonstration
finite-prime escape
→ Cosmic Formula completion
→ fresh factors outside a finite prime universe
→ Lean verification
→ visual explanation

Track 2 — post-video research continuation
GN5 local obstruction
→ signed exponent-five reduction
→ golden-integer factorization
→ unit-sector elimination
→ strict golden-lift descent
→ Lean-checked positive-natural theorem surface
→ independent human review
```

### Public entry points

| Entry | Purpose |
|---|---|
| [`DkMath/Hackathon`](../../../DkMath/Hackathon/README.md) | Compact Lean-facing project entrance |
| [Devpost project](https://devpost.com/software/dkmath-verifiable-ai-mathematical-research) | Hackathon submission page and project updates |
| [PR #56](https://github.com/Deskuma/dkmath/pull/56) | Complete second-track implementation history |
| [`DkMath.FLT.Five.Main`](../../../DkMath/FLT/Five/Main.lean) | Final exponent-five theorem surface |
| [Axiom-surface inspection](../../../DkMathTest/FLT/Five/CheckAxioms.lean) | Explicit `#print axioms` audit entry point |
| [Final FLT5 implementation report](../../../DkMath/FLT/Five/docs/repo-flt5-cp-005-final.md) | Compact completion report |

## Final Video

The final narrated video combines the original finite-prime demonstration with
a post-recording update on the exponent-five formalization. Its final running
time is exactly three minutes.

A direct YouTube link is intentionally not embedded here. Search YouTube for:

```text
DkMath A Lean-Checked Formalization of the Exponent-5 Case Open for Review
```

The repository also contains the original animation and the reproducible media
pipeline.

- [Cosmic Formula prototype animation](./visual/media/videos/cosmic_formula_scene/720p30/CosmicFormulaPrototype.mp4)
- [Final submission pipeline](./submission/README.md)
- [Post-video appendix pipeline](./submission/dkmath-flt5-video-appendix/README.md)

---

## Track 1 — Cosmic Formula Inversion Demonstration

### Goal

The first public demonstration follows a short, exact mathematical path:

```text
finite prime universe
→ product of known primes
→ coprime offset
→ completed square
→ factorization outside the original universe
→ Lean verification
→ visual explanation
```

The purpose was not to create an isolated theorem file. The goal was to show
that an AI coding agent can inspect a large formal library, reuse existing
abstractions, isolate missing bridges, implement only the necessary layer, and
report the exact boundary reached.

### Mathematical contract

Let `S` be a finite set of prime numbers and define:

$$
P=\prod_{p\in S}p.
$$

Choose a positive integer `u` satisfying:

$$
\gcd(P,u)=1.
$$

If a prime `q` divides `P+u`, then it cannot belong to the original finite set:

$$
q\mid P+u\Longrightarrow q\notin S.
$$

The Cosmic Formula completion is:

$$
P(P+2u)+u^2=(P+u)^2.
$$

DkMath reads this as:

```text
Big  = (P + u)²
Body = P(P + 2u)
Gap  = u²
```

with:

$$
\mathrm{Big}=\mathrm{Body}+\mathrm{Gap}.
$$

### Demonstration example

The recorded example uses:

$$
S=\{2,3,5,7\},\qquad P=210,\qquad u=11.
$$

Then:

$$
P+u=221=13\cdot17.
$$

Both `13` and `17` lie outside the original finite set. The completion is:

$$
210\cdot232+11^2=221^2.
$$

Lean modules:

- [`FinitePrimeEscape.lean`](../../../DkMath/Hackathon/FinitePrimeEscape.lean)
- [`CosmicCompletion.lean`](../../../DkMath/Hackathon/CosmicCompletion.lean)
- [`Demo.lean`](../../../DkMath/Hackathon/Demo.lean)

---

## Track 2 — Post-Video GN5 / Exponent-Five Formalization

### How the second track began

The original video reached the concrete fifth-degree observation:

$$
GN(5,1,1)=31,
$$

and showed in Lean that this value is not a perfect fifth power. At recording
time, that was deliberately presented as a local GN5 channel rather than a
completed general theorem.

After the recording, the same research loop continued:

```text
human direction
→ GPT-5.6 mathematical review and checkpoint design
→ Codex repository investigation and Lean implementation
→ Lean feedback and proof repair
→ final theorem-surface and axiom audit
```

The implementation history is preserved in
[PR #56 — `FLT/Five: close the signed golden zero-sector descent`](https://github.com/Deskuma/dkmath/pull/56).

### Lean-checked theorem surface

The final public declarations include:

```lean
goldenZeroSectorFactorExclusion
goldenZeroSectorArithmeticExclusion
flt5Target
fermatFive_no_positive_solution
```

The ordinary-argument theorem has the scope:

$$
x,y,z\in\mathbb N_{>0}\Longrightarrow x^5+y^5\ne z^5.
$$

The public entry point is
[`DkMath.FLT.Five.Main`](../../../DkMath/FLT/Five/Main.lean).

### Descent structure

The final stage uses the golden lift:

$$
T(r,s)=(r^2+rs+s^2,s^2).
$$

Its norm reconstructs the required fifth-degree invariant, while the returned
packet has a strictly smaller second-coordinate absolute measure. Strong
induction then closes the infinite-descent contradiction.

Key source files:

- [`SignedGoldenZeroSectorInversion.lean`](../../../DkMath/FLT/Five/SignedGoldenZeroSectorInversion.lean)
- [`SignedGoldenZeroSectorFactorization.lean`](../../../DkMath/FLT/Five/SignedGoldenZeroSectorFactorization.lean)
- [`SignedGoldenZeroSectorDescent.lean`](../../../DkMath/FLT/Five/SignedGoldenZeroSectorDescent.lean)
- [`SignedGoldenZeroSectorFinal.lean`](../../../DkMath/FLT/Five/SignedGoldenZeroSectorFinal.lean)
- [`Main.lean`](../../../DkMath/FLT/Five/Main.lean)

### Review boundary

> [!NOTE]
> The repository currently presents this as a Lean-checked implementation under
> its explicit theorem contract. The next stage is independent human work:
> mathematical inspection, dependency review, axiom-surface inspection,
> reproduction, simplification, and correction where necessary.
>
> This project record does not claim completed external peer review or
> established acceptance by the mathematical community.

Suggested review path:

```text
PR #56 history
→ Main.lean theorem signatures
→ SignedGoldenZeroSectorFinal.lean
→ SignedGoldenZeroSectorDescent.lean
→ CheckAxioms.lean
→ independent build reproduction
```

---

## Why This Matters

The mathematical artifacts are important, but the central hackathon result is
the complete verifiable workflow.

The project demonstrates that one compact human–AI loop can:

1. begin with an educationally understandable example;
2. expose it as exact Lean declarations;
3. let GPT-5.6 review theorem strength and research direction;
4. let Codex inspect and modify a real repository at scale;
5. use Lean errors as formal feedback rather than rhetorical confidence;
6. preserve implementation history in checkpoints and pull requests;
7. turn the verified material into visual, narrated, reproducible media;
8. leave a public surface for later human review.

The code, reports, PR history, and publication pipeline are all part of the
submission—not merely the final video.

## Roles in the Workflow

### Human researcher

The human researcher:

- selected the mathematical direction;
- supplied the original interpretations and research questions;
- decided which claims were meaningful;
- controlled scope and stopping rules;
- accepted only theorem surfaces checked by Lean;
- chose how strongly the result should be presented publicly.

### GPT-5.6

GPT-5.6 was used to:

- refine informal observations into theorem contracts;
- review theorem strength and possible overclaims;
- compare proposed structures with existing DkMath architecture;
- design bounded Codex checkpoints;
- inspect completed reports and identify the next obstruction;
- translate the result between DkMath language and standard mathematics;
- prepare narration, explanatory structure, and publication text.

### Codex

Codex was used to:

- inspect a large Lean 4 codebase and its historical reports;
- locate reusable definitions rather than create parallel APIs;
- implement, refactor, and connect the proof tower;
- repair proof failures from Lean diagnostics;
- produce checkpoint reports and implementation maps;
- create Manim, Kokoro TTS, subtitle, and FFmpeg tooling;
- assemble the final three-minute video.

### Lean

Lean checks the theorem terms accepted by the project. Numerical experiments,
AI explanations, visualizations, and prose remain supplementary and do not
replace the formal verification gate.

---

## Reproduction

From the Lean workspace:

```bash
cd lean/dk_math
lake build DkMath.Hackathon.Demo
lake build DkMath.FLT.Five.Main
lake build DkMathTest.FLT.Five.CheckAxioms
```

Reviewers may also import the compact aggregate:

```lean
import DkMath.FLT.Five
```

The axiom inspection file enumerates the main route using `#print axioms` and
ends with the final theorem surface.

---

## Documentation Map

The documentation is part of the deliverable. It records not only the accepted
result, but how the project was scoped, audited, implemented, stopped, resumed,
and published.

### Core project documents

1. [PROJECT.md](./PROJECT.md)
2. [MATHEMATICAL_CONTRACT.md](./MATHEMATICAL_CONTRACT.md)
3. [ROADMAP.md](./ROADMAP.md)
4. [ARCHITECTURE.md](./ARCHITECTURE.md)
5. [GLOSSARY.md](./GLOSSARY.md)
6. [DECISIONS.md](./DECISIONS.md)
7. [RISKS_AND_STOPPING_RULES.md](./RISKS_AND_STOPPING_RULES.md)
8. [EXISTING_DKMATH_MAP.md](./EXISTING_DKMATH_MAP.md)
9. [VISUAL_STORYBOARD.md](./VISUAL_STORYBOARD.md)
10. [DEMO_CONTRACT.md](./DEMO_CONTRACT.md)
11. [CHECKPOINTS.md](./CHECKPOINTS.md)
12. [CODEX_PLAN.md](./CODEX_PLAN.md)
13. [FINAL_HANDOFF.md](./FINAL_HANDOFF.md)

### Publication and media

- [Submission package](./submission/README.md)
- [Post-video FLT5 appendix](./submission/dkmath-flt5-video-appendix/README.md)
- [Visual implementation](./visual/README.md)
- [TTS pipeline](./tts/README.md)

### FLT5 implementation record

- [Implementation plan](../../../DkMath/FLT/Five/docs/FLT5_IMPLEMENTS_PLAN.md)
- [Checkpoint summary](../../../DkMath/FLT/Five/docs/flt5-cp-001-to-cp-004-summary.md)
- [Final report](../../../DkMath/FLT/Five/docs/repo-flt5-cp-005-final.md)
- [PR #56](https://github.com/Deskuma/dkmath/pull/56)

---

## Verification Policy

Every accepted implementation checkpoint records, where applicable:

```text
checkpoint identifier
goal
model and reasoning level
files changed
definitions and theorems added
build targets
formal verification status
genuine obstruction
next permitted action
session identifier
```

The project separates four kinds of evidence:

```text
Lean theorem declarations     formal verification surface
CI and reproduction commands  build evidence
numerical experiments          exploratory evidence
visual and written material    explanatory evidence
```

These layers support one another but are not interchangeable.

## Terminology Boundary

### Fresh prime factor

A prime divisor of `P+u` that is not contained in the original finite prime set.
This is the preferred term for the first demonstration.

### Finite prime universe

The finite arithmetic world generated by `S`, its product `P`, and associated
residue information. This is DkMath project terminology, not a replacement for
standard algebraic definitions.

### Lean-checked formalization

A collection of declarations accepted by Lean under the imported environment
and encoded assumptions. It does not by itself mean that external mathematical
review has been completed.

### Independent review

Human inspection of the mathematical reductions, definitions, dependencies,
axiom surface, reproducibility, exposition, and potential corrections.

## Non-Goals and Scope Limits

This project does not claim:

- a proof of the Collatz conjecture;
- a new general prime-number theorem;
- a new general primitive-prime-divisor theorem;
- a solution of general-exponent Fermat's Last Theorem;
- completed external peer review of the exponent-five implementation;
- cryptographic security;
- a complete DkReal inversion theory;
- that AI-generated prose is mathematical evidence.

The exponent-five statement exposed by the current Lean API is specifically the
positive-natural theorem encoded in `DkMath.FLT.Five.Main`.

## Acknowledgments

At the time the video was produced and edited, the project had reached only a local obstruction based on GN5.

After the video was published and the hackathon submission was complete, I still had a little energy left. I therefore decided to continue the implementation as a second phase, to see how far the GN5 perspective could actually take us when put into practice.

What emerged from that continuation was a Lean formalization of the exponent-five case of Fermat’s Last Theorem.

Several formalizations of the exponent-five case already exist. In this project, however, we proceeded directly from GN5 without consulting those implementations, following the route that arose from our own investigation. I made the decisions about the mathematical direction and about what was appropriate to publish.

During the implementation, we encountered a difficult question: how could the relevant unit be identified and handled? The AI also struggled with this problem for a considerable time.

The breakthrough was inspired by a comment left by a reader on one of my articles on note.

“A unit is always present. However, its form changes with the space in which it appears.”

I had previously explained this idea using the metaphor of a 🎗️“red ribbon.” That explanation aligned with the problem before us with surprising precision and became the key to overcoming the obstacle.

Without that comment, I do not think we would have passed this particular barrier.

A brief and seemingly modest comment led to an idea that helped us overcome one of the most difficult stages of the implementation. I would therefore like to record my gratitude here. Thank you very much.

Independent external review of the Lean implementation begins from this point.

The AI worked extraordinarily hard. Now it is time for human readers to work equally hard to understand what has been constructed.

When the formal understanding certified by Lean and the mathematical understanding of human readers finally meet, I believe this work will become a genuine step toward the truth.

---

## Authors and License

D. and Wise Wolf

The Lean source code is released under the MIT license used by the DkMath
project. The documentation records a human–AI collaborative mathematical
research process and should be read together with the checked source.
