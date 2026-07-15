# Roadmap

## DkMath — Cosmic Formula Inversion

This roadmap defines the planned development sequence for the OpenAI Build Week Hackathon project.

It separates:

- required milestones;
- stretch milestones;
- repository-audit work;
- Lean implementation;
- inverse-projection research;
- visual production;
- submission packaging.

The roadmap is directional, not speculative.

Each phase must end in one of three states:

```text
completed:
  the required artifact or theorem exists and passes its verification gates

blocked:
  a genuine mathematical or repository-API obstruction has been isolated

deferred:
  the phase is valid but intentionally postponed to protect the minimum viable submission
```

Codex must not continue automatically from one phase into the next.

A new checkpoint instruction is required for every implementation phase.

---

## 1. Project Route

The intended project route is:

```text
Phase 0
Project scaffold and fixed documentation
        ↓
Phase 1
Existing DkMath repository audit
        ↓
Phase 2
Finite prime escape theorem
        ↓
Phase 3
Cosmic Formula completion bridge
        ↓
Phase 4
Concrete Lean demonstration
        ↓
Phase 5
Normalized bounded projection
        ↓
Phase 6
Inverse formula and uniqueness
        ↓
Phase 7
DkReal interval reconstruction
        ↓
Phase 8
Manim visual implementation
        ↓
Phase 9
Unified Lean and visual demonstration
        ↓
Phase 10
Submission packaging and recording
```

The minimum viable project ends successfully after Phases 0–4 and Phase 8–10.

Phases 5–7 are stronger milestones.

They improve the research narrative but must not endanger the verified finite-prime demonstration.

---

## 2. Milestone Classes

The roadmap uses three milestone classes.

### Required

Required for a valid hackathon submission:

```text
project documentation
repository audit
finite prime escape theorem
Cosmic Formula completion theorem
concrete Lean demo
visual demonstration
recorded Codex workflow
submission package
```

### Preferred

Strongly desired:

```text
normalized rational projection
exact inverse formula
injectivity
normalized Body / Gap conservation
```

### Stretch

Attempt only after the required path is secure:

```text
DkReal nested-interval bridge
unique macro-integer reconstruction
interactive visualization
broader finite-prime-universe exploration
```

---

## 3. Global Completion Rule

The project is considered submission-ready when:

```text
1. the public Lean demo builds;
2. the mathematical claims match MATHEMATICAL_CONTRACT.md;
3. the Manim sequence expresses the same theorem path;
4. the Codex development process has been recorded;
5. setup and verification instructions are reproducible;
6. all public novelty and limitation statements are accurate;
7. the submission video is complete.
```

The inverse-projection and DkReal stretch layers are not required for submission readiness.

---

## 4. Phase 0 — Project Scaffold and Fixed Documentation

### Status

```text
in progress
```

### Purpose

Create a stable project prefix before any major Codex implementation session.

The documents must explain:

- project identity;
- mathematical contract;
- architecture;
- terminology;
- roadmap;
- checkpoints;
- Codex behavior;
- stopping conditions;
- visual story;
- final demo behavior.

### Required Documents

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

### Existing Lean Scaffold

```text
DkMath/Hackathon/FinitePrimeEscape.lean
DkMath/Hackathon/CosmicCompletion.lean
DkMath/Hackathon/Demo.lean
```

### Completion Conditions

```text
all stable project documents exist
document reading order is fixed
mathematical theorem contract is fixed
demo values are fixed
dependency direction is fixed
tracking anchors are documented
Codex audit instruction can be written without ambiguity
```

### Stopping Rule

Stop documentation expansion when all later phases can be described without introducing new project terminology.

Do not turn Phase 0 into a complete exposition of DkMath.

### Output

```text
stable project documentation prefix
```

---

## 5. Phase 1 — Existing DkMath Repository Audit

### Status

```text
accepted — report-hack-001.md
```

### Purpose

Determine which required theorem surfaces already exist in DkMath and which declarations require:

- direct reuse;
- thin wrappers;
- specialized corollaries;
- genuinely new lemmas.

This phase is investigation-only.

### Codex Permissions

Codex may:

```text
read project documentation
search the DkMath repository
inspect imports
inspect theorem statements
inspect existing proof dependencies
write an audit report
propose edits to EXISTING_DKMATH_MAP.md
```

Codex may not:

```text
edit Lean source files
refactor existing DkMath modules
create new theorem declarations
change the mathematical contract
begin Manim implementation
```

### Audit Targets

Codex must search for existing APIs involving:

```text
Finset products
prime membership
product divisibility
Nat.Coprime
prime divisor existence
Euclid-style finite prime escape
FreshPrimeFactor-like predicates
Big / Body / Gap
Cosmic Formula square completion
normalized Cosmic Formula
rational projection
inverse maps
DkReal nested intervals
interval width
floor and ceil uniqueness
unique integer candidates
```

### Required Audit Classification

Every relevant declaration must be classified as:

```text
direct reuse
thin wrapper
specialized corollary
genuinely missing
not suitable
dangerous dependency
```

### Required Report

```text
docs/hackathon/cosmic-formula-inversion-260715/
  report-hack-001.md
```

### Completion Conditions

```text
reusable theorem map completed
candidate imports identified
dependency risks identified
smallest viable Lean surface proposed
first genuine missing lemma identified
no Lean source edited
```

### Stopping Rule

Stop after the repository map is complete enough to design Phase 2.

Do not solve the missing lemmas during the audit.

### Output

```text
reviewed repository reuse map
```

---

## 6. Phase 2 — Finite Prime Escape Theorem

### Status

```text
accepted — report-hack-002.md
```

### Purpose

Implement the general finite prime escape theorem.

Let:

$$
P=\prod_{p\in S}p
$$

Assume:

$$
\gcd(P,u)=1
$$

Then every prime divisor of `P + u` lies outside `S`.

The preferred public existence theorem is:

$$
\exists q,\ \operatorname{Prime}(q)\land q\mid P+u\land q\notin S
$$

under:

$$
1<P+u
$$

### Target Module

```text
DkMath/Hackathon/FinitePrimeEscape.lean
```

### Intended Theorem Layers

```text
membership implies divisibility of product
shared divisor of P and P + u divides u
coprimality excludes original primes
every supplied prime divisor is fresh
a fresh prime divisor exists when 1 < P + u
```

### Preferred Implementation Strategy

```text
reuse existing DkMath and Mathlib APIs
avoid new structures unless required
use a thin hackathon facade
separate divisor exclusion from divisor existence
keep unnecessary positivity assumptions out of local lemmas
```

### Verification Gates

```text
focused module build
hackathon aggregate build if available
new file no-sorry
git diff --check
theorem contract review
```

### Completion Conditions

```text
general exclusion theorem builds
general existence theorem builds
hypotheses match MATHEMATICAL_CONTRACT.md
all new declarations are documented
report identifies reused APIs
```

### Stopping Rules

Stop if:

```text
a required existing product-divisibility API cannot be reused safely
prime-divisor existence requires a larger unexpected abstraction
a reverse dependency into core DkMath becomes necessary
the proposed FreshPrimeFactor predicate duplicates an existing predicate
```

At the first obstruction, report the smallest missing theorem.

### Required Report

```text
report-hack-002.md
```

### Output

```text
verified finite prime escape API
```

---

## 7. Phase 3 — Cosmic Formula Completion Bridge

### Status

```text
accepted — report-hack-003.md
```

### Purpose

Expose the square-completion identity through the existing DkMath Cosmic Formula surface.

The required theorem is:

$$
P(P+2u)+u^2=(P+u)^2
$$

The project interpretation is:

```text
Body = P(P + 2u)
Gap  = u²
Big  = (P + u)²
```

### Target Module

```text
DkMath/Hackathon/CosmicCompletion.lean
```

### Required Audit Before Editing

Codex must inspect existing declarations involving:

```text
CosmicFormula
Big
Body
Gap
CoreBeamGap
ResidualNat
ResidualInt
GN
BodyGapSplit
BodyGapKernelSplit
square completion
```

### Implementation Preference

Use the strongest appropriate existing theorem in this order:

```text
1. direct reuse
2. theorem alias
3. specialized wrapper
4. local ring proof
```

Do not create a second Big / Body / Gap hierarchy.

### Theorem Surface

Expected theorem shapes include:

```lean
theorem cosmic_completion_nat
    (P u : ℕ) :
    P * (P + 2 * u) + u ^ 2 = (P + u) ^ 2
```

and, if an existing DkMath split API is suitable:

```lean
def cosmicCompletionSplit ...
```

or a theorem exposing the identity through that API.

### Verification Gates

```text
focused module build
FinitePrimeEscape compatibility build
new file no-sorry
git diff --check
dependency review
```

### Completion Conditions

```text
general completion theorem builds
existing DkMath structure is reused where appropriate
no parallel Cosmic Formula hierarchy created
formal theorem and visual interpretation remain distinct
```

### Stopping Rules

Stop if:

```text
reuse requires importing an excessively broad unrelated module
existing Cosmic Formula abstractions use incompatible domains
a proposed bridge introduces a dependency cycle
formal Euclidean geometry becomes necessary
```

The square identity itself may be proved locally if the deeper bridge is too expensive.

### Required Report

```text
report-hack-003.md
```

### Output

```text
verified Cosmic Formula completion facade
```

---

## 8. Phase 4 — Concrete Lean Demonstration

### Status

```text
accepted — report-hack-004.md
```

### Purpose

Build the fixed public example.

### Target Module

```text
DkMath/Hackathon/Demo.lean
```

### Fixed Data

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

### Required Facts

$$
2\cdot3\cdot5\cdot7=210
$$

$$
\gcd(210,11)=1
$$

$$
210+11=221
$$

$$
221=13\cdot17
$$

$$
13\notin S
$$

$$
17\notin S
$$

$$
210\cdot232+11^2=221^2
$$

### Public Demo Surface

The demo should expose small readable declarations such as:

```text
demoPrimeSet
demoP
demoU
demoBoundary
demo_product
demo_coprime
demo_factorization
demo_thirteen_fresh
demo_seventeen_fresh
demo_cosmic_completion
demo_complete
```

Exact names may change after repository review.

### Implementation Strategy

```text
reuse general Phase 2 and Phase 3 theorems
use norm_num or decide for concrete arithmetic
avoid reproving the general theorem numerically
keep imports compact
make the final file suitable for OBS recording
```

### Completion Conditions

```text
Demo.lean builds
all fixed numerical facts are verified
the general theorem is visibly reused
the final theorem surface is short enough for a demo
the same numbers are ready for Manim
```

### Stopping Rule

Do not add unrelated examples.

Do not generalize the demo module into another library layer.

### Required Report

```text
report-hack-004.md
```

### Output

```text
minimum viable verified Lean demonstration
```

---

## 9. Minimum Viable Submission Gate

After Phase 4, evaluate the project before continuing.

### Required Check

```text
Can the project already be submitted with:
- the verified finite theorem;
- the Cosmic Formula visual;
- the recorded Codex process;
- a short Manim animation?
```

If yes, mark:

```text
MVP_SECURED = true
```

From this point onward, all additional research must preserve the working MVP.

### Required Preservation Rule

Before every later Codex session:

```text
confirm Demo.lean still builds
confirm the fixed example remains unchanged
confirm later work is isolated from the MVP modules
```

---

## 10. Phase 5 — Normalized Bounded Projection

### Status

```text
preferred milestone
not started
```

### Purpose

Select and formalize one bounded projection convention.

Candidate unsigned projection:

$$
\pi(P,u)=\frac{P}{P+u}
$$

Candidate signed projection:

$$
\Pi(P,u)=-\frac{P}{P+u}
$$

Only one convention should become the primary public API.

### Decision Requirement

Before implementation, record in `DECISIONS.md`:

```text
chosen projection
domain
codomain interval
reason
visual meaning
inverse formula
```

### Preferred Domain

Start over `ℚ` unless existing DkMath APIs strongly favor `ℝ`.

### Required Theorems

For the unsigned version:

$$
0\le\frac{P}{P+u}<1
$$

For the signed version:

$$
-1<-\frac{P}{P+u}\le0
$$

under the appropriate positivity assumptions.

### Normalized Conservation

$$
\frac{P(P+2u)}{(P+u)^2}+\frac{u^2}{(P+u)^2}=1
$$

### Distinction to Preserve

```text
linear Gap coordinate:
  u / (P + u)

square Gap mass:
  u² / (P + u)²
```

### Possible Module

The final placement must follow the repository audit.

Possible hackathon facade:

```text
DkMath/Hackathon/Projection.lean
```

Do not create this file before the architecture decision is recorded.

### Completion Conditions

```text
one projection convention chosen
forward interval theorem builds
normalized Body / Gap conservation builds
concrete demo projection builds
no competing convention implemented
```

### Stopping Rules

Stop if:

```text
the projection duplicates an existing DkMath API
domain coercions expand into broad refactoring
the proof requires unnecessary real analysis
both signed and unsigned conventions begin to grow simultaneously
```

### Required Report

```text
report-hack-005.md
```

### Output

```text
verified bounded projection
```

---

## 11. Phase 6 — Exact Inverse and Injectivity

### Status

```text
preferred milestone
not started
```

### Purpose

Prove that the chosen bounded coordinate reconstructs `P` for fixed positive `u`.

For the unsigned coordinate:

$$
x=\frac{P}{P+u}
$$

the inverse is:

$$
P=\frac{ux}{1-x}
$$

For the signed coordinate:

$$
x=-\frac{P}{P+u}
$$

the inverse is:

$$
P=-\frac{ux}{1+x}
$$

### Required Theorems

```text
denominator nonzero on the chosen domain
left inverse
right inverse on the image
injectivity for fixed positive u
uniqueness of reconstructed P
```

### Preferred Domain

```text
ℚ first
ℝ only when needed
```

### Completion Conditions

```text
exact inverse theorem builds
injectivity theorem builds
demo value reconstructs exactly
formal domain boundaries are documented
finite P does not map to the limiting endpoint
```

### Stopping Rules

Stop if:

```text
the inverse requires an unplanned equivalence hierarchy
the proof becomes a general topology project
the intended domain cannot be represented without substantial coercion work
the project begins claiming surjectivity onto an endpoint not attained by finite P
```

### Required Report

```text
report-hack-006.md
```

### Output

```text
verified forward and inverse projection pair
```

---

## 12. Phase 7 — DkReal Interval Reconstruction

### Status

```text
stretch milestone
not started
```

### Purpose

Connect the inverse-projection program to existing DkReal nested-interval machinery.

### Intended Structure

Let:

$$
I_n=[a_n,b_n]
$$

with:

$$
I_{n+1}\subseteq I_n
$$

and shrinking width.

Apply the inverse map to obtain macro-scale intervals:

$$
J_n=f_u^{-1}(I_n)
$$

The intended uniqueness criterion is:

$$
\operatorname{width}(J_n)<1
$$

which implies that `J_n` contains at most one integer.

### Audit Targets

Codex must inspect:

```text
DkReal
GapInterval
nested intervals
width-zero results
rational endpoints
floor and ceil
integer interval cardinality
unique integer in interval
monotone maps on intervals
```

### Required Intermediate Milestones

```text
A. identify existing DkReal interval type
B. map projected intervals through the inverse
C. prove interval inclusion or monotonicity
D. prove width control
E. prove at-most-one natural candidate
F. connect the concrete demo
```

Each milestone requires a separate checkpoint.

### Completion Conditions

The stretch phase is complete only if:

```text
existing DkReal structures are reused
the inverse map acts on the interval representation
width control is proved
integer-candidate uniqueness is proved
the demo reconstruction is verified
```

### Stopping Rules

Stop immediately if:

```text
a parallel interval library would be required
the current DkReal API lacks the needed map operation
monotonicity of the inverse is the first genuine missing theorem
width transport cannot be expressed cleanly
integer uniqueness requires a missing floor / ceil bridge
```

Record the smallest missing bridge and return to the secured MVP.

### Required Reports

Use one report per sub-checkpoint:

```text
report-hack-007a.md
report-hack-007b.md
report-hack-007c.md
...
```

### Output

```text
optional verified DkReal reconstruction layer
```

---

## 13. Phase 8 — Manim Visual Implementation

### Status

```text
required
accepted — report-hack-008a.md
```

### Purpose

Create the visual explanation of the already-fixed theorem.

### Input Documents

```text
MATHEMATICAL_CONTRACT.md
VISUAL_STORYBOARD.md
DEMO_CONTRACT.md
DECISIONS.md
```

### Fixed Visual Route

```text
finite prime labels
→ product P = 210
→ Body P(P + 2u)
→ Gap u²
→ completed square (P + u)²
→ boundary 221
→ factors 13 and 17
→ fresh factors highlighted
→ Lean theorem shown
```

### Visual Invariants

```text
P = 210
u = 11
P + u = 221
13 and 17 are the fresh factors
Body / Gap / Big colors remain stable
geometry does not claim to cause primality
```

### Initial Time Budget

Target:

```text
45–60 seconds
```

### Implementation Stages

```text
A. static layout prototype
B. Body and Gap animation
C. completion animation
D. boundary factorization
E. Lean verification overlay
F. final render
```

### Completion Conditions

```text
animation renders successfully
equations are readable
the fixed example is correct
the visual sequence matches the Lean theorem
no unsupported claim appears
render time and source are reproducible
```

### Stopping Rules

Stop visual expansion if:

```text
Euclidean precision work does not improve the story
prime spirals or aperiodic tilings distract from the theorem
interactive controls delay the main render
the scene exceeds the submission time budget
```

### Required Report

```text
report-hack-008.md
```

### Output

```text
rendered primary visual demonstration
```

---

## 14. Phase 9 — Unified Lean and Visual Demo

### Status

```text
required
accepted — report-hack-009a.md
```

### Purpose

Connect the verified theorem, visual scene, and recorded agent process into one demonstration path.

### Demo Sequence

```text
1. show the mathematical question
2. show finite prime universe S
3. show P and u
4. play square completion
5. reveal 221 = 13 × 17
6. show Lean theorem
7. show successful build
8. briefly show Codex repository work
9. state the exact verified result
10. state the broader inverse-projection direction
```

### Required Alignment Table

Create a table mapping:

```text
visual scene
Lean theorem
documentation section
spoken narration
```

No scene may lack a corresponding mathematical source.

### Completion Conditions

```text
all visual claims map to Lean or explicit interpretation
the build shown is the current branch build
the theorem names shown are stable
the narration does not overclaim
the full path fits the target duration
```

### Required Report

```text
report-hack-009.md
```

### Output

```text
integrated project demo
```

---

## 15. Phase 10 — Submission Packaging

### Status

```text
required
accepted — report-hack-010a.md
```

### Purpose

Prepare the final hackathon submission.

### Required Package

```text
public branch
project README
setup instructions
Lean build instructions
Manim render instructions
demo video
project screenshots
formal theorem summary
AI workflow summary
limitations
credits and authorship
```

### Reproducibility Checklist

```text
repository clone works
branch checkout works
Lean toolchain is documented
lake build command is documented
Manim environment is documented
render command is documented
demo files are linked
```

### Submission Narrative

The final narrative should answer:

```text
What did we build?
Why is it useful?
What did Codex do?
What did Lean verify?
What does the visual show?
What remains future work?
```

### Completion Conditions

```text
submission form completed
video uploaded
repository accessible
build steps tested
final theorem list frozen
limitations reviewed
all project links valid
```

### Output

```text
submitted hackathon project
```

---

## 16. Checkpoint Numbering

The planned checkpoint sequence is:

```text
hack-000:
  branch and repository scaffold

hack-001:
  repository audit

hack-002:
  finite prime escape

hack-003:
  Cosmic Formula completion

hack-004:
  concrete Lean demo

hack-005:
  bounded projection

hack-006:
  exact inverse and injectivity

hack-007a+:
  DkReal reconstruction sub-checkpoints

hack-008:
  Manim implementation

hack-009:
  unified demo

hack-010:
  submission packaging
```

Actual checkpoint numbers may be subdivided.

Completed checkpoint numbers must never be reused.

---

## 17. Codex Session Classes

Each Codex session must be classified before execution.

### Audit Session

```text
read and report only
no source edits
```

### Implementation Session

```text
bounded theorem and file targets
explicit stopping rule
Lean verification required
```

### Repair Session

```text
repair a known failing checkpoint
no new scope
```

### Visual Session

```text
Manim-only work
mathematical contract already fixed
```

### Integration Session

```text
connect existing completed artifacts
no new mathematical theory
```

The session class must appear in the checkpoint instruction.

---

## 18. Credit Budget Strategy

Codex credits are a finite project resource.

The project should prefer:

```text
human–Wise Wolf planning before Codex
stable documentation before repository exploration
one bounded implementation target per session
stopping at the first genuine obstruction
reuse over refactoring
focused builds before full builds
```

Suggested budget priority:

```text
highest priority:
  Lean theorem implementation
  genuine proof obstruction repair
  final integration

medium priority:
  repository audit
  Manim implementation

low priority:
  prose
  documentation drafting
  speculative exploration
  unrelated DkMath branches
```

Every session must record:

```text
starting credits
ending credits
credits consumed
elapsed time
model
reasoning level
files changed
result
```

---

## 19. Branch Protection Strategy

The working branch is:

```text
hackathon/cosmic-formula-inversion
```

The required MVP should be preserved through commits at:

```text
documentation complete
audit complete
finite theorem complete
Cosmic completion complete
demo complete
visual complete
submission complete
```

Later projection or DkReal work must not destroy the last known working MVP commit.

---

## 20. Decision Gates

The roadmap contains explicit decision gates.

### Gate A — After Audit

Question:

```text
Can the finite theorem be implemented as a thin facade?
```

If no, reduce scope before implementation.

### Gate B — After Finite Prime Escape

Question:

```text
Is the general theorem clean enough for the public demo?
```

If no, improve the facade without expanding the mathematics.

### Gate C — After Concrete Demo

Question:

```text
Is the minimum viable submission secure?
```

If yes, preserve it before inverse-projection work.

### Gate D — Before DkReal

Question:

```text
Does existing DkReal infrastructure provide a realistic short bridge?
```

If no, defer DkReal.

### Gate E — Before Final Render

Question:

```text
Does every visual claim correspond to the formal contract?
```

If no, simplify the animation.

---

## 21. Global Stopping Conditions

The project must stop expanding when any of the following becomes true:

```text
the submission deadline requires packaging;
the MVP is complete and remaining work risks destabilizing it;
Codex credits fall below the final integration reserve;
a stretch phase exposes a genuinely new research program;
visual complexity no longer improves comprehension;
the next theorem is unrelated to the public project story.
```

Stopping is a successful project decision when the verified MVP is secure.

---

## 22. Out-of-Scope Branches

During the hackathon, Codex must not continue into:

```text
Collatz convergence
FLT
RH
ABC
Erdős #1196
general aperiodic tiling theory
prime-distribution asymptotics
cryptographic construction
general DkMath refactoring
```

Existing theorems from these areas may be reused only when they directly satisfy a documented project dependency.

No new research checkpoint may be opened inside those branches from a hackathon instruction.

---

## 23. Supporting Collatz Footage Route

The recorded Collatz cp-320 session may be used as supporting footage.

Its role is:

```text
showing agent capability
showing large-repository navigation
showing Lean repair
showing genuine-obstruction isolation
```

Its role is not:

```text
main project theorem
proof of Collatz convergence
dependency of the finite prime demo
```

The final video may use a short excerpt before or after the main demonstration.

---

## 24. Final Project Shape

The ideal completed project has four visible layers.

```text
Layer 1 — Mathematical Contract

finite prime escape
Cosmic Formula completion
bounded projection
inverse reconstruction

Layer 2 — Formal Verification

Lean theorem modules
existing DkMath reuse
build reports

Layer 3 — Agent Workflow

Codex audit
implementation
repair
stopping rule
obstruction report

Layer 4 — Human Explanation

Manim animation
documentation
submission narration
```

The minimum viable project may omit the full inverse reconstruction layer.

It must not omit formal verification or visual explanation.

---

## 25. Roadmap Summary

The required path is:

```text
documentation
→ repository audit
→ finite prime escape
→ Cosmic Formula completion
→ concrete Lean demo
→ Manim visualization
→ unified demo
→ submission
```

The stronger path adds:

```text
bounded projection
→ exact inverse
→ DkReal interval reconstruction
```

The roadmap is successful when the project reaches the strongest verified milestone available within the hackathon budget without weakening the already-secured minimum viable demonstration.
