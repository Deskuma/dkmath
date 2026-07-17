# Architecture

## DkMath — Cosmic Formula Inversion

This document defines the software, theorem, dependency, documentation, visualization, and agent-execution architecture of the hackathon project.

Its purpose is to keep the project structurally narrow even though it is built on top of the much larger DkMath research library.

The governing architecture principle is:

```text
deep reusable library
→ thin verified hackathon facade
→ concrete demonstration
→ visual presentation
```

The hackathon branch must expose a short, readable path through DkMath without duplicating or reorganizing the underlying library.

---

## 1. Architectural Goals

The architecture must support all of the following:

```text
reuse of existing DkMath theorems
small public Lean modules
clear dependency direction
bounded Codex tasks
stable mathematical terminology
separation of theorem and visualization
reproducible verification
optional extension into projection and DkReal
```

The architecture must prevent:

```text
parallel mathematical hierarchies
reverse dependencies into core DkMath
unbounded repository refactoring
mixing demo facts with foundational definitions
mixing visual interpretation with formal theorem statements
mixing required milestones with stretch research
```

---

## 2. Repository Context

The project lives inside:

```text
repository:
  Deskuma/dkmath

working branch:
  hackathon/cosmic-formula-inversion

base branch:
  nightly
```

The relevant repository root for Lean work is:

```text
lean/dk_math/
```

The hackathon source modules live under:

```text
lean/dk_math/DkMath/Hackathon/
```

The hackathon documentation lives under:

```text
lean/dk_math/docs/hackathon/cosmic-formula-inversion-260715/
```

Visual assets should live in a dedicated project directory selected during the Manim phase.

A likely placement is:

```text
python/hackathon/cosmic_formula_inversion/
```

or:

```text
docs/hackathon/cosmic-formula-inversion-260715/manim/
```

The final location must be recorded in `DECISIONS.md`.

---

## 3. High-Level Architecture

The complete project architecture has six layers.

```text
Layer 1 — Existing Mathematical Infrastructure

Mathlib
DkMath algebra
DkMath number theory
DkMath Cosmic Formula
DkMath DkReal
other directly reusable DkMath APIs

Layer 2 — Hackathon Formal Facade

FinitePrimeEscape.lean
CosmicCompletion.lean
optional Projection.lean
optional Reconstruction.lean

Layer 3 — Concrete Demo

Demo.lean

Layer 4 — Agent and Project Control

project documentation
checkpoint instructions
Codex reports
review reports
decision records

Layer 5 — Visualization

Manim source
rendered scenes
equation and theorem overlays

Layer 6 — Submission Surface

README
demo video
build instructions
screenshots
public theorem summary
```

Dependencies flow downward through these layers.

No lower layer may become a dependency of a higher foundational layer.

---

## 4. Dependency Direction

The permitted dependency direction is:

```text
Mathlib
  ↓
Existing DkMath modules
  ↓
DkMath.Hackathon.FinitePrimeEscape
  ↓
DkMath.Hackathon.CosmicCompletion
  ↓
optional hackathon projection and reconstruction modules
  ↓
DkMath.Hackathon.Demo
  ↓
visual and submission artifacts
```

The exact order between `FinitePrimeEscape` and `CosmicCompletion` may remain independent if no theorem dependency is required.

A preferred graph is:

```text
                         ┌──────────────────────────────┐
                         │ Existing DkMath NumberTheory │
                         └──────────────┬───────────────┘
                                        │
                                        ▼
                         ┌──────────────────────────────┐
                         │ FinitePrimeEscape.lean       │
                         └──────────────┬───────────────┘
                                        │
                                        │
┌──────────────────────────────┐        │
│ Existing CosmicFormula APIs  │        │
└──────────────┬───────────────┘        │
               │                        │
               ▼                        │
┌──────────────────────────────┐        │
│ CosmicCompletion.lean        │        │
└──────────────┬───────────────┘        │
               │                        │
               └────────────┬───────────┘
                            ▼
                 ┌─────────────────────┐
                 │ Demo.lean           │
                 └─────────────────────┘
```

Optional projection modules may depend on both arithmetic and Cosmic Formula facades if that produces a meaningful theorem.

---

## 5. Prohibited Dependency Directions

The following directions are prohibited:

```text
DkMath.CosmicFormula.* → DkMath.Hackathon.*
DkMath.NumberTheory.*  → DkMath.Hackathon.*
DkMath.DkReal.*        → DkMath.Hackathon.*
Mathlib-facing core    → demo-specific constants
```

The hackathon facade must not become a prerequisite for core DkMath.

The following is also prohibited:

```text
Demo.lean
→ foundational theorem definitions
```

Definitions required by general theorems belong in the relevant general module, not in the demo.

---

## 6. Required Lean Module Surface

The initial required modules are:

```text
DkMath/Hackathon/
├── FinitePrimeEscape.lean
├── CosmicCompletion.lean
└── Demo.lean
```

Possible later modules are:

```text
DkMath/Hackathon/
├── Projection.lean
├── InverseProjection.lean
└── DkRealReconstruction.lean
```

These optional files must not be created until their phase begins.

Unused empty modules should not be added speculatively.

---

## 7. `FinitePrimeEscape.lean`

### Responsibility

This module owns the hackathon-facing finite-prime theorem surface.

It should contain only declarations directly related to:

```text
finite prime set
product of the finite set
coprime offset
prime divisors of P + u
freshness relative to the original set
existence of a fresh prime factor
```

### Expected Inputs

```lean
S : Finset ℕ
u : ℕ
q : ℕ
```

### Intended Core Quantity

```lean
∏ p ∈ S, p
```

A local abbreviation may be used inside proofs.

A new global structure wrapping `S`, `P`, and `u` should not be introduced unless the repository audit demonstrates a clear benefit.

### Preferred Declaration Classes

```text
thin theorem wrappers
specialized corollaries
optional predicate alias
public existence theorem
```

### Possible Public Predicate

A new predicate may be introduced only if no existing equivalent is found.

```lean
def FreshPrimeFactor
    (S : Finset ℕ)
    (n q : ℕ) : Prop :=
  Nat.Prime q ∧ q ∣ n ∧ q ∉ S
```

This predicate should not encode the construction of `P`.

It should describe only the relationship between:

```text
original finite set S
target number n
candidate prime q
```

### Expected Theorem Layers

```text
prime membership gives divisibility of the product
common divisor of P and P + u divides u
coprimality excludes a prime from the original set
every prime divisor of P + u is fresh
a fresh prime divisor exists when 1 < P + u
```

### Import Policy

Imports should be selected after audit.

The module should prefer narrow imports such as:

```lean
import Mathlib
import DkMath.<specific reusable module>
```

It should not import all of `DkMath` unless the audit establishes that the broad import is materially simpler and harmless for the demo.

---

## 8. `CosmicCompletion.lean`

### Responsibility

This module owns the hackathon-facing Cosmic Formula completion theorem.

The central identity is:

$$
P(P+2u)+u^2=(P+u)^2
$$

The module should connect this identity to existing DkMath abstractions where possible.

### Formal Responsibilities

```text
square-completion theorem
Big / Body / Gap naming bridge
normalized form if Phase 5 begins
small projection-facing corollaries when justified
```

### Formal Non-Responsibilities

This module does not own:

```text
prime-divisor existence
finite prime set definitions
Euclidean set decomposition
Manim geometry
DkReal intervals
```

### Preferred Implementation Order

```text
1. search for an exact existing theorem
2. reuse or alias the theorem
3. specialize a generic DkMath split
4. prove a thin wrapper with ring
```

### Acceptable Local Definitions

If necessary:

```lean
def cosmicCompletionBig (P u : ℕ) : ℕ :=
  (P + u) ^ 2

def cosmicCompletionBody (P u : ℕ) : ℕ :=
  P * (P + 2 * u)

def cosmicCompletionGap (u : ℕ) : ℕ :=
  u ^ 2
```

These definitions should not be added if existing DkMath Big / Body / Gap definitions already fit the theorem.

If introduced, they are demo-facing names, not a replacement hierarchy.

### Main Public Theorem

```lean
theorem cosmicCompletion
    (P u : ℕ) :
    P * (P + 2 * u) + u ^ 2 = (P + u) ^ 2
```

### Interpretation Boundary

The theorem proves an equality in arithmetic.

The Manim scene may interpret the terms as areas.

No Lean theorem in this module needs to formalize polygonal cutting or Euclidean congruence for the minimum viable project.

---

## 9. `Demo.lean`

### Responsibility

This module presents the shortest public path through the general theorems.

It must be suitable for:

```text
OBS recording
judge-facing code display
README excerpts
build demonstrations
final theorem screenshots
```

### Fixed Definitions

The module may define:

```lean
def demoPrimeSet : Finset ℕ := {2, 3, 5, 7}

def demoP : ℕ := 210

def demoU : ℕ := 11

def demoBoundary : ℕ := 221
```

If direct numeric literals are clearer than named definitions for a theorem, either style is acceptable.

The public surface should remain readable.

### Required Reuse

`Demo.lean` must reuse:

```text
FinitePrimeEscape general theorem
CosmicCompletion general theorem
```

It must not prove the mathematical ideas independently by `norm_num` alone.

`norm_num` may prove concrete arithmetic facts.

### Expected Demo Theorems

```text
demo_product
demo_coprime
demo_boundary
demo_factorization
demo_thirteen_fresh
demo_seventeen_fresh
demo_cosmic_completion
demo_complete
```

### Demo Theorem Style

Prefer small declarations that can be displayed separately.

Avoid one enormous conjunction containing every fact unless a final bundled theorem adds clear presentation value.

### Import Policy

Prefer:

```lean
import DkMath.Hackathon.FinitePrimeEscape
import DkMath.Hackathon.CosmicCompletion
```

Do not import unrelated DkMath branches directly into `Demo.lean`.

---

## 10. Optional Projection Architecture

Projection work begins only after the MVP is secured.

Possible files:

```text
DkMath/Hackathon/Projection.lean
DkMath/Hackathon/InverseProjection.lean
```

A single file may be sufficient if the theorem surface remains small.

### Projection Responsibilities

```text
chosen forward projection
interval membership
normalized Body / Gap identity
linear Gap coordinate
demo projection value
```

### Inverse Responsibilities

```text
denominator nonzero
exact inverse
left inverse
injectivity
uniqueness
```

### Domain Policy

Prefer:

```text
ℚ for exact first implementation
ℝ only when existing APIs require it
```

### Convention Policy

Only one public primary projection should exist.

Candidate unsigned convention:

$$
\pi(P,u)=\frac{P}{P+u}
$$

Candidate signed convention:

$$
\Pi(P,u)=-\frac{P}{P+u}
$$

The chosen convention must be recorded before source creation.

---

## 11. Optional DkReal Reconstruction Architecture

Possible file:

```text
DkMath/Hackathon/DkRealReconstruction.lean
```

This file must be a bridge to existing DkReal structures.

It must not define a separate nested-interval framework.

### Intended Dependencies

```text
existing DkReal interval modules
hackathon projection or inverse projection
integer uniqueness theorem
```

### Intended Responsibilities

```text
map a projected interval through the inverse
prove interval containment
transport width
prove width < 1 uniqueness
connect the concrete demo
```

### Stopping Boundary

The file must not grow into:

```text
new real-number construction
new interval lattice
new floor / ceil framework
general topology refactor
```

At the first missing DkReal bridge, stop and report.

---

## 12. Aggregate Import Architecture

An optional aggregate module may be created later:

```text
DkMath/Hackathon.lean
```

Possible content:

```lean
import DkMath.Hackathon.FinitePrimeEscape
import DkMath.Hackathon.CosmicCompletion
import DkMath.Hackathon.Demo
```

Optional projection modules may be added when completed.

The aggregate should be created only when it improves the public build or demo command.

It should not be added to the top-level `DkMath.lean` automatically.

Whether the hackathon facade becomes part of `DkMath.lean` is a separate decision.

---

## 13. Existing DkMath Reuse Architecture

The repository audit must search at least the following conceptual areas.

```text
DkMath.CosmicFormula.*
DkMath.NumberTheory.*
DkMath.Algebra.*
DkMath.DkReal.*
DkMath.Petal.*
DkMath.ABC.*
DkMath.KUS.*
```

This does not authorize edits in those areas.

It authorizes inspection for reusable declarations.

### Reuse Classification

Each candidate declaration must receive one classification.

```text
DIRECT

Use the declaration exactly as written.

WRAPPER

Expose the declaration under a hackathon-facing theorem name.

COROLLARY

Prove a small result from the declaration.

BRIDGE

Translate between two existing representations.

MISSING

No suitable declaration exists.

REJECTED

The declaration is related but semantically unsuitable.

DANGEROUS

Using the declaration would create an undesirable dependency or excessive import.
```

The classifications belong in:

```text
EXISTING_DKMATH_MAP.md
```

---

## 14. Theorem Naming Architecture

The hackathon facade should use names that are:

```text
short
standard where possible
specific to the theorem meaning
stable for video recording
independent of internal proof strategy
```

Preferred naming examples:

```text
prime_dvd_product_add_coprime_not_mem
exists_fresh_prime_factor
all_primeFactors_fresh
cosmicCompletion
normalizedCosmicCompletion
projection_mem_Icc
projection_inverse
demo_thirteen_fresh
```

Avoid names that include:

```text
hackathon
temporary
new
test
attempt
finalFinal
```

The module path already identifies the hackathon facade.

---

## 15. Definition Versus Theorem Policy

Introduce a new definition only when it supports multiple public theorems or gives a stable concept needed by the visual and formal layers.

Prefer a theorem when a named concept is not reusable.

For example:

```text
Good candidate for a definition:
  FreshPrimeFactor

Possible unnecessary definitions:
  DemoKnownPrimeWorld
  CosmicEscapeUniverse
  CompletedBoundaryPrimeChannel
```

Project terminology belongs primarily in documentation.

Formal declarations should remain mathematically conventional.

---

## 16. Domain Architecture

The project should use the weakest domain sufficient for each layer.

```text
ℕ:
  divisibility
  prime factors
  finite products
  demo arithmetic
  square completion

ℤ:
  subtraction-sensitive bridge lemmas
  signed coordinates when useful

ℚ:
  exact normalized projection
  exact inverse
  interval bounds

ℝ:
  continuous visual interpretation
  limits
  compatibility with existing real APIs

DkReal:
  nested rational approximation
  verified reconstruction
```

Do not lift a theorem to `ℝ` before its discrete arithmetic content is complete.

Do not force a rational projection through natural-number division.

---

## 17. Coercion Architecture

Projection phases may involve coercions such as:

```lean
(P : ℚ)
(u : ℚ)
```

or:

```lean
(P : ℝ)
(u : ℝ)
```

The project should isolate coercion-heavy proofs in dedicated lemmas.

Do not allow coercion normalization to dominate the public theorem surface.

A preferred pattern is:

```lean
def projectionQ (P u : ℕ) : ℚ :=
  P / (P + u)
```

with explicit casts inside the definition.

The exact implementation should follow existing DkMath conventions.

---

## 18. Documentation Architecture

The documentation directory contains both stable and evolving documents.

### Stable Project Prefix

```text
README.md
PROJECT.md
MATHEMATICAL_CONTRACT.md
ROADMAP.md
ARCHITECTURE.md
GLOSSARY.md
DECISIONS.md
RISKS_AND_STOPPING_RULES.md
```

These documents should change infrequently after the first audit.

### Repository State Documents

```text
EXISTING_DKMATH_MAP.md
CHECKPOINTS.md
CODEX_PLAN.md
```

These documents evolve as implementation proceeds.

### Presentation Documents

```text
VISUAL_STORYBOARD.md
DEMO_CONTRACT.md
```

These evolve with the visual implementation but must remain consistent with the mathematical contract.

### Historical Documents

```text
1st_PLAN.md
report-hack-*.md
UUID tracking anchors
```

Historical documents should not be rewritten to simulate a cleaner past.

Corrections should be recorded in later reports.

---

## 19. Documentation Reading Architecture

Codex should read documents in the following stable order:

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

The order separates:

```text
project meaning
→ mathematical limits
→ execution structure
→ current repository knowledge
→ current task
```

Codex should not repeatedly inspect empty UUID tracking-anchor files after confirming that they are empty.

---

## 20. Tracking-Anchor Architecture

UUID-named empty files are intentional project metadata.

Example:

```text
6a54173a-e5f8-83ee-9983-6932a7be858c
```

Their role is to connect a repository state to an originating research conversation.

Rules:

```text
preserve filename
preserve empty content
do not delete
do not rename
do not interpret as source input
do not repeatedly open
```

The empty file itself is part of the repository history architecture.

---

## 21. Checkpoint Architecture

Every Codex implementation checkpoint must have:

```text
one primary goal
one bounded file set
a list of required theorem surfaces
a list of existing APIs to inspect
verification gates
stopping rules
a report destination
```

Checkpoint instructions should use stage labels.

Example:

```text
Stage A — repository inspection
Stage B — local theorem
Stage C — public wrapper
Stage D — concrete example
Stage E — verification
Stage F — report
Stage G — stopping rule
```

A checkpoint may stop before completing all stages when it reaches a listed genuine obstruction.

---

## 22. Report Architecture

Reports should be written under:

```text
docs/hackathon/cosmic-formula-inversion-260715/
```

Naming convention:

```text
report-hack-001.md
report-hack-002.md
report-hack-003.md
```

Sub-checkpoints may use:

```text
report-hack-007a.md
report-hack-007b.md
```

Each report should contain:

```text
Status
Files changed
Definitions added
Theorems added
Existing APIs reused
Build results
Mathematical meaning
Meaning boundaries
Genuine obstruction
Next permitted action
Credit usage
Elapsed time
Session identifier
```

Reports are factual records.

They should not contain speculative claims presented as implementation results.

---

## 23. Review Architecture

The Wise Wolf review is separate from the Codex report.

The review should determine:

```text
accept
accept with conditions
return for revision
```

The review should examine:

```text
theorem meaning
contract compliance
dependency direction
API reuse
naming
module placement
actual remaining obstruction
next checkpoint design
```

Build status stated in a completed checkpoint report is treated as verified input.

Review effort should not be spent re-litigating unrelated existing warnings.

---

## 24. Visualization Architecture

The visual system is downstream from the theorem system.

The data flow is:

```text
MATHEMATICAL_CONTRACT.md
        ↓
VISUAL_STORYBOARD.md
        ↓
Manim scene source
        ↓
rendered output
        ↓
DEMO_CONTRACT.md integration
```

The animation must not introduce its own mathematical definitions.

### Visual Layer Responsibilities

```text
spatial arrangement
motion
color semantics
equation transformation
factor highlighting
Lean theorem overlay
```

### Formal Layer Responsibilities

```text
divisibility
coprimality
freshness
square identity
projection
inverse
uniqueness
```

The visual layer explains.

The formal layer proves.

---

## 25. Visual Data Architecture

All scene constants should derive from one fixed demo configuration.

A possible Python structure is:

```python
from dataclasses import dataclass

@dataclass(frozen=True)
class DemoData:
    primes: tuple[int, ...] = (2, 3, 5, 7)
    product: int = 210
    offset: int = 11
    boundary: int = 221
    fresh_factors: tuple[int, ...] = (13, 17)
```

The exact implementation may vary.

The important condition is that scene values are not duplicated inconsistently across separate files.

The Lean and Manim values should be manually cross-checked in the integration phase.

No automatic Lean-to-Manim extraction is required for the MVP.

---

## 26. Color-Semantics Architecture

The storyboard should define stable colors for:

```text
known prime universe
Body
Gap
Big boundary
fresh prime factors
Lean verification
```

A suggested semantic mapping is:

```text
known-prime components:
  neutral or cool colors

Body:
  one stable base color

Gap:
  contrasting highlight color

completed boundary:
  bright outline

fresh factors:
  distinct accent color

verified theorem:
  success highlight
```

Exact colors belong in `VISUAL_STORYBOARD.md`.

The architecture only requires semantic consistency.

---

## 27. Demo Architecture

The final demo has four synchronized tracks.

```text
Track A — Visual

the square completion and factor reveal

Track B — Formal

Lean theorem statements and build success

Track C — Agent

Codex repository audit and implementation footage

Track D — Narrative

spoken explanation and limitation statement
```

The tracks should converge on the same statement:

> The completed boundary `P + u` has prime divisors outside the finite prime set used to build `P`, under the coprimality condition.

The demo must not attempt to display the full DkMath library structure.

---

## 28. Build Architecture

Each Lean checkpoint should use increasing build gates.

### Focused Gate

```bash
lake build DkMath.Hackathon.FinitePrimeEscape
```

or the current target module.

### Hackathon Aggregate Gate

If an aggregate module exists:

```bash
lake build DkMath.Hackathon
```

### Relevant Dependency Gate

```bash
lake build DkMath.Hackathon.Demo
```

### Top-Level Gate

Use when required by the checkpoint:

```bash
lake build DkMath
```

### Source Audit

```bash
rg -n "sorry|admit" DkMath/Hackathon
git diff --check
```

The exact working directory must match repository conventions.

---

## 29. Import-Surface Architecture

Imports should remain narrow enough that the public facade reveals its true dependencies.

A broad import may be used temporarily during audit.

Before completion, Codex should report:

```text
which imports are essential
which imports are transitive
which imports can be narrowed
```

Import minimization is secondary to theorem completion but should be reviewed before final submission.

Do not perform unrelated global import cleanup.

---

## 30. API Stability Architecture

Once a theorem is used in:

```text
Manim overlay
README
submission video
screenshots
```

its name becomes presentation-stable.

Renaming after that point requires updating all presentation artifacts.

Therefore theorem names should be frozen after Phase 4.

Later implementation should add new theorems rather than casually rename demo-facing declarations.

---

## 31. Error-Recovery Architecture

Codex may repair:

```text
type mismatches
missing imports
coercion failures
theorem-name mismatches
local proof failures
namespace errors
```

Codex must stop when a failure reveals:

```text
a missing mathematical invariant
an incompatible domain model
a dependency cycle
a required core-library refactor
a theorem stronger than the contract
```

The report must distinguish:

```text
Lean engineering obstacle
mathematical obstacle
architecture obstacle
```

---

## 32. Credit-Conservation Architecture

The architecture is designed to reduce Codex credit consumption.

### Human and Wise Wolf Work

Use non-Codex work for:

```text
project design
mathematical contract
roadmap
architecture
storyboard
review
submission prose
```

### Codex Work

Reserve Codex for:

```text
repository audit
Lean implementation
Lean proof repair
Manim source implementation
integration
```

### Session Boundaries

Each session should read the stable context and then execute one bounded task.

Do not spend one session on:

```text
audit
implementation
visualization
submission prose
```

all at once.

---

## 33. MVP Preservation Architecture

After Phase 4, create or identify a known-good commit containing:

```text
FinitePrimeEscape.lean
CosmicCompletion.lean
Demo.lean
passing builds
```

All later work must preserve that commit as a fallback.

Projection, DkReal, or visual work should occur in isolated files or later commits.

The minimum verified theorem surface must remain recoverable even if stretch work fails.

---

## 34. Branch and Commit Architecture

Recommended commit boundaries:

```text
commit 1:
  project scaffold

commit 2:
  stable documentation

commit 3:
  repository audit map

commit 4:
  finite prime escape

commit 5:
  Cosmic Formula completion

commit 6:
  concrete demo

commit 7:
  projection

commit 8:
  inverse

commit 9:
  DkReal bridge

commit 10:
  Manim visual

commit 11:
  integration

commit 12:
  submission package
```

Actual commits may be subdivided.

Each commit should correspond to a meaningful checkpoint state.

---

## 35. Security and Execution Architecture

The project does not require:

```text
network services
persistent databases
user authentication
secret keys
production deployment
```

The primary execution environments are:

```text
Lean toolchain
local Git repository
Codex workspace
Python / Manim environment
video recording environment
```

Do not add unnecessary web frameworks or deployment systems to make the demo appear more application-like.

The formal workflow itself is the product.

---

## 36. Submission Architecture

The final public project should expose a simple entry path.

```text
README
  ↓
project overview
  ↓
Lean build command
  ↓
Demo.lean
  ↓
rendered video
  ↓
development reports
```

Advanced DkMath theory should remain available through links, not placed in the main judge-facing path.

The submission should clearly distinguish:

```text
verified theorem
visual interpretation
agent workflow
future research
```

---

## 37. Architecture Decision Records

Major structural decisions belong in `DECISIONS.md`.

Examples:

```text
ADR-001:
  Hackathon facade remains downstream of core DkMath.

ADR-002:
  The fixed demo uses P = 210 and u = 11.

ADR-003:
  Fresh prime is preferred over primitive prime divisor.

ADR-004:
  Projection begins over ℚ.

ADR-005:
  DkReal remains a stretch milestone.

ADR-006:
  Manim visualization does not formalize Euclidean set geometry.

ADR-007:
  Empty UUID files are preserved as tracking anchors.
```

Decision identifiers should not be reused.

---

## 38. Architecture Invariants

The following invariants must hold throughout the project.

### Dependency Invariant

```text
Core DkMath never depends on the hackathon facade.
```

### Mathematical Invariant

```text
The formal theorem never exceeds MATHEMATICAL_CONTRACT.md.
```

### Demo Invariant

```text
P = 210
u = 11
P + u = 221
fresh factors = 13 and 17
```

### Terminology Invariant

```text
fresh prime factor is not called primitive unless sequence-relative hypotheses exist
```

### Visual Invariant

```text
geometry illustrates the shared boundary value but does not claim to cause primality
```

### Agent Invariant

```text
Codex stops at the first listed genuine obstruction
```

### Verification Invariant

```text
public formal claims are build-gated
```

### Historical Invariant

```text
reports and tracking anchors are preserved
```

---

## 39. Architecture Completion Criteria

The architecture phase is complete when:

```text
Lean module responsibilities are fixed
dependency direction is fixed
optional modules are clearly separated
documentation roles are fixed
Codex reading order is fixed
report and review roles are fixed
visual and formal layers are separated
MVP preservation strategy is fixed
tracking anchors are documented
```

The repository audit may refine import choices and theorem locations.

It must not alter the main architecture without a recorded decision.

---

## 40. Architecture Summary

The project architecture is:

```text
Existing DkMath
  provides the deep mathematical infrastructure.

Hackathon Lean modules
  expose the smallest verified public path.

Demo.lean
  fixes one readable numerical example.

Project documents
  constrain Codex and preserve research intent.

Manim
  translates the theorem into motion and geometry.

Lean
  remains the authority for formal truth.

Reports and reviews
  preserve the path from idea to verified result.
```

The project succeeds architecturally when a judge can follow one short route through the system without needing to understand the entire DkMath repository, while an expert can still inspect the full formal dependency chain behind that route.
