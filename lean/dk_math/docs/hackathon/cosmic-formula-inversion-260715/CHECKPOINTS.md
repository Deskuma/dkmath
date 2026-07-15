# Checkpoints

## DkMath — Cosmic Formula Inversion

This document records the controlled development checkpoints for the hackathon project.

A checkpoint is the smallest reviewable unit of project progress.

Each checkpoint defines:

```text
one primary objective
one bounded set of permitted files
one required output surface
one verification plan
one stopping rule
one report destination
one review outcome
```

A checkpoint may end in either of two successful states:

```text
COMPLETED:
  the requested artifacts and verification gates are complete

STOPPED:
  the first genuine obstruction has been isolated and reported precisely
```

Codex must not continue automatically into the next checkpoint.

Every new checkpoint requires a separately reviewed instruction.

---

## 1. Document Status

```text
DOCUMENT STATUS:
  INITIAL CHECKPOINT REGISTRY

CURRENT PROJECT PHASE:
  Phase 0 — stable documentation

CURRENT CHECKPOINT:
  hack-000

NEXT PLANNED CHECKPOINT:
  hack-001 — existing DkMath repository audit

LEAN IMPLEMENTATION STATUS:
  not started

MVP STATUS:
  not yet secured
```

---

## 2. Checkpoint Authority

The authority order for checkpoint execution is:

```text
1. current checkpoint instruction
2. CHECKPOINTS.md
3. CODEX_PLAN.md
4. RISKS_AND_STOPPING_RULES.md
5. DECISIONS.md
6. MATHEMATICAL_CONTRACT.md
7. ARCHITECTURE.md
8. ROADMAP.md
9. PROJECT.md
10. README.md
```

The current checkpoint instruction may refine implementation details.

It may not silently contradict an accepted mathematical or architectural decision.

When a contradiction is found:

```text
stop
report the contradiction
request a project decision
```

---

## 3. Checkpoint Identifier Policy

Checkpoint identifiers use:

```text
hack-NNN
```

Examples:

```text
hack-000
hack-001
hack-002
```

Sub-checkpoints use a suffix:

```text
hack-007a
hack-007b
hack-007c
```

Rules:

```text
identifiers are unique
completed identifiers are never reused
stopped identifiers are never reused
revisions receive a new identifier
reports preserve the original identifier
```

A repair checkpoint may refer to an earlier checkpoint but must receive a new identifier.

Example:

```text
hack-002:
  initial finite-prime implementation

hack-002r1:
  bounded repair of the accepted implementation surface
```

The preferred project convention is to use the next unused numeric identifier rather than accumulating many repair suffixes.

---

## 4. Checkpoint Status Vocabulary

Each checkpoint has one status.

### `PLANNED`

The checkpoint is defined but no Codex session has begun.

### `READY`

All prerequisite documents and decisions are complete.

The instruction may now be issued.

### `IN_PROGRESS`

The Codex session is currently executing or its result is awaiting collection.

### `STOPPED`

The checkpoint reached a genuine obstruction before completing its full target.

A precise obstruction report exists.

### `COMPLETED`

The required implementation or artifact exists and all checkpoint gates passed.

### `ACCEPTED`

The Wise Wolf review accepted the checkpoint.

### `ACCEPTED_WITH_CONDITIONS`

The main result is accepted, but bounded follow-up work remains.

### `RETURNED`

The checkpoint failed contract, architecture, or theorem-meaning review.

### `DEFERRED`

The checkpoint remains valid but is postponed.

### `CANCELLED`

The checkpoint is no longer part of the active project route.

Historical records remain preserved.

---

## 5. Checkpoint Classes

Every checkpoint must declare one class.

### Audit

```text
repository investigation
no source implementation
report and map updates only
```

### Implementation

```text
bounded source edits
new declarations or artifacts
verification required
```

### Repair

```text
fix a known bounded failure
no new mathematical scope
```

### Review Integration

```text
apply accepted naming, import, documentation, or facade corrections
```

### Visual

```text
Manim source and render work
formal theorem contract already fixed
```

### Integration

```text
connect completed formal, visual, and narrative artifacts
no new mathematical theory
```

### Submission

```text
package, test, record, and publish completed artifacts
```

---

## 6. Required Checkpoint Header

Every Codex instruction must begin with a header equivalent to:

````md
# Checkpoint hack-XXX

## Session Class

```text
AUDIT / IMPLEMENTATION / REPAIR / VISUAL / INTEGRATION / SUBMISSION
```

## Primary Goal

State one bounded goal.

## Permitted Files

List every file Codex may edit.

## Read-Only Files

List important files that may be inspected but not edited.

## Prohibited Scope

List adjacent work that must not begin.

## Required Report

State the exact report path.

## Stopping Rule

State the first genuine obstruction rule.
````

Codex must not infer broader file permissions from the roadmap.

---

## 7. Required Checkpoint Stages

Implementation instructions should use explicit stages.

Recommended structure:

```text
Stage A — read and inspect
Stage B — identify exact reusable API
Stage C — implement the smallest local bridge
Stage D — expose the public theorem surface
Stage E — verify focused builds
Stage F — verify integration gates
Stage G — write the report
Stage H — stop
```

Not every checkpoint requires every stage.

The final stage must always include a stopping instruction.

---

## 8. Required Completion Metadata

Every checkpoint report must include:

```text
checkpoint identifier
session class
status
primary goal
model
reasoning level
start time
end time
elapsed time
starting credits
ending credits
credits consumed
files inspected
files changed
definitions added
theorems added
existing declarations reused
verification commands
verification results
no-sorry result
git diff result
mathematical meaning
meaning boundary
first genuine obstruction
next permitted action
session identifier
```

Unknown metadata must be marked:

```text
not recorded
```

It must not be guessed.

---

## 9. Verification Levels

A checkpoint may require one or more verification levels.

### Level 0 — Document Verification

```text
required files exist
required headings exist
internal references are consistent
no binding contradiction remains
```

### Level 1 — Focused Source Verification

```text
target module builds
target source contains no sorry or admit
```

### Level 2 — Facade Verification

```text
dependent hackathon module builds
public theorem surface elaborates
```

### Level 3 — Relevant Aggregate Verification

```text
hackathon aggregate or Demo.lean builds
```

### Level 4 — Top-Level Verification

```text
relevant DkMath top-level build passes
```

### Level 5 — Presentation Verification

```text
Manim scene renders
displayed theorem names are current
displayed values match Lean
```

### Level 6 — Submission Reproduction

```text
fresh clone or clean workspace build succeeds
render instructions succeed
public links resolve
```

The current instruction must state which levels are required.

---

## 10. Review Outcomes

After a report is received, Wise Wolf assigns one outcome.

### Accept

```text
the checkpoint satisfies its contract
```

### Accept with Conditions

```text
the core result is valid
minor bounded work remains
```

### Return for Revision

```text
the theorem meaning is wrong
the architecture is violated
scope was exceeded
required reuse is absent
the report is materially incomplete
```

### Accept Stopping Point

```text
the original target was not fully completed
the first genuine obstruction was isolated correctly
the checkpoint produced a valid research boundary
```

A stopped checkpoint does not need to be converted into a completed checkpoint before the next theorem is designed.

---

## 11. Current Checkpoint Registry

| Checkpoint | Class | Goal | Status | Report |
|---|---|---|---|---|
| `hack-000` | documentation | establish project scaffold and stable context | `COMPLETED` | project documents |
| `hack-001` | audit | map existing DkMath and Mathlib APIs | `ACCEPTED` | `report-hack-001.md` |
| `hack-002` | implementation | finite prime escape theorem | `ACCEPTED` | `report-hack-002.md` |
| `hack-003` | implementation | Cosmic Formula completion bridge | `ACCEPTED` | `report-hack-003.md` |
| `hack-004` | implementation | fixed concrete Lean demo | `ACCEPTED` | `report-hack-004.md` |
| `hack-005` | implementation | bounded projection | `DEFERRED` | `report-hack-005.md` |
| `hack-006` | implementation | exact inverse and injectivity | `DEFERRED` | `report-hack-006.md` |
| `hack-007a+` | implementation | DkReal reconstruction sub-bridges | `DEFERRED` | `report-hack-007*.md` |
| `hack-008a` | visual | primary Manim sequence | `ACCEPTED` | `report-hack-008a.md` |
| `hack-009a` | integration | unified formal and visual demo | `ACCEPTED` | `report-hack-009a.md` |
| `hack-010a` | submission | reproducible submission package | `ACCEPTED` | `report-hack-010a.md` |
| `hack-010b` | closure | final handoff and project closure | `COMPLETED` | `report-hack-010b.md` |

Statuses must be updated after each accepted review.

---

# Checkpoint Definitions

## 12. Checkpoint `hack-000` — Project Scaffold and Stable Context

### Class

```text
DOCUMENTATION
```

### Status

```text
IN_PROGRESS
```

### Primary Goal

Create the stable project context required before repository-aware Codex execution.

### Existing Scaffold

```text
branch:
  hackathon/cosmic-formula-inversion

Lean modules:
  DkMath/Hackathon/FinitePrimeEscape.lean
  DkMath/Hackathon/CosmicCompletion.lean
  DkMath/Hackathon/Demo.lean

documentation directory:
  docs/hackathon/cosmic-formula-inversion-260715/
```

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

### Historical and Tracking Files

```text
1st_PLAN.md
UUID-named empty tracking anchor
```

### Completion Conditions

```text
all required documents exist
Codex reading order is fixed
mathematical contract is fixed
architecture is fixed
demo constants are fixed
risk and stopping rules are fixed
first audit checkpoint can be issued without ambiguity
```

### Prohibited Scope

```text
no Lean theorem implementation
no repository-wide source audit
no Manim implementation
no projection implementation
```

### Verification Level

```text
Level 0
```

### Required Report

```text
docs/hackathon/cosmic-formula-inversion-260715/
  report-hack-000.md
```

### Stopping Rule

Stop adding documentation when no new terminology is required to describe the remaining checkpoints.

### Expected Review Outcome

```text
ACCEPT
```

or:

```text
ACCEPT_WITH_CONDITIONS
```

for minor cross-document corrections.

---

## 13. Checkpoint `hack-001` — Existing DkMath Repository Audit

### Class

```text
AUDIT
```

### Status

```text
PLANNED
```

### Prerequisites

```text
hack-000 accepted
all stable documents present
no unresolved binding contradiction
```

### Primary Goal

Identify the exact existing DkMath and Mathlib declarations needed by the MVP.

### Read-Only Source Scope

Codex may inspect:

```text
README.md
AGENT.md
SUMMARY.md
__dkmath-all.lean.txt.gz
__summary_report_data.tar.gz
__theorems-heading.txt
DkMath source modules
Mathlib source declarations
```

### Permitted Edits

```text
EXISTING_DKMATH_MAP.md
report-hack-001.md
```

Optional:

```text
CHECKPOINTS.md status field only
```

only when explicitly authorized.

### Prohibited Edits

```text
all Lean source files
all Manim source files
core project contracts
tracking anchors
historical plans
```

### Required Audit Targets

```text
Finset product membership divisibility
Nat.Coprime exclusion
prime-divisor existence
fresh-prime predicates
Euclid-style finite escape
Big / Body / Gap
Cosmic Formula square completion
GN square specialization
projection candidates
DkReal interval candidates
width less than one integer uniqueness
```

### Required Classification

Each relevant declaration must be classified:

```text
DIRECT
WRAPPER
COROLLARY
BRIDGE
MISSING
REJECTED
DANGEROUS
DEMO_ONLY
```

### Required Stages

```text
Stage A:
  read stable project documents

Stage B:
  read repository instructions

Stage C:
  inspect theorem databases and source

Stage D:
  map finite-prime theorem route

Stage E:
  map Cosmic Formula route

Stage F:
  identify projection and DkReal entry points

Stage G:
  update EXISTING_DKMATH_MAP.md

Stage H:
  write report-hack-001.md

Stage I:
  stop without editing Lean
```

### Completion Conditions

```text
exact finite-prime API route identified
exact Cosmic Formula route identified
candidate imports identified
rejected near matches recorded
first genuinely missing theorem named
Phase 2 file scope proposed
no Lean source edited
```

### Verification Level

```text
Level 0
```

### Required Report

```text
report-hack-001.md
```

### Stopping Rule

Stop when the first implementation checkpoint can be written without broad repository search.

Do not prove or implement missing lemmas.

### Next Permitted Action

```text
Wise Wolf review of the audit
```

No implementation session begins before review.

---

## 14. Checkpoint `hack-002` — Finite Prime Escape

### Class

```text
IMPLEMENTATION
```

### Status

```text
PLANNED
```

### Prerequisites

```text
hack-001 accepted
exact imports and reusable declarations identified
FreshPrimeFactor decision resolved
```

### Primary Goal

Implement the general finite prime escape theorem in a thin facade.

### Primary Target Module

```text
DkMath/Hackathon/FinitePrimeEscape.lean
```

### Permitted Files

```text
DkMath/Hackathon/FinitePrimeEscape.lean
report-hack-002.md
EXISTING_DKMATH_MAP.md
```

The map may be updated only with implementation-confirmed findings.

### Read-Only Files

```text
existing DkMath modules
Mathlib source
project contract documents
```

### Required Theorem Layers

#### Local Product Divisibility

$$
q\in S\Longrightarrow q\mid\prod_{p\in S}p
$$

Prefer direct reuse.

#### Supplied Prime-Divisor Exclusion

$$
\operatorname{Prime}(q)\land q\mid P+u\land\gcd(P,u)=1\Longrightarrow q\notin S
$$

where `P` is the product of `S`.

#### Universal Freshness

$$
\forall q,\ \operatorname{Prime}(q)\land q\mid P+u\Longrightarrow q\notin S
$$

#### Fresh-Prime Existence

$$
1<P+u\Longrightarrow\exists q,\ \operatorname{Prime}(q)\land q\mid P+u\land q\notin S
$$

### Hypothesis Audit

The report must state whether the following are logically required:

```text
all members of S are prime
S.Nonempty
0 < u
0 < P
1 < P + u
```

Do not retain unused assumptions merely for narrative convenience.

### Required Reuse

```text
existing Finset product theorem
existing Coprime or gcd theorem
existing prime-divisor existence theorem
```

### Prohibited Scope

```text
no Cosmic Formula implementation
no demo constants
no projection
no DkReal
no core DkMath refactor
no general commutative-monoid abstraction project
```

### Required Stages

```text
Stage A:
  confirm exact audited declarations and imports

Stage B:
  implement or expose the supplied-divisor exclusion theorem

Stage C:
  implement the universal freshness theorem

Stage D:
  implement the existence theorem

Stage E:
  add concise theorem documentation

Stage F:
  run focused verification

Stage G:
  write report-hack-002.md

Stage H:
  stop
```

### Verification Levels

```text
Level 1
Level 2 when a dependent test surface exists
```

### Minimum Completion

The supplied-divisor exclusion theorem builds.

### Full Completion

Both exclusion and existence theorems build.

### Genuine Obstruction Examples

```text
no suitable prime-divisor existence theorem
existing freshness predicate has incompatible semantics
required theorem forces a dependency cycle
product representation requires a foundational bridge
```

### Stopping Rule

Stop at the smallest theorem that cannot be closed through direct reuse or a short local proof.

Do not continue into Cosmic Completion.

### Required Report

```text
report-hack-002.md
```

### Next Permitted Action

```text
Wise Wolf review
```

---

## 15. Checkpoint `hack-003` — Cosmic Formula Completion Bridge

### Class

```text
IMPLEMENTATION
```

### Status

```text
PLANNED
```

### Prerequisites

```text
hack-002 accepted or accepted stopping point
Cosmic Formula audit findings reviewed
```

The square identity may proceed even if fresh-prime existence remains stopped, provided the supplied-divisor theorem surface is stable.

### Primary Goal

Expose the square-completion identity through the cleanest suitable DkMath facade.

### Target Module

```text
DkMath/Hackathon/CosmicCompletion.lean
```

### Permitted Files

```text
DkMath/Hackathon/CosmicCompletion.lean
report-hack-003.md
EXISTING_DKMATH_MAP.md
```

### Required Main Theorem

$$
P(P+2u)+u^2=(P+u)^2
$$

### Preferred Reuse Order

```text
1. direct existing theorem
2. thin theorem wrapper
3. specialization of generic exponent theorem
4. local ring proof
```

### Optional Theorem

If an existing GN bridge is narrow and clear:

$$
P(P+2u)=P\cdot GN_2(P,u)
$$

This optional theorem must not delay the main completion theorem.

### Prohibited Scope

```text
no formal Euclidean geometry
no new foundational Big / Body / Gap hierarchy
no projection
no DkReal
no unrelated GN generalization
```

### Required Stages

```text
Stage A:
  confirm exact audited Cosmic Formula declarations

Stage B:
  select direct reuse, wrapper, specialization, or ring fallback

Stage C:
  implement the general completion theorem

Stage D:
  expose Big / Body / Gap interpretation only when existing APIs fit

Stage E:
  run focused build

Stage F:
  verify compatibility with FinitePrimeEscape imports

Stage G:
  write report-hack-003.md

Stage H:
  stop
```

### Verification Levels

```text
Level 1
Level 2
```

### Completion Conditions

```text
general identity builds
no parallel Cosmic Formula hierarchy is created
the report identifies the actual reuse decision
visual interpretation remains separate from formal equality
```

### Stopping Rule

If deeper DkMath reuse is more expensive than a correct thin ring wrapper, use the wrapper and report the deferred deeper bridge.

Stop before projection or formal geometry.

### Required Report

```text
report-hack-003.md
```

---

## 16. Checkpoint `hack-004` — Concrete Lean Demo

### Class

```text
IMPLEMENTATION
```

### Status

```text
PLANNED
```

### Prerequisites

```text
hack-002 accepted
hack-003 accepted
public general theorem names provisionally stable
```

### Primary Goal

Create an OBS-ready concrete demonstration using the fixed values.

### Target Module

```text
DkMath/Hackathon/Demo.lean
```

### Permitted Files

```text
DkMath/Hackathon/Demo.lean
report-hack-004.md
DEMO_CONTRACT.md alignment table
VISUAL_STORYBOARD.md alignment table
```

Only alignment tables may be updated in the visual documents.

### Fixed Values

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
P+u=221=13\cdot17
$$

### Required Public Surface

Equivalent declarations for:

```text
demoPrimeSet
demoP
demoU
demoBoundary
demo_product
demo_coprime
demo_boundary
demo_factorization
demo_thirteen_prime
demo_seventeen_prime
demo_thirteen_fresh
demo_seventeen_fresh
demo_cosmic_completion
```

### Required Structural Reuse

```text
demo freshness uses the general finite-prime theorem
demo completion uses the general Cosmic Formula theorem
```

### Permitted Automation

```text
norm_num
decide
native_decide
ring
simp
```

for concrete facts.

### Prohibited Scope

```text
no additional numerical examples
no projection
no DkReal
no exploratory theorem collection
no public theorem-name churn after acceptance
```

### Required Stages

```text
Stage A:
  define or confirm fixed demo constants

Stage B:
  prove product, coprimality, boundary, and factorization

Stage C:
  specialize the general freshness theorem to 13 and 17

Stage D:
  specialize the general completion theorem

Stage E:
  create a compact public presentation surface

Stage F:
  run all required builds

Stage G:
  update alignment tables

Stage H:
  write report-hack-004.md

Stage I:
  stop
```

### Verification Levels

```text
Level 1
Level 2
Level 3
```

Optional:

```text
Level 4
```

when required by repository convention.

### Completion Conditions

```text
Demo.lean builds
fixed data is correct
general theorems are visibly reused
new hackathon modules contain no sorry
the public theorem surface is concise
theorem names are ready to freeze
```

### MVP Gate

After acceptance:

```text
MVP_FORMAL_CORE_SECURED = true
```

A known-good commit must be preserved.

### Stopping Rule

Do not continue into projection.

Do not add more examples.

### Required Report

```text
report-hack-004.md
```

---

## 17. Formal MVP Acceptance Gate

The formal MVP gate occurs immediately after `hack-004`.

### Required Questions

```text
Does Demo.lean build?

Does the general finite-prime theorem build?

Does the general Cosmic Formula theorem build?

Are the fixed values correct?

Are public theorem names stable?

Can the formal result already support the primary Manim story?
```

### Pass State

```text
FORMAL_MVP = SECURED
```

### Required Action

```text
create or identify a known-good commit
record the commit hash
freeze public theorem names
update CHECKPOINTS.md
```

### Failure State

Design a bounded repair checkpoint.

Do not begin projection or visual integration until the gate passes.

---

## 18. Checkpoint `hack-005` — Bounded Projection

### Class

```text
IMPLEMENTATION
```

### Status

```text
DEFERRED
```

### Prerequisites

```text
formal MVP secured
projection convention selected through a new accepted ADR
existing projection APIs audited
```

### Primary Goal

Formalize one bounded projection convention over the weakest practical exact domain.

### Candidate Unsigned Projection

$$
\pi(P,u)=\frac{P}{P+u}
$$

### Candidate Signed Projection

$$
\Pi(P,u)=-\frac{P}{P+u}
$$

Only one convention may be selected.

### Preferred Domain

```text
ℚ
```

### Possible Target Module

```text
DkMath/Hackathon/Projection.lean
```

The exact file must be authorized by the checkpoint instruction.

### Required Theorems

For the selected convention:

```text
definition of projection
denominator positivity or nonzero theorem
bounded interval theorem
concrete demo projection
normalized Body / Gap conservation
```

The normalized conservation theorem is:

$$
\frac{P(P+2u)}{(P+u)^2}+\frac{u^2}{(P+u)^2}=1
$$

### Prohibited Scope

```text
no second projection convention
no complete inverse
no DkReal
no general topology
no endpoint-surjectivity claim
```

### Verification Levels

```text
Level 1
Level 2
Level 3
```

### Completion Conditions

```text
one projection convention exists
its image bound builds
normalized conservation builds
Demo.lean still builds
```

### Stopping Rule

Stop if coercion or domain architecture becomes the main project.

Return to the secured MVP.

### Required Report

```text
report-hack-005.md
```

---

## 19. Checkpoint `hack-006` — Exact Inverse and Injectivity

### Class

```text
IMPLEMENTATION
```

### Status

```text
DEFERRED
```

### Prerequisites

```text
hack-005 accepted
projection convention frozen
```

### Primary Goal

Prove exact reconstruction on the forward image for fixed positive `u`.

### Unsigned Inverse Candidate

$$
P=\frac{ux}{1-x}
$$

### Signed Inverse Candidate

$$
P=-\frac{ux}{1+x}
$$

Only the selected convention is implemented.

### Required Theorem Layers

```text
inverse denominator is nonzero
forward then inverse returns P
inverse then forward returns x on the image
projection is injective for fixed positive u
concrete demo reconstruction
```

### Prohibited Scope

```text
no surjectivity onto an unjustified ambient interval
no DkReal intervals
no varying-u injectivity claim without correct pair structure
no general Möbius transformation library
```

### Verification Levels

```text
Level 1
Level 2
Level 3
```

### Completion Conditions

```text
exact left inverse builds
injectivity builds
image restriction is explicit
Demo.lean remains unchanged and builds
```

### Stopping Rule

Stop at the first domain, denominator, or image-characterization theorem not present in the current contract.

### Required Report

```text
report-hack-006.md
```

---

## 20. Checkpoint Family `hack-007` — DkReal Reconstruction

### Class

```text
IMPLEMENTATION
```

### Status

```text
DEFERRED
```

### Prerequisites

```text
formal MVP secured
hack-006 accepted
DkReal audit confirms a short realistic bridge
submission reserve protected
```

This family must be divided into separate sub-checkpoints.

---

## 21. Checkpoint `hack-007a` — DkReal Entry Bridge

### Primary Goal

Identify and implement the smallest bridge from the selected rational projection into the existing DkReal representation.

### Permitted Scope

```text
existing DkReal type
existing interval constructor
projection value embedding
membership theorem
```

### Prohibited Scope

```text
no width transport
no integer uniqueness
no new interval framework
```

### Stopping Rule

Stop if no compatible existing DkReal constructor or embedding exists.

### Required Report

```text
report-hack-007a.md
```

---

## 22. Checkpoint `hack-007b` — Inverse Interval Mapping

### Primary Goal

Map a projected interval through the exact inverse formula.

### Required Surface

```text
inverse monotonicity on the selected interval
endpoint mapping
membership transport
reconstructed macro interval
```

### Stopping Rule

Stop if a general interval-map or monotonicity bridge is missing.

### Required Report

```text
report-hack-007b.md
```

---

## 23. Checkpoint `hack-007c` — Width Transport

### Primary Goal

Prove a bound on the width of the inverse-mapped interval.

### Potential Requirements

```text
denominator lower bound
endpoint algebra
local Lipschitz estimate
monotone rational inverse
```

### Stopping Rule

Stop when the first missing width-transport invariant is isolated.

Do not open a general analysis project.

### Required Report

```text
report-hack-007c.md
```

---

## 24. Checkpoint `hack-007d` — Integer-Candidate Uniqueness

### Primary Goal

Prove that reconstructed interval width below one implies at most one integer candidate.

### Required Theorem

$$
\operatorname{width}(I)<1\Longrightarrow\operatorname{AtMostOne}\{z\in\mathbb Z\mid z\in I\}
$$

The exact Lean shape must follow existing APIs.

### Required Distinction

```text
at most one:
  uniqueness only

exactly one:
  existence plus uniqueness
```

### Stopping Rule

Stop if floor, ceiling, or integer interval APIs require a new infrastructure layer.

### Required Report

```text
report-hack-007d.md
```

---

## 25. Checkpoint `hack-007e` — Concrete DkReal Reconstruction

### Primary Goal

Apply the accepted DkReal bridge to the fixed demo.

### Required Result

```text
the original macro value lies in the reconstructed interval
the interval contains at most one natural-number candidate
the candidate is demoP
```

Only state exact uniqueness when both existence and at-most-one have been proved.

### Stopping Rule

Stop if the concrete bridge requires new general theory beyond accepted `hack-007a`–`hack-007d` results.

### Required Report

```text
report-hack-007e.md
```

---

## 26. DkReal Family Termination Rule

The entire `hack-007` family stops when any sub-checkpoint reaches an accepted genuine obstruction.

At that point:

```text
record the strongest completed sub-checkpoint
preserve the formal MVP
return to visual or submission work
```

A stopped DkReal family does not block the hackathon submission.

---

## 27. Checkpoint `hack-008` — Primary Manim Demonstration

### Class

```text
VISUAL
```

### Status

```text
PLANNED
```

### Prerequisites

```text
formal MVP secured
public theorem names frozen
visual source directory decided
color palette accepted
```

Projection and DkReal are not prerequisites.

### Primary Goal

Create and render the fixed 45–60 second Manim theorem sequence.

### Permitted Files

The exact Manim source root selected by ADR.

Also:

```text
report-hack-008.md
VISUAL_STORYBOARD.md alignment table
DEMO_CONTRACT.md alignment table
```

### Fixed Scene Route

```text
finite prime set
→ product P
→ coprime offset u
→ Body
→ Gap
→ completed square
→ boundary 221
→ factors 13 and 17
→ freshness comparison
→ Lean verification
```

### Required Prototype Stages

```text
Stage A:
  shared data configuration

Stage B:
  static layout

Stage C:
  Body and Gap completion motion

Stage D:
  factor reveal

Stage E:
  Lean theorem panel

Stage F:
  primary render

Stage G:
  alignment verification

Stage H:
  report

Stage I:
  stop
```

### Required Data

```text
S = {2, 3, 5, 7}
P = 210
u = 11
boundary = 221
fresh factors = 13 and 17
Body = 48720
Gap = 121
Big = 48841
```

### Verification Level

```text
Level 5
```

### Completion Conditions

```text
primary scene renders
duration is approximately 45–60 seconds
equations are readable
values match Lean
formal theorem names are current
no unsupported claim appears
```

### Prohibited Scope

```text
no automatic Lean-to-Python extraction requirement
no interactive web application
no prime spirals
no aperiodic tiling
no formal Euclidean geometry
no unverified projection epilogue
```

### Stopping Rule

Stop after the smallest complete readable render.

Optional effects must not delay the primary render.

### Required Report

```text
report-hack-008.md
```

---

## 28. Checkpoint `hack-009` — Unified Demo Integration

### Class

```text
INTEGRATION
```

### Status

```text
PLANNED
```

### Prerequisites

```text
formal MVP secured
hack-008 accepted
actual build footage available
Codex audit or implementation footage available
```

### Primary Goal

Create one synchronized judge-facing demonstration.

### Required Tracks

```text
visual theorem track
Lean verification track
Codex process track
narration track
```

### Required Alignment Artifact

Create a final mapping:

| Timestamp | Visual claim | Lean anchor | Narration | Status |
|---|---|---|---|---|
| pending | pending | pending | pending | pending |

No row may remain `pending` at completion.

### Required Stages

```text
Stage A:
  choose final sequence and duration

Stage B:
  insert Manim output

Stage C:
  insert actual Codex footage

Stage D:
  insert actual Lean build success

Stage E:
  record or add narration

Stage F:
  add captions and limitation text

Stage G:
  verify theorem and value alignment

Stage H:
  export final demo

Stage I:
  write report-hack-009.md

Stage J:
  stop
```

### Required Limitation Statements

```text
finite theorem
fresh rather than primitive
geometry does not cause factorization
no Collatz convergence claim
projection is future work unless verified
```

### Verification Level

```text
Level 5
```

### Completion Conditions

```text
final video exports
all claims have formal or interpretive classification
actual theorem names appear
actual build output appears
duration meets submission needs
captions are readable
```

### Prohibited Scope

```text
no new theorem implementation
no theorem renaming
no new mathematical branch
```

### Required Report

```text
report-hack-009.md
```

---

## 29. Checkpoint `hack-010` — Submission Packaging

### Class

```text
SUBMISSION
```

### Status

```text
PLANNED
```

### Prerequisites

```text
formal MVP secured
primary video complete
public theorem names frozen
repository branch ready
```

### Primary Goal

Produce a reproducible public hackathon submission.

### Required Deliverables

```text
public branch
final README
project description
demo video
thumbnail
screenshots
Lean build instructions
Manim render instructions
formal theorem summary
AI workflow explanation
limitations
credits
```

### Required Reproduction Tests

```text
branch checkout
focused Lean builds
Demo.lean build
no-sorry audit
git diff check
Manim environment setup
Manim render command
video playback
public links
```

### Required Stages

```text
Stage A:
  freeze repository state

Stage B:
  test Lean reproduction path

Stage C:
  test Manim reproduction path

Stage D:
  finalize README and project text

Stage E:
  upload video and images

Stage F:
  verify all links

Stage G:
  complete submission form

Stage H:
  write report-hack-010.md

Stage I:
  stop
```

### Verification Level

```text
Level 6
```

### Completion Conditions

```text
repository is accessible
build instructions are tested
render instructions are tested
video is accessible
submission text is accurate
limitations are explicit
form is submitted
```

### Prohibited Scope

```text
no new stretch mathematics
no theorem renaming
no major visual redesign
no repository-wide refactor
```

### Required Report

```text
report-hack-010.md
```

---

# Repair and Revision Checkpoints

## 30. Repair Checkpoint Conditions

A repair checkpoint is created only when:

```text
the previous checkpoint target is fundamentally sound
the remaining issue is bounded
the mathematical contract does not need redesign
```

Examples:

```text
fix one import
repair one Lean coercion bridge
rename one theorem before freeze
update one alignment table
repair one Manim render error
```

A repair checkpoint must not include adjacent enhancements.

---

## 31. Repair Checkpoint Template

````md
# Checkpoint hack-XXX — Repair

## Parent Checkpoint

```text
hack-YYY
```

## Repair Class

```text
LEAN / IMPORT / NAMING / DOCUMENTATION / VISUAL / INTEGRATION
```

## Exact Defect

State one defect.

## Permitted Files

List the smallest file set.

## Required Result

State the exact corrected artifact.

## Prohibited Scope

No new theorem or feature unless essential to the repair.

## Verification Gates

List focused checks.

## Stopping Rule

Stop if the repair reveals a new mathematical or architecture obstruction.

## Required Report

```text
report-hack-XXX.md
```
````

---

## 32. Contract-Change Checkpoints

A contract-change checkpoint is required when:

```text
the theorem assumptions change
the theorem conclusion changes
the fixed demo values change
the projection convention changes
the dependency direction changes
the public contribution claim changes
```

Before implementation:

```text
create a new ADR
update MATHEMATICAL_CONTRACT.md
update affected roadmap and demo documents
review the change
```

Codex may propose a change.

Codex may not implement it first and document it afterward.

---

# Report Registry

## 33. Report Paths

All hackathon checkpoint reports live under:

```text
docs/hackathon/cosmic-formula-inversion-260715/
```

Planned reports:

```text
report-hack-000.md
report-hack-001.md
report-hack-002.md
report-hack-003.md
report-hack-004.md
report-hack-005.md
report-hack-006.md
report-hack-007a.md
report-hack-007b.md
report-hack-007c.md
report-hack-007d.md
report-hack-007e.md
report-hack-008.md
report-hack-009.md
report-hack-010.md
```

Reports must not overwrite historical reports.

Corrections use a later report or review.

---

## 34. Checkpoint Report Template

````md
# Report — Checkpoint hack-XXX

## Status

```text
COMPLETED / STOPPED
```

## Session

```text
Class:
Model:
Reasoning level:
Session identifier:
Start:
End:
Elapsed:
Starting credits:
Ending credits:
Credits consumed:
```

## Primary Goal

Restate the checkpoint goal.

## Files Inspected

- exact paths

## Files Changed

- exact paths

## Definitions Added

- exact declaration names

## Theorems Added

- exact declaration names

## Existing APIs Reused

- declaration
- module
- role

## Verification

```text
command:
result:
```

## Mathematical Meaning

State exactly what is now verified.

## Meaning Boundary

State the stronger claims not proved.

## First Genuine Obstruction

State one exact obstruction or `none`.

## Out-of-Scope Work Not Taken

- adjacent routes deliberately avoided

## Next Permitted Action

State one bounded next action.

## Stop Confirmation

Confirm that no later checkpoint work was begun.
````

---

## 35. Review Record Template

````md
# Review — Checkpoint hack-XXX

## Outcome

```text
ACCEPT
ACCEPT_WITH_CONDITIONS
RETURN_FOR_REVISION
ACCEPT_STOPPING_POINT
```

## Core Judgment

State whether the checkpoint advances the intended theorem path.

## Mathematical Review

- theorem meaning
- hypotheses
- conclusion
- strength boundary

## Architecture Review

- module placement
- dependency direction
- reuse quality
- public facade quality

## Presentation Review

- naming
- comments
- demo suitability

## Genuine Obstruction Review

State whether the reported obstruction is the true first missing bridge.

## Required Corrections

- bounded items only

## Next Checkpoint

State the next permitted checkpoint and its primary goal.
````

---

# Checkpoint State Transitions

## 36. Normal State Transition

```text
PLANNED
→ READY
→ IN_PROGRESS
→ COMPLETED
→ ACCEPTED
```

or:

```text
PLANNED
→ READY
→ IN_PROGRESS
→ STOPPED
→ ACCEPT_STOPPING_POINT
```

---

## 37. Revision Transition

```text
IN_PROGRESS
→ COMPLETED
→ RETURNED
→ new repair checkpoint
```

Do not reopen the original checkpoint identifier.

---

## 38. Deferred Transition

```text
PLANNED
→ DEFERRED
```

A deferred checkpoint may later become:

```text
DEFERRED
→ READY
```

only after prerequisites and resource conditions are rechecked.

---

## 39. Cancellation Transition

```text
PLANNED
→ CANCELLED
```

Use cancellation when a later accepted decision removes the checkpoint from the project.

The record remains in this document with its reason.

---

# Resource Gates

## 40. Pre-Session Credit Gate

Before a Codex checkpoint begins, record:

```text
current balance
estimated checkpoint cost
required integration reserve
maximum acceptable session duration
```

Do not start when the estimated session would consume the integration reserve.

---

## 41. Mid-Session Resource Stop

Stop the current Codex session when:

```text
credits exceed the checkpoint budget
the same search repeats without progress
the task expands beyond permitted files
a genuine obstruction is already known
```

Write a partial report before further planning.

---

## 42. Final Integration Reserve

The project must preserve sufficient credits for:

```text
final Lean repair
Manim repair
integration
reproduction fixes
submission packaging
```

The exact reserve is recorded in `CODEX_PLAN.md`.

Stretch checkpoints cannot consume the reserve without a new decision.

---

# MVP Gates

## 43. Documentation Gate

Pass when:

```text
hack-000 accepted
```

Unlocks:

```text
hack-001
```

---

## 44. Audit Gate

Pass when:

```text
hack-001 accepted
```

Unlocks:

```text
hack-002
hack-003
```

The audit review determines their order if repository dependencies differ from the provisional roadmap.

---

## 45. Formal Core Gate

Pass when:

```text
hack-002 accepted
hack-003 accepted
hack-004 accepted
```

Unlocks:

```text
hack-008
```

Also marks:

```text
FORMAL_MVP = SECURED
```

---

## 46. Stretch Gate

Pass when:

```text
FORMAL_MVP = SECURED
credit reserve remains sufficient
submission schedule remains safe
```

May unlock:

```text
hack-005
hack-006
hack-007*
```

These checkpoints remain optional.

---

## 47. Visual Gate

Pass when:

```text
hack-008 accepted
```

Unlocks:

```text
hack-009
```

---

## 48. Submission Gate

Pass when:

```text
hack-009 accepted
```

Unlocks:

```text
hack-010
```

No new mathematics should begin after this gate.

---

# Scope Firewall

## 49. Prohibited Adjacent Research

No hackathon checkpoint may begin new work on:

```text
Collatz convergence
Riemann hypothesis
ABC conjecture
Fermat's Last Theorem
Erdős open problems
prime-density asymptotics
general primitive-divisor theory
aperiodic tilings
cryptographic security
general DkMath refactoring
```

Existing declarations from these areas may be reused only when directly required by the current contract.

---

## 50. Collatz Footage Boundary

The existing Collatz cp-320 recording is a supporting artifact.

No checkpoint in this registry authorizes further Collatz implementation.

Its permitted uses are:

```text
short agent-capability excerpt
proof-repair example
genuine-obstruction example
```

Required limitation:

```text
No Collatz convergence claim is made.
```

---

# Current Action

## 51. Immediate Remaining Work in `hack-000`

The remaining Phase 0 documents are:

```text
CODEX_PLAN.md
```

After it is drafted:

```text
cross-document consistency review
report-hack-000.md
hack-000 acceptance
```

Then the first Codex instruction may be issued for:

```text
hack-001 — repository audit
```

---

## 52. First Codex Session Boundary

The first Codex session must:

```text
read the stable document prefix
read repository instructions
inspect source and theorem databases
update EXISTING_DKMATH_MAP.md
write report-hack-001.md
stop
```

It must not:

```text
edit Lean source
prove a theorem
create a new module
begin Manim work
change the mathematical contract
```

---

## 53. Checkpoint Summary

The active project sequence is:

```text
hack-000
stable project context

hack-001
repository audit

hack-002
finite prime escape

hack-003
Cosmic Formula completion

hack-004
fixed Lean demo

hack-008
Manim theorem visualization

hack-009
unified demo

hack-010
submission
```

The optional stronger sequence is:

```text
hack-005
bounded projection

hack-006
exact inverse

hack-007a–hack-007e
DkReal reconstruction
```

The central checkpoint rule is:

```text
one goal
one bounded scope
one exact report
one stopping point
```

The central success rule is:

```text
complete the checkpoint
or
isolate the first genuine obstruction
```

The central project rule is:

```text
protect the verified MVP
```
