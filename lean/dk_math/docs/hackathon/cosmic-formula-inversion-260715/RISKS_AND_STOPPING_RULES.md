# Risks and Stopping Rules

## DkMath — Cosmic Formula Inversion

This document defines the conditions under which the project must:

- continue;
- narrow scope;
- isolate a missing theorem;
- defer a phase;
- preserve the minimum viable project;
- stop Codex execution;
- stop research expansion;
- begin submission packaging.

The project treats stopping as a controlled research result, not as failure.

A checkpoint is successful when it either:

```text
completes its stated target
```

or:

```text
isolates the first genuine obstruction with enough precision to design the next theorem
```

Codex must not cross a stopping boundary merely because additional exploration appears possible.

---

## 1. Purpose

The project is built on a large and active formal mathematics repository.

Without explicit stopping rules, a small hackathon task can expand into:

```text
general number theory
Cosmic Formula refactoring
DkReal infrastructure
formal Euclidean geometry
major open problems
repository-wide cleanup
visual experimentation
```

This document protects:

- the mathematical contract;
- the working branch;
- Codex credits;
- the submission deadline;
- the verified minimum viable result;
- the distinction between engineering and mathematical obstacles.

---

## 2. Governing Principle

The global rule is:

> Stop at the first genuine obstruction that lies outside the current checkpoint contract.

Do not continue by:

- inventing an adjacent theory;
- weakening the theorem silently;
- replacing proof with computation;
- broadening imports until the result accidentally builds;
- modifying foundational DkMath APIs without authorization;
- turning a local bridge into a repository refactor;
- claiming a stronger result than Lean proves.

At every stopping point, record:

```text
what was attempted
what Lean accepted
what failed
why the failure is genuine
the smallest missing theorem or invariant
the exact files involved
the next permitted action
```

---

## 3. Obstacle Classification

Before stopping, classify the obstacle.

### 3.1. Local Lean Engineering Obstacle

Examples:

```text
missing import
namespace mismatch
incorrect theorem name
coercion normalization
Nat subtraction issue
typeclass inference failure
local tactic failure
finite-set syntax issue
```

Required response:

```text
repair inside the current checkpoint
```

Do not stop immediately unless repeated repair reveals a deeper incompatibility.

---

### 3.2. Repository Discovery Obstacle

Examples:

```text
candidate theorem exists but cannot be located
several similar APIs have unclear semantics
source database and module structure disagree
import path is uncertain
```

Required response:

```text
search the repository
inspect theorem statements
inspect direct dependencies
update EXISTING_DKMATH_MAP.md
```

Stop only when the remaining uncertainty requires design review rather than additional search.

---

### 3.3. Mathematical Obstacle

Examples:

```text
a required implication is false without an additional hypothesis
a requested injection has no evident invariant
existence is available but uniqueness is missing
a bound required for reconstruction is unavailable
the theorem requires a genuinely new lemma
```

Required response:

```text
stop
state the smallest missing theorem
do not replace it with a numerical experiment
```

---

### 3.4. Architecture Obstacle

Examples:

```text
core DkMath would need to import the hackathon facade
a dependency cycle would be created
a public theorem requires a large unrelated module
a new abstraction duplicates an existing hierarchy
the chosen domain is incompatible with required APIs
```

Required response:

```text
stop
report the dependency graph
propose the smallest architecture correction
```

---

### 3.5. Scope Obstacle

Examples:

```text
the task expands into Collatz
the task expands into a prime-distribution theorem
formal geometry becomes the main workload
DkReal reconstruction requires a new real-number framework
the visualization becomes a separate research project
```

Required response:

```text
stop
return to the current phase objective
defer the adjacent research direction
```

---

### 3.6. Resource Obstacle

Examples:

```text
Codex credit consumption exceeds the checkpoint budget
the submission reserve is threatened
rendering time blocks integration
a session repeatedly explores without producing a theorem surface
```

Required response:

```text
stop the session
preserve the current state
write a partial report
replan outside Codex
```

---

## 4. Global Stop Conditions

The entire project must stop expanding and enter submission mode when any of the following occurs.

```text
the verified MVP is complete and the deadline is near
remaining credits are needed for integration or repair
the next theorem is not required by the public story
the next phase is a new research program
visual complexity no longer improves comprehension
a stable demo exists and later work risks breaking it
submission packaging becomes the critical path
```

At that point:

```text
freeze theorem names
freeze demo constants
freeze visual semantics
run final builds
render final video
complete documentation
prepare submission
```

---

## 5. Minimum Viable Project Protection

The MVP consists of:

```text
finite prime escape theorem
Cosmic Formula completion theorem
concrete Demo.lean
Manim visualization
recorded Codex workflow
submission documentation
```

Once the MVP build passes, create or identify a known-good commit.

After that point, every stretch checkpoint must satisfy:

```text
the MVP modules remain unchanged unless explicitly authorized
Demo.lean still builds
the fixed numerical example remains unchanged
new imports do not destabilize the public facade
the known-good commit remains recoverable
```

If a stretch phase threatens the MVP:

```text
stop
revert or isolate the stretch work
continue submission from the known-good commit
```

---

## 6. Credit Protection Rules

Codex credits are reserved for repository-dependent execution.

### Permitted High-Value Uses

```text
repository audit
Lean theorem implementation
Lean proof repair
Manim source implementation
integration
final build repair
```

### Prohibited Low-Value Uses

```text
drafting ordinary prose
repeating project documents
speculative mathematical brainstorming
unbounded theorem search without a target
repository-wide stylistic cleanup
rewriting accepted reports
```

### Session Budget Rule

Before each Codex session, record:

```text
starting credits
session class
primary goal
maximum acceptable scope
required reserve after completion
```

After each session, record:

```text
ending credits
credits consumed
elapsed time
result
first genuine obstruction
```

### Credit Emergency Stop

Stop immediately when:

```text
the session exceeds its planned budget without closing a stage
the agent repeats equivalent searches
the agent begins unrelated implementation
the remaining balance threatens final integration
```

The early-reset mechanism is emergency reserve, not planned routine capacity.

---

## 7. Documentation Phase Risks

### Risk DOC-001 — Documentation Expands into a Complete DkMath Treatise

Trigger:

```text
documents begin explaining unrelated DkMath branches
the same concept is repeated across many files
new terms are introduced without implementation relevance
```

Response:

```text
stop expanding
move nonessential material to historical notes
retain only project-facing definitions
```

Completion boundary:

```text
Codex can understand the project, theorem contract, architecture, and stopping rules without further conceptual invention
```

---

### Risk DOC-002 — Documents Contradict One Another

Trigger:

```text
different projection conventions appear
different demo values appear
fresh and primitive are conflated
MVP and stretch requirements disagree
```

Response:

```text
stop implementation
resolve the contradiction in DECISIONS.md
update dependent documents
```

No Codex session should begin while a binding contradiction remains.

---

### Risk DOC-003 — Historical Files Are Mistaken for Current Instructions

Trigger:

```text
Codex follows 1st_PLAN.md instead of the current checkpoint
an old report overrides a later decision
```

Response:

```text
preserve the historical file
clarify current authority in README.md
state the current instruction path explicitly
```

---

### Risk DOC-004 — Tracking Anchors Are Deleted or Inspected Repeatedly

Trigger:

```text
UUID-named empty files are treated as junk
Codex repeatedly opens them
content is added to them
```

Response:

```text
stop
restore the anchor
restate ADR-016
```

---

## 8. Repository Audit Risks

### Risk AUD-001 — Audit Turns into Implementation

Trigger:

```text
Lean source files are edited
new theorem declarations are created
proof attempts begin
```

Response:

```text
stop immediately
revert unauthorized source edits
record findings only
```

The audit phase ends with a report, not code.

---

### Risk AUD-002 — Search Is Too Broad

Trigger:

```text
Codex scans unrelated research branches without a direct concept target
the audit becomes a repository summary
```

Response:

```text
restrict search to terms in MATHEMATICAL_CONTRACT.md
record only declarations relevant to the current theorem surface
```

---

### Risk AUD-003 — Similar Names Are Treated as Equivalent

Trigger:

```text
a theorem is selected because its name sounds relevant
FreshPrimeFactor is confused with primitive divisors
Big / Body / Gap declarations from incompatible domains are merged
```

Response:

```text
inspect exact types
inspect hypotheses
inspect conclusions
classify as REJECTED when semantics differ
```

---

### Risk AUD-004 — Broad `import DkMath` Hides True Dependencies

Trigger:

```text
the proposed facade imports the entire library without analysis
required declarations cannot be traced to their modules
```

Response:

```text
identify direct source modules
record broad import only as a temporary audit convenience
```

Import minimization may wait until theorem completion, but true dependencies must be known.

---

### Risk AUD-005 — No Exact Existing Theorem Is Found

Trigger:

```text
search exhausts relevant modules
only partial lemmas exist
```

Response:

```text
classify the smallest missing result as MISSING
state its proposed theorem shape
stop the audit
```

Do not implement it during the audit.

---

## 9. Finite Prime Escape Risks

### Risk FPE-001 — Product Representation Mismatch

Trigger:

```text
existing theorem uses a different Finset product form
binder syntax causes incompatible rewriting
product is stored through a wrapper structure
```

Response:

```text
seek a thin bridge theorem
avoid creating a second product definition
```

Stop if the bridge requires a foundational refactor.

---

### Risk FPE-002 — Unnecessary Prime Hypotheses Are Added

Trigger:

```text
a local divisibility lemma assumes every member of S is prime
positivity is added where coprimality alone is sufficient
nonempty S is added without use
```

Response:

```text
separate local and public theorem layers
remove unused assumptions
report the logical role of each hypothesis
```

---

### Risk FPE-003 — Exclusion and Existence Are Conflated

Trigger:

```text
the theorem assumes a prime divisor but is described as proving existence
a size condition is added to the supplied-divisor theorem
```

Response:

```text
split the theorem surface
```

Required layers:

```text
given prime divisor is outside S
a fresh prime divisor exists when 1 < P + u
```

---

### Risk FPE-004 — Freshness Is Replaced by Primitiveness

Trigger:

```text
sequence-relative terminology enters theorem names or reports
earlier-stage conditions are implied but not present
```

Response:

```text
stop
rename to fresh
restore the mathematical contract
```

---

### Risk FPE-005 — A Numerical Proof Replaces the General Theorem

Trigger:

```text
only P = 210 and u = 11 are proved
the general theorem is deferred without reporting an obstruction
```

Response:

```text
stop the demo implementation
return to the general theorem
```

The concrete example supplements the general theorem.

---

### Risk FPE-006 — Prime-Divisor Existence Requires an Unexpected Large Bridge

Trigger:

```text
available existence theorem uses an incompatible factorization framework
constructive extraction becomes a major task
```

Response:

```text
retain the universal supplied-divisor theorem
isolate the missing existence bridge
stop
```

A supplied-divisor theorem may still form a valid intermediate checkpoint.

---

### Risk FPE-007 — Theorem Is Overgeneralized

Trigger:

```text
Codex begins abstracting over arbitrary commutative monoids
the task moves from Nat divisibility into generic algebra
```

Response:

```text
stop abstraction
return to ℕ unless an existing generic theorem can be reused directly
```

---

## 10. Cosmic Completion Risks

### Risk CC-001 — Parallel Big / Body / Gap Hierarchy

Trigger:

```text
new foundational structures duplicate existing DkMath declarations
the hackathon layer defines a second Cosmic Formula framework
```

Response:

```text
stop
audit existing declarations
prefer aliases, wrappers, or local notation
```

---

### Risk CC-002 — Arithmetic Identity Becomes Formal Euclidean Geometry

Trigger:

```text
the proof begins defining rectangles, polygons, congruence, or area measure
```

Response:

```text
stop
return to the arithmetic equality
defer Euclidean dissection
```

The MVP requires only:

$$
P(P+2u)+u^2=(P+u)^2
$$

---

### Risk CC-003 — Deep Existing API Is More Expensive Than a Thin Ring Wrapper

Trigger:

```text
reusing a generic DkMath abstraction requires many coercions or unrelated imports
the proof surface becomes less readable than the identity
```

Response:

```text
use a local theorem proved by ring
document why the deeper bridge was rejected or deferred
```

The public theorem may remain thin even when broader DkMath theory exists.

---

### Risk CC-004 — Geometry Is Said to Produce Primes

Trigger:

```text
comments, narration, or theorem documentation imply causal prime generation
```

Response:

```text
stop presentation work
restore the arithmetic–geometry boundary
```

Approved wording:

```text
the completed boundary has prime factors outside the original set
```

---

### Risk CC-005 — Nat Subtraction Is Introduced Unnecessarily

Trigger:

```text
Body is defined as Big - Gap in Nat
truncated subtraction complicates the theorem
```

Response:

```text
prefer the additive identity
```

---

## 11. Demo Module Risks

### Risk DEMO-001 — Demo Reproves General Theory Numerically

Trigger:

```text
norm_num proves freshness without invoking the general theorem
the demo does not visibly reuse the facade
```

Response:

```text
stop
rewrite the demo to apply the general theorem
use automation only for concrete arithmetic
```

---

### Risk DEMO-002 — Demo Values Drift

Trigger:

```text
a different prime set appears
u changes from 11
boundary changes from 221
only one fresh factor is shown
```

Response:

```text
stop
restore ADR-006
update no visual or formal layer independently
```

---

### Risk DEMO-003 — Public Surface Becomes Too Large

Trigger:

```text
Demo.lean contains exploratory helpers
many internal lemmas obscure the final result
```

Response:

```text
move general helpers to their owning modules
keep Demo.lean presentation-focused
```

---

### Risk DEMO-004 — One Giant Bundled Theorem Hides the Story

Trigger:

```text
all facts are packed into an unreadable conjunction
individual results cannot be shown in the video
```

Response:

```text
expose small named theorems
retain a bundle only as an optional final summary
```

---

### Risk DEMO-005 — Theorem Names Change After Recording

Trigger:

```text
public names are renamed after screenshots or video overlays exist
```

Response:

```text
stop renaming
freeze the public theorem surface after acceptance
```

---

## 12. Projection Risks

### Risk PROJ-001 — Both Signed and Unsigned Conventions Are Implemented

Trigger:

```text
two parallel APIs appear
documentation alternates between intervals
inverse formulas duplicate
```

Response:

```text
stop
select one convention through DECISIONS.md
remove or isolate the unselected experiment
```

---

### Risk PROJ-002 — Projection Begins Before MVP Security

Trigger:

```text
projection files are created before Demo.lean builds
finite theorem remains incomplete
```

Response:

```text
stop
return to the MVP sequence
```

---

### Risk PROJ-003 — Natural-Number Division Is Used for Normalization

Trigger:

```text
P / (P + u) is interpreted in Nat
the projected value collapses to zero
```

Response:

```text
stop
move the definition to ℚ or the selected exact field
```

---

### Risk PROJ-004 — Real Analysis Is Introduced Too Early

Trigger:

```text
continuity, topology, or limits appear before the rational identity is complete
```

Response:

```text
stop
prove the exact rational theorem first
```

---

### Risk PROJ-005 — Endpoint Surjectivity Is Overclaimed

Trigger:

```text
finite P is claimed to attain the limiting endpoint
the map is called bijective onto a closed interval without proof
```

Response:

```text
stop
state the exact image or restrict the inverse theorem to the image
```

---

### Risk PROJ-006 — Linear Gap and Square Gap Are Confused

Trigger:

```text
u / (P + u) is identified with u² / (P + u)²
```

Response:

```text
stop
separate the definitions
prove the square relation explicitly
```

---

### Risk PROJ-007 — Coercion Proofs Dominate the Public API

Trigger:

```text
public theorem statements expose large cast expressions
most code is domain-conversion repair
```

Response:

```text
isolate casts in helper lemmas
stop if the chosen domain is architecturally unsuitable
```

---

## 13. Inverse Projection Risks

### Risk INV-001 — Denominator Conditions Are Hidden

Trigger:

```text
division by 1 - x or 1 + x occurs without a nonzero proof
```

Response:

```text
stop
make the domain condition explicit
```

---

### Risk INV-002 — Algebraic Rearrangement Is Called Complete Inversion

Trigger:

```text
only one formula equality is proved
injectivity, image restriction, or inverse laws are absent
```

Response:

```text
rename the result accurately
separate formula, left inverse, right inverse, and injectivity
```

---

### Risk INV-003 — Surjectivity Beyond the Image Is Attempted

Trigger:

```text
the proof seeks a preimage for arbitrary interval values
```

Response:

```text
stop
prove the inverse only on the forward image unless broader surjectivity is part of a reviewed contract
```

---

### Risk INV-004 — Fixed `u` Is Forgotten

Trigger:

```text
injectivity is claimed while both P and u vary freely
```

Response:

```text
stop
fix positive u or state the correct pair-level theorem
```

---

### Risk INV-005 — Exact and Interval Reconstruction Are Merged

Trigger:

```text
an approximate interval theorem is used as an exact inverse
```

Response:

```text
stop
separate the phases
```

---

## 14. DkReal Risks

### Risk DKR-001 — Parallel DkReal Framework

Trigger:

```text
new nested interval types are defined
new real-number constructors appear
```

Response:

```text
stop immediately
audit existing DkReal APIs
```

---

### Risk DKR-002 — Missing Interval Map Operation

Trigger:

```text
the inverse cannot be applied to existing intervals
monotonicity direction is unavailable
```

Response:

```text
stop
state the exact interval-map bridge required
```

---

### Risk DKR-003 — Width Transport Is Missing

Trigger:

```text
mapped interval containment is proved but no width bound follows
```

Response:

```text
stop
isolate the missing Lipschitz, monotonicity, or endpoint theorem
```

---

### Risk DKR-004 — Width Less Than One Is Treated as Existence

Trigger:

```text
at-most-one integer becomes exactly one integer
```

Response:

```text
stop
separate existence from uniqueness
```

---

### Risk DKR-005 — Floor and Ceiling Become a New Infrastructure Project

Trigger:

```text
the checkpoint begins rebuilding floor, ceil, or integer interval cardinality
```

Response:

```text
stop
identify the smallest missing Mathlib or DkMath bridge
defer the phase
```

---

### Risk DKR-006 — Stretch Work Threatens Submission

Trigger:

```text
DkReal work consumes the integration reserve
the MVP is no longer the current focus
```

Response:

```text
stop the stretch phase
return to the secured MVP
```

---

## 15. Visualization Risks

### Risk VIS-001 — Visual Story Diverges from Lean

Trigger:

```text
different constants appear
an unproved implication is animated
freshness is shown without coprimality
```

Response:

```text
stop rendering
compare every scene with DEMO_CONTRACT.md
```

---

### Risk VIS-002 — Geometry Claims More Than the Arithmetic Identity

Trigger:

```text
the animation implies formal area dissection
the Gap is shown as causing factorization
```

Response:

```text
simplify the narration
label the scene as visualization of the identity
```

---

### Risk VIS-003 — Scene Becomes Too Long

Trigger:

```text
the main sequence exceeds approximately sixty seconds
multiple side stories are added
```

Response:

```text
remove nonessential scenes
preserve the fixed nine-step route
```

---

### Risk VIS-004 — Prime Spirals, Tilings, or Circular Sectors Take Over

Trigger:

```text
the animation shifts to unrelated geometric research
```

Response:

```text
stop
move experiments to future-work material
```

---

### Risk VIS-005 — Equations Become Unreadable

Trigger:

```text
text is too small
too many simultaneous formulas appear
transitions are faster than reading time
```

Response:

```text
reduce content
split scenes
prioritize the shared boundary value
```

---

### Risk VIS-006 — Color Semantics Drift

Trigger:

```text
Gap and Body exchange colors
fresh primes use the known-prime color
Lean verification lacks a consistent signal
```

Response:

```text
stop final rendering
restore the palette contract
```

---

### Risk VIS-007 — Manim Environment Becomes a Packaging Project

Trigger:

```text
custom rendering infrastructure or web deployment is added
```

Response:

```text
stop
use a standard reproducible local render command
```

---

### Risk VIS-008 — Automatic Lean-to-Python Extraction Expands Scope

Trigger:

```text
cross-language code generation becomes necessary for the demo
```

Response:

```text
stop
use manually synchronized constants for the MVP
```

---

## 16. Agent Behavior Risks

### Risk AGENT-001 — Codex Ignores the Reading Order

Trigger:

```text
implementation begins before documents are read
accepted decisions are contradicted
```

Response:

```text
stop the session
restart with the stable prefix
```

---

### Risk AGENT-002 — Codex Treats a Plan as Permission to Implement All Phases

Trigger:

```text
one session edits arithmetic, projection, DkReal, and Manim
```

Response:

```text
stop
revert out-of-scope edits
retain only the current checkpoint work
```

---

### Risk AGENT-003 — Codex Continues Past a Stopping Rule

Trigger:

```text
a genuine obstruction is identified but adjacent exploration continues
```

Response:

```text
terminate the session
preserve the obstruction report
```

---

### Risk AGENT-004 — Codex Silently Changes the Contract

Trigger:

```text
hypotheses are added or removed
the theorem is weakened
terminology changes
demo constants change
```

Response:

```text
stop
return the checkpoint for revision
record any proposed contract change in DECISIONS.md
```

---

### Risk AGENT-005 — Codex Refactors Unrelated Code

Trigger:

```text
large changes occur outside permitted files
style cleanup appears in core modules
```

Response:

```text
stop
revert unrelated changes
narrow file permissions in the next instruction
```

---

### Risk AGENT-006 — Codex Repeats Failed Search Patterns

Trigger:

```text
the same theorem queries and files are revisited without new information
```

Response:

```text
stop
summarize the search boundary
classify the declaration as missing or unresolved
```

---

### Risk AGENT-007 — Progress Reports Become Vague

Trigger:

```text
report says “mostly complete”
remaining theorem is not named
build gates are unclear
```

Response:

```text
require exact declarations, files, and obstruction statements
```

---

### Risk AGENT-008 — Agent Claims Success from Numerical Tests

Trigger:

```text
examples pass but the general theorem is absent
```

Response:

```text
reject the checkpoint
return to the theorem contract
```

---

## 17. Lean Verification Risks

### Risk LEAN-001 — `sorry` or `admit` Appears in New Public Modules

Trigger:

```text
unfinished proof placeholders are present
```

Response:

```text
checkpoint cannot be accepted
repair or stop at the missing theorem
```

---

### Risk LEAN-002 — Axiom Is Added to Bypass the Goal

Trigger:

```text
new axiom or unsafe assumption replaces proof
```

Response:

```text
reject the checkpoint
remove the axiom
report the actual obstruction
```

---

### Risk LEAN-003 — Only a Focused File Builds

Trigger:

```text
the target module passes but Demo.lean or the relevant aggregate fails
```

Response:

```text
repair within checkpoint scope
or report the integration obstruction
```

---

### Risk LEAN-004 — Broad Imports Hide a Name Collision

Trigger:

```text
the module builds only under `import DkMath`
narrow imports expose ambiguity or missing dependency
```

Response:

```text
record the dependency
narrow imports before final submission when practical
```

---

### Risk LEAN-005 — The Statement Builds but Means the Wrong Thing

Trigger:

```text
Nat division truncates
freshness is encoded incorrectly
membership uses the wrong set
the fixed boundary is not P + u
```

Response:

```text
reject despite build success
correct the theorem statement
```

Lean verification validates the encoded proposition, not the intended prose.

---

### Risk LEAN-006 — Concrete Automation Hides General Reuse

Trigger:

```text
the demo passes entirely by decide or norm_num
```

Response:

```text
require explicit use of the general theorem in at least one public demo result
```

---

## 18. Submission Risks

### Risk SUB-001 — Submission Overstates Mathematical Novelty

Trigger:

```text
finite prime escape is presented as a new theorem
the project claims a new proof of prime infinitude
```

Response:

```text
stop publication
correct the contribution statement
```

---

### Risk SUB-002 — Open Problems Are Implied Solved

Trigger:

```text
Collatz footage appears without limitation text
DkMath research branches are described as completed
```

Response:

```text
add explicit scope language
remove misleading scenes
```

---

### Risk SUB-003 — Demo Cannot Be Reproduced

Trigger:

```text
build command is missing
toolchain version is unclear
Manim render command fails
```

Response:

```text
stop submission
repair reproduction instructions
```

---

### Risk SUB-004 — Repository Entry Path Is Too Complex

Trigger:

```text
judges must inspect the entire DkMath library to find the demo
```

Response:

```text
simplify README links
point directly to Demo.lean and the rendered video
```

---

### Risk SUB-005 — Process Overshadows the Result

Trigger:

```text
most of the video is Codex logs
the mathematical demo is too brief to understand
```

Response:

```text
restore balance
use agent footage as supporting evidence only
```

---

### Risk SUB-006 — Mathematics Overshadows the Developer Tool

Trigger:

```text
the submission looks like a theorem note with no agent workflow
```

Response:

```text
show the audit, implementation, Lean verification, and stopping-rule process
```

---

### Risk SUB-007 — Final Integration Begins Too Late

Trigger:

```text
stretch work continues while video and packaging remain incomplete
```

Response:

```text
stop stretch work
enter submission mode
```

---

## 19. Phase-Specific Stopping Rules

### Phase 0 — Documentation

Stop when:

```text
the project can be understood without new terminology
all binding documents exist
current contradictions are resolved
the first audit instruction is unambiguous
```

Do not continue documenting unrelated DkMath theory.

---

### Phase 1 — Repository Audit

Stop when:

```text
reusable APIs are classified
candidate imports are identified
the smallest missing theorem is stated
no Lean source has been edited
```

Do not implement.

---

### Phase 2 — Finite Prime Escape

Stop at the first of:

```text
general exclusion theorem completed
general existence theorem completed
existing predicate conflict discovered
prime-divisor existence bridge genuinely missing
dependency reversal required
```

Do not proceed to Cosmic Completion automatically.

---

### Phase 3 — Cosmic Completion

Stop at the first of:

```text
existing DkMath theorem reused
thin ring wrapper completed
parallel hierarchy would be required
formal geometry becomes necessary
```

Do not begin projection.

---

### Phase 4 — Demo

Stop when:

```text
fixed data is verified
general theorems are reused
public theorem surface builds
OBS-ready file exists
```

Do not add additional examples.

---

### Phase 5 — Projection

Stop at the first of:

```text
one convention selected and proved
existing projection API conflicts
coercion architecture becomes dominant
both conventions begin to coexist
```

---

### Phase 6 — Inverse

Stop at the first of:

```text
exact inverse completed
injectivity completed
domain mismatch discovered
surjectivity beyond image becomes necessary
```

---

### Phase 7 — DkReal

Stop at the first of:

```text
interval bridge completed
monotonicity bridge missing
width transport missing
integer uniqueness bridge missing
parallel DkReal framework would be required
```

Return to MVP when stopped.

---

### Phase 8 — Manim

Stop when:

```text
the primary sixty-second scene renders
all values match Lean
all claims match the contract
```

Do not expand into unrelated visual research.

---

### Phase 9 — Integration

Stop when:

```text
Lean, Manim, narration, and Codex footage align
the final duration is acceptable
the theorem names are frozen
```

No new mathematics after this point.

---

### Phase 10 — Submission

Stop only when:

```text
repository is accessible
build is reproducible
video is uploaded
submission form is complete
limitations are accurate
```

---

## 20. Required Stop Report Template

When a checkpoint stops at an obstruction, use:

````md
## Stopping Point

### Completed

- exact declarations or artifacts completed

### Failed Target

- exact theorem or artifact not completed

### Obstacle Class

```text
Lean engineering
repository discovery
mathematical
architecture
scope
resource
```

### First Genuine Obstruction

State one precise obstruction.

### Smallest Missing Theorem or Bridge

```lean
theorem proposed_name ...
```

or:

```text
exact missing API behavior
```

### Evidence

- relevant Lean goal
- relevant existing theorem
- incompatible types or hypotheses
- dependency path

### Out-of-Scope Routes Not Taken

- adjacent approaches deliberately avoided

### Current Build State

- focused module
- demo module
- no-sorry
- git diff

### Next Permitted Action

State one bounded next action.

### Prohibited Continuation

State what must not be attempted next.
````

---

## 21. Required Completion Report Template

When a checkpoint completes, use:

```md
## Completion

### Proved

- exact theorem list

### Reused

- exact existing declarations and modules

### Added

- files
- definitions
- theorems

### Mathematical Meaning

- exact statement now verified

### Meaning Boundary

- stronger claims not proved

### Verification

- focused build
- aggregate build
- no-sorry
- git diff check

### Resource Use

- model
- reasoning level
- elapsed time
- credits consumed
- session identifier

### Next Permitted Action

- one bounded next checkpoint
```

---

## 22. Review Outcomes

A stopped or completed checkpoint receives one of three review outcomes.

### Accept

Use when:

```text
the theorem matches the contract
architecture is sound
report is exact
```

### Accept with Conditions

Use when:

```text
the mathematics is correct
minor naming, documentation, or facade work remains
```

### Return for Revision

Use when:

```text
the statement is wrong
scope was exceeded
dependency rules were broken
proof was replaced by computation
meaning was overstated
```

A genuine obstruction report may be fully accepted even when the original target is not complete.

---

## 23. Escalation Rule

Escalate from Codex execution back to human–Wise Wolf planning when:

```text
the mathematical contract needs revision
a new ADR is required
two repository APIs are semantically incompatible
the next theorem changes the project story
a stretch phase threatens the MVP
the credit budget must be reallocated
```

Codex may recommend a decision.

Codex must not make a binding project decision independently.

---

## 24. Non-Negotiable Rules

The following rules cannot be bypassed inside a checkpoint.

```text
Do not delete tracking anchors.

Do not create reverse dependencies into core DkMath.

Do not replace the general theorem with the demo example.

Do not call fresh factors primitive without sequence-relative hypotheses.

Do not claim that geometry creates primes.

Do not claim open problems are solved.

Do not create a second DkReal framework.

Do not implement both projection conventions.

Do not continue past the first genuine obstruction.

Do not consume the final integration reserve on speculative work.

Do not weaken or strengthen the mathematical contract silently.
```

---

## 25. Final Stop Strategy

The project’s preferred stopping hierarchy is:

```text
Best case:
  MVP + projection + inverse + DkReal + visual + submission

Strong case:
  MVP + projection + inverse + visual + submission

Successful case:
  MVP + visual + submission

Emergency successful case:
  verified Lean demo + recorded Codex footage + clear documentation + submission
```

The project must prefer a complete lower tier over an unfinished higher tier.

A narrower verified result is better than a broad unverified narrative.

---

## 26. Summary

The central execution rule is:

```text
complete the bounded checkpoint
or
stop at the first genuine obstruction
```

The central scope rule is:

```text
protect the verified MVP
```

The central mathematical rule is:

```text
state exactly what Lean proves
```

The central architecture rule is:

```text
reuse DkMath through a thin downstream facade
```

The central resource rule is:

```text
reserve Codex for repository-dependent implementation
```

The central submission rule is:

```text
freeze expansion early enough to deliver a reproducible project
```

Stopping is not the absence of progress.

In this project, a precise stopping point is part of the verified research trace.
