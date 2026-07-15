# Codex Plan

## DkMath — Cosmic Formula Inversion

This document defines how Codex is used throughout the hackathon project.

It governs:

- repository investigation;
- Lean implementation;
- proof repair;
- Manim implementation;
- integration;
- reporting;
- credit conservation;
- stopping behavior.

This file is not itself a checkpoint instruction.

It defines the execution protocol from which each checkpoint-specific instruction is written.

The current checkpoint instruction is always read last and remains the immediate operational authority.

---

## 1. Plan Status

```text
DOCUMENT STATUS:
  INITIAL EXECUTION PLAN

CURRENT PROJECT PHASE:
  Phase 0 — stable documentation

CURRENT CHECKPOINT:
  hack-000

NEXT CODEX SESSION:
  hack-001 — repository audit

NEXT SESSION CLASS:
  AUDIT

LEAN SOURCE EDITING IN NEXT SESSION:
  prohibited

PRIMARY NEXT OUTPUT:
  EXISTING_DKMATH_MAP.md
  report-hack-001.md
```

---

## 2. Codex Mission

Codex is used as the repository-aware implementation agent for the project.

Its mission is:

```text
read the fixed mathematical contract
inspect the existing DkMath repository
identify the smallest reusable theorem route
implement only the missing bridge
verify the result with Lean
stop at the first genuine obstruction
report exactly what changed
```

Codex is not responsible for independently redefining:

- the project objective;
- the mathematical theorem contract;
- the fixed demo values;
- public terminology;
- submission claims;
- the distinction between MVP and stretch work.

Codex may recommend changes.

It may not silently apply them when they alter project meaning.

---

## 3. Human–AI–Lean Division of Work

### "D."

Responsible for:

```text
project ownership
mathematical direction
repository and branch control
recording Codex sessions
accepting or rejecting project decisions
visual judgment
final submission
```

### Wise Wolf

Responsible for:

```text
theorem-contract design
project architecture
checkpoint instruction design
Codex report review
mathematical interpretation
obstruction analysis
next-checkpoint design
submission narrative support
```

### Codex

Responsible for:

```text
repository search
source inspection
API comparison
Lean implementation
proof repair
build execution
bounded Manim implementation
factual checkpoint reporting
```

### Lean

Responsible for:

```text
formal type checking
proof validation
rejection of invalid formal claims
```

Lean is the final authority for the encoded theorem.

### Manim

Responsible for:

```text
visual explanation
motion
layout
equation transitions
presentation
```

Manim does not prove the theorem.

---

## 4. Core Codex Operating Rule

The principal execution rule is:

> Complete the bounded checkpoint, or stop at the first genuine obstruction.

Codex must not continue by:

- opening adjacent research;
- creating a parallel theory;
- weakening the theorem silently;
- replacing a general theorem with a numerical example;
- adding axioms;
- adding `sorry`;
- modifying unrelated files;
- performing repository-wide cleanup;
- consuming credits after the true obstruction is known.

A precise stopping point is a valid checkpoint result.

---

## 5. Stable Context Protocol

Every major Codex session begins with the same stable documentation prefix.

Required reading order:

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

The reading order separates:

```text
project identity
→ mathematical contract
→ roadmap
→ architecture
→ terminology
→ binding decisions
→ stopping rules
→ known repository map
→ visual contract
→ checkpoint registry
→ execution protocol
→ current task
```

The current instruction must remain the final document in the context sequence.

---

## 6. Repository Instruction Protocol

Before searching or editing DkMath, Codex must read the repository-level instructions.

Required files:

```text
README.md
AGENT.md
SUMMARY.md
```

The repository-specific instructions take precedence over generic implementation habits when they do not conflict with the hackathon mathematical contract.

The repository provides additional source databases:

```text
__dkmath-all.lean.txt.gz
__summary_report_data.tar.gz
__theorems-heading.txt
```

Codex should use them to reduce broad source traversal.

---

## 7. Source Database Protocol

### Lean Source Database

Use:

```bash
zgrep -n "SEARCH_TERM" __dkmath-all.lean.txt.gz
```

Use surrounding context only when needed:

```bash
zcat __dkmath-all.lean.txt.gz | sed -n 'START,ENDp'
```

Avoid decompressing the entire source database into a persistent duplicate file unless the checkpoint explicitly requires it.

### Theorem Heading Index

Search:

```bash
rg -n "SEARCH_TERM" __theorems-heading.txt
```

This index is preferred when declaration names are likely to be known or semantically close.

### Summary Report Archive

Inspect the archive:

```bash
tar -tf __summary_report_data.tar.gz
```

Read one report without extracting the full archive:

```bash
tar -xOf __summary_report_data.tar.gz PATH/TO/REPORT.txt
```

Extract only when repeated cross-report inspection materially benefits the current checkpoint.

### Search Order

Use:

```text
exact declaration search
→ theorem heading search
→ source database search
→ summary report search
→ direct module inspection
→ Mathlib inspection
```

---

## 8. Tracking Anchor Protocol

UUID-named empty files are intentional conversation-tracking anchors.

Example:

```text
6a54173a-e5f8-83ee-9983-6932a7be858c
```

Codex rules:

```text
confirm emptiness at most once when necessary
do not repeatedly open
do not delete
do not rename
do not add content
do not classify as junk
do not include in source-cleanup proposals
```

The filename is the metadata.

The empty content is intentional.

---

## 9. Session Classes

Every Codex session must declare one class before execution.

### Audit Session

```text
purpose:
  repository investigation

source edits:
  prohibited

expected output:
  theorem map
  import map
  audit report
```

### Implementation Session

```text
purpose:
  add a bounded theorem or source artifact

source edits:
  permitted only in listed files

verification:
  required
```

### Repair Session

```text
purpose:
  repair one known bounded defect

new scope:
  prohibited
```

### Review-Integration Session

```text
purpose:
  apply accepted naming, import, documentation, or API corrections

new mathematics:
  prohibited
```

### Visual Session

```text
purpose:
  implement or repair Manim scenes

formal theorem contract:
  already fixed
```

### Integration Session

```text
purpose:
  combine completed Lean, Manim, recording, and narration artifacts

new theorem work:
  prohibited
```

### Submission Session

```text
purpose:
  reproduce, package, and publish the completed project

new research:
  prohibited
```

---

## 10. Session Boundary Rule

One Codex session should normally perform one checkpoint.

A session must not combine:

```text
repository audit
Lean theorem implementation
projection research
DkReal research
Manim implementation
submission writing
```

unless the current checkpoint explicitly defines a narrow integration task involving already-completed artifacts.

The preferred session shape is:

```text
one primary goal
one bounded file set
one theorem or artifact surface
one build sequence
one report
one stopping point
```

---

## 11. Checkpoint Prompt Architecture

Every checkpoint-specific Codex instruction should contain the following sections.

```text
Checkpoint identifier
Session class
Primary goal
Current verified state
Required reading
Permitted files
Read-only files
Prohibited files
Required theorem or artifact surface
Existing APIs to inspect
Implementation stages
Verification commands
Completion conditions
Stopping conditions
Report path
Final stop instruction
```

The instruction must not rely on Codex inferring permissions from the roadmap.

Permissions must be explicit.

---

## 12. Recommended Checkpoint Instruction Skeleton

````md
# Checkpoint hack-XXX

## Session Class

```text
IMPLEMENTATION
```

## Primary Goal

State one bounded target.

## Current Verified State

List only facts established by accepted earlier checkpoints.

## Required Reading

Read the stable project prefix and the current instruction.

## Permitted Files

```text
exact file list
```

## Read-Only Files

```text
exact source families or documents
```

## Prohibited Scope

```text
adjacent work that must not begin
```

## Required Theorem Surface

```lean
theorem exact_target_shape ...
```

## Existing APIs to Inspect

- exact concept list

## Stages

### Stage A — Audit the immediate dependency surface

### Stage B — Implement the smallest local bridge

### Stage C — Expose the public theorem

### Stage D — Run focused verification

### Stage E — Run integration verification

### Stage F — Write the report

### Stage G — Stop

## Completion Conditions

- exact checklist

## Stopping Conditions

- first genuine obstruction list

## Required Report

```text
exact/path/report-hack-XXX.md
```

## Final Instruction

Stop after the report. Do not begin the next checkpoint.
````

---

## 13. Progress Reporting Protocol

Codex should provide concise milestone reports during execution.

Useful milestone reports include:

```text
stable documents read
repository instructions read
exact API candidate found
first theorem surface implemented
focused build passed
integration build passed
genuine obstruction isolated
report written
```

Progress reports should contain:

```text
what changed
what evidence exists
what remains
whether the stopping rule has triggered
```

The project does not require hidden chain-of-thought or raw private reasoning.

Codex should report:

```text
decisions
evidence
Lean goals
theorem dependencies
observed failures
implemented repairs
```

It should not be asked to expose private internal reasoning traces.

---

## 14. Context Compaction Protocol

Long Codex sessions may compact earlier context.

To protect the task after compaction, the current instruction must contain a compact execution kernel.

The execution kernel should repeat:

```text
checkpoint identifier
primary goal
permitted files
prohibited scope
required output
build gates
stopping rule
report path
```

Codex progress summaries should preserve these items.

After any context compaction, Codex must verify:

```text
current checkpoint
current permitted files
current stage
current first unresolved goal
current stopping condition
```

If any of these become ambiguous:

```text
stop
re-read the current instruction
do not infer scope from memory
```

---

## 15. File Permission Protocol

Each checkpoint must divide files into three groups.

### Permitted Edit Files

Codex may modify only these files.

### Read-Only Files

Codex may inspect but not modify these files.

### Prohibited Files

Codex must neither modify nor reformat these files.

The absence of a file from the permitted list means it is not editable.

Codex must not use a seemingly harmless edit to bypass this rule.

Examples of unauthorized edits:

```text
formatting an imported core module
renaming an existing theorem
changing a project contract
editing a historical report
deleting an empty tracking anchor
adding a top-level import
```

---

## 16. Git Protocol

Unless the current checkpoint explicitly authorizes it, Codex must not:

```text
create or switch branches
commit
push
pull
merge
rebase
reset
amend commits
change remotes
delete untracked files broadly
```

Codex may use read-only Git inspection:

```bash
git status --short
git diff --stat
git diff
git log --oneline -n 10
```

At checkpoint completion, Codex should report the working-tree state.

Any commit action remains under explicit user control unless separately authorized.

---

## 17. Lean Implementation Protocol

Before adding a declaration, Codex must determine whether the required result is:

```text
DIRECT
WRAPPER
COROLLARY
BRIDGE
MISSING
DEMO_ONLY
```

Preferred implementation order:

```text
1. direct reuse
2. theorem alias or wrapper
3. specialization
4. short local proof
5. genuinely new lemma
```

Codex must not begin with a new abstraction merely because it makes the local proof aesthetically uniform.

---

## 18. Weakest Practical Domain Rule

Use the weakest domain sufficient for the theorem.

```text
ℕ:
  finite products
  divisibility
  primes
  gcd
  concrete arithmetic
  square completion

ℤ:
  subtraction-sensitive bridges

ℚ:
  exact projection
  exact inverse
  interval calculations

ℝ:
  real-analysis compatibility
  limits
  continuous interpretation

DkReal:
  nested interval reconstruction
```

Do not lift discrete arithmetic into `ℝ` before the natural-number theorem is complete.

Do not define normalization through natural-number division.

---

## 19. Theorem Strength Protocol

Codex must prove the theorem actually requested.

It must not silently replace:

```text
general theorem
with
one numerical example
```

```text
existence
with
a supplied witness theorem
```

```text
universal freshness
with
one fresh factor
```

```text
at most one
with
exactly one
```

```text
left inverse
with
a rearranged formula
```

```text
image-restricted inverse
with
surjectivity onto a larger interval
```

Codex must also avoid unnecessary overgeneralization.

A small `Nat` theorem should not become a generic algebra hierarchy unless a directly reusable generic theorem already exists.

---

## 20. Assumption Audit Protocol

Every implementation report must identify the logical role of each hypothesis.

For the finite-prime theorem, inspect:

```text
all members of S are prime
S is nonempty
0 < u
0 < P
Nat.Coprime P u
1 < P + u
q is prime
q divides P + u
```

Classify each as:

```text
essential to the local theorem
essential only to existence
essential only to public interpretation
unnecessary
```

Do not retain assumptions solely because they sound natural.

---

## 21. Naming Protocol

Public theorem names should be:

```text
descriptive
mathematically standard
stable
independent of proof strategy
short enough for video display
```

Avoid:

```text
temp
attempt
new
final
final2
hack
test
magic
universeEscapePortal
```

Preferred style:

```lean
prime_dvd_product_add_coprime_not_mem
exists_fresh_prime_factor
cosmicCompletion
demo_thirteen_fresh
demo_cosmic_completion
```

Once names are used in recorded or rendered presentation artifacts, they are frozen unless a repair checkpoint explicitly authorizes renaming.

---

## 22. Documentation Comment Protocol

New public declarations should have concise doc comments explaining:

```text
the exact mathematical meaning
the role in the hackathon facade
the assumptions that matter
the distinction from stronger terminology
```

Comments should not claim:

```text
mathematical novelty
prime creation
complete inversion
open-problem resolution
```

Comments may use DkMath vocabulary when the standard mathematical meaning remains clear.

---

## 23. No-Sorry Protocol

New public hackathon modules must contain no:

```lean
sorry
admit
axiom
```

used to bypass a requested proof.

Search the permitted Lean source files:

```bash
rg -n "\bsorry\b|\badmit\b|\baxiom\b" DkMath/Hackathon
```

Existing axioms in imported libraries are not altered by this rule.

The report must distinguish:

```text
new declaration introduced by the checkpoint
existing declaration in an imported dependency
```

---

## 24. Build Protocol

Use increasing verification gates.

### Focused Build

Build the current target module first.

Example:

```bash
lake build DkMath.Hackathon.FinitePrimeEscape
```

### Dependent Facade Build

Build the next dependent hackathon module when available.

Example:

```bash
lake build DkMath.Hackathon.Demo
```

### Aggregate Build

If an aggregate exists:

```bash
lake build DkMath.Hackathon
```

### Relevant Top-Level Build

Run only when required by the checkpoint:

```bash
lake build DkMath
```

### Diff Check

```bash
git diff --check
```

### Working-Tree Inspection

```bash
git status --short
```

Do not consume large amounts of time repeatedly running the broadest build after every local edit.

---

## 25. Build Failure Protocol

Classify each failure before changing architecture.

### Local Failure

Examples:

```text
unknown declaration
namespace mismatch
type mismatch
coercion mismatch
unsolved arithmetic goal
missing simp theorem
```

Action:

```text
repair inside the checkpoint
```

### Dependency Failure

Examples:

```text
required import causes a cycle
core module would need the hackathon facade
broad import creates name conflicts
```

Action:

```text
stop and report architecture obstruction
```

### Mathematical Failure

Examples:

```text
goal is false under current hypotheses
required uniqueness does not follow
bound is missing
```

Action:

```text
stop and report the smallest missing theorem or hypothesis
```

---

## 26. Proof Repair Protocol

Codex may repair local Lean failures by:

```text
finding the correct theorem name
adding a permitted import
changing tactic order
rewriting through an existing equality
isolating casts
adding a local helper lemma
using Nat.Coprime APIs
using ring or norm_num where appropriate
```

Codex must not repair a proof by:

```text
adding an unreviewed assumption
weakening the theorem
using sorry
adding an axiom
editing unrelated core theory
changing the fixed demo data
```

---

## 27. Genuine Obstruction Protocol

A genuine obstruction should be expressed as one exact missing bridge.

Preferred form:

```lean
theorem required_bridge
    (exact inputs)
    (exact hypotheses) :
    exact conclusion
```

or:

```text
Existing type A has no operation that maps its interval representation
through the selected monotone inverse while preserving endpoint membership.
```

A report must include evidence:

```text
current Lean goal
nearest existing declaration
hypothesis mismatch
domain mismatch
dependency path
```

Avoid vague obstruction language such as:

```text
the library is complicated
the proof seems difficult
more theory may be needed
```

---

## 28. Stop Confirmation Protocol

Every Codex report ends with an explicit confirmation:

```text
The checkpoint stopped after its required report.
No later checkpoint implementation was begun.
```

For audit sessions:

```text
No Lean source file was edited.
```

For implementation sessions:

```text
No out-of-scope module was edited.
```

For visual sessions:

```text
No mathematical theorem surface was changed.
```

---

## 29. Report Protocol

Each checkpoint report must be factual and reproducible.

Required top-level sections:

```text
Status
Session metadata
Primary goal
Files inspected
Files changed
Definitions added
Theorems added
Existing APIs reused
Verification commands
Verification results
Mathematical meaning
Meaning boundary
First genuine obstruction
Out-of-scope routes not taken
Resource use
Next permitted action
Stop confirmation
```

The report path is fixed by the checkpoint instruction.

Reports must not overwrite earlier historical reports.

---

## 30. Session Metadata Protocol

Record:

```text
checkpoint
session class
model
reasoning level
session identifier
start time
end time
elapsed time
starting credits
ending credits
credits consumed
```

When information is unavailable, write:

```text
not recorded
```

Do not estimate unknown metadata after the session.

---

## 31. Credit Planning Snapshot

Planning snapshot:

```text
date:
  2026-07-15

hackathon credits after prior capability test:
  2214

integration reserve:
  514
```

The reserve protects:

```text
final Lean repair
Manim repair
integration
reproduction fixes
submission packaging
```

The planning balance is not a requirement to spend all available credits.

---

## 32. Planned Credit Envelope

Initial planning allocation:

| Work                             | Target credits |
| -------------------------------- | -------------: |
| `hack-001` repository audit      |            180 |
| `hack-002` finite prime escape   |            360 |
| `hack-003` Cosmic completion     |            180 |
| `hack-004` concrete demo         |            180 |
| `hack-008` Manim implementation  |            300 |
| `hack-009` integration           |            250 |
| `hack-010` submission and repair |            250 |
| protected reserve                |            514 |
| **total**                        |       **2214** |

These are control targets, not automatic permissions.

Unused credits return to the project reserve.

A checkpoint may be stopped before its target budget when the result is complete or the genuine obstruction is already known.

---

## 33. Stretch Work Credit Gate

The following checkpoints are not funded by the initial required allocation:

```text
hack-005
hack-006
hack-007a–hack-007e
```

Stretch work begins only when:

```text
formal MVP is secured
primary visual route remains on schedule
integration reserve remains intact
sufficient credits were saved from required checkpoints
or
additional credits become available
```

A new decision must state the stretch budget before execution.

---

## 34. Mid-Session Credit Stop

Stop a Codex session when any of the following occurs:

```text
the checkpoint credit target is exceeded without closing a stage
the same searches repeat
the agent has already isolated the genuine obstruction
the task begins expanding into another checkpoint
the remaining balance threatens the protected reserve
```

Write a partial report before further planning.

Do not continue merely because the session is still technically active.

---

## 35. Model Selection Protocol

Use the strongest repository-capable Codex model available within the hackathon environment.

Current preferred model:

```text
GPT-5.6 Sol
```

Actual model names may change.

Always record the exact model used.

### Audit Sessions

Preferred reasoning level:

```text
light
```

Increase only when:

```text
several near-matching APIs have materially different semantics
dependency analysis becomes ambiguous
```

### Lean Implementation Sessions

Preferred reasoning level:

```text
light or medium
```

Use medium when:

```text
the proof requires several connected repository APIs
the Lean goal exposes a genuine structural choice
```

### Repair Sessions

Preferred reasoning level:

```text
light
```

unless the failure is mathematical rather than syntactic.

### DkReal or Deep Bridge Sessions

Preferred reasoning level:

```text
medium
```

These sessions are optional and begin only after the MVP gate.

Do not switch model or reasoning level during a checkpoint without recording the reason.

---

## 36. Time Planning Protocol

Suggested session time limits:

```text
audit:
  15–30 minutes

small theorem wrapper:
  15–30 minutes

finite-prime implementation:
  30–60 minutes

Cosmic Formula bridge:
  15–30 minutes

concrete demo:
  15–30 minutes

Manim prototype:
  30–60 minutes

integration:
  30–60 minutes
```

Time limits are stopping signals, not automatic failure points.

If a session reaches its limit:

```text
finish the current bounded diagnostic
write the report
stop
```

---

## 37. OBS Recording Protocol

Record Codex sessions that materially demonstrate the developer-tool workflow.

### Audit Recording

Capture:

```text
stable project instructions
repository searches
source database use
theorem classification
audit report creation
```

### Implementation Recording

Capture:

```text
checkpoint instruction
source inspection
first source edit
Lean build
one meaningful repair
successful build
final report
```

### Visual Recording

Capture:

```text
storyboard input
Manim implementation
render failure or repair
successful render
```

The recording is evidence of the process.

It is not a substitute for the report or Lean build.

---

## 38. Codex Footage Selection Protocol

The final demo should use only short high-value excerpts.

Good footage:

```text
exact theorem search
bounded source edit
Lean goal repair
successful build
precise stopping report
```

Low-value footage:

```text
long idle searches
repeated scrolling
large unrelated code blocks
unreadable terminal output
```

The main video should show the result before extended process footage.

---

## 39. Audit Session Plan — `hack-001`

### Session Class

```text
AUDIT
```

### Primary Goal

Map the exact existing DkMath and Mathlib theorem route for the formal MVP.

### Permitted Edits

```text
docs/hackathon/cosmic-formula-inversion-260715/
  EXISTING_DKMATH_MAP.md

docs/hackathon/cosmic-formula-inversion-260715/
  report-hack-001.md
```

### Source Permissions

All Lean source is read-only.

### Required Search Domains

```text
Finset product divisibility
Nat.Coprime
prime-divisor existence
finite-prime escape
fresh-prime predicate
primitive-factor near matches
Cosmic Formula
Big
Body
Gap
GN square specialization
projection candidates
DkReal interval entry points
width less than one integer uniqueness
```

### Required Output

The report must identify:

```text
exact declaration names
exact module paths
normalized theorem types
hypothesis differences
import costs
rejected near matches
dangerous dependencies
smallest Phase 2 source surface
first genuinely missing theorem
```

### Hard Stop

```text
do not edit Lean
do not prove missing theorems
do not create new modules
do not begin Manim
stop after the audit report
```

---

## 40. Finite Prime Session Plan — `hack-002`

### Session Class

```text
IMPLEMENTATION
```

### Primary Goal

Implement the general finite prime escape facade.

### Target File

```text
DkMath/Hackathon/FinitePrimeEscape.lean
```

### Expected Theorem Route

```text
member of S
→ divides product P
→ divides P and P + u
→ divides u
→ contradicts Coprime P u
→ not a member of S
```

Then:

```text
prime-divisor existence
+
supplied-divisor exclusion
→ fresh-prime existence
```

### Required Public Layers

```text
supplied prime divisor is outside S
all prime divisors are outside S
a fresh prime divisor exists when 1 < P + u
```

### Hard Stop

Do not begin Cosmic Completion.

---

## 41. Cosmic Formula Session Plan — `hack-003`

### Session Class

```text
IMPLEMENTATION
```

### Primary Goal

Expose:

$$
P(P+2u)+u^2=(P+u)^2
$$

through the smallest suitable public theorem surface.

### Target File

```text
DkMath/Hackathon/CosmicCompletion.lean
```

### Reuse Priority

```text
existing exact theorem
→ wrapper
→ specialization
→ local ring proof
```

### Hard Stop

Do not create formal planar geometry.

Do not begin projection.

---

## 42. Concrete Demo Session Plan — `hack-004`

### Session Class

```text
IMPLEMENTATION
```

### Primary Goal

Build an OBS-ready public module using:

```text
S = {2, 3, 5, 7}
P = 210
u = 11
P + u = 221
221 = 13 × 17
```

### Target File

```text
DkMath/Hackathon/Demo.lean
```

### Structural Requirement

The demo must reuse:

```text
the general finite-prime theorem
the general Cosmic Formula theorem
```

### Hard Stop

Do not add more examples.

Do not begin projection.

---

## 43. Projection Session Plan — `hack-005`

### Status

```text
DEFERRED
```

### Entry Gate

Requires:

```text
formal MVP secured
projection ADR accepted
credit budget approved
```

### Primary Goal

Implement one bounded rational projection convention.

### Hard Stop

Do not implement both signed and unsigned variants.

Do not begin DkReal.

---

## 44. Inverse Session Plan — `hack-006`

### Status

```text
DEFERRED
```

### Primary Goal

Prove the exact inverse on the image and injectivity for fixed positive `u`.

### Hard Stop

Do not claim surjectivity onto an unjustified closed interval.

Do not begin interval reconstruction.

---

## 45. DkReal Session Family Plan — `hack-007`

### Status

```text
DEFERRED
```

### Required Subdivision

```text
hack-007a:
  DkReal entry bridge

hack-007b:
  inverse interval mapping

hack-007c:
  width transport

hack-007d:
  at-most-one integer candidate

hack-007e:
  concrete reconstruction
```

Each sub-checkpoint receives its own instruction, budget, report, and stopping rule.

The family stops permanently for the hackathon when one accepted genuine obstruction makes the next bridge too large.

---

## 46. Manim Session Plan — `hack-008`

### Session Class

```text
VISUAL
```

### Entry Gate

Requires:

```text
formal MVP secured
theorem names frozen
visual directory decided
```

### Primary Goal

Produce the smallest complete 45–60 second render.

### Implementation Order

```text
shared data configuration
static layout
Body / Gap completion
factor reveal
freshness comparison
Lean panel
primary render
```

### Hard Stop

Do not build an interactive application.

Do not add unrelated geometric research.

---

## 47. Integration Session Plan — `hack-009`

### Session Class

```text
INTEGRATION
```

### Primary Goal

Combine:

```text
Manim render
actual Lean code
actual build output
Codex footage
narration
captions
limitation statements
```

### Hard Stop

No theorem implementation or renaming is permitted.

---

## 48. Submission Session Plan — `hack-010`

### Session Class

```text
SUBMISSION
```

### Primary Goal

Produce a reproducible public package.

### Required Checks

```text
branch checkout
Lean build
no-sorry audit
Manim render
video links
screenshots
README links
submission text
limitations
```

### Hard Stop

No new stretch research.

---

## 49. First Audit Instruction Preparation

After `hack-000` is accepted, the first executable Codex instruction should be written as a separate document or prompt.

It must include:

```text
the exact repository path
the exact documentation path
the exact permitted files
the exact source databases
the required map sections
the report template
the no-Lean-edit rule
the final stop instruction
```

It should not restate every project document.

It should rely on the stable prefix and focus on execution.

---

## 50. Audit Search Strategy

The first audit should search in this order.

### Stage A — Finite Product

Search:

```text
Finset product
dvd product
member divides product
prime product
```

### Stage B — Coprime Escape

Search:

```text
Nat.Coprime
dvd add
dvd subtraction
ModEq
not_mem
Euclid
finite prime
```

### Stage C — Prime-Divisor Existence

Search:

```text
exists prime divisor
minFac
prime_minFac
exists_prime_and_dvd
```

### Stage D — Freshness Predicates

Search:

```text
FreshPrimeFactor
fresh prime
new prime
primitive divisor
PrimitiveSet
```

Inspect semantics carefully.

### Stage E — Cosmic Formula

Search:

```text
CosmicFormula
Big
Body
Gap
square completion
GN
Gnomon
```

### Stage F — Projection and DkReal Entry Points

Search:

```text
projection
inverse projection
normalize
GapInterval
DkReal
width
unique integer
floor
ceil
```

The audit should identify entry points only.

It should not fully design the stretch proof.

---

## 51. Audit Completion Test

The first audit is complete when the following questions can be answered without another broad repository search.

```text
Which theorem proves a member divides the product?

Which theorem or proof route uses Coprime to exclude original factors?

Which theorem supplies a prime divisor of n > 1?

Does a matching fresh-prime predicate exist?

Does the complete finite-prime theorem already exist?

Which Cosmic Formula theorem best matches the square case?

Is a ring wrapper preferable?

Which imports are required?

Which projection convention best matches existing DkMath?

What is the DkReal entry type?

What is the first genuinely missing theorem?

Which exact files may hack-002 edit?
```

---

## 52. Report Review Loop

After each Codex report:

```text
1. D. provides the checkpoint report or repository diff.

2. Wise Wolf reviews theorem meaning and architecture.

3. The checkpoint receives:
   ACCEPT,
   ACCEPT_WITH_CONDITIONS,
   RETURN_FOR_REVISION,
   or ACCEPT_STOPPING_POINT.

4. Binding findings update:
   EXISTING_DKMATH_MAP.md,
   CHECKPOINTS.md,
   or DECISIONS.md.

5. The next checkpoint instruction is drafted.

6. Codex does not begin until the instruction is reviewed.
```

---

## 53. Repair Session Trigger

Create a repair checkpoint only when:

```text
the parent theorem contract remains correct
the defect is local
the required file set is small
the repair does not open new mathematics
```

Examples:

```text
one theorem name is wrong
one import is too broad
one Lean proof fails after integration
one Manim equation is misaligned
one report omits required metadata
```

Do not use a repair checkpoint to conceal a contract change.

---

## 54. Contract Change Trigger

Return to human–Wise Wolf planning before Codex execution when:

```text
the theorem assumptions must change
the theorem conclusion must change
the fixed demo values must change
the projection convention must change
the dependency architecture must change
the public contribution claim must change
```

Required sequence:

```text
new ADR
→ contract update
→ roadmap and demo update
→ review
→ new checkpoint
```

Implementation must not precede the decision.

---

## 55. Out-of-Scope Firewall

No Codex hackathon session may begin new work on:

```text
Collatz convergence
Riemann hypothesis
ABC conjecture
Fermat's Last Theorem
Erdős open problems
general prime-density theory
general primitive-divisor theory
aperiodic tiling
cryptographic security
full Euclidean area formalization
repository-wide DkMath refactoring
```

Existing results from these areas may be reused only when the current checkpoint names the exact dependency.

---

## 56. Collatz Work Freeze

The Collatz cp-320 session is supporting footage.

It demonstrated:

```text
large-repository navigation
substantial Lean implementation
proof repair
build verification
genuine-obstruction isolation
```

No checkpoint in this plan authorizes further Collatz implementation.

Required public limitation:

```text
No Collatz convergence claim is made.
```

---

## 57. Public Claim Protocol

Approved project contribution wording:

```text
A verifiable AI-assisted mathematical research workflow built on DkMath.
```

Approved agent wording:

```text
Codex inspected the repository and implemented the formal bridge under a fixed theorem contract.
```

Approved verification wording:

```text
Lean verified the encoded theorem.
```

Approved visual wording:

```text
Manim explains the shared arithmetic and geometric boundary.
```

Avoid:

```text
Codex discovered a new theorem
the Gap creates primes
the project proves prime infinitude
the inverse is complete
DkMath proves Collatz
```

unless a future accepted theorem exactly supports the statement.

---

## 58. Final Session Checklist

Before beginning any Codex session:

```text
[ ] checkpoint identifier exists

[ ] session class is declared

[ ] primary goal is singular

[ ] prerequisites are accepted

[ ] stable documents are current

[ ] current instruction is reviewed

[ ] permitted files are explicit

[ ] prohibited scope is explicit

[ ] theorem or artifact surface is explicit

[ ] verification commands are explicit

[ ] stopping conditions are explicit

[ ] report path is explicit

[ ] starting credits are recorded

[ ] integration reserve is protected

[ ] OBS recording decision is made
```

---

## 59. Final Report Checklist

Before accepting a Codex report:

```text
[ ] exact status is stated

[ ] files inspected are listed

[ ] files changed are listed

[ ] declarations are named

[ ] reused APIs are named

[ ] build commands are listed

[ ] build results are listed

[ ] no-sorry result is listed

[ ] git diff result is listed

[ ] theorem meaning is stated

[ ] stronger non-results are stated

[ ] first genuine obstruction is precise

[ ] credit usage is recorded

[ ] next permitted action is singular

[ ] stop confirmation is present
```

---

## 60. Success Hierarchy

The project should prefer completion in this order.

### Ideal Completion

```text
formal MVP
+
bounded projection
+
exact inverse
+
DkReal reconstruction
+
visual demo
+
submission
```

### Strong Completion

```text
formal MVP
+
bounded projection
+
exact inverse
+
visual demo
+
submission
```

### Required Successful Completion

```text
formal MVP
+
visual demo
+
recorded Codex process
+
submission
```

### Emergency Successful Completion

```text
verified Demo.lean
+
clear documentation
+
existing Codex footage
+
accurate submission
```

A complete lower tier is preferred over an incomplete higher tier.

---

## 61. Current Immediate Plan

The immediate sequence is:

```text
1. finish CODEX_PLAN.md

2. perform cross-document consistency review

3. write report-hack-000.md

4. accept hack-000

5. write the exact hack-001 Codex instruction

6. record starting credits and OBS state

7. run the audit-only Codex session

8. review report-hack-001.md

9. design hack-002 from actual repository evidence
```

No Lean theorem implementation begins before Step 8 is complete.

---

## 62. Codex Plan Summary

The Codex workflow is:

```text
fixed project meaning
→ stable context prefix
→ bounded checkpoint
→ repository inspection
→ smallest implementation
→ Lean verification
→ exact report
→ Wise Wolf review
→ next checkpoint
```

The central scope rule is:

```text
one checkpoint per session
```

The central implementation rule is:

```text
reuse before invention
```

The central proof rule is:

```text
prove exactly the requested theorem
```

The central verification rule is:

```text
public claims are build-gated
```

The central resource rule is:

```text
protect the integration reserve
```

The central stopping rule is:

```text
complete the target
or
isolate the first genuine obstruction
```

The central project goal is not autonomous code generation.

It is a traceable collaboration in which:

```text
human mathematical direction
Codex repository implementation
Lean formal verification
Manim visual explanation
```

remain connected from the first contract to the final public demonstration.
