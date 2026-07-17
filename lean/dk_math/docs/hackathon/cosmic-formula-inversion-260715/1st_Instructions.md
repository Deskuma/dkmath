# Checkpoint hack-001 — Existing DkMath Repository Audit

## Session Class

```text
AUDIT
```

## Opening Instruction

Wake up inside the DkMath project.

You are entering a large, active Lean 4 mathematical research repository. The project has already fixed its mathematical meaning, architecture, terminology, scope boundaries, demo data, checkpoint process, and stopping rules.

Your first responsibility is not to write code.

Your first responsibility is to understand the project accurately, inspect the existing repository, and determine the smallest theorem route already available inside DkMath and Mathlib.

Read the project documents carefully. Build a reliable internal model of the project. Then perform the bounded repository audit defined below.

Do not ask for permission to begin.

Do not begin implementation.

---

## Checkpoint Identity

```text
Checkpoint:
  hack-001

Project:
  DkMath — Cosmic Formula Inversion

Repository:
  Deskuma/dkmath

Working branch:
  hackathon/cosmic-formula-inversion

Primary task:
  existing DkMath and Mathlib API audit

Expected result:
  an exact reuse map and audit report

Lean source editing:
  strictly prohibited
```

---

## Primary Goal

Identify the smallest existing theorem and dependency route for the formal MVP:

```text
finite prime set S
→ finite product P
→ Coprime P u
→ prime divisor q of P + u
→ q ∉ S
→ existence of a fresh prime factor
→ Cosmic Formula square completion
→ concrete Demo.lean
```

Also identify only the entry points, not complete implementations, for:

```text
bounded rational projection
exact inverse projection
DkReal nested intervals
inverse interval mapping
width transport
width < 1 integer uniqueness
```

The audit must determine:

```text
what already exists
what needs only a wrapper
what needs a small corollary
what needs a representation bridge
what is genuinely missing
what is semantically unsuitable
what is architecturally dangerous
```

---

## Current Project State

The project documentation phase is complete enough to begin the first repository audit.

The current Lean scaffold contains:

```text
lean/dk_math/DkMath/Hackathon/FinitePrimeEscape.lean
lean/dk_math/DkMath/Hackathon/CosmicCompletion.lean
lean/dk_math/DkMath/Hackathon/Demo.lean
```

These files are read-only during this checkpoint.

The fixed public demonstration is:

```text
S = {2, 3, 5, 7}
P = 210
u = 11
P + u = 221
221 = 13 × 17
```

The central arithmetic theorem is finite-set freshness:

```text
q prime
q ∣ P + u
P = product of S
Coprime P u
→
q ∉ S
```

The central Cosmic Formula identity is:

```text
P(P + 2u) + u² = (P + u)²
```

The project term is:

```text
fresh prime factor
```

Do not replace it with:

```text
primitive prime divisor
```

unless exact sequence-relative primitive-divisor hypotheses are present.

---

## Absolute Rules

```text
Do not edit any Lean source file.

Do not create any Lean declaration.

Do not prove a missing theorem during this session.

Do not create a new module.

Do not refactor existing DkMath code.

Do not begin Manim work.

Do not begin projection implementation.

Do not begin DkReal implementation.

Do not change the mathematical contract.

Do not change the fixed demo values.

Do not delete, rename, populate, or repeatedly inspect UUID tracking anchors.

Do not modify historical documents.

Do not continue beyond the audit report.
```

A related declaration is not considered reusable merely because its name sounds relevant.

Inspect its exact:

```text
module
namespace
domain
arguments
hypotheses
conclusion
dependency path
semantic meaning
```

---

## Permitted Edit Files

You may edit only:

```text
lean/dk_math/docs/hackathon/cosmic-formula-inversion-260715/EXISTING_DKMATH_MAP.md

lean/dk_math/docs/hackathon/cosmic-formula-inversion-260715/report-hack-001.md
```

If `report-hack-001.md` does not exist, create it.

No other file is editable.

The absence of a file from this list means that it is read-only.

---

## Read-Only Project Documents

Read the following project documents in exactly this order:

```text
1.  lean/dk_math/docs/hackathon/cosmic-formula-inversion-260715/README.md

2.  lean/dk_math/docs/hackathon/cosmic-formula-inversion-260715/PROJECT.md

3.  lean/dk_math/docs/hackathon/cosmic-formula-inversion-260715/MATHEMATICAL_CONTRACT.md

4.  lean/dk_math/docs/hackathon/cosmic-formula-inversion-260715/ROADMAP.md

5.  lean/dk_math/docs/hackathon/cosmic-formula-inversion-260715/ARCHITECTURE.md

6.  lean/dk_math/docs/hackathon/cosmic-formula-inversion-260715/GLOSSARY.md

7.  lean/dk_math/docs/hackathon/cosmic-formula-inversion-260715/DECISIONS.md

8.  lean/dk_math/docs/hackathon/cosmic-formula-inversion-260715/RISKS_AND_STOPPING_RULES.md

9.  lean/dk_math/docs/hackathon/cosmic-formula-inversion-260715/EXISTING_DKMATH_MAP.md

10. lean/dk_math/docs/hackathon/cosmic-formula-inversion-260715/VISUAL_STORYBOARD.md

11. lean/dk_math/docs/hackathon/cosmic-formula-inversion-260715/DEMO_CONTRACT.md

12. lean/dk_math/docs/hackathon/cosmic-formula-inversion-260715/CHECKPOINTS.md

13. lean/dk_math/docs/hackathon/cosmic-formula-inversion-260715/CODEX_PLAN.md

14. this checkpoint instruction
```

Treat:

```text
1st_PLAN.md
```

as historical context only.

It does not override the current stable documents.

Do not inspect the empty UUID tracking-anchor file. Its empty state is already known and intentional.

---

## Repository-Level Instructions

After reading the stable project documents, locate and read the governing repository files:

```text
README.md
AGENT.md
SUMMARY.md
```

Use the versions governing the `lean/dk_math` source tree.

Follow those repository instructions unless they conflict with the explicit mathematical or scope boundary of this checkpoint.

The source databases available to the audit include:

```text
__dkmath-all.lean.txt.gz
__summary_report_data.tar.gz
__theorems-heading.txt
```

Locate them by filename rather than assuming an undocumented path.

---

## First Progress Report — Wake-Up Confirmation

After reading the stable project documents and repository instructions, emit one concise progress report containing exactly these points:

```text
Project identity
Primary arithmetic theorem
Primary Cosmic Formula identity
Fixed demo values
Required dependency direction
Permitted edit files
Prohibited implementation scope
Stopping rule
```

Do not wait for a response after this progress report.

Continue directly into the repository audit.

Do not summarize every document individually.

---

## Reuse Classification

Classify every relevant declaration with one primary label.

### `DIRECT`

```text
The exact required declaration already exists and can be applied directly.
```

### `WRAPPER`

```text
The mathematical result already exists, but the hackathon facade needs a stable public-facing theorem name or specialization.
```

### `COROLLARY`

```text
The requested theorem follows through a small amount of local reasoning from existing declarations.
```

### `BRIDGE`

```text
The required mathematics exists, but two representations, domains, or APIs must be connected.
```

### `MISSING`

```text
No suitable existing declaration was found.
```

### `REJECTED`

```text
A related declaration exists but its mathematical meaning does not match the contract.
```

### `DANGEROUS`

```text
The declaration is related but would create a dependency cycle, reverse dependency, excessive unrelated import, or foundational refactor.
```

### `DEMO_ONLY`

```text
The fact should be proved locally as concrete arithmetic with norm_num, decide, ring, or equivalent automation.
```

Do not use `MISSING` until the relevant theorem index, source database, direct source modules, and Mathlib alternatives have been checked.

---

# Execution Stages

## Stage A — Absorb the Project Contract

Read the project documentation in the required order.

Confirm internally that the project distinguishes:

```text
finite-set freshness
from
sequence-relative primitiveness
```

```text
prime-divisor exclusion
from
prime-divisor existence
```

```text
arithmetic square identity
from
formal Euclidean dissection
```

```text
MVP theorem work
from
projection and DkReal stretch work
```

```text
formal theorem
from
visual interpretation
```

Do not modify any file during Stage A.

---

## Stage B — Read Repository Instructions and Establish Search Paths

Read the governing repository instructions.

Locate:

```text
Lean source root
DkMath module root
theorem heading index
compressed Lean source database
summary report archive
Mathlib source access
```

Record the exact discovered paths in `report-hack-001.md`.

Do not unpack or duplicate the complete Lean source database unless direct compressed searches prove insufficient.

Preferred commands include:

```bash
rg -n "SEARCH_TERM" PATH
```

```bash
zgrep -n "SEARCH_TERM" __dkmath-all.lean.txt.gz
```

```bash
zcat __dkmath-all.lean.txt.gz | sed -n 'START,ENDp'
```

```bash
tar -tf __summary_report_data.tar.gz
```

```bash
tar -xOf __summary_report_data.tar.gz PATH/TO/REPORT.txt
```

Use exact declaration search before broad semantic search.

---

## Stage C — Audit Finite Product and Coprimality APIs

Find the exact declarations supporting:

```text
S : Finset ℕ
P = product of S
q ∈ S → q ∣ P
Nat.Coprime P u
q ∣ P
q ∣ P + u
→ q ∣ u
a nontrivial divisor cannot divide both coprime numbers
```

Search both DkMath and Mathlib.

Search terms should include combinations of:

```text
Finset.prod
dvd_prod
dvd_prod_of_mem
mem
Nat.Coprime
gcd
dvd_gcd
dvd_add
dvd_add_iff
Nat.ModEq
not_mem
prime
```

For each useful declaration, record:

```text
exact module
exact declaration name
normalized type
required hypotheses
conclusion
classification
import cost
intended use
```

Determine whether the cleanest route stays entirely in `ℕ`.

Do not introduce an `ℤ` bridge merely because subtraction appears natural.

---

## Stage D — Audit Finite Prime Escape and Freshness APIs

Search for an existing theorem equivalent or close to:

```text
q prime
q ∣ product(S) + u
Coprime (product(S)) u
→
q ∉ S
```

Also search for an existence theorem equivalent to:

```text
1 < product(S) + u
→
∃ q, q prime ∧ q ∣ product(S) + u ∧ q ∉ S
```

Search terms should include:

```text
fresh prime
FreshPrimeFactor
prime not_mem
prime divisor outside
finite prime
Euclid
product add
coprime product
forall_not_dvd
exists_prime_and_dvd
exists_prime_dvd
minFac
PrimitiveSet
primitive divisor
BezoutBridge
```

Inspect primitive-divisor APIs only to determine whether they are reusable or must be rejected.

Do not classify a primitive-divisor theorem as an exact freshness theorem unless its sequence-relative hypotheses specialize cleanly and the public terminology remains `fresh`.

Explicitly answer:

```text
Does a matching FreshPrimeFactor predicate already exist?

Does the supplied-divisor exclusion theorem already exist?

Does the fresh-prime existence theorem already exist?

Is primality of every member of S logically required for exclusion?

Is S.Nonempty required?

Is 0 < u required for arithmetic exclusion?

What exact theorem supplies a prime divisor of n > 1?
```

---

## Stage E — Audit Cosmic Formula APIs

Search the existing DkMath library for:

```text
CosmicFormula
Big
Body
Gap
Core
Beam
GN
Gnomon
square completion
Body + Gap = Big
power difference
```

Find the cleanest route to:

```text
P * (P + 2 * u) + u ^ 2 = (P + u) ^ 2
```

Determine whether this should be:

```text
DIRECT:
  an exact existing theorem

WRAPPER:
  a public alias or specialization

COROLLARY:
  a short consequence of a generic theorem

BRIDGE:
  a translation into existing Big / Body / Gap structures

MISSING:
  absent from DkMath but trivial as a local ring theorem
```

Explicitly inspect whether:

```text
the square case is already present
a generic exponent theorem specializes to d = 2
GN₂(P, u) is already connected to P + 2u
an existing Big / Body / Gap structure is suitable for the thin facade
reuse would require an excessively broad or unrelated import
```

The audit must be willing to recommend a local `ring` wrapper when that is cleaner than forcing a deep abstraction into the public MVP.

Do not formalize Euclidean rectangles, areas, polygons, or dissections.

---

## Stage F — Audit Projection Entry Points

This stage is reconnaissance only.

Search for existing definitions or theorems related to:

```text
projection
inverse projection
normalization
bounded coordinate
unit interval
signed interval
ratio
left inverse
right inverse
injective
fractional linear map
Möbius transformation
```

Compare the candidate project projections:

```text
unsigned:
  P / (P + u)

signed:
  -P / (P + u)
```

Record:

```text
existing formula
domain
codomain
interval convention
inverse formula
DkReal compatibility
import cost
```

Do not select a convention unless repository evidence makes one clearly preferable.

A recommendation may be written in the audit report.

Do not implement either projection.

---

## Stage G — Audit DkReal Entry Points

This stage is also reconnaissance only.

Search for:

```text
DkReal
GapInterval
nested interval
interval containment
interval width
shrinking width
map interval
monotone
inverse image
floor
ceil
unique integer
AtMostOne
width_lt_one
```

Identify:

```text
the primary DkReal type
the primary rational interval representation
nestedness theorems
width definitions
membership theorems
available interval-map operations
available width-transport results
available integer-candidate uniqueness results
```

Do not design or implement a complete DkReal proof.

Name the first likely missing bridge.

Possible outcomes include:

```text
projection value → DkReal embedding already exists

inverse interval mapping is missing

width transport is missing

width < 1 integer uniqueness is missing

all required entry points already exist
```

---

## Stage H — Update `EXISTING_DKMATH_MAP.md`

Update the existing map in place.

Rules:

```text
Preserve all MAP identifiers.

Do not renumber existing sections.

Replace TO AUDIT with exact findings.

Add exact declaration names.

Add exact module paths.

Add normalized theorem types.

Record required hypotheses.

Record semantic mismatches.

Record import cost.

Record rejected near matches.

Record dangerous dependencies.

Record the final reuse recommendation.
```

For each MVP concept, the final map must contain either:

```text
one confirmed usable route
```

or:

```text
one precise MISSING record
```

Do not fill uncertain findings with guesses.

Use:

```text
NOT FOUND AFTER SEARCH
```

when appropriate, and list the searches performed.

---

## Stage I — Write `report-hack-001.md`

Create the audit report with the following structure.

````md
# Report — Checkpoint hack-001

## Status

```text
COMPLETED
```

or:

```text
STOPPED
```

## Session Metadata

```text
Checkpoint:
Session class:
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

Use `not recorded` for unavailable values.

## Primary Goal

Restate the audit goal.

## Stable Documents Read

List the project documents.

## Repository Instructions Read

List the governing repository files.

## Search Sources

List:

- theorem indexes;
- compressed source database;
- summary reports;
- direct modules;
- Mathlib sources.

## Modules Inspected

List exact module paths.

## Finite Prime Route

State the exact proposed theorem path.

## Cosmic Formula Route

State the exact proposed theorem path.

## Projection Entry Points

State findings without implementation.

## DkReal Entry Points

State findings without implementation.

## Confirmed Reusable Declarations

For each:

- module;
- declaration;
- normalized type;
- classification;
- intended role.

## Rejected Near Matches

For each:

- declaration;
- reason for rejection.

## Dangerous Dependencies

List any dependency or import risks.

## Genuinely Missing Lemmas

State the smallest missing theorem or bridge in an exact Lean-like shape.

## Proposed `hack-002` Implementation Surface

State:

- exact file permitted to change;
- proposed imports;
- proposed definitions;
- proposed theorem names;
- required build commands.

## Assumption Audit

Classify:

- all members of `S` prime;
- `S.Nonempty`;
- `0 < u`;
- `0 < P`;
- `Nat.Coprime P u`;
- `1 < P + u`;
- `Nat.Prime q`;
- `q ∣ P + u`.

## Files Changed

This must contain only:

- `EXISTING_DKMATH_MAP.md`;
- `report-hack-001.md`.

## No-Source-Edit Confirmation

Confirm explicitly:

```text
No Lean source file was edited.
```

## First Genuine Obstruction

State one exact obstruction or `none`.

## Out-of-Scope Routes Not Taken

List adjacent work deliberately avoided.

## Next Permitted Action

State only:

```text
Wise Wolf review of checkpoint hack-001.
```

## Stop Confirmation

Confirm:

```text
The checkpoint stopped after the audit report.
No Lean implementation was begun.
No later checkpoint work was begun.
```
````

---

## Stage J — Verify the Audit Boundary

Before stopping, run:

```bash
git status --short
```

and:

```bash
git diff --check
```

Inspect the diff and confirm that only the two permitted documentation files changed.

Do not run Lean builds merely to simulate progress.

This checkpoint contains no Lean source changes.

If the repository has unrelated pre-existing working-tree changes, record them without modifying them.

---

## Completion Conditions

Checkpoint `hack-001` is complete when all of the following are true:

```text
The stable project documents were read.

The repository-level instructions were read.

The exact Finset product-divisibility route was identified.

The exact Coprime exclusion route was identified.

The exact prime-divisor existence route was identified.

FreshPrimeFactor or its absence was determined.

Primitive-divisor near matches were classified correctly.

The Cosmic Formula square-completion route was identified.

Candidate projection entry points were identified.

Candidate DkReal entry points were identified.

The first genuinely missing theorem was named.

EXISTING_DKMATH_MAP.md was updated.

report-hack-001.md was written.

Only the two permitted files changed.

No Lean source file was edited.

No implementation checkpoint was begun.
```

---

## Genuine Stopping Conditions

Stop the audit early and report `STOPPED` if:

```text
the governing repository instructions cannot be located;

the source databases are unavailable or unreadable and direct source traversal cannot replace them;

the project documents contain a binding contradiction that changes the requested theorem;

the actual branch or repository state does not contain the expected scaffold;

the exact source root cannot be determined safely;

the permitted report files cannot be edited without modifying prohibited files.
```

Do not stop merely because:

```text
an exact theorem does not exist;

several near matches exist;

the eventual proof will require a new small lemma;

projection or DkReal remains incomplete.
```

Those are normal audit findings.

---

## Prohibited Continuation

After the report is written, do not:

```text
edit FinitePrimeEscape.lean;

edit CosmicCompletion.lean;

edit Demo.lean;

prove the proposed missing theorem;

create FreshPrimeFactor;

run hack-002;

create projection modules;

create DkReal bridges;

begin Manim work;

modify CHECKPOINTS.md;

modify DECISIONS.md;

modify the mathematical contract;

commit or push.
```

---

## Final Instruction

Complete the repository audit.

Update only:

```text
EXISTING_DKMATH_MAP.md
report-hack-001.md
```

Then stop.

The next action belongs to the human–Wise Wolf review process.

Do not begin implementation.
