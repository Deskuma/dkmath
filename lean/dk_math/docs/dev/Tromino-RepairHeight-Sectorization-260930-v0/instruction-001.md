# instruction-001 — RepairDistance + StateSector generic kernels

## Role

Act as the production Lean implementer for the first formalization checkpoint
of the Tromino repair-height / sectorization campaign.

The Python simulation phase is closed at OBS-020. Do not extend the simulator
in this checkpoint.

The task is to formalize the two generic structural kernels that explain the
observations:

1. repair height is minimum distance to a fixed exit set in a symmetric repair
   relation;
2. a child chamber obtained by restricting admissible states is the rooted
   reachable component of the restricted parent relation.

Do not implement the concrete Kempe-coloring bridge yet unless it becomes a
tiny unavoidable dependency. It is planned for the next checkpoint.

---

## Repository / branch

```text
repository: Deskuma/dkmath
branch:     dev/Tromino-RepairHeight-Sectorization-260930-v0
base:       develop
```

Read first:

```text
lean/dk_math/docs/dev/Tromino-RepairHeight-Sectorization-260930-v0/README.md
lean/dk_math/docs/dev/Tromino-RepairHeight-Sectorization-260930-v0/ROADMAP.md
docs/not_implements/Tromino-RepairHeight-Sectorization-LeanPlan-260930.md
python/Tromino/ROADMAP.md
```

Inspect current source signatures before editing:

```text
DkMath/Tromino/State.lean
DkMath/Tromino/Exchange.lean
DkMath/Tromino/GraphColoringBridge.lean
```

These concrete modules are context only. The new generic kernels should not
depend on them unless necessary.

---

## Frozen evidence and interpretation

The W9 chamber census found:

```text
32 states
48 admissible one-point state edges
repair heights 8,9,10
all 48 edges satisfy |delta h| <= 1
```

The six exact child-admissible sectors gave:

```text
98 child-state evaluations
21 equal to matched parent W9 height
77 lower
0 higher
all six fixed-topology child chambers satisfy |delta h| <= 1
```

The structural audit shows that repair height on one fixed repair graph is
shortest distance to the exit set.

Therefore the first theorem is not a numerical Tromino theorem. It is a
generic graph-distance theorem.

The sector census shows that the correct structural abstraction is full child
admissibility, not an added-edge-only predictor.

Do not encode the census numbers into production.

---

## Task 1 — implement exact-length paths

Create:

```text
DkMath/Tromino/RepairDistance.lean
```

Use a generic type and binary relation:

```lean
variable {State : Type*}
variable (step : State -> State -> Prop)
```

Implement a small exact-length path relation, conceptually:

```lean
Steps step n x y
```

Preferred constructors:

```text
zero:
  Steps step 0 x x

succ/prepend:
  step x y
  -> Steps step n y z
  -> Steps step (n+1) x z
```

The exact constructor names may differ if a cleaner API emerges.

Required helper lemmas:

```text
refl / zero
prepend
concat / add
reverse_of_symmetric
```

The reverse theorem must use an explicit hypothesis:

```lean
Symmetric step
```

Do not introduce graph finiteness.

If Mathlib already has a tiny exact-length relation that makes all later proofs
strictly simpler, it may be used, but avoid coupling this kernel to a large or
unstable graph-distance API.

---

## Task 2 — define exit reachability and repair height

Define:

```lean
CanExitAt step exit n x : Prop
```

with semantics:

```text
there exists y,
exit y and
Steps step n x y
```

Define an explicit reachability predicate or use:

```lean
∃ n, CanExitAt step exit n x
```

Do not assign a natural repair height to an unreachable state.

Preferred repair height shape:

```lean
repairHeight step exit x hreachable : ℕ
```

using Nat.find, or another equally small construction whose minimum property
is direct.

Required theorems:

```text
repairHeight_spec
repairHeight_minimal
```

The mathematical convention must satisfy:

```text
if exit x, then repairHeight x = 0
```

when supplied with the corresponding reachability witness.

Do not reproduce the Python helper behavior that only records first exits
after at least one repair move.

---

## Task 3 — prove the one-step unit-slope theorem

Assume:

```lean
hsymm : Symmetric step
hxy   : step x y
hx    : ∃ n, CanExitAt step exit n x
hy    : ∃ n, CanExitAt step exit n y
```

Prove the two directed inequalities:

```text
repairHeight x <= repairHeight y + 1
repairHeight y <= repairHeight x + 1
```

and expose one public paired theorem if that produces the cleanest API.

Proof strategy should be structural:

```text
minimal path from y to Exit
+ prepend edge x -> y
=> candidate path from x of length h(y)+1
=> h(x) <= h(y)+1
```

Use relation symmetry for the reverse direction.

Optionally derive:

```lean
Nat.dist (repairHeight ... x ...) (repairHeight ... y ...) <= 1
```

only if Mathlib makes the statement and proof small. The paired inequalities
are the required deliverable.

Do not introduce integer coercions merely to state an absolute-difference
version.

---

## Task 4 — implement restricted state relation

Create:

```text
DkMath/Tromino/StateSector.lean
```

Define:

```lean
Restricted (R : State -> State -> Prop) (A : State -> Prop)
    (x y : State) : Prop
```

with exact semantics:

```text
A x and A y and R x y
```

Prove only the elementary API needed for the chamber theorem. If useful,
include symmetry preservation:

```text
Symmetric R -> Symmetric (Restricted R A)
```

but do not grow a generic graph library.

---

## Task 5 — rooted reachability / chamber and sectorization theorem

Define a rooted reachability predicate for an arbitrary relation. Reuse the
exact-length Steps relation from RepairDistance if that keeps the API small.

A natural semantic form is:

```lean
Reachable R root x := ∃ n, Steps R n root x
```

and a chamber may be represented as the predicate/set of reachable states.

Formalize the following theorem schema.

Given:

```lean
hchild :
  ∀ x y, childStep x y ↔ Restricted parentStep childAdmissible x y
```

prove that for every root/state:

```text
reachable under childStep from root
iff
reachable under Restricted parentStep childAdmissible from root
```

or package the equivalent set equality if that API is cleaner.

This is the generic sectorization theorem.

Important root boundary:
if the chosen restricted-relation definition requires admissibility at both
endpoints, be explicit about whether a zero-step root must satisfy
childAdmissible root. Do not hide a root-admissibility assumption.

Do not introduce connected-component machinery beyond what this theorem
requires.

---

## Task 6 — finite regression for repair height

Add a small test module under:

```text
DkMathTest/Tromino/
```

Construct a finite path-shaped relation with three states and an exit at one
endpoint.

Verify kernel-checked heights:

```text
0
1
2
```

and verify the unit-slope theorem on its adjacent edges.

The regression may use Fin 3, a small inductive type, or another compact
carrier.

Do not build a generic BFS implementation.

---

## Task 7 — finite regression for sectorization

Construct a small finite parent relation for which an admissibility predicate
removes states/edges and splits the parent graph into more than one restricted
component.

Choose a root in one component and prove that the child chamber is exactly the
rooted restricted sector predicted by the generic theorem.

This test exists to catch orientation and zero-step/root-admissibility errors.

Do not encode the real 32-state W9 chamber.

---

## Task 8 — axiom audits

Add focused axiom-audit modules consistent with current repository convention,
preferably:

```text
DkMathTest/Tromino/RepairDistanceAxiomAudit.lean
DkMathTest/Tromino/StateSectorAxiomAudit.lean
```

Print axioms for the main exported theorems.

Expected ordinary baseline may include:

```text
propext
Classical.choice
Quot.sound
```

depending on the construction and Mathlib dependencies.

No new axiom declaration is allowed.

---

## Task 9 — integration boundary

Do not implement KempeRepair.lean in checkpoint 001 unless all generic work
is complete and the addition is trivially small.

Do not modify broad Tromino coloring/reduction modules.

Do not add a Four Color theorem endpoint.

Do not claim or formalize:

```text
childHeight <= parentHeight for every preserving flip
cross-topology repair-height preservation
all preserving flips are transport-compatible
repair heights always lie in three consecutive levels
```

The simulation data do not justify these statements.

---

## Validation

Run focused builds from:

```text
lean/dk_math
```

Required commands, adjusted only for exact module names:

```text
lake build DkMath.Tromino.RepairDistance
lake build DkMath.Tromino.StateSector
lake build DkMathTest.Tromino.RepairDistanceRegression
lake build DkMathTest.Tromino.StateSectorRegression
lake build DkMathTest.Tromino.RepairDistanceAxiomAudit
lake build DkMathTest.Tromino.StateSectorAxiomAudit
```

Also run:

```text
git diff --check
```

Scan changed Lean files for:

```text
sorry
admit
axiom
unsafe
```

Distinguish existing/imported axioms reported by #print axioms from newly
declared axioms.

If the exact test file split differs, record the actual focused commands.

---

## Deliverable

Create:

```text
lean/dk_math/docs/dev/Tromino-RepairHeight-Sectorization-260930-v0/report-001.md
```

The report must include:

```text
Outcome A / B / C
files changed
final Steps representation
final repairHeight representation
reachability convention for unreachable states
zero-height exit convention
repairHeight_spec theorem
repairHeight_minimal theorem
unit-slope theorem names
Restricted definition
rooted reachability / chamber definition
sectorization theorem names
finite regression results
axiom audit results
focused build commands and results
git diff --check result
forbidden-token scan result
any deviation from instruction
recommendation for instruction-002 / KempeRepair
```

Outcome policy:

```text
Outcome A:
  RepairDistance + StateSector + finite regressions are production-proved;
  generic unit-slope and sectorization theorems are complete;
  checkpoint 002 may begin concrete Kempe integration.

Outcome B:
  the generic kernels build but one public theorem/API boundary needs repair;
  report the exact obstruction and keep concrete Kempe integration deferred.

Outcome C:
  the selected path/reachability representation obstructs the core proof;
  stop, preserve the useful partial kernel, and report the obstruction rather
  than building a large graph framework.
```
