# instruction-003 — admissible repair chamber integration

## Role

Act as the production Lean implementer for checkpoint 003 of the Tromino
repair-height / sectorization campaign.

Checkpoint 001 and checkpoint 002 are complete with Outcome A.

Frozen production kernels:

```text
DkMath/Tromino/RepairDistance.lean
DkMath/Tromino/StateSector.lean
DkMath/Tromino/KempeRepair.lean
```

This checkpoint integrates the concrete singleton-Kempe step with an explicit
state-admissibility predicate and rooted chamber semantics.

The central structural distinction is mandatory:

```text
chamber graph
  = SingletonKempeStep restricted to admissible states

repair-height graph
  = the full SingletonKempeStep graph
```

An admissible chamber edge is therefore also a repair edge, but shortest
repair paths are not assumed to remain inside the admissible chamber.

Do not conflate these two graphs.

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
lean/dk_math/docs/dev/Tromino-RepairHeight-Sectorization-260930-v0/report-001.md
lean/dk_math/docs/dev/Tromino-RepairHeight-Sectorization-260930-v0/report-002.md
docs/not_implements/Tromino-RepairHeight-Sectorization-LeanPlan-260930.md
python/Tromino/experiments/OBS-016-AdmissibleOnePointStateLandscape/README.md
python/Tromino/experiments/OBS-019-SixExactChildAdmissibleSectors/README.md
python/Tromino/experiments/OBS-020-UnitSlopeStructural/README.md
```

Inspect exact current signatures before editing:

```text
DkMath/Tromino/RepairDistance.lean
DkMath/Tromino/StateSector.lean
DkMath/Tromino/KempeRepair.lean
```

---

## Semantic correction to preserve

`Reachable R root root` always holds by `Steps.zero`.

Therefore:

```text
Reachable (Restricted R A) root root
```

does NOT by itself imply `A root`.

The statement in report-001 suggesting that zero-step restricted reachability
already requires an admissible root is not the actual semantics of the
production definition.

Do not change `Reachable` or `Steps.zero` to repair this.

Instead introduce an explicit admissible-chamber predicate carrying root
admissibility.

---

## Task 1 — create RepairChamber production module

Create:

```text
DkMath/Tromino/RepairChamber.lean
```

Import the minimum required frozen modules, preferably:

```text
DkMath.Tromino.KempeRepair
```

which already reaches the generic sector/reachability kernel.

Do not import Python, Port triangulation, planar-map, or Four Color layers.

---

## Task 2 — explicit admissible chamber semantics

For a generic relation `R` and predicate `A`, define a rooted chamber that
really requires the root to be admissible.

Preferred semantic shape:

```lean
def AdmissibleChamber
    (R : State -> State -> Prop)
    (A : State -> Prop)
    (root x : State) : Prop :=
  A root ∧ Reachable (Restricted R A) root x
```

The exact name may differ if repository naming suggests a cleaner choice.

Required theorems:

```text
admissibleChamber_root_iff:
  AdmissibleChamber R A root root <-> A root

admissibleChamber_target:
  AdmissibleChamber R A root x -> A x
```

To prove target admissibility, promote the useful regression fact from
checkpoint 001 into production in the smallest appropriate place:

```text
A root
Reachable (Restricted R A) root x
-> A x
```

This may live in `RepairChamber.lean` or be added as a small theorem to
`StateSector.lean`. Do not redesign the frozen API.

Also expose:

```text
AdmissibleChamber R A root x
-> Reachable (Restricted R A) root x
```

if it improves later proofs.

---

## Task 3 — concrete admissible singleton-Kempe step

For:

```lean
G          : SimpleGraph V
mutable    : V -> Prop
admissible : G.Coloring TrominoState -> Prop
```

define:

```text
AdmissibleSingletonKempeStep
  = Restricted (SingletonKempeStep G mutable) admissible
```

or an equivalent transparent abbreviation.

Prove symmetry using only frozen facts:

```text
singletonKempeStep_symmetric
restricted_symmetric
```

Required theorem semantics:

```text
Symmetric (AdmissibleSingletonKempeStep G mutable admissible)
```

Do not re-prove Kempe symmetry.

---

## Task 4 — one-point recolor enters the admissible chamber graph

Prove:

```text
OnePointRecolor G mutable source target
admissible source
admissible target
->
AdmissibleSingletonKempeStep G mutable admissible source target
```

The proof must reuse:

```text
onePointRecolor_singletonKempeMove
```

plus the two endpoint admissibility hypotheses.

This theorem is the formal fixed-topology version of the OBS-016 statement:

```text
proper one-point recoloring
+ Missing-valid endpoints
-> admissible state-graph edge
```

Mathlib `G.Coloring` already supplies properness. The extra `admissible`
predicate represents the additional state-space gate.

---

## Task 5 — concrete repair chamber

Define a convenient concrete rooted chamber, conceptually:

```text
SingletonKempeRepairChamber
  G mutable admissible root x
```

as the explicit admissible chamber for:

```text
SingletonKempeStep G mutable
```

Required properties:

```text
root membership iff admissible root;
chamber membership implies admissible target;
chamber membership implies restricted-step reachability.
```

Keep the definition predicate-based. No finite enumeration or BFS is needed.

---

## Task 6 — sectorization interface after state transport

Checkpoint 001 already proves relation-level sectorization.

Package a concrete theorem suitable for a child-state relation that has
already been transported/projected into the same coloring-state carrier.

Given:

```text
hroot : admissible root

hchild :
  forall x y,
    childStep x y
      <-> AdmissibleSingletonKempeStep G mutable admissible x y
```

prove a theorem with semantics:

```text
Reachable childStep root x
<->
SingletonKempeRepairChamber G mutable admissible root x.
```

The proof should be a thin use of:

```text
chamber_sectorization / reachable_iff_restricted
```

plus `hroot`.

Important boundary:

This theorem begins AFTER a child topology/state system has been identified
with the parent coloring carrier.

Do not claim that arbitrary child topologies admit such a transport.

The actual cross-topology projection/equivalence is a later frontier.

---

## Task 7 — two-graph unit-slope theorem

This is the central integration theorem.

Suppose:

```text
hchamber :
  AdmissibleSingletonKempeStep
    G mutable admissible source target
```

and both endpoints have reachable exits in the FULL repair graph:

```text
hsource : exists n,
  CanExitAt (SingletonKempeStep G mutable) exit n source

htarget : exists n,
  CanExitAt (SingletonKempeStep G mutable) exit n target
```

Prove:

```text
repairHeight (SingletonKempeStep G mutable) exit source hsource
  <= repairHeight (SingletonKempeStep G mutable) exit target htarget + 1

and

repairHeight (SingletonKempeStep G mutable) exit target htarget
  <= repairHeight (SingletonKempeStep G mutable) exit source hsource + 1.
```

The proof must project `hchamber` to the underlying `SingletonKempeStep` and
reuse:

```text
singletonKempe_repairHeight_unit_slope
```

Do NOT redefine repair height on the restricted chamber graph for this
required theorem.

This distinction formalizes OBS-020 exactly:

```text
admissible one-point state edge
  ⊆ repair-move edge

therefore full repair distance is unit-slope across every chamber edge.

An optional restricted-graph height theorem may be added only if trivial and
clearly named as a different notion.

---

## Task 8 — Missing-valid abstraction boundary

There is currently no Lean production definition named `MissingColor` or
equivalent that packages the Python blocker/remaining/prefix policy.

Do not invent a solver-specific structure merely to give the predicate a
concrete name.

For checkpoint 003:

```text
admissible : G.Coloring TrominoState -> Prop
```

is the production abstraction boundary.

It may represent any conjunction such as:

```text
fixed restore-prefix agreement
Missing-Color invariant
child-context constraints
other state-space gates
```

provided those predicates are supplied by a later application layer.

Do not claim that every such predicate is realizable by the Python policy.

---

## Task 9 — finite regression

Add:

```text
DkMathTest/Tromino/RepairChamberRegression.lean
```

Use a small finite graph/coloring fixture.

Regression must verify at least:

```text
1. an admissible root belongs to its chamber;
2. an inadmissible root is NOT in the explicit AdmissibleChamber,
   even though raw zero-step Reachable would hold;
3. a proper one-point recolor with both admissible endpoints gives an
   AdmissibleSingletonKempeStep;
4. an inadmissible endpoint blocks the restricted chamber edge;
5. concrete childStep = restricted parent step gives the sectorization
   interface;
6. full repairHeight is unit-slope across an admissible chamber edge.
```

The regression should explicitly catch the zero-step root semantic boundary.

Do not reproduce W9 or the six-sector census.

---

## Task 10 — axiom audit

Add:

```text
DkMathTest/Tromino/RepairChamberAxiomAudit.lean
```

Audit the main exported theorems:

```text
admissible-chamber root iff
admissible-chamber target admissibility
admissible singleton-Kempe step symmetry
one-point recolor -> admissible step
concrete sectorization interface
two-graph repairHeight unit-slope theorem
```

No new axiom declaration is allowed.

---

## Explicit non-goals

Do not implement or claim:

```text
a concrete Python-compatible MissingColor solver state
child-to-parent topology projection or equivalence
cross-topology repair-height monotonicity
childHeight <= parentHeight
height-label preservation
general non-singleton Kempe-chain recoloring
finite W9 enumeration
six-sector cardinality theorem
universal four-colorability
the Four Color Theorem
```

Do not modify the Port triangulation/reduction theorem chain.

---

## Validation

Run focused builds from `lean/dk_math`.

Required minimum:

```text
lake build DkMath.Tromino.RepairChamber
lake build DkMathTest.Tromino.RepairChamberRegression
lake build DkMathTest.Tromino.RepairChamberAxiomAudit
```

Also re-run frozen dependencies if changed or if integration exposes an issue:

```text
lake build DkMath.Tromino.RepairDistance
lake build DkMath.Tromino.StateSector
lake build DkMath.Tromino.KempeRepair
```

Run:

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

Record deprecation/linter warnings separately from proof failures.

---

## Deliverable

Create:

```text
lean/dk_math/docs/dev/Tromino-RepairHeight-Sectorization-260930-v0/report-003.md
```

The report must include:

```text
Outcome A / B / C
files changed
AdmissibleChamber definition
zero-step/root-admissibility correction
target-admissibility theorem
AdmissibleSingletonKempeStep definition
symmetry theorem
one-point recolor -> admissible step theorem
concrete chamber definition
sectorization interface theorem
two-graph repairHeight unit-slope theorem
explicit statement that height uses the full repair graph
finite regression results
axiom audit results
focused build commands and results
git diff --check result
forbidden-token scan result
any deviation from instruction
exact remaining frontier after checkpoint 003
```

Outcome policy:

```text
Outcome A:
  explicit admissible-root chamber semantics is production-proved;
  concrete singleton-Kempe steps restrict cleanly by admissibility;
  child-step sectorization after same-carrier transport is packaged;
  full repair distance is production-proved unit-slope across chamber edges;
  the remaining frontier is concrete child-topology/state transport and/or
  a concrete Missing-valid application predicate.

Outcome B:
  admissible chamber and unit-slope integration are proved, but the concrete
  sectorization wrapper needs an API repair;
  preserve the two-graph distinction and report the exact issue.

Outcome C:
  the current restricted-relation/root semantics obstructs a clean chamber
  API; do not alter Steps/Reachable destructively. Report the exact
  obstruction and preserve proven helper lemmas.
```
