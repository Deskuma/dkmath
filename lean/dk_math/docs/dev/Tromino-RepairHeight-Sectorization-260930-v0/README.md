# Tromino Repair Height / Sectorization Lean 260930 v0

Status: ACTIVE

## Purpose

This branch formalizes the structural content extracted from the completed
Python Tromino simulation campaign through OBS-020.

The simulation campaign established two distinct structural layers:

1. repair height on a fixed repair-move graph is shortest distance to the exit set;
2. child chambers produced by preserving flips are rooted connected components
   of a parent state relation restricted by a child-admissibility predicate.

The first production goal is intentionally generic. It does not begin from
planar maps, Four Color, or concrete Kempe geometry.

Source research plan:

```text
docs/not_implements/Tromino-RepairHeight-Sectorization-LeanPlan-260930.md
```

Frozen experimental evidence:

```text
python/Tromino/ROADMAP.md
OBS-019 — Six Exact Child-Admissible Sectors
OBS-020 — Unit-Slope Is Structural
```

---

## Repository / branch

```text
repository: Deskuma/dkmath
branch:     dev/Tromino-RepairHeight-Sectorization-260930-v0
base:       develop
```

Development documents:

```text
lean/dk_math/docs/dev/Tromino-RepairHeight-Sectorization-260930-v0/
```

First production surface:

```text
DkMath/Tromino/RepairDistance.lean
DkMath/Tromino/StateSector.lean
```

Expected first-checkpoint audits/regressions:

```text
DkMathTest/Tromino/RepairDistanceAxiomAudit.lean
DkMathTest/Tromino/StateSectorAxiomAudit.lean
DkMathTest/Tromino/RepairDistanceRegression.lean
DkMathTest/Tromino/StateSectorRegression.lean
```

The exact test split may be reduced if one small regression module is cleaner.

---

## Mathematical kernel A — repair distance

Work over an arbitrary state type and relation:

```text
State : Type*
step  : State -> State -> Prop
exit  : State -> Prop
```

with symmetry:

```text
Symmetric step
```

Define an exact-length path relation, conceptually:

```text
Steps step n x y
```

and prove the minimal path algebra needed downstream:

```text
zero / refl
prepend
append / concat
reverse under Symmetric step
```

Define:

```text
CanExitAt step exit n x
```

as existence of an exit state reachable in exactly n steps.

For a state with an explicit reachability witness, define repair height as the
least such natural number, preferably using Nat.find or an equally small
kernel-checked construction.

The mathematical convention is:

```text
if x already satisfies exit, repairHeight x = 0.
```

Do not reproduce the Python implementation artifact that begins recording
exits only after a move.

Required semantic facts:

```text
repairHeight_spec
repairHeight_minimal
```

and the core unit-slope theorem:

```text
step x y
->
repairHeight x <= repairHeight y + 1
and
repairHeight y <= repairHeight x + 1
```

under the required reachability hypotheses.

This theorem is purely a graph-distance fact. It must not depend on Tromino
states, finite graphs, planarity, or coloring.

---

## Mathematical kernel B — state sectorization

For a relation R and admissibility predicate A, define the restricted relation:

```text
Restricted R A x y
iff
A x and A y and R x y
```

Define rooted reachability/chamber semantics for the restricted relation.

The core theorem must package:

```text
childStep x y
<->
Restricted parentStep childAdmissible x y
```

implies that the child chamber rooted at root is exactly the rooted reachable
component of the parent relation restricted to child-admissible states.

The generic theorem must not mention:

```text
six sectors
32 W9 states
17 preserving flips
specific Python witness IDs
```

Those are calibration evidence, not theorem parameters.

---

## Later concrete bridge — not checkpoint 001

After the generic kernels are stable, add a separate concrete module:

```text
DkMath/Tromino/KempeRepair.lean
```

using the existing production carrier and graph-coloring layer:

```text
DkMath.Tromino.State
DkMath.Tromino.Exchange
DkMath.Tromino.GraphColoringBridge
```

The later target is:

```text
proper one-point recolor
-> singleton two-color Kempe component
-> legal repair move
-> unit-slope repair height
```

Checkpoint 001 must not force this bridge into the generic kernels.

---

## Existing production facts to preserve

Current Tromino production already contains:

```text
TrominoState := ZMod 2 × ZMod 2
exchange
exchange_self_inverse
exchange_comp
regionSimpleGraph
RegionPotential.toColoring
```

The generic repair-distance and sectorization kernels should remain independent
of these concrete APIs unless a tiny import is genuinely necessary.

---

## Claims explicitly outside this branch

Do not state or imply:

```text
childHeight <= parentHeight for every preserving flip
height preservation under sectorization
all preserving flips are transport-compatible
repair heights always occupy three consecutive levels
a universal coloring theorem
a proof of the Four Color Theorem
```

The frozen sector census already shows that cross-topology height preservation
is false in the tested family.

---

## Proof discipline

Production code must satisfy:

```text
no sorry
no admit
no new axiom declarations
no hidden finiteness assumption
no Python witness data embedded in generic theorems
focused module builds before broader integration
axiom audit for exported core theorems
git diff --check
```

Prefer a small local inductive path relation over depending on a large graph
distance API unless Mathlib already provides an obviously simpler stable fit.

---

## Current status

```text
branch:
  CREATED

simulation evidence:
  FROZEN THROUGH OBS-020

TRH-001 RepairDistance:
  COMPLETE / APPROVED

TRH-002 StateSector:
  COMPLETE / APPROVED

TRH-003 finite calibration:
  COMPLETE / APPROVED

checkpoint-001:
  Outcome A
  see report-001.md

TRH-004 KempeRepair:
  COMPLETE / APPROVED
  Outcome A
  see report-002.md

TRH-005 admissible repair chamber:
  READY / NEXT CHECKPOINT
```
