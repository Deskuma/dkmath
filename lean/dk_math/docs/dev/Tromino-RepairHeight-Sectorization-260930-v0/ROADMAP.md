# Tromino Repair Height / Sectorization Roadmap 260930 v0

## Campaign objective

Promote the structural results behind OBS-019 and OBS-020 from finite Python
evidence into reusable Lean theorems, while keeping experimental Four-Color
claims outside the theorem layer.

The formalization chain is:

```text
symmetric repair relation
-> exact-length paths
-> minimum distance to Exit
-> unit-slope repair height

parent relation + admissibility predicate
-> restricted relation
-> rooted reachable chamber
-> sectorization identity

proper one-point recolor
-> singleton Kempe exchange
-> Tromino-facing unit-slope theorem
```

---

## TRH-000 — campaign scaffold

Status: COMPLETE

Created from develop:

```text
dev/Tromino-RepairHeight-Sectorization-260930-v0
```

Development hub:

```text
lean/dk_math/docs/dev/Tromino-RepairHeight-Sectorization-260930-v0/
```

Research source:

```text
docs/not_implements/Tromino-RepairHeight-Sectorization-LeanPlan-260930.md
python/Tromino/ROADMAP.md
```

---

## TRH-001 — generic repair-distance kernel

Status: COMPLETE / APPROVED — Outcome A

Production target:

```text
DkMath/Tromino/RepairDistance.lean
```

Required results:

```text
Steps
Steps.prepend
Steps.concat / Steps.add
Steps.reverse_of_symmetric

CanExitAt
repairHeight
repairHeight_spec
repairHeight_minimal

unit-slope:
  step x y
  -> hx <= hy + 1
  and hy <= hx + 1
```

Requirements:

```text
no finiteness dependency if avoidable
height requires explicit exit reachability
exit-at-root gives height zero
no concrete Tromino coloring dependency
```

---

## TRH-002 — generic state-sector kernel

Status: COMPLETE / APPROVED — Outcome A

Production target:

```text
DkMath/Tromino/StateSector.lean
```

Required concepts:

```text
Restricted R A
rooted reachability / chamber
```

Required theorem:

```text
childStep = parentStep restricted to childAdmissible
->
child rooted chamber
=
rooted component of the restricted parent relation
```

The theorem must remain independent of the OBS-019 numeric census.

---

## TRH-003 — finite calibration and axiom audit

Status: COMPLETE / APPROVED — Outcome A

Add small kernel-checked regressions.

Minimum calibration:

```text
1. path graph with exit-distance heights 0,1,2;
2. restricted relation whose admissibility predicate splits the parent graph
   and whose rooted chamber selects exactly one sector.
```

Audit exported core theorems with #print axioms.

Expected ordinary baseline:

```text
propext
Classical.choice
Quot.sound
```

or a smaller dependency set if the implementation permits it.

No new axiom is acceptable.

---

## TRH-004 — concrete singleton Kempe bridge

Status: COMPLETE / APPROVED — Outcome A

Production target:

```text
DkMath/Tromino/KempeRepair.lean
```

Use:

```text
DkMath.Tromino.State
DkMath.Tromino.Exchange
SimpleGraph coloring APIs
DkMath.Tromino.GraphColoringBridge
```

Target:

```text
source proper
target proper
differ only at unlocked vertex v
source v = a
target v = b
a != b
->
the source {a,b}-Kempe component containing v is {v}
```

Then derive that a proper one-point recolor is one legal singleton Kempe
exchange and feed that edge into TRH-001.

---

## TRH-005 — Tromino-facing integration

Status: READY / ACTIVE NEXT CHECKPOINT

Only after TRH-004 is stable, expose application-level theorems connecting the
generic unit-slope result to the repair-state semantics used by the simulation.

Do not encode Python search policy or finite witness IDs into production.

---

## Acceptance boundary for checkpoint 001

Checkpoint 001 is complete only if:

```text
RepairDistance.lean builds
StateSector.lean builds
generic unit-slope theorem is proved
generic sectorization theorem is proved
finite regressions build
axiom audits are recorded
no sorry/admit/new axiom
git diff --check succeeds
no Four Color endpoint claim
```

Checkpoint 001 may stop before KempeRepair.lean.

---

## Checkpoint 001 result

See:

```text
report-001.md
```

Outcome A established the generic exact-length path kernel, explicit-reachability
repair height, paired unit-slope theorem, restricted relation, rooted
sectorization theorem, finite regressions, and focused axiom audits.

The concrete Kempe layer remained intentionally outside checkpoint 001.

---

## Checkpoint 002 result

See:

```text
report-002.md
```

Outcome A established the concrete one-point recolor predicate, two-color
support/reachability, singleton Kempe-component theorem, V4 exchange bridge,
symmetric singleton-Kempe step relation, and its thin repair-height unit-slope
corollary.

A semantic boundary to preserve in checkpoint 003:

```text
Reachable (Restricted R A) root root
```

holds by the zero-step constructor even when `A root` is false. Therefore a
rooted admissible chamber that is intended to consist only of admissible states
must carry root admissibility explicitly. The checkpoint-001 production
theorems remain valid; this is a chamber-semantics refinement.

---

## Current queue

```text
TRH-000  COMPLETE
TRH-001  COMPLETE / APPROVED
TRH-002  COMPLETE / APPROVED
TRH-003  COMPLETE / APPROVED
TRH-004  COMPLETE / APPROVED
TRH-005  READY
```
