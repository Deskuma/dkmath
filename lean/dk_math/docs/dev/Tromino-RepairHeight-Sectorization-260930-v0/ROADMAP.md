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

## TRH-005 — Tromino-facing admissible-chamber integration

Status: COMPLETE / APPROVED — Outcome A

Only after TRH-004 is stable, expose application-level theorems connecting the
generic unit-slope result to the repair-state semantics used by the simulation.

Do not encode Python search policy or finite witness IDs into production.

---

## TRH-006 — shared-coordinate state projection / chamber transport

Status: COMPLETE / APPROVED — Outcome A

Production targets:

```text
DkMath/Tromino/StateProjectionTransport.lean
```

Goals:

```text
generic injective state projection
+ restricted-parent edge preservation
+ local restricted-edge lifting
->
child rooted chamber = projected parent admissible sector

different SimpleGraph colorings on a shared vertex type
-> common mutable-coordinate projection
```

This formalizes the transport pattern used in OBS-019/020 without asserting
that every topology-changing flip satisfies the transport hypotheses.

---

## TRH-007 — partial restoration state / Missing-valid kernel

Status: COMPLETE / APPROVED — Outcome A

The Python repair state is a partial coloring: already-colored vertices carry
colors while the remaining vertices are still uncolored. Formalize that
semantic layer before attempting a concrete flip provider.

Production target:

```text
DkMath/Tromino/RestorationRepairState.lean
```

Required structure:

```text
fixed colored set
remaining set
shared mutable coordinates
fixed outside-mutable color context
properness only on colored-colored edges
Missing-valid at every remaining vertex
one-coordinate state transitions
bridge to KempeRepair on the induced colored subgraph
```

---

## TRH-008 — local edge-flip delta / exact-sector transport certificate

Status: READY / ACTIVE NEXT CHECKPOINT

Production target:

```text
DkMath/Tromino/RestorationFlipTransport.lean
```

Formalize the Python topology change as a local undirected edge replacement:

```text
remove (u,v)
add    (a,b)
all other adjacencies unchanged
```

Then package the additional state-space condition that distinguishes the six
OBS-019 exact transport cases from the eleven state-regenerating cases.

The key point is:

```text
topology flip alone
DOES NOT imply
child chamber projects into parent chamber.
```

Exact transport requires an explicit rooted compatibility certificate.

---

## TRH-009 — concrete finite OBS-019 calibration provider

Status: DEFERRED

After TRH-008 fixes the certificate, decide whether to encode one small finite
transport-compatible witness as a Lean regression/provider or keep the W9
numeric census exclusively in Python evidence.

No universal preserving-flip theorem is authorized.

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

## Checkpoint 003 result

See:

```text
report-003.md
```

Outcome A established explicit admissible-root chamber semantics, admissible
singleton-Kempe steps, same-carrier sectorization, and full-repair-graph
unit slope across chamber edges.

The remaining structural frontier is no longer repair distance or Kempe
geometry. It is the state transport used when parent and child topologies have
different coloring types but share the same mutable-coordinate projection.

---

## Checkpoint 004 result

See:

```text
report-004.md
```

Overall Outcome A established the generic rooted chamber transport packet,
exact path map/lift, chamber-image equality, induced-edge exactness, and the
graph-independent mutable-coordinate projection shared across different graph
coloring types.

A new semantic boundary is now explicit: the Python OBS-019 state is not a
total graph coloring. It is a partial restoration coloring with an uncolored
remaining set. Therefore the concrete Missing-valid layer must be modeled
before a sound flip provider can be claimed.

---

## Checkpoint 005 result

See:

```text
report-005.md
```

Outcome A established the partial restoration carrier, realization semantics,
properness on already-colored vertices, Missing-validity, admissible
one-coordinate transitions, the induced-colored-graph bridge to
`OnePointRecolor` / `SingletonKempeMove`, and the combined parent/child
admissibility filter.

The remaining gap is now sharply localized: describe the actual topology
delta and certify when the child rooted chamber remains inside the parent
admissible state space. The simulation already shows that this compatibility
is not automatic.

---

## Current queue

```text
TRH-000  COMPLETE
TRH-001  COMPLETE / APPROVED
TRH-002  COMPLETE / APPROVED
TRH-003  COMPLETE / APPROVED
TRH-004  COMPLETE / APPROVED
TRH-005  COMPLETE / APPROVED
TRH-006  COMPLETE / APPROVED
TRH-007  COMPLETE / APPROVED
TRH-008  READY
TRH-009  DEFERRED
```
