# instruction-002 — concrete singleton Kempe bridge

## Role

Act as the production Lean implementer for checkpoint 002 of the Tromino
repair-height / sectorization campaign.

Checkpoint 001 is complete with Outcome A. The generic kernels are frozen:

```text
DkMath/Tromino/RepairDistance.lean
DkMath/Tromino/StateSector.lean
```

Do not redesign them unless an actual proof obstruction is found.

This checkpoint builds the concrete graph-coloring bridge:

```text
proper one-point recolor
-> singleton two-color Kempe component
-> legal singleton Kempe move
-> repairHeight unit-slope corollary
```

Keep the result local to a fixed graph/topology.

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
docs/not_implements/Tromino-RepairHeight-Sectorization-LeanPlan-260930.md
```

Inspect current source signatures before editing:

```text
DkMath/Tromino/RepairDistance.lean
DkMath/Tromino/StateSector.lean
DkMath/Tromino/State.lean
DkMath/Tromino/Exchange.lean
DkMath/Tromino/GraphColoringBridge.lean
```

Also inspect the exact Mathlib `SimpleGraph.Coloring` API available in the
repository toolchain before choosing theorem field names.

---

## Frozen checkpoint-001 API

Use the production theorems already proved:

```text
Steps
CanExitAt
repairHeight
repairHeight_spec
repairHeight_minimal
repairHeight_eq_zero_of_exit
repairHeight_le_succ_of_step
repairHeight_unit_slope

Restricted
Reachable
reachable_iff_restricted
chamber_sectorization
```

Do not duplicate their proofs.

---

## Task 1 — create KempeRepair production module

Create:

```text
DkMath/Tromino/KempeRepair.lean
```

Use an arbitrary simple graph:

```lean
G : SimpleGraph V
```

and proper four-state colorings of that graph using the existing
`TrominoState` carrier.

Prefer `G.Coloring TrominoState` if its API makes the proof small. If a plain
function plus explicit properness hypothesis is substantially cleaner, that
is acceptable, but explain the choice in the report.

Do not introduce planarity, rotation systems, faces, or Port maps here.

---

## Task 2 — define one-point recolor semantics

Define a small relation describing two proper colorings that differ at exactly
one allowed vertex.

Recommended semantic shape:

```text
OnePointRecolor G mutable source target
iff
there exists v,
  mutable v,
  source v != target v,
  and for every u != v, target u = source u.
```

`mutable : V -> Prop` represents the unlocked/allowed-vertex predicate from
the simulation without importing simulation-specific state.

Required properties:

```text
witness extraction
symmetry of OnePointRecolor
source/target equality away from the witness
```

Do not require a unique witness unless it follows immediately and is useful.

---

## Task 3 — define the two-color Kempe support relation

For a coloring `c` and colors `a b : TrominoState`, define the two-color
support predicate:

```text
c x = a OR c x = b.
```

Define the local two-color adjacency relation by combining:

```text
G.Adj x y
support x
support y
```

Then define two-color reachability using the existing checkpoint-001
`Reachable` / `Steps` kernel rather than adding a second path library.

Recommended concepts:

```text
TwoColorSupport
TwoColorStep
KempeReachable
```

Names may differ if repository style suggests better ones.

Do not depend on a heavyweight connected-component API unless it makes the
proof clearly smaller.

---

## Task 4 — prove the singleton Kempe component theorem

Let `source` and `target` be proper colorings and suppose they differ only at
the one-point recolor witness `v`.

Set:

```text
a = source v
b = target v
```

with `a != b`.

Prove the two key local exclusions.

From properness of `source`:

```text
no neighbor of v has source color a.
```

From properness of `target` plus equality away from v:

```text
no neighbor of v has source color b.
```

Therefore `v` has no adjacent vertex in the source `{a,b}` two-color support.

Use this to prove the actual component statement:

```text
KempeReachable G source a b v u
->
u = v
```

and preferably the iff form:

```text
KempeReachable G source a b v u
<->
u = v.
```

This is the formal version of the OBS-020 structural audit:

```text
every admissible one-point state edge is a singleton Kempe exchange.
```

The proof must be generic in `G`, `V`, and the recolor location.

---

## Task 5 — connect with the V4 exchange kernel

Use the existing:

```text
exchange
existsUnique_nonzero_exchange_to
exchange_self_inverse
```

to show that the recolor at `v` is exactly a nontrivial V4 translation.

At minimum expose a theorem of the form:

```text
there exists a unique nonzero delta
such that
exchange delta (source v) = target v.
```

Prefer reusing `existsUnique_nonzero_exchange_to` directly rather than
re-proving the V4 algebra.

If useful, prove the concrete delta is `source v + target v`, but this is not
required if it complicates the public API.

---

## Task 6 — package a legal singleton Kempe move relation

Define a relation between proper colorings that captures the concrete move
needed by repair distance.

The relation should contain enough semantic content to justify the name
singleton Kempe move, not merely alias `OnePointRecolor` without proof.

A good design is one of:

```text
A. structure/predicate containing:
   - one-point recolor witness
   - singleton two-color component theorem
   - V4 exchange witness;

or

B. define the semantic Kempe move relation first, then prove every
   OnePointRecolor inhabits it.
```

Choose the smaller maintainable representation.

Required result:

```text
OnePointRecolor
->
SingletonKempeMove.
```

Also prove:

```text
Symmetric SingletonKempeMove
```

if the relation is intended to feed `repairHeight_unit_slope` directly.

If symmetry of the richer relation would force a large general Kempe theory,
keep the repair-distance step relation as `OnePointRecolor` and prove
`Symmetric OnePointRecolor`; record that design explicitly. Do not
over-engineer general Kempe component transport merely for symmetry.

---

## Task 7 — Tromino-facing unit-slope corollary

Instantiate the generic checkpoint-001 theorem on the concrete one-point /
singleton-Kempe step relation.

For an arbitrary exit predicate on the coloring-state type, prove a corollary
with semantics:

```text
source and target are one legal singleton Kempe step apart
and both can reach Exit
->
h(source) <= h(target) + 1
and
h(target) <= h(source) + 1.
```

The theorem should be a thin application of `repairHeight_unit_slope`, not a
new shortest-path proof.

Do not add cross-topology comparison. The graph `G` is fixed throughout.

---

## Task 8 — finite regression

Add a small regression under:

```text
DkMathTest/Tromino/
```

Use a tiny graph and two proper `TrominoState` colorings differing at one
allowed vertex.

Check:

```text
OnePointRecolor holds;
the source two-color component at the changed vertex is singleton;
the V4 exchange witness exists;
the packaged singleton Kempe move holds;
the repair-height unit-slope corollary typechecks on the concrete relation.
```

Keep the fixture small. Do not reproduce the W9 chamber.

---

## Task 9 — axiom audit

Add:

```text
DkMathTest/Tromino/KempeRepairAxiomAudit.lean
```

Audit the main exported theorems, including:

```text
one-point recolor symmetry
singleton component theorem
one-point -> singleton Kempe theorem
Tromino-facing repair-height unit-slope theorem
```

No new axiom declaration is allowed.

---

## Explicit non-goals

Do not implement or claim:

```text
general Kempe-chain recoloring of non-singleton components
cross-topology Kempe transport
childHeight <= parentHeight
height preservation under sectorization
all preserving flips are transport-compatible
the 32-state W9 witness as production data
the six-sector census as a theorem parameter
universal four-colorability
the Four Color Theorem
```

Do not modify the Port triangulation/reduction theorem chain.

---

## Validation

Run focused builds from `lean/dk_math`.

Required minimum:

```text
lake build DkMath.Tromino.KempeRepair
lake build DkMathTest.Tromino.KempeRepairRegression
lake build DkMathTest.Tromino.KempeRepairAxiomAudit
```

Also re-run the core dependencies if the new module exposes a problem:

```text
lake build DkMath.Tromino.RepairDistance
lake build DkMath.Tromino.StateSector
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

Record deprecation warnings separately from proof/build failures.

---

## Deliverable

Create:

```text
lean/dk_math/docs/dev/Tromino-RepairHeight-Sectorization-260930-v0/report-002.md
```

The report must contain:

```text
Outcome A / B / C
files changed
exact coloring representation used
OnePointRecolor definition
two-color support / step / reachability definitions
singleton component theorem names
V4 exchange bridge theorem names
final singleton Kempe move representation
symmetry theorem used for repair distance
repair-height unit-slope corollary theorem names
finite regression results
axiom audit results
focused build commands and results
git diff --check result
forbidden-token scan result
any deviation from this instruction
recommendation for checkpoint 003 / Tromino-facing integration
```

Outcome policy:

```text
Outcome A:
  proper one-point recolor is production-proved to be a singleton Kempe move;
  the concrete step relation is symmetric;
  the repairHeight unit-slope corollary is production-proved;
  checkpoint 003 may integrate Missing-valid / chamber semantics.

Outcome B:
  singleton component geometry is proved, but the chosen move packaging or
  repair-distance symmetry interface needs a small redesign;
  report the exact boundary and do not expand into general Kempe theory.

Outcome C:
  the current Mathlib coloring representation blocks the local theorem;
  preserve any proven adjacency/color exclusion lemmas and report the exact
  API obstruction rather than replacing the graph-coloring layer wholesale.
```
