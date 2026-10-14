# instruction-007 — frozen OBS-019 neighbor-01 calibration / campaign closeout

## Role

Checkpoint 006 is complete with Outcome A.

The abstract/formal campaign is now structurally complete. This final
checkpoint does NOT add a new general production theorem. It kernel-checks one
actual frozen OBS-019 transport-compatible case against the formal transport
abstraction and then closes the campaign.

Use the smallest exact case: OBS-019 neighbor 1.

## Repository / branch

```text
repository: Deskuma/dkmath
branch:     dev/Tromino-RepairHeight-Sectorization-260930-v0
base:       develop
```

## Frozen provenance — authoritative sources

Read these exact committed files first:

```text
python/Tromino/experiments/OBS-019-SixExactChildAdmissibleSectors/README.md
python/Tromino/experiments/OBS-019-SixExactChildAdmissibleSectors/summary.json
python/Tromino/results/repair-depth/w9-flip-chamber-census-v24/summary.json
python/Tromino/results/repair-depth/w9-flip-chamber-census-v24/neighbor-01.json
python/Tromino/results/repair-depth/w9-state-component-v24/summary.json
python/Tromino/results/repair-depth/seeded-w9-frontier-d10-v24/best_frontier_witness.json
```

Also inspect parent states:

```text
python/Tromino/results/repair-depth/w9-state-component-v24/state-008.json
python/Tromino/results/repair-depth/w9-state-component-v24/state-010.json
python/Tromino/results/repair-depth/w9-state-component-v24/state-012.json
python/Tromino/results/repair-depth/w9-state-component-v24/state-014.json
```

Do not silently regenerate or reinterpret the data. The committed JSON is the
calibration source.

## Frozen case identity

The calibration must record and verify these source facts:

```text
witness job_seed = 11000009
step             = 16
neighbor index   = 1
flip move        = [4,21,5,17]
removed edge     = [4,21]
added edge       = [5,17]

mutable vertices = [4,5,8,9,10,12,13,14,15,17,18]
remaining        = [19,20,21,22,23]

child states     = 4
child baseline   = child index 2
matched parent ids = [8,10,12,14]
child baseline parent id = 12

child edges:
  (0,3)
  (1,2)
  (2,3)

parent induced edges on {8,10,12,14}:
  (8,14)
  (10,12)
  (12,14)
```

The parent induced-edge list above is read from the frozen W9 parent
`summary.json` and matches the child edge list under:

```text
0 -> 8
1 -> 10
2 -> 12
3 -> 14.
```

## Task 1 — regression-only calibration module

Create:

```text
DkMathTest/Tromino/OBS019Neighbor01Calibration.lean
```

Do NOT add a new production module.

The fixture may use small local inductive/Fin types. Keep all numeric frozen
data in the test layer.

## Task 2 — local Python-color decoder

Inside the test module only, define the calibration mapping:

```text
0 -> (0,0)
1 -> (0,1)
2 -> (1,0)
3 -> (1,1)
```

into `TrominoState`.

Use an explicit finite type or constructors, not an unchecked `Nat` partial
function if avoidable.

This mapping is only a representation of the four Python color labels for the
calibration. Do not export it as a production semantic theorem.

## Task 3 — encode the shared mutable coordinate order

Use exactly this order:

```text
[4,5,8,9,10,12,13,14,15,17,18]
```

A local `Fin 11` coordinate carrier is acceptable.

Define the four child projection rows exactly as frozen in neighbor-01:

```text
child 0 = [0,3,1,1,1,0,0,1,0,1,3]
child 1 = [0,3,1,1,1,0,1,0,0,1,3]
child 2 = [0,3,1,1,1,0,3,0,0,1,3]
child 3 = [0,3,1,1,1,0,3,1,0,1,3]
```

These correspond respectively to parent ids:

```text
8, 10, 12, 14.
```

Verify from the frozen parent state files that the parent mutable projections
are exactly the same four rows.

Do not copy all 32 parent states into Lean.

## Task 4 — prove exact coordinate matching

Define a local mapping:

```text
child index 0 -> parent id 8
child index 1 -> parent id 10
child index 2 -> parent id 12
child index 3 -> parent id 14
```

Prove:

```text
the mapping is injective;
each child mutable projection equals its matched parent projection;
child baseline index 2 maps to parent id 12.
```

Prefer finite case proofs / `decide` where clean.

## Task 5 — prove the frozen induced-edge match

Define only the LOCAL child relation and LOCAL parent induced relation needed
for this four-state sector.

Child relation edges:

```text
0--3
1--2
2--3
```

Parent local induced relation edges:

```text
8--14
10--12
12--14
```

Both relations must be symmetric/undirected.

Prove the exact relation transport:

```text
childEdge c d
<->
parentInducedEdge (map c) (map d).
```

This theorem is the kernel-checked form of the frozen
`induced_subgraph_match = true` claim for neighbor 1.

Do not reconstruct all 48 W9 parent edges.

## Task 6 — rooted component calibration

Use child baseline index `2` as root.

Prove all four child states are reachable from root under the frozen child
edge relation.

Equivalently prove the rooted child component is exactly `{0,1,2,3}`.

Then prove the mapped parent local rooted component is exactly
`{8,10,12,14}`.

A Finset statement is welcome if small, but ordinary pointwise reachability
theorems are sufficient.

## Task 7 — instantiate the generic transport kernel

Build a test-local `RootedChamberTransport` using:

```text
Child  = the four frozen child states
Parent = the four selected frozen parent-sector states
project = the exact child->parent mapping
childStep = frozen child edge relation
parentStep = frozen parent induced edge relation
parentAdmissible = True on the four-state parent-sector carrier
```

If representing Parent directly as the four selected states is cleaner, keep
a separate theorem exposing their original ids 8/10/12/14.

Use the existing checkpoint-004 theorem:

```text
RootedChamberTransport.reachable_iff_admissibleChamber
```

to prove the final calibration statement.

This is regression calibration, not a new production abstraction.

## Task 8 — provenance guard

Add simple compile-time theorems/definitions recording:

```text
obs019Neighbor01Seed = 11000009
obs019Neighbor01Step = 16
obs019Neighbor01Move = (4,21,5,17)
obs019Neighbor01ParentIds = [8,10,12,14]
```

Use test-local constants. The point is to make accidental drift visible in
future edits.

Do not build a JSON parser in Lean.

## Task 9 — optional height data boundary

The corresponding parent first-exit depths are frozen as:

```text
parent id 8  -> 9
parent id 10 -> 9
parent id 12 -> 10
parent id 14 -> 9
```

You MAY record these as test-local provenance constants.

Do NOT derive or claim child-height preservation, cross-topology monotonicity,
or any new height theorem from them.

Height is not the target of this closeout checkpoint.

## Task 10 — axiom audit

Create:

```text
DkMathTest/Tromino/OBS019Neighbor01AxiomAudit.lean
```

Audit at least:

```text
coordinate-match theorem
induced-edge exactness theorem
rooted child reachability theorem
test-local RootedChamberTransport construction
final chamber-equivalence calibration theorem
```

No new axiom declarations.

## Task 11 — campaign documentation closeout

After the calibration builds, update:

```text
lean/dk_math/docs/dev/Tromino-RepairHeight-Sectorization-260930-v0/README.md
lean/dk_math/docs/dev/Tromino-RepairHeight-Sectorization-260930-v0/ROADMAP.md
```

to mark:

```text
TRH-009 COMPLETE / APPROVED
campaign status COMPLETE / READY FOR PR
```

Preserve the explicit nonclaims:

```text
no universal preserving-flip transport theorem;
no cross-topology repair-height monotonicity;
no height preservation theorem;
no W9 full-table theorem;
no Four Color theorem;
no Port-chain closure.
```

## Task 12 — final report

Create:

```text
lean/dk_math/docs/dev/Tromino-RepairHeight-Sectorization-260930-v0/report-007.md
```

Record:

```text
overall Outcome A / B / C
authoritative frozen source files
seed / step / neighbor / move
mutable coordinate order
four child projection rows
matched parent ids
edge lists
baseline mapping
coordinate-match theorem names
induced-edge theorem name
rooted component theorem names
RootedChamberTransport fixture name
final chamber-equivalence calibration theorem
axiom audit
build results
git diff --check
forbidden-token scan
warnings
final campaign status
remaining research frontier
```

## Explicit non-goals

Do not implement or claim:

```text
the whole 32-state W9 table in Lean
all six OBS-019 exact neighbors
the eleven state-regenerating neighbors
a face-level triangulation implementation
a universal preserving-flip theorem
safe-candidate ranking
repair BFS
cross-topology repair-height monotonicity
childHeight <= parentHeight
height-label preservation
Four Color Theorem
Port-chain closure
```

## Validation

From `lean/dk_math` run:

```text
lake build DkMathTest.Tromino.OBS019Neighbor01Calibration
lake build DkMathTest.Tromino.OBS019Neighbor01AxiomAudit
lake build DkMath.Tromino.RestorationFlipTransport
lake build DkMath.Tromino.RestorationRepairState
lake build DkMath.Tromino.StateProjectionTransport
git diff --check
```

Scan changed Lean files for:

```text
sorry
admit
axiom
unsafe
```

Outcome A:

```text
the frozen OBS-019 neighbor-01 data is kernel-calibrated against the generic
transport abstraction;
the campaign is complete and ready for PR to develop.
```

Outcome B:

```text
the frozen coordinate/edge data calibrates, but generic packet construction
needs a small test-fixture API repair; keep production unchanged and report
the exact issue.
```

Outcome C:

```text
the committed frozen data does not agree with the claimed 4-state exact
transport pattern; report the exact mismatch and do not edit the source data
to force success.
```
