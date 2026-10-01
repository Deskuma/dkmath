# instruction-006 — local edge-flip delta / exact-sector transport certificate

## Role

Checkpoint 005 is complete with Outcome A.

This checkpoint formalizes the topology delta used by the Python
`PlantedTriangulation.apply_flip` and separates it from the additional
state-space certificate required for exact OBS-019 transport.

The Python flip semantics are:

```text
remove diagonal (u,v)
add diagonal    (a,b)
all other graph adjacencies unchanged.
```

Do NOT prove that every legal/preserving flip is transport-compatible.
The OBS-019 census explicitly found only 6 exact child-admissible sectors
among 17 preserving neighbors.

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
lean/dk_math/docs/dev/Tromino-RepairHeight-Sectorization-260930-v0/report-005.md
python/Tromino/experiments/OBS-019-SixExactChildAdmissibleSectors/README.md
python/Tromino/search/repair_depth_search.py
```

Inspect exact current APIs:

```text
DkMath/Tromino/RestorationRepairState.lean
DkMath/Tromino/StateProjectionTransport.lean
DkMath/Tromino/RepairChamber.lean
```

## Task 1 — create production module

Create:

```text
DkMath/Tromino/RestorationFlipTransport.lean
```

Keep the new module independent of the Port triangulation reduction chain.

## Task 2 — unordered graph-edge identity

Define a tiny predicate for equality with an undirected edge:

```text
SameUndirectedEdge x y u v
```

with semantics:

```text
(x = u and y = v) or (x = v and y = u).
```

Prove the obvious symmetry/orientation lemmas needed below.

Do not introduce a heavy quotient edge type merely for this checkpoint.

## Task 3 — local single-edge replacement

For two simple graphs on the SAME vertex type:

```lean
GParent GChild : SimpleGraph V
```

define a structure/predicate, preferably:

```text
SingleEdgeReplacement GParent GChild u v a b
```

carrying at least:

```text
old_edge : GParent.Adj u v
new_nonedge : not GParent.Adj a b

adj_iff : for all x y,
  GChild.Adj x y iff
    (GParent.Adj x y and not SameUndirectedEdge x y u v)
    or SameUndirectedEdge x y a b.
```

The exact package may additionally record useful endpoint distinctness if
required by SimpleGraph irreflexivity.

This is the Lean abstraction of Python `apply_flip`.

Required consequences:

```text
old diagonal is absent in child;
new diagonal is present in child;
adjacency is unchanged for pairs that are neither the old nor new diagonal.
```

Do not encode triangular faces in this checkpoint.

## Task 4 — properness transport under one edge replacement

Using `ProperOnColored`, prove both directional criteria.

Parent -> child:

```text
ProperOnColored GParent colored assignment
and
(colored a -> colored b -> assignment a != assignment b)
->
ProperOnColored GChild colored assignment.
```

The removed old edge cannot create a violation; only the added new edge needs
the extra endpoint-separation condition.

Child -> parent:

```text
ProperOnColored GChild colored assignment
and
(colored u -> colored v -> assignment u != assignment v)
->
ProperOnColored GParent colored assignment.
```

Only the removed old diagonal needs to be checked when reconstructing parent
properness.

Expose context/state corollaries when parent and child contexts share the
same colored predicate and the same realized assignment.

Do not claim either direction without the required diagonal-color condition.

## Task 5 — MissingAt locality under the topology delta

Prove that adjacency at a vertex `w` is unchanged when `w` is not one of:

```text
u, v, a, b.
```

Then derive a MissingAt locality theorem.

At minimum, for the SAME colored predicate and SAME assignment:

```text
w notin {u,v,a,b}
->
MissingAt GParent colored assignment w
<->
MissingAt GChild colored assignment w.
```

If a small more general congruence lemma for MissingAt is useful, it may be
added first.

Do NOT claim MissingValid is globally preserved by a flip. Endpoint remaining
vertices may gain or lose a colored neighbor.

## Task 6 — compatible restoration-context delta

Package the non-topological context data needed to compare parent and child
restoration states.

Suggested structure:

```text
RestorationFlipContext
```

or equivalent, containing:

```text
replacement : SingleEdgeReplacement ...
parentContext : RestorationContext GParent mutable
childContext  : RestorationContext GChild mutable
same_colored  : parentContext.colored = childContext.colored
same_remaining : parentContext.remaining = childContext.remaining
```

Do NOT require the two `base` assignments to be equal. Python restore-prefix
recomputation can change fixed outside-mutable colors between parent/child
contexts.

The shared state carrier remains:

```text
MutableCoordinates mutable.
```

## Task 7 — exact rooted sector certificate

The exact OBS-019 transport condition is not a theorem of edge replacement
alone. Package it explicitly.

Recommended certificate:

```text
ExactRestorationSectorCertificate
```

for:

```text
parentContext
childContext
root : MutableCoordinates mutable
```

with at least:

```text
child_root_admissible : RestorationAdmissible childContext root

parent_on_child_chamber :
  for all state,
  Reachable (AdmissibleRestorationStep childContext) root state
  -> RestorationAdmissible parentContext state.
```

This second field is the proof-level version of the Python condition:

```text
every projected child-component state is found inside the parent admissible
component/state set.
```

Do not strengthen it to:

```text
forall state, child admissible state -> parent admissible state
```

unless such a stronger theorem is independently available.

## Task 8 — exact sector theorem from the certificate

Prove:

```text
Reachable (AdmissibleRestorationStep childContext) root state
<->
AdmissibleChamber
  (CoordinateOnePointStep mutable)
  (TransportAdmissible parentContext childContext)
  root state.
```

This is the corrected OBS-019 sector statement on the shared coordinate
carrier.

Forward direction:

```text
child reachable
-> every child path state is child admissible;
-> certificate supplies parent admissibility on the rooted child chamber;
-> same coordinate edges become TransportAdmissibleRestorationStep edges.
```

Reverse direction:

```text
combined parent/child admissible restricted path
-> in particular every edge is a child admissible coordinate edge;
-> child reachability.
```

Use the existing `Steps` / `Reachable` / `AdmissibleChamber` kernels.

Do not force this theorem through `RootedChamberTransport` if the rooted-only
certificate makes a direct proof substantially cleaner.

## Task 9 — exact edge identity on the certified sector

Prove the local relation identity:

```text
TransportAdmissibleRestorationStep parentContext childContext source target
iff
AdmissibleRestorationStep parentContext source target
and RestorationAdmissible childContext source
and RestorationAdmissible childContext target.
```

Reuse the existing theorem where possible.

Also prove the child-facing form:

under parent admissibility of the two endpoints,

```text
AdmissibleRestorationStep childContext source target
iff
TransportAdmissibleRestorationStep parentContext childContext source target.
```

This is the theorem-level analogue of the Python induced-subgraph equality on
states already known to lie in both admissibility domains.

## Task 10 — certificate implies StateProjectionTransport packet on the
rooted child chamber subtype

Define the rooted child-chamber subtype:

```text
{state // Reachable (AdmissibleRestorationStep childContext) root state}
```

or an equivalent named abbreviation.

Using subtype value as the projection, build a
`RootedChamberTransport` whose parent relation/admissibility represents the
combined parent/child filtered state graph.

The packet must reuse the checkpoint-004 generic transport API and provide:

```text
projection injectivity;
root alignment;
map_step;
lift_step.
```

This verifies that the new concrete restoration certificate actually feeds
the generic transport kernel rather than living beside it.

## Task 11 — what the edge flip does NOT prove

Add production-facing theorems or comments making the separation explicit:

```text
SingleEdgeReplacement
does not by itself provide
ExactRestorationSectorCertificate.
```

No fake theorem or negative metatheorem is needed; the API separation and
module documentation are sufficient.

## Task 12 — finite regressions

Add:

```text
DkMathTest/Tromino/RestorationFlipTransportRegression.lean
```

Include two small fixtures.

### Regression A — local edge replacement

Use a finite graph where one diagonal is removed and another added.

Verify:

```text
old edge absent in child;
new edge present in child;
unaffected adjacency equivalence;
parent properness transfers to child when the new endpoints differ;
child properness transfers to parent when the old endpoints differ;
MissingAt is unchanged at a vertex outside the four flip endpoints.
```

### Regression B — exact rooted sector certificate

Use tiny parent/child restoration contexts on the shared coordinate carrier
where:

```text
the child root component has 2 or 3 states;
all states in that rooted child component are parent-admissible;
the parent has at least one additional admissible state/component;
```

and verify:

```text
child reachability iff combined parent/child admissible chamber membership;
the rooted child-chamber subtype builds the generic transport packet.
```

Also include a tiny counter-calibration state showing why a blanket
`child admissible -> parent admissible` assumption is not built into the API,
if this is easy to express without bloating the fixture.

Do not encode W9.

## Task 13 — axiom audit

Add:

```text
DkMathTest/Tromino/RestorationFlipTransportAxiomAudit.lean
```

Audit at least:

```text
unaffected adjacency theorem
properness parent->child
properness child->parent
MissingAt locality
exact rooted sector theorem
child-facing edge exactness theorem
rooted child-chamber transport packet / its main chamber theorem
```

No new axiom declarations.

## Explicit non-goals

Do not implement or claim:

```text
a face-level triangulation flip object
that every preserving Python flip satisfies the exact-sector certificate
a concrete W9 state table
the six OBS-019 cases as a universal theorem
safe-candidate ranking
repair BFS
cross-topology repair-height monotonicity
childHeight <= parentHeight
height-label preservation
Four Color Theorem
```

Do not modify the Port triangulation/reduction theorem chain.

## Validation

From `lean/dk_math` run:

```text
lake build DkMath.Tromino.RestorationFlipTransport
lake build DkMathTest.Tromino.RestorationFlipTransportRegression
lake build DkMathTest.Tromino.RestorationFlipTransportAxiomAudit
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

Record warnings separately from failures.

## Deliverable

Create:

```text
lean/dk_math/docs/dev/Tromino-RepairHeight-Sectorization-260930-v0/report-006.md
```

Record:

```text
overall Outcome A / B / C
files changed
SingleEdgeReplacement representation
adjacency locality theorem names
properness transfer theorem names
MissingAt locality theorem
RestorationFlipContext representation
ExactRestorationSectorCertificate representation
exact rooted sector theorem
child-facing edge exactness theorem
rooted child-chamber subtype
RootedChamberTransport packet construction
regression results
axiom audit
build results
git diff --check
forbidden-token scan
deviations
remaining requirements for any finite OBS-019 calibration provider
```

Outcome A:

```text
the local edge-replacement topology delta is production-formalized;
the exact rooted sector compatibility is isolated as an explicit certificate;
the certificate proves the OBS-019-style chamber identity and instantiates
the generic StateProjectionTransport kernel.
```

Outcome B:

```text
the topology delta or exact-sector certificate is complete, but the subtype
packet integration needs a small API repair; preserve completed theorems and
report the exact boundary.
```

Outcome C:

```text
the rooted-only compatibility certificate is insufficient for the requested
exact sector or packet theorem; report the missing hypothesis explicitly and
do not replace it with a blanket global child->parent admissibility axiom.
```
