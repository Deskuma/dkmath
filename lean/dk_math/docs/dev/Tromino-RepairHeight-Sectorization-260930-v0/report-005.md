# Tromino RepairHeight Sectorization — instruction-005 closeout

Date: 2026-09-30

## Overall outcome

Outcome A. The partial restoration state, Missing-valid semantics, induced
colored-graph bridge, and parent/child admissibility filter are formalized and
kernel-checked. The next checkpoint may attempt a concrete topology-flip
transport provider.

## Production files

Added:

- `DkMath/Tromino/RestorationRepairState.lean`;
- `DkMathTest/Tromino/RestorationRepairStateRegression.lean`;
- `DkMathTest/Tromino/RestorationRepairStateAxiomAudit.lean`.

The existing `KempeRepair` and `StateProjectionTransport` modules were used as
dependencies and were not extended with topology-specific claims.

## Restoration state and predicates

`RestorationContext G mutable` carries:

- `colored` and `remaining` predicates;
- a graph-independent `base : V → TrominoState` assignment;
- `mutable_colored`;
- `remaining_uncolored`.

The restoration coordinate carrier is the existing
`MutableCoordinates mutable`.  The realization is:

```text
realize context state v =
  if mutable v then state ⟨v, h⟩ else context.base v
```

The exported realization facts are `realize_mutable`, `realize_outside`, and
`realize_injective`.

`ProperOnColored G colored assignment` checks only edges whose two endpoints
are colored.  `MissingAt` states that one `TrominoState` color is absent from
all colored neighbors of a vertex, and `MissingValid` requires this at every
remaining vertex.  `RestorationAdmissible` is exactly the conjunction of
context properness and Missing-validity.

No counting API, palette enumeration, or `safe_candidates` theorem was added.

## One-coordinate and induced-graph bridges

`CoordinateOnePointStep mutable` uses a mutable-coordinate subtype witness,
requires a changed coordinate, and requires all other coordinates to agree.
`coordinateOnePointStep_symmetric` proves symmetry.  The restricted relation
`AdmissibleRestorationStep` is symmetric by
`admissibleRestorationStep_symmetric`.

`ColoredVertex context` is the subtype of `context.colored`, and
`ColoredGraph context` is the exact Mathlib induced graph
`G.induce {v | context.colored v}`.  `partialColoring` turns a proper partial
assignment into a proper `TrominoState` coloring of only that induced graph.
The mutable predicate is lifted with `liftedMutable`, and
`mutableToColored` supplies the canonical colored-vertex representative.

`coordinateOnePointStep_onePointRecolor` constructs the existing
`OnePointRecolor` witness from a coordinate step and proper source/target
states.  `admissibleRestorationStep_onePointRecolor` specializes this to an
admissible edge, and
`admissibleRestorationStep_singletonKempeMove` derives the existing
`SingletonKempeMove` through `onePointRecolor_singletonKempeMove`.

## Parent/child context interface

`TransportAdmissible parentContext childContext state` is the conjunction of
the parent and child `RestorationAdmissible` predicates on the shared
`MutableCoordinates mutable` carrier.

`TransportAdmissibleRestorationStep` restricts the graph-independent
coordinate step by this combined predicate.  The theorem
`transportAdmissibleRestorationStep_iff` identifies it exactly with the
parent admissible coordinate edge plus child admissibility at both endpoints.
No claim is made that a topology flip supplies this admissibility.

## Regression results

The Fin-5 regression contains colored vertices, remaining vertices, and a
mutable colored vertex. It verifies:

1. `realize` selects mutable coordinates and fixed outside values;
2. properness ignores edges incident to remaining vertices;
3. MissingAt/MissingValid succeed when a color is absent;
4. MissingValid fails for four differently colored colored neighbors;
5. a proper and Missing-valid coordinate change is an admissible restoration
   step;
6. the edge produces an induced-graph `OnePointRecolor`;
7. the same edge produces a `SingletonKempeMove`;
8. the combined parent/child filter has the intended endpoint behavior.

The fixture contains no W9 table and no search procedure.

## Validation and audit

The following commands succeeded:

```text
lake build DkMath.Tromino.RestorationRepairState
lake build DkMathTest.Tromino.RestorationRepairStateRegression
lake build DkMathTest.Tromino.RestorationRepairStateAxiomAudit
lake build DkMath.Tromino.KempeRepair
lake build DkMath.Tromino.StateProjectionTransport
```

The axiom audit reports no axioms for coordinate-step symmetry. The remaining
induced-coloring and restricted-step theorems report only the standard
`propext`, `Classical.choice`, and `Quot.sound` dependencies inherited from
the relevant Mathlib graph/coloring constructions. No new axiom declaration
was added.

`git diff --check` and no-index checks for the added files produced no
whitespace diagnostics. The forbidden-token scan found no `sorry`, `admit`,
`axiom`, or `unsafe` in the added Lean files.

The warning cleanup pass migrated the affected relations to `Std.Symm`,
replaced flexible finite-fixture simplification with explicit case proofs,
removed unused tactics and simp arguments, and fixed the constructor-name
linter. The focused production, regression, and audit builds now emit no
warnings. Axiom-audit `info` lines are dependency reports, not build warnings.

## Deviations and remaining requirements

`realize` and `partialColoring` are marked `noncomputable` because their
predicate-indexed branches use classical decidability; this does not add an
axiom declaration or finite-search dependency.

The remaining concrete requirements are a real topology-changing flip
provider, its child/parent admissibility proof, and any sound transport packet
needed to apply the shared-coordinate API. This checkpoint does not claim
safe-candidate ranking, repair search, cross-topology height monotonicity,
`childHeight ≤ parentHeight`, height-label preservation, the six OBS-019
sectors as a universal theorem, Four Color, or a Port reduction result.
