# Tromino RepairHeight Sectorization — instruction-004 closeout

Date: 2026-09-30

## Overall outcome

Outcome A. The complete instruction-004 checkpoint succeeded: generic chamber
transport, shared mutable-coordinate projection, regressions, audits, and
validation are all complete.

The A/B/C labels below are work-section labels from the implementation report,
not separate checkpoint outcome grades.

## Outcome A — generic rooted chamber transport

Added `DkMath/Tromino/StateProjectionTransport.lean`.

The module is graph-independent and provides `RootedChamberTransport` with
the requested injective projection, root alignment, admissible parent root,
step mapping, and step lifting fields.  It also provides:

- exact-length path mapping through `map_steps`;
- exact-length path lifting through `lift_steps`;
- the central equivalence
  `Reachable childStep childRoot c ↔ AdmissibleChamber ... (project c)`;
- the image characterization of the parent chamber;
- induced edge exactness on projected child points.

The proofs use the existing exact-length `Steps` and the existing
`AdmissibleChamber` definition.  No relation or root semantics were changed.

## Outcome B — shared mutable coordinates

The same module adds the graph-independent `MutableCoordinates`,
`AgreesOutside`, and `SameMutableProjection` interfaces, together with:

- `mutableColorProjection`, whose codomain depends only on the vertex type and
  mutable predicate;
- fixed-context injectivity for same-graph colorings agreeing outside the
  mutable set;
- the equivalence between `SameMutableProjection` and pointwise equality on
  mutable vertices for colorings on different graphs with the same vertex
  type.

No child coloring is coerced into a parent coloring.

## Outcome C — regression, audit, and boundary

Added:

- `DkMathTest/Tromino/StateProjectionTransportRegression.lean`;
- `DkMathTest/Tromino/StateProjectionTransportAxiomAudit.lean`.

The regression covers an abstract two-point child relation mapped into one
component of a four-point parent relation, while a second admissible parent
component remains outside the root chamber.  It checks chamber equivalence,
the exact image statement, induced edge exactness, and the extra-component
boundary.  It also checks mutable-coordinate comparison across two different
tiny graph topologies on the same vertex type, plus fixed-context injectivity.

The following validation commands succeeded:

```text
lake build DkMath.Tromino.StateProjectionTransport
lake build DkMathTest.Tromino.StateProjectionTransportRegression
lake build DkMathTest.Tromino.StateProjectionTransportAxiomAudit
lake build DkMath.Tromino.StateSector
lake build DkMath.Tromino.RepairChamber
```

The axiom audit reports no axioms for the generic path map/lift, chamber
equivalence, image, or induced-edge theorems.  The coloring extensionality
theorems report the standard `propext`, `Classical.choice`, and `Quot.sound`
dependencies.

`git diff --check` and no-index checks for the new files produced no whitespace
diagnostics.  The forbidden-construct scan found no `sorry`, `admit`, new
anchored `axiom`, or `unsafe` occurrence in the added modules.

The only warnings are pre-existing `Symmetric` deprecation warnings in the
Tromino dependency chain, existing flexible-simp warnings in the imported
tiny coloring fixture, and local test-fixture linter suggestions for the
abstract packet proof.

## Remaining requirements

This checkpoint intentionally does not provide a concrete `OBS-019` child
provider, a universal flip transport theorem, a `MissingColor` theorem, a
cross-topology height theorem, a `childHeight` construction, a Four Color
theorem, or a Port chain.  Those require a separate concrete transport packet
and are not implied by the generic projection/chamber API.
