# TRM-013 report: closed transition network / alternating involutions

Date: 2026-09-25
Branch: `research/Tromino-ExchangeCalculus-260924-v0`

## Scope

TRM-013 adds the first global finite transition layer above TRM-012. A
`BoundaryNetwork` records finitely many region-indexed boundary signatures.
`NetworkPort` retains both the region identity and the local port index.
`ClosedBoundaryNetwork` packages a label-preserving involutive crossing, a
same-label local pairing at every region, and the perfectness condition that
each local residual set is empty.

The implementation stops at the finite two-neighbor transition structure and
periodic orbits. It does not introduce odd residual endpoints, ghost ports,
physical boundary extraction, planar or cyclic order, noncrossing claims,
XOR/path transport, `BoundaryIR`, optimization, or Four Color reasoning.

## Production API

Production is `DkMath/Tromino/TransitionGraph.lean`:

- `BoundaryNetwork`, `NetworkPort`, `BoundaryCrossing`, and
  `ClosedBoundaryNetwork` provide the closed finite network certificate;
- `crossPort` exposes the involutive crossing and proves region change,
  non-selfness, and label preservation;
- `localMatePort` applies the local `BoundaryPairing`, with involutivity,
  region preservation, same-label preservation, and non-selfness obtained
  from local perfectness;
- `transitionNeighbors` is the two-element finite neighborhood, and
  `TransitionAdj` has symmetry, irreflexivity, and degree-two cardinality;
- `transitionStep` is `localMatePort (crossPort p)`, while
  `transitionStepInv` is `crossPort (localMatePort p)`;
- `transitionEquiv` packages the two inverse laws, with separate injectivity
  and surjectivity theorems;
- `transitionStep_sameLabel` and its iterate form preserve the boundary delta;
- `transitionStep_periodic` obtains a positive period from the finite
  permutation order, without claiming that one step is itself involutive.

No `SimpleGraph` dependency was needed: the explicit `TransitionAdj` relation
is sufficient for the requested finite symmetric degree-two layer.

## Two-region audit

`DkMathTest/Tromino/TransitionGraphAxiomAudit.lean` constructs two regions,
each with signature `A A`, and uses the canonical local pairings. The crossing
swaps the two region indices while preserving the local index. The audit
checks:

1. the total `NetworkPort` type has four elements;
2. crossing and local pairing are involutive;
3. the transition neighborhood has cardinality two;
4. adjacency is symmetric and irreflexive;
5. the opposite exchange order is a left inverse;
6. every port has a positive periodic transition orbit; and
7. one transition preserves its boundary label.

## Computability and axiom audit

The production and audit sources contain no `sorry`, `admit`, `unsafe`,
`noncomputable`, or new project-local `axiom` declaration. The finite
transition definitions are ordinary executable declarations. The focused
`#print axioms` output reports the existing foundational dependencies
(`propext`, `Quot.sound`, and `Classical.choice` through finite ordered-set
infrastructure); no new project-local axiom is introduced.

## Validation

Focused builds completed successfully:

```text
lake build DkMath.Tromino.TransitionGraph
lake build DkMathTest.Tromino.TransitionGraphAxiomAudit
```

The audit build completed successfully at 1498 jobs. The only emitted build
warning is the pre-existing `PieceExchange` unnecessary-`simpa` linter
notice; no proof failure remains.

## Stop boundary

TRM-013 stops at a finite symmetric two-neighbor transition relation and the
positive periodicity of its directed permutation. Geometric embedding,
cycle-planarity, endpoint extraction, and global combinatorial conclusions
remain deferred.
