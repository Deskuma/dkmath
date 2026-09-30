# Tromino Repair Height Sectorization — instruction-006 closeout

Date: 2026-10-01

## Overall outcome

Outcome A. The local single-edge replacement delta is formalized, the exact
rooted-sector compatibility is isolated as an explicit certificate, and that
certificate instantiates the generic `StateProjectionTransport` kernel.

The module remains independent of the Port triangulation/reduction chain.

## Files added

- `DkMath/Tromino/RestorationFlipTransport.lean`;
- `DkMathTest/Tromino/RestorationFlipTransportRegression.lean`;
- `DkMathTest/Tromino/RestorationFlipTransportAxiomAudit.lean`;
- this report.

## Production API

The undirected endpoint predicate is `SameUndirectedEdge`. The local topology
delta is represented by:

```text
SingleEdgeReplacement GParent GChild u v a b
```

It records the old parent edge, the new parent nonedge, and the full child
adjacency equivalence. The main consequences are:

- `SingleEdgeReplacement.old_edge_absent`;
- `SingleEdgeReplacement.new_edge_present`;
- `SingleEdgeReplacement.adj_unchanged`;
- `SingleEdgeReplacement.adj_at_unchanged`.

Properness transport is exposed by:

- `properOnColored_parent_to_child`;
- `properOnColored_child_to_parent`;
- `restorationContext_proper_parent_to_child`;
- `restorationContext_proper_child_to_parent`.

The endpoint-excluded Missing-Color locality theorem is
`missingAt_flip_locality`. No global `MissingValid` preservation claim is
made.

## Restoration-sector certificate

`RestorationFlipContext` packages the replacement and the shared colored and
remaining predicates without requiring equal parent/child base assignments.

`ExactRestorationSectorCertificate` contains:

- `child_root_admissible`;
- `parent_on_child_chamber`, restricted to states reachable in the rooted
  child admissible relation.

The exact shared-coordinate theorem is
`exactRestorationSector_iff`. The relation identity and child-facing form are:

- `exactRestorationSector_edge_iff`;
- `childAdmissibleRestorationStep_iff_transport`.

The rooted child chamber is `RootedChildChamber`. The subtype-value packet is
constructed by `exactRestorationSectorTransport`, and its main generic
chamber theorem is `exactRestorationSectorTransport_chamber_iff`.

The API and comments keep the separation explicit: a
`SingleEdgeReplacement` does not itself provide an
`ExactRestorationSectorCertificate`.

## Regression

The finite regression checks:

- removal of the old diagonal and addition of the new diagonal;
- unchanged adjacency away from the four endpoints;
- both properness transport directions;
- `MissingAt` locality outside the flip endpoints;
- a parent/child restoration context on shared mutable coordinates;
- the rooted exact-sector equivalence;
- construction and use of the `RootedChamberTransport` packet.

The context uses fixed colors at vertices 0 and 1 and mutable vertices 2 and
3, with the child edge between the mutable vertices. It is a small
two-state-sector calibration fixture; no W9 table is encoded.

## Axiom audit

The audit reports no axioms for the local adjacency and MissingAt theorems.
The restoration-sector and packet theorems depend only on the standard
`propext`, `Classical.choice`, and `Quot.sound` dependencies inherited from
the existing restoration and transport kernels. No new axiom declaration was
added.

## Validation

The following builds succeeded sequentially without warnings:

```text
lake build DkMath.Tromino.RestorationFlipTransport
lake build DkMathTest.Tromino.RestorationFlipTransportRegression
lake build DkMathTest.Tromino.RestorationFlipTransportAxiomAudit
lake build DkMath.Tromino.RestorationRepairState
lake build DkMath.Tromino.StateProjectionTransport
```

`git diff --check` and no-index checks for the three new files produced no
whitespace diagnostics after cleanup. The changed Lean files contain no
`sorry`, `admit`, `axiom`, or `unsafe` tokens.

## Deviations and remaining requirements

The regression keeps the two-state calibration as a small context fixture;
the production theorem is deliberately certificate-driven and does not export
a finite cardinality theorem. A concrete provider still requires:

- a real topology-changing triangulation flip;
- a proof of the corresponding child/parent restoration certificate;
- separate finite calibration for the six OBS-019-compatible cases.

This checkpoint does not claim that every preserving flip is transport
compatible, nor does it add W9 data, safe-candidate ranking, repair BFS,
cross-topology height monotonicity, height-label preservation, Four Color, or
any Port reduction result.
