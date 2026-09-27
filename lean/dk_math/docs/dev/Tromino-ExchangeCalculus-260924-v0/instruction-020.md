# TRM-021 — SimpleGraph/Dart bridge / standard Coloring landing

## Goal

Bridge the completed label-only RegionPotential theory into Mathlib's standard
SimpleGraph / Dart / Coloring APIs.

This checkpoint is not planar-map extraction yet.

The goals are:

1. forget the FlowNetwork crossing multigraph to a region SimpleGraph;
2. map each FlowNetworkPort to a Mathlib SimpleGraph.Dart;
3. make the information loss from parallel edges explicit;
4. turn any RegionPotential into a Mathlib SimpleGraph.Coloring TrominoState;
5. show zero holonomy + rooted reachability therefore gives a standard proper
   four-state graph coloring of the supplied region graph.

Do not claim planarity, arbitrary planar-map extraction, or the Four-Color theorem.

## Mathlib API basis

Use current Mathlib APIs:

- SimpleGraph.fromRel
- SimpleGraph.Dart
- SimpleGraph.Dart.symm
- SimpleGraph.Coloring
- SimpleGraph.Coloring.mk

Do not build a competing graph/coloring framework.

## Production

Create:

DkMath/Tromino/GraphColoringBridge.lean

Import RegionPotential and the specific Mathlib graph/coloring modules needed.

## A. Underlying region SimpleGraph

For N : FlowNetwork and C : FlowCrossing N define:

```lean
def regionSimpleGraph (C : FlowCrossing N) :
  SimpleGraph (Fin N.regionCount)
```

using the existence of a crossing port from one region to another.

A preferred underlying relation is:

```text
r -> s iff exists p : FlowNetworkPort N,
  p.1 = r and (C.cross p).1 = s.
```

Use SimpleGraph.fromRel or a direct SimpleGraph constructor.

Required theorems:

- every crossing port induces adjacency:
  regionSimpleGraph C .Adj p.1 (C.cross p).1;
- adjacency is exactly existence of at least one crossing port between the
  two regions, up to the orientation convention;
- no loops, following C.changesRegion.

Because crossing is involutive, the relation is already symmetric. If
fromRel is used, simplify the iff theorem accordingly.

## B. Parallel-edge information boundary

FlowNetworkPort can distinguish multiple physical crossing ports connecting
the same two regions.

SimpleGraph cannot: it records only adjacency.

Document and theorem-test this information boundary.

Do not claim a bijection between FlowNetworkPort and SimpleGraph.Dart.

If useful, provide a fixture with two distinct ports whose resulting darts are
equal.

This is expected and important.

## C. Port to Dart

Define:

```lean
def flowPortToDart
  (C : FlowCrossing N)
  (p : FlowNetworkPort N) :
  (regionSimpleGraph C).Dart
```

with:

- fst = flowEdgeSource C p;
- snd = flowEdgeTarget C p.

Prove simp-style theorems for fst/snd.

Main reversal theorem:

```text
flowPortToDart C (reverseEdge C p)
=
(flowPortToDart C p).symm.
```

This should align DkMath's crossing involution with Mathlib Dart.symm.

Also prove Dart.edge is unchanged under crossing/reversal, either by reuse of
Mathlib Dart.edge_symm or by the above theorem.

## D. Dart has a port witness

Because SimpleGraph adjacency is generated from crossing ports, prove:

For every d : (regionSimpleGraph C).Dart,
there exists p : FlowNetworkPort N such that

- p.1 = d.fst;
- (C.cross p).1 = d.snd.

Do not claim uniqueness.

This theorem is the precise relation between the simple graph and the original
port multigraph.

## E. RegionPotential to Mathlib Coloring

Define:

```lean
def RegionPotential.toColoring
  (P : RegionPotential C) :
  (regionSimpleGraph C).Coloring TrominoState
```

using SimpleGraph.Coloring.mk with color := P.state.

The validity proof should use:

- adjacency -> crossing-port witness;
- regionPotential_adjacent_ne.

Required simp theorem:

```text
P.toColoring r = P.state r.
```

Do not create a new four-color carrier: TrominoState already has card 4.

## F. Four-state cardinal calibration

Expose or prove:

```text
Fintype.card TrominoState = 4
```

by reusing card_state if possible.

Then prove the coloring is genuinely a coloring by a 4-element type.

If Mathlib's Colorable API is convenient, derive:

```text
(regionSimpleGraph C).Colorable 4.
```

Prefer using P.toColoring.colorable and card_state.

If the exact theorem requires typeclass plumbing, a theorem exhibiting
Nonempty ((regionSimpleGraph C).Coloring TrominoState) plus card_state is
sufficient.

## G. Recovery-to-standard-coloring theorem

Package the main bridge:

Given:

- base : Fin N.regionCount;
- RootedRegionConnected C base;
- RegionZeroHolonomy C;

prove existence of:

```text
(regionSimpleGraph C).Coloring TrominoState
```

and, if clean:

```text
(regionSimpleGraph C).Colorable 4.
```

Construction:

1. use TRM-020 regionPotential_exists_of_zeroHolonomy with any baseState,
   preferably 0;
2. convert the potential with RegionPotential.toColoring.

This is a standard graph-coloring landing theorem for the supplied flow
certificate.

State scope carefully:

It does not prove such a flow certificate exists for every planar graph.

## H. Converse calibration from potential/coloring

Do not claim every arbitrary Mathlib Coloring determines the existing
FlowSignature labels unless a label assignment is supplied.

However, for a RegionPotential-derived coloring, prove the original crossing
label is recovered:

```text
P.toColoring source + P.toColoring target
=
flowEdgeLabel C p.
```

This should be a thin corollary of regionPotential_edgeLabel.

## I. Connectedness bridge — optional

Mathlib has SimpleGraph.Reachable / Walk APIs.

If the bridge is small, prove:

```text
RegionReachable C r s ->
(regionSimpleGraph C).Reachable r s.
```

The converse should also hold because every SimpleGraph adjacency has a port
witness, but implementing full Mathlib Walk conversion may be more work.

Treat this as optional. Do not let it block the core Dart/Coloring bridge.

## J. Audit fixtures

Create:

DkMathTest/Tromino/GraphColoringBridgeAxiomAudit.lean

Audit at least:

1. two-region pure Flow fixture produces a SimpleGraph adjacency;
2. a port maps to a Dart with expected endpoints;
3. crossing/reverse port maps to Dart.symm;
4. explicit RegionPotential maps to a Mathlib Coloring;
5. coloring values are expected 0 / deltaA in the two-region fixture;
6. every graph adjacency receives distinct states;
7. Colorable 4 if implemented;
8. duplicate/parallel A A ports may map to the same Dart, confirming
   non-injectivity is intentional;
9. the three-region odd-holonomy fixture cannot yield a RegionPotential, so
   this checkpoint must not manufacture a coloring through the recovery theorem.

## K. Mathlib / planarity boundary

Record in the report:

- Mathlib has SimpleGraph, Dart, Walk, Coloring infrastructure;
- no standard planar embedding / rotation-system API was identified in the
  repository survey used for this checkpoint.

Therefore the next planar layer will likely require a DkMath combinatorial-map
certificate rather than assuming an existing Mathlib planar-map object.

Do not implement that object in TRM-021.

## L. Computability / axioms

Definitions:

- regionSimpleGraph
- flowPortToDart
- RegionPotential.toColoring

should be ordinary computable definitions where Mathlib's API permits.

No sorry, admit, unsafe, new axiom, or new noncomputable production declaration.

## M. Validation

Build:

- DkMath.Tromino.RegionPotential
- DkMath.Tromino.GraphColoringBridge
- DkMathTest/Tromino/GraphColoringBridgeAxiomAudit

Regression-build:

- DkMathTest/Tromino.RegionPotentialAxiomAudit
- DkMathTest/Tromino.RegionWalkAxiomAudit

Run git diff --check, forbidden-construct scan, and #print axioms.

## N. Report

Create:

docs/dev/Tromino-ExchangeCalculus-260924-v0/report-020.md

Record:

- regionSimpleGraph representation;
- exact adjacency iff theorem;
- port-to-Dart bridge;
- reversal/Dart.symm theorem;
- parallel-edge information loss;
- RegionPotential -> Mathlib Coloring bridge;
- Colorable 4 result if available;
- recovery theorem from zero holonomy;
- Mathlib planarity API survey result;
- recommended next combinatorial-map / rotation-system checkpoint.

## Stop condition

Stop once a label-only zero-holonomy FlowNetwork can be converted, through
RegionPotential, into a standard Mathlib proper coloring of the underlying
region SimpleGraph, and the FlowNetworkPort-to-Dart relation is explicit.

Do not proceed to planar embedding, rotation systems, face extraction, ghost
completion, BoundaryIR, optimization, or Four-Color theorem claims without
review.
