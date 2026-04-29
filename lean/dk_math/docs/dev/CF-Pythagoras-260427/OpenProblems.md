# CF-Pythagoras Open Problems

cid: 69e72cfc-9944-83e8-8786-53c02b36fb89

This note records the tasks intentionally left open at the end of Chapter 2.
It is not a failure list; it is the handoff boundary for the next branch.

## P0: Cubic Exceptional Branch

Chapter 2 closes the ordinary cubic primitive branch, where the primitive prime
satisfies `q != 3`.  The branch `q = 3` remains separate because the current
valuation contradiction route uses the hypothesis `q ∤ 3`.

Next action:

```text
Design a separate `CubicExceptionalFLTContext` or theorem family for q = 3.
```

Questions to settle:

- Which replacement invariant handles the prime that divides the degree?
- Should the exceptional branch use a different valuation normalization?
- Can the existing PowerBeam/GN bridge still be reused after the valuation
  split changes?

## P1: Automatic GN Fuel Supply

The current context endpoints consume one of the following inputs:

```text
v_q(GN(3, a-b, b)) <= 1
Squarefree(|GN(3, a-b, b)|)
```

They do not yet derive that fuel automatically.

Next action:

```text
Connect primitive / Zsigmondy / squarefree APIs so that the GN-side fuel can be
produced by a reusable theorem.
```

Questions to settle:

- Which Zsigmondy theorem should be promoted out of research files?
- Can the existing `ZsigmondyCyclotomicSquarefree` layer produce exactly the
  shape expected by `CubicPrimitiveFLTContext`?
- Should the fuel be supplied as valuation upper bounds, squarefreeness, or both?

## P2: General Degree Bridge

The current ordinary branch is specialized to `d = 3`.  Earlier layers already
have degree-parametric PowerGap / PowerBeam definitions, but the primitive
context and clean contradiction endpoints are cubic-specific.

Next action:

```text
Identify the smallest degree-parametric API that preserves the clean cubic
surface while preparing for d >= 4.
```

Questions to settle:

- Which parts of `PowerGapBeamGcd` should remain degree-parametric?
- Where should degree-specific exceptional branches live?
- Should there be a generic `PrimitiveFLTContext d` before adding more
  degree-specific contexts?

## P3: d = 4 Route

The Pythagorean square-lift viewpoint naturally points toward the fourth-power
route.  This should be treated as a separate route, not mixed into the cubic
ordinary branch.

Next action:

```text
Draft the d = 4 route map from square-lifted Pythagorean data to a PowerBeam or
descent-style obstruction.
```

Questions to settle:

- Is the d = 4 route best handled by PowerBeam valuation, classical descent, or
  a bridge between them?
- Which existing Pythagorean parametrization lemmas are reusable?
- Should the route start from primitive Pythagorean triples or from general FLT
  shape?

## P4: Import Boundary / Aggregation

`PowerGapBeamGN` should stay lightweight.  `PowerGapBeamPrimitive` is allowed to
import heavier primitive and valuation machinery.  The aggregate import layer
should preserve that separation.

Next action:

```text
Keep the lightweight bridge importable without pulling in the existing research
`sorry` warning; isolate heavy primitive routes behind explicit imports.
```

Questions to settle:

- Should a future `DkMath.CosmicFormula.All` split lightweight and research
  imports?
- Should Chapter 2 route files be grouped under a dedicated namespace/module?
- Which warnings are acceptable in aggregate builds, and which should be kept
  out of lightweight targets?

## P5: S3 Planning

S3 should not reopen Chapter 2.  It should begin from the boundary recorded in
`RouteMap.md`, choose one unresolved axis, and make that axis explicit.

Candidate S3 directions:

- S3-A: exceptional cubic branch `q = 3`
- S3-B: GN fuel automation
- S3-C: general degree bridge
- S3-D: d = 4 route from Pythagorean square-lift data
- S3-E: import/package cleanup for lightweight vs heavy route layers
