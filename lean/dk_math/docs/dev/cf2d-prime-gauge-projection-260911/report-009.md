# CPG-V1-009 — Projection / CF2D bridge

Date: 2026-09-12  
Status: complete

## Implemented API

Added the production Projection owner:

- [Basic.lean](../../../DkMath/CosmicFormula/Projection/Basic.lean)
- [CF2DBridge.lean](../../../DkMath/CosmicFormula/Projection/CF2DBridge.lean)

The namespace is `DkMath.CosmicFormula.Projection`. The minimal rational real
map from the sample source is now available as:

```lean
Pi P = -P / (P + 1)
U P = 1 / (P + 1)
```

The production theorems are:

```text
cosmicProjection_gap_eq
cosmicProjection_inverse
cosmicProjection_injective
projectionGap_eq_regularPhaseStep
projection_add_one_eq_regularPhaseStep
```

The first three establish the gap identity, involution, and injectivity on the
explicit non-pole domain. The CF2D bridge instantiates the projection at
`P = (k : ℝ) - 1` and identifies both `U P` and `Pi P + 1` with
`regularPhaseStep k`, under `0 < k`.

Only the minimal `Pi`/`U` formulas and their bridge were promoted from
`DkMath.Samples.Projection`; unrelated sample definitions and interval
statements remain outside this production owner.

## Scope boundary

- The result is an exact finite real-coordinate API.
- The pole `P = -1` is handled by explicit nonzero-denominator hypotheses.
- No projection surjectivity, interval placement, density, limit, or continuum
  realization theorem is introduced.
- The next milestone, CPG-V1-010, is a separate world-modulus projection/mesh
  API.

## Validation

Executed from `lean/dk_math`:

```bash
lake build DkMath.CosmicFormula.Projection.Basic \
  DkMath.CosmicFormula.Projection.CF2DBridge \
  DkMathTest.CosmicFormula.ProjectionCF2DBridge
```

Result: exit 0, `Build completed successfully (8695 jobs)`.

Additional checks on the fresh build log `/tmp/cpg-v1-009-build.log`:

- independent `warning:` scan: no matches;
- forbidden-construct scan of the production/test files: no matches for
  `sorry`, `admit`, user `axiom`, `unsafe`, or `native_decide`;
- `#print axioms` for all five public theorems: only `propext`,
  `Classical.choice`, and `Quot.sound`.

The shell profile emitted an environment permission warning before Lake; the
Lean build itself completed without errors or warnings.

## Roadmap transition

`CPG-V1-009` is complete as independent Projection/CF2D geometry/API work.
The next source milestone is `CPG-V1-010`, world-modulus projection / mesh.
