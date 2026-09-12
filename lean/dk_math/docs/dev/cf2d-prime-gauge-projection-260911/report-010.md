# CPG-V1-010 — World-modulus projection / mesh

Date: 2026-09-12  
Status: complete

## Implemented API

Added the production module
[WorldModulus.lean](../../../DkMath/CosmicFormula/Projection/WorldModulus.lean).
For a finite certified prime family `S`, it provides:

```text
worldModulus_projection_gap
worldModulus_projection_add_one
freshPrime_refinement_mesh
```

Writing `M = primeWorldModulus S`, the first two theorems establish the exact
finite identities

```text
U (M - 1) = 1 / M
Pi (M - 1) + 1 = 1 / M
```

For a fresh prime `q`, the mesh theorem uses the existing product update
`primeWorldModulus (insert q S) = q * primeWorldModulus S` and proves

```text
1 / M' = (1 / M) / q.
```

The implementation uses the existing `KnownPrimeScales` positivity provider,
the production Projection/CF2D bridge, and `primeWorldModulus_insert`. No new
observer structure or sample-source dependency was introduced.

## Scope boundary

- These are exact finite real-coordinate and mesh-refinement identities.
- The mesh is not promoted to a limit or density statement.
- No prime existence, interval placement, or continuum realization theorem is
  introduced.
- The next milestone, CPG-V1-011, is the separate finite normalized-grid
  approximation API.

## Validation

Executed from `lean/dk_math`:

```bash
lake build DkMath.CosmicFormula.Projection.WorldModulus \
  DkMathTest.CosmicFormula.ProjectionWorldModulus
```

Result: exit 0, `Build completed successfully (8702 jobs)`.

Additional checks on the fresh build log `/tmp/cpg-v1-010-build.log`:

- independent `warning:` scan: no matches;
- forbidden-construct scan of the production/test files: no matches for
  `sorry`, `admit`, user `axiom`, `unsafe`, or `native_decide`;
- `#print axioms` for all three public theorems: only `propext`,
  `Classical.choice`, and `Quot.sound`.

The shell profile emitted an environment permission warning before Lake; the
Lean build itself completed without errors or warnings.

## Roadmap transition

`CPG-V1-010` is complete as independent finite world-modulus mesh work. The
next source milestone is `CPG-V1-011`, finite normalized grid.
