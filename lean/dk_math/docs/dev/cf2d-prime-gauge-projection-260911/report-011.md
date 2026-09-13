# CPG-V1-011 — Finite normalized grid

Date: 2026-09-12  
Status: complete

## Implemented API

Added the production module
[NormalizedGrid.lean](../../../DkMath/CosmicFormula/Projection/NormalizedGrid.lean).
It defines the endpoint-inclusive finite real grid

```lean
normalizedGrid k = { (j : ℝ) / k | j ≤ k }.
```

The module provides:

```text
mem_normalizedGrid
normalizedGrid_approx
```

For `0 < k` and `0 ≤ x ≤ 1`, `normalizedGrid_approx` constructs a natural
index `j ≤ k` satisfying

```text
|x - j / k| ≤ 1 / k.
```

The proof uses the finite choice `j = ⌊k x⌋₊`, with the standard floor bounds.
The endpoint-inclusive convention matches the theorem's `j ≤ k` bound and
allows the endpoint `x = 1` to be represented exactly.

## Scope boundary

- This is a pointwise finite approximation theorem.
- No sequence of moduli, mesh limit, dense-subset theorem, or growth provider
  is introduced.
- Grid membership is a real-coordinate fact and does not assert primality or
  arithmetic realization of any grid point.

## Validation

Executed from `lean/dk_math`:

```bash
lake build DkMath.CosmicFormula.Projection.NormalizedGrid \
  DkMathTest.CosmicFormula.ProjectionNormalizedGrid
```

Result: exit 0, `Build completed successfully (2998 jobs)`.

Additional checks on the fresh build log `/tmp/cpg-v1-011-build.log`:

- independent `warning:` scan: no matches;
- forbidden-construct scan of the production/test files: no matches for
  `sorry`, `admit`, user `axiom`, `unsafe`, or `native_decide`;
- `#print axioms` for `normalizedGrid_approx`: only `propext`,
  `Classical.choice`, and `Quot.sound`.

The shell profile emitted an environment permission warning before Lake; the
Lean build itself completed without errors or warnings.

## Roadmap transition

`CPG-V1-011` is complete as independent finite normalized-grid API work.
Further dense/limit work requires a separately authorized growth provider and
campaign.
