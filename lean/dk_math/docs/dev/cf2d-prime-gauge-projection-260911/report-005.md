# CPG-V1-005 — parent-independent relative shape

Date: 2026-09-12  
Status: complete

## Implemented API

The production module
[GoldbachRefinement.lean](../../../DkMath/NumberTheory/PrimeGauge/GoldbachRefinement.lean)
now proves:

```lean
DkMath.NumberTheory.PrimeGauge.goldbach_reservedChild_relative_shape
```

From the two phase-level target equations

```lean
(primeWorldChild S r jL : ZMod q) = (n : ZMod q)
(primeWorldChild S r jR : ZMod q) = -(n : ZMod q)
```

it derives

```lean
((jL : ZMod q) - (jR : ZMod q)) *
    (primeWorldModulus S : ZMod q) = (2 * n : ℕ)
```

The proof expands `primeWorldChild S r j = r + j * primeWorldModulus S`,
cancels the common parent term, and normalizes the additive inverse in
`ZMod q`. No primality, fresh-prime, parent-bound, or interval hypothesis is
needed beyond the two supplied target equations.

The focused regression checks the concrete instance `S = {2, 3, 5}`, `q = 7`,
`r = 1`, `n = 10`, `jL = 1`, and `jR = 5`.

## Scope boundary

- This is a finite quotient identity expressing the relative shape of the two
  reserved child coordinates.
- It does not provide absolute placement of either child index.
- It does not convert `ZMod` subtraction into natural subtraction or discharge
  interval endpoint/proper-obstruction conditions.
- It does not assert child primality or prove a Goldbach, Strong Goldbach,
  universal escape, projection, mesh, or continuum theorem.
- Its role is a structural normalization; strict information gain remains
  unestablished until CPG-V1-007.

## Validation

Executed from `lean/dk_math`:

```bash
lake build DkMath.NumberTheory.PrimeGauge.GoldbachRefinement \
  DkMathTest.NumberTheory.PrimeGaugeGoldbachRefinement
```

Result: exit 0, `Build completed successfully (8705 jobs)`.

Additional checks on the fresh build log `/tmp/cpg-v1-005-build.log`:

- independent `warning:` scan: no matches;
- forbidden-construct scan of the production/test files: no matches for
  `sorry`, `admit`, user `axiom`, `unsafe`, or `native_decide`;
- `#print axioms` for `goldbach_reservedChild_relative_shape` and the two
  cardinality theorems: only `propext`, `Classical.choice`, and `Quot.sound`.

The shell profile emitted an environment permission warning before Lake; the
Lean build itself completed without errors or warnings.

## Roadmap transition

`CPG-V1-005` is complete. The next checkpoint is `CPG-V1-006`, the cross-fiber
center-transport law. The CPG-V1-007 information-gain stop gate remains
mandatory before any Projection or continuum implementation.
