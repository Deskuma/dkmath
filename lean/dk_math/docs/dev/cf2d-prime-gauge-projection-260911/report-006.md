# CPG-V1-006 — cross-fiber center transport

Date: 2026-09-12  
Status: complete

## Implemented API

The production module
[GoldbachRefinement.lean](../../../DkMath/NumberTheory/PrimeGauge/GoldbachRefinement.lean)
now proves:

```lean
DkMath.NumberTheory.PrimeGauge.goldbach_reservedChild_relative_shape_succ
```

Given left/right raw target equations at center `n` on a fiber with parent `r`
and at center `n + 1` on a fiber with parent `r'`, it proves

```lean
(((jL' : ZMod q) - jR') - ((jL : ZMod q) - jR)) *
    (primeWorldModulus S : ZMod q) = 2
```

The proof applies CPG-V1-005 independently to the two fibers and subtracts
the resulting relative-shape identities. The parent terms and the choice of
`r` versus `r'` therefore disappear. The result requires no additional
primality, fresh-prime, bounded-index, or interval hypotheses beyond the four
supplied target equations.

The focused regression checks `S = {2, 3, 5}`, `q = 7`, `r = r' = 1`,
`n = 10`, `(jL, jR) = (1, 5)`, and `(jL', jR') = (5, 1)`.

## Scope boundary

- This is a finite `ZMod q` cross-fiber transport identity.
- It does not establish a natural-number ordering, interval placement, or
  proper Goldbach obstruction statement for the child indices.
- It does not assert child primality or prove Goldbach, Strong Goldbach,
  universal escape, projection, mesh, or continuum realization.
- The dynamic phase now has the requested structural successor law, but strict
  information gain over existing finite CRT/capacity APIs has not been shown.
  CPG-V1-007 remains the mandatory stop gate.

## Validation

Executed from `lean/dk_math`:

```bash
lake build DkMath.NumberTheory.PrimeGauge.GoldbachRefinement \
  DkMathTest.NumberTheory.PrimeGaugeGoldbachRefinement
```

Result: exit 0, `Build completed successfully (8705 jobs)`.

Additional checks on the fresh build log `/tmp/cpg-v1-006-build.log`:

- independent `warning:` scan: no matches;
- forbidden-construct scan of the production/test files: no matches for
  `sorry`, `admit`, user `axiom`, `unsafe`, or `native_decide`;
- `#print axioms` for the new successor theorem: only `propext` and
  `Quot.sound`.

The shell profile emitted an environment permission warning before Lake; the
Lean build itself completed without errors or warnings.

## Roadmap transition

`CPG-V1-006` is complete. The next authorized work item is the CPG-V1-007
information-gain audit. Projection and continuum implementation remain behind
that gate.
