# CPG-V1-008 — finite prime-family synchronization

Date: 2026-09-12  
Status: complete

## Implemented API

Added the production module
[PrimorialSync.lean](../../../DkMath/NumberTheory/PrimeGauge/PrimorialSync.lean)
with:

```lean
DkMath.NumberTheory.PrimeGauge.all_primeGauge_return_iff_worldModulus_dvd
DkMath.NumberTheory.PrimeGauge.primeGauge_worldModulus_is_first_positive_sync
```

For a finite `KnownPrimeScales S`, the first theorem proves the exact
equivalence

```lean
(∀ p ∈ S, regularKernel p ^ n = 1) ↔
  primeWorldModulus S ∣ n
```

The proof uses the existing CF2D return bridge for each prime and the finite
pairwise-coprime product argument for `primeWorldModulus S`. The second theorem
packages positivity, return at the world modulus itself, and minimality among
positive simultaneous-return exponents.

The focused regression
[PrimeGaugeSynchronization.lean](../../../DkMathTest/NumberTheory/PrimeGaugeSynchronization.lean)
checks `primeWorldModulus {2,3,5} = 30`, simultaneous return at `n = 60`, the
converse divisibility direction at `n = 42`, and the first-positive bound at
`n = 60`.

## Scope boundary

- This is a finite reusable synchronization API for a certified prime family.
- It identifies the family common period with the product-modulus divisibility
  condition; it does not identify the order of a product kernel with that
  modulus.
- It does not assert prime existence, Goldbach, interval escape, Projection
  surjectivity, mesh convergence, or continuum realization.
- The existing `PrimorialUniverse/FinitePrimeSynchronization` API was inspected
  as a related finite common-multiple provider. This module keeps the
  `PrimeGauge` owner and adds the explicit CF2D return equivalence without
  importing the PrimorialUniverse namespace.

## Validation

Executed from `lean/dk_math`:

```bash
lake build DkMath.NumberTheory.PrimeGauge.PrimorialSync \
  DkMathTest.NumberTheory.PrimeGaugeSynchronization
```

Result: exit 0, `Build completed successfully (8701 jobs)`.

Additional checks on the fresh build log `/tmp/cpg-v1-008-build.log`:

- independent `warning:` scan: no matches;
- forbidden-construct scan of the production/test files: no matches for
  `sorry`, `admit`, user `axiom`, `unsafe`, or `native_decide`;
- `#print axioms` for both public theorems: only `propext`,
  `Classical.choice`, and `Quot.sound`.

The shell profile emitted an environment permission warning before Lake; the
Lean build itself completed without errors or warnings.

## Roadmap transition

`CPG-V1-008` is complete. The next source milestone is `CPG-V1-009`, which must
extract only the minimal Projection/CF2D bridge into a production owner with a
separate geometry/API objective.
