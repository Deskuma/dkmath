# DRC-001 — Integral matrix lattice landing

## Outcome A

The requested matrix iff theorem is kernel-checked, with focused regressions
and a public-theorem axiom audit. This report makes no mathematical novelty
claim.

## Preflight

- Branch: `research/DkMath-ResearchConnections-261003-v0`.
- Initial HEAD: `49fcfa27f5f7b259f8114f89ea64a5c91c875bff`; the specified base
  `f16282e5b44bd5fe5afa1a15d29f1598cae575cd` is an ancestor. The initial worktree
  was clean.
- Lean: `leanprover/lean4:v4.34.1`; Mathlib manifest revision: `v4.34.1`,
  checkout `d13f23b723b8a846827a245b89c10fc7d3f11612`.
- Inspected `TraceOneLatticeLanding.lean`, `TraceOnePowerLanding.lean`,
  `GNDegreeFactorization.lean`, `DkMath/Lib.lean`, and the pinned matrix APIs.
- `DkMath.NumberTheory.GN_mul_degree` already exists in
  `DkMath/NumberTheory/GNDegreeFactorization.lean`.
- Targeted searches of pinned Mathlib and DkMath found no existing theorem
  expressing this exact integral image/divisibility iff. Existing adjugate,
  Cramer, kernel, and field-surjectivity results supply the surrounding APIs.

## Public theorem and proof

File: `DkMath/Lib/NumberTheory/FiniteFreeLatticeLanding.lean`.

```lean
DkMath.Lib.NumberTheory.exists_mulVec_eq_iff_adjugate_dvd
```

For any finite decidable index type, integer square matrix `M`, integer vector
`v`, and hypothesis `M.det ≠ 0`, the theorem states:

```lean
(∃ w, M *ᵥ w = v) ↔ ∀ i, M.det ∣ (M.adjugate *ᵥ v) i
```

The forward proof uses `Matrix.mulVec_mulVec`, `Matrix.adjugate_mul`,
`Matrix.smul_mulVec`, and `Matrix.one_mulVec` to identify the adjugate product
with `M.det • w`. Each coordinate then has the explicit divisibility witness
`w i`.

The reverse proof chooses integer coordinate witnesses from divisibility,
forms `M.adjugate *ᵥ v = M.det • w`, and multiplies by `M`. It uses
`Matrix.mul_adjugate` and `Matrix.mulVec_smul` to obtain
`M.det • v = M.det • (M *ᵥ w)`. `mul_left_cancel₀ hdet` cancels the determinant
coordinatewise. Determinants and adjugates use Mathlib throughout.

`DkMath/Lib.lean` now imports the production module.

## Regressions and hypothesis boundary

File: `DkMathTest/Lib/NumberTheory/FiniteFreeLatticeLandingCalibration.lean`.
All names below have prefix `DkMathTest.FiniteFreeLatticeLanding`.

- `diagonal_landing`: `diag(2,3)` and vector `(4,9)` pass the criterion:
  determinant `6`, adjugate product `(12,18)`, quotient `(2,3)`.
- `mixed_landing`: matrix `[[2,1],[1,2]]` and vector `(4,5)` pass it:
  determinant `3`, adjugate product `(3,6)`, quotient `(1,2)`.
- `mixed_coordinate_failure`: the zeroth adjugate coordinate for `(1,0)`
  is `2`, which is not divisible by determinant `3`.
- `mixed_not_landing`: the public theorem excludes that vector from the image.
- `singular_boundary`: `diag(2,0)` is nonzero with determinant zero. For the
  same vector `(1,0)`, all adjugate-product coordinates are zero and hence
  divisible by determinant zero, but no integer preimage exists because its
  first image coordinate would have to satisfy `2 * w 0 = 1`.

The general theorem uses no finite enumeration. The two-dimensional numerical
regressions use `fin_cases`, `norm_num`, and integer arithmetic.

## TraceOne relationship and algebra wrapper

The existing TraceOne criterion is the concrete rank-2 version: multiplication
by `beta = (c,d)` has coordinate matrix

```text
M_beta = [[c, s*d], [d, c+d]]
det M_beta = c^2 + c*d - s*d^2
adj M_beta * (a,b) = (a*c + a*d - s*b*d, b*c - a*d).
```

These are exactly the two polynomial coordinates and norm in
`traceOne_dvd_iff_polynomial_norm_dvd_mul_conj_coordinates`. This relationship
is documented algebraically; a Lean specialization bridge is not added here.

The optional finite-free algebra wrapper is deferred to DRC-001B. Its API
boundary is a chosen `Basis ι ℤ A`, the multiplication matrix
`Algebra.leftMulMatrix`, basis coordinates, and a nonzero determinant hypothesis.
The pinned `Matrix/ToLin.lean` supplies `Algebra.leftMulMatrix_mulVec_repr` and
`LinearMap.toMatrix_mulVec_repr`. No concrete API limitation blocked the core
theorem. Basis reconstruction and divisibility transport are follow-up work;
the implemented API ends at integer matrices. No norm identification is needed
or claimed by the implementation.

## Validation

Commands ran from `lean/dk_math`:

| Command | Result |
| --- | --- |
| `lake env lean DkMath/Lib/NumberTheory/FiniteFreeLatticeLanding.lean` | Pass, exit 0 |
| `lake build DkMath.Lib.NumberTheory.FiniteFreeLatticeLanding` | Pass, 1614 jobs |
| `lake env lean DkMathTest/Lib/NumberTheory/FiniteFreeLatticeLandingCalibration.lean` | Pass, exit 0 |
| `lake env lean DkMathTest/Lib/NumberTheory/FiniteFreeLatticeLandingAxiomAudit.lean` | Pass, exit 0 |
| `lake build DkMath.Lib` | Pass, 8946 jobs |
| `lake build` | Pass, 10335 jobs, exit 0 |
| Final combined build of `DkMath.Lib` and both new test modules | Pass, 8948 jobs, exit 0 |
| `lake build DkMathTest` | Pass, 10915 jobs, exit 0 |

The audit file prints:

```text
'DkMath.Lib.NumberTheory.exists_mulVec_eq_iff_adjugate_dvd'
depends on axioms: [propext, Classical.choice, Quot.sound]
```

There is no `sorryAx` or project-added axiom in that dependency list. A recursive
source scan of the 23 local files in the `DkMath.Lib` import closure found no
`sorry`, `admit`, or axiom declaration candidates. This scan covers local sources;
the public theorem's printed dependency list is the kernel-level audit.

`git diff --check` and `git diff --no-index --check /dev/null <file>` for each
new file produced no whitespace diagnostics. The latter returns exit 1 for
the new-file differences, as expected. Build logs are available in
`/tmp/drc-001-full-build.log`, `/tmp/drc-001-test-build.log`, and
`/tmp/drc-001-final-focused.log`.
