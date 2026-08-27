# GWSS-001M-C1L direct numerator function rank — Codex implementation instructions

Date: 2026-08-21

Repository: `Deskuma/dkmath`

Branch: `wip/RH-CFBRC-guinand-weil-source-rank-audit-260820-v0`

## 0. Mission

Continue the GWSS Mellin source-rank route after the successful arbitrary numerator-jet bridge in `0016`.

Implement and audit only:

```text
GWSS-001M-C1L-A  extract all coefficient-row equations from a zero function combination
GWSS-001M-C1L-B  use the existing Vandermonde coefficient matrix to annihilate all coefficients
GWSS-001M-C1L-C  optional thin LinearIndependent wrapper
```

Do **not** start:

```text
GWSS-001M-C1E  finite evaluation-point existence
GWSS-001M-C2   actual Xi-window full-rank transfer
GWSS-002       off-critical witness construction
GWSS-003       arithmetic control
GWSS-004       classical Guinand-Weil infrastructure
```

The purpose of this assignment is to close function-level rank without building a large abstract function-space/span library.

The current trusted frontier is:

```text
GWSS-001M-C0
  FINITE-TAU-LOW-RANK-SEPARATION-FOUND

GWSS-001M-C1 algebraic coefficient rank
  GENERAL-FINITE-ORBIT-JET-COEFFICIENT-RANK-FOUND

GWSS-001M-C1J
  arbitrary symmetric-numerator jet FOUND
  exact coefficient-matrix bridge FOUND

current missing bridge
  GENERAL-MELLIN-NUMERATOR-LINEAR-INDEPENDENCE-GAP
```

The immediate target is a direct annihilation theorem:

```text
if a finite linear combination of the numerator functions
vanishes for every real τ,
then every scalar coefficient is zero.
```

Do not treat missing generic `LinearIndependent` wrappers as a mathematical obstruction.

## 1. Mandatory orientation before editing

Before any edit, report:

```text
current branch
current HEAD
working-tree status
Lean toolchain
0014, 0015, 0016 read
PascalCenteredXiMellinGeneralFiniteRankAudit.lean read
PascalCenteredXiMellinGeneralNumeratorJetAudit.lean read
global objective
current GWSS stage
load-bearing boundary
next unresolved Gap
```

Global objective:

```text
zero configuration
  -> independent source
  -> off-critical detector
  -> arithmetic control
  -> centered-coordinate uniqueness
  -> RiemannHypothesis
```

Current stage:

```text
GWSS-001M-C1L
```

Load-bearing boundary:

```text
NO RH assumption
NO classical Weil positivity
NO Li criterion
NO fixed-Xi defect-vanishing provider
NO T -> infinity horizontal decay
NO limit exchange across unrelated limits
NO prime-side sign assumption
NO carrier-dependent selector as independent source
NO finite-evaluation existence claim in this assignment
```

Current mathematical inputs already proved:

```text
mellinSymmetricNumerator
mellinSymmetricNumeratorJetCoeff
mellinSymmetricNumeratorJetCoeff_eq_coefficientMatrix
tendsto_mellinSymmetricNumerator_generalJet
mellinJetCoefficientMatrix_det_ne_zero
```

## 2. Core strategy — direct annihilation, not abstract span machinery

Let:

```text
z : Fin n -> ℂ
c : Fin n -> ℂ
```

Assume the squared coordinates are nonzero and pairwise distinct:

```text
∀ j, z j ^ 2 ≠ 0
Pairwise (fun i j => z i ^ 2 ≠ z j ^ 2)
```

Assume the function combination vanishes identically:

```text
∀ τ : ℝ,
  ∑ j, c j * mellinSymmetricNumerator τ (z j) = 0
```

Do **not** begin by introducing a function-space basis, span, dual space, or evaluation functional infrastructure.

Instead prove directly that for every jet row `m < n`:

```text
∑ j, c j * mellinSymmetricNumeratorJetCoeff m (z j) = 0
```

Then identify this finite family of row equations with the matrix equation for:

```text
mellinJetCoefficientMatrix (fun j => z j ^ 2)
```

and use its already-proved nonzero determinant to conclude all `c j = 0`.

## 3. C1L-A — extract coefficient-row equations

### A1. Preferred helper theorem

Implement a helper that extracts the next coefficient equation from the identically-zero combination, assuming all lower coefficient equations are already known.

A suitable theorem shape is:

```lean
theorem mellinSymmetricNumerator_combination_nextJet_eq_zero
    {n : ℕ} (z c : Fin n → ℂ) (m : ℕ)
    (hzero : ∀ τ : ℝ,
      ∑ j, c j * mellinSymmetricNumerator τ (z j) = 0)
    (hlower : ∀ r < m,
      ∑ j, c j * mellinSymmetricNumeratorJetCoeff r (z j) = 0) :
    ∑ j, c j * mellinSymmetricNumeratorJetCoeff m (z j) = 0 := by
  ...
```

The exact binder style may change if another Lean shape is cleaner.

### A2. Mathematical proof

For each fixed `m`, define the finite lower polynomial contribution:

```text
P_m(τ)
  := ∑ j, c_j *
       ∑ r < m, a_r(z_j) * τ^(2r+2)
```

where:

```text
a_r(z) := mellinSymmetricNumeratorJetCoeff r z
```

From `hlower`, finite-sum rearrangement should give:

```text
P_m(τ) = 0
```

for every `τ`.

From `hzero`, the normalized combination therefore satisfies, on the punctured neighborhood:

```text
0
  = ∑ j, c_j *
      (mellinSymmetricNumerator τ (z_j)
        - ∑ r<m a_r(z_j) τ^(2r+2))
      / τ^(2m+2)
```

Use:

```text
tendsto_mellinSymmetricNumerator_generalJet m (z j)
```

for each `j` and finite-sum `Tendsto` closure to obtain the limit:

```text
∑ j, c_j * a_m(z_j)
```

The left side is identically zero on the punctured filter, hence its limit is zero.

Conclude:

```text
∑ j, c_j * a_m(z_j) = 0
```

### A3. Important Lean discipline

Keep this proof finite.

Allowed operations:

```text
Finset.sum
Tendsto.const_mul
Tendsto.mul_const
finite sum of Tendsto
EventuallyEq / Tendsto.congr'
field_simp on τ ≠ 0
ring / ring_nf
```

Do not introduce:

```text
infinite sums over the jet index
formal power-series equality of the whole combination
interchange of infinite sum and limit
analytic identity theorem
complexification of the real τ parameter unless actually needed
```

The general finite jet theorem already contains the needed analytic content.

## 4. C1L-A2 — all first n jet equations

Using the helper above, prove by induction on `m` that all rows indexed by `Fin n` vanish.

Preferred theorem shape:

```lean
theorem mellinSymmetricNumerator_combination_allJetRows_eq_zero
    {n : ℕ} (z c : Fin n → ℂ)
    (hzero : ∀ τ : ℝ,
      ∑ j, c j * mellinSymmetricNumerator τ (z j) = 0) :
    ∀ r : Fin n,
      ∑ j, c j * mellinSymmetricNumeratorJetCoeff r.1 (z j) = 0 := by
  ...
```

The induction must use only previously established lower rows.

Do not assume coefficient uniqueness as a black box.

## 5. C1L-B — convert row equations to a matrix kernel statement

Recall from `0015/0016`:

```lean
mellinSymmetricNumeratorJetCoeff_eq_coefficientMatrix
```

Hence the row equations are exactly:

```text
for every r : Fin n,
  ∑ j,
    mellinJetCoefficientMatrix (fun j => (z j)^2) r j * c j
  = 0
```

This is the matrix-vector equation:

```text
M *ᵥ c = 0
```

up to multiplication order of complex scalars. Normalize with commutativity if needed.

### B1. Preferred path

Reuse pinned Matrix API if it is compact:

```text
det M ≠ 0
  -> M is invertible / nonsingular
  -> M.mulVec is injective
  -> c = 0
```

Search pinned Mathlib only for the minimal exact theorem needed.

Possible useful concepts to audit:

```text
Matrix.det_ne_zero_iff
Matrix.mulVec
Matrix.mulVecLin
Matrix.nonsingInv
Matrix.mul_nonsing_inv
Matrix.nonsing_inv_mul
Matrix.det_nonsing_inv
```

Do not assume names; inspect the pinned API.

### B2. Acceptable fallback

If the matrix-vector injectivity wrapper is awkward, use the nonsingular inverse directly:

```text
M *ᵥ c = 0
```

left-multiply by `M⁻¹` / `nonsingInv M`, derive:

```text
c = 0
```

This is still a compact finite-dimensional argument and is within scope.

Do not build a new generic linear algebra library.

## 6. Main load-bearing theorem

Target a direct theorem of the following semantic strength:

```lean
theorem mellinSymmetricNumerator_combination_eq_zero_imp_coeff_zero
    {n : ℕ} {z : Fin n → ℂ}
    (hq : ∀ j, z j ^ 2 ≠ 0)
    (hpair : Pairwise (fun i j => z i ^ 2 ≠ z j ^ 2))
    (c : Fin n → ℂ)
    (hzero : ∀ τ : ℝ,
      ∑ j, c j * mellinSymmetricNumerator τ (z j) = 0) :
    ∀ j, c j = 0 := by
  ...
```

Equivalent conclusion shapes are acceptable:

```text
c = 0
```

or:

```text
funext ...
```

as long as the theorem clearly states coefficient annihilation.

Mandatory proof dependency:

```text
hzero
  -> all finite jet-row equations
  -> mellinJetCoefficientMatrix mulVec c = 0
  -> mellinJetCoefficientMatrix_det_ne_zero hq hpair
  -> c = 0
```

Do not bypass the already-proved Vandermonde coefficient theorem with a second independent Vandermonde proof.

## 7. C1L-C — optional thin LinearIndependent wrapper

Only after the direct annihilation theorem is complete, optionally add:

```lean
theorem linearIndependent_mellinSymmetricNumerator
    {n : ℕ} {z : Fin n → ℂ}
    (hq : ∀ j, z j ^ 2 ≠ 0)
    (hpair : Pairwise (fun i j => z i ^ 2 ≠ z j ^ 2)) :
    LinearIndependent ℂ
      (fun j : Fin n =>
        (fun τ : ℝ => mellinSymmetricNumerator τ (z j))) := by
  ...
```

This wrapper is useful but **not required** for the primary mathematical success classification if the direct annihilation theorem is proved.

If the wrapper becomes awkward because of finitely-supported scalar conventions, stop after the direct theorem and document that the function-rank fact is already established extensionally.

## 8. Zero-independent family firewall

The family remains:

```text
τ -> mellinSymmetricNumerator τ z
```

No parameter value may be chosen from the actual Xi zero carrier in this assignment.

The theorem may quantify over arbitrary `z : Fin n -> ℂ`, subject only to squared-coordinate nonzero/distinctness.

This is essential: the rank result must concern a prescribed analytic family, not a support-dependent selector.

## 9. Stop conditions

Stop and report precisely if one of these occurs:

```text
A. finite-sum limit extraction itself needs a missing general theorem
B. converting all jet rows to Matrix.mulVec becomes blocked by a concrete API mismatch
C. determinant nonzero cannot be turned into vector-kernel triviality without a genuinely large development
D. a hidden dependence on actual zero locations enters the weight family
```

If stopping, distinguish:

```text
FINITE-JET-COMBINATION-EXTRACTION-API-GAP
MATRIX-KERNEL-TRIVIALITY-API-GAP
FUNCTION-RANK-INFORMATION-OBSTRUCTION
```

Do not label an API inconvenience as an information obstruction.

Before stopping for B or C, inspect pinned Mathlib Matrix determinant/nonsingular inverse APIs and attempt one compact local helper.

## 10. Success classification

If the direct coefficient-annihilation theorem is proved, classify:

```text
GENERAL-MELLIN-NUMERATOR-FUNCTION-RANK-FOUND
```

This classification does not require the thin `LinearIndependent` wrapper.

After success, the next unresolved Gap becomes exactly:

```text
GENERAL-FINITE-MELLIN-EVALUATION-BRIDGE-GAP
```

Do **not** solve that Gap in the same assignment.

## 11. Why finite evaluation is deliberately deferred

Once function rank is proved, the next stage will ask:

```text
Given n linearly independent numerator functions,
find n real evaluation points τ_i
such that the evaluation matrix is invertible.
```

At that later stage, use the key numerator fact:

```text
mellinSymmetricNumerator 0 z = 0
```

Therefore any evaluation matrix with nonzero determinant automatically has:

```text
τ_i ≠ 0
```

for every selected row `i`, because a row at `τ_i = 0` would be identically zero.

Do not implement this finite-evaluation theorem in C1L.

## 12. Required module/report outputs

Prefer a focused module such as:

```text
DkMath/RH/CFBRC/PascalCenteredXiMellinNumeratorFunctionRankAudit.lean
```

and a report:

```text
docs/wip/RH-CFBRC-guinand-weil-source-rank-audit/
0018-GWSS-001M-C1L-direct-function-rank-report.md
```

The report must state:

```text
global objective
current stage
load-bearing boundary
all-jet-row extraction status
matrix-kernel status
direct coefficient-annihilation theorem status
optional LinearIndependent wrapper status
primary classification
next unresolved Gap
GWSS-002 authorization status
verification
```

## 13. Verification

At minimum run:

```text
lake build DkMath.RH.CFBRC.PascalCenteredXiMellinNumeratorFunctionRankAudit
git diff --check
```

Also inspect:

```text
#print axioms mellinSymmetricNumerator_combination_allJetRows_eq_zero
#print axioms mellinSymmetricNumerator_combination_eq_zero_imp_coeff_zero
```

If a public `LinearIndependent` wrapper is added, inspect it too.

Requirements:

```text
NO sorry
NO admit
NO new axiom
```

Axiom footprint should remain the standard foundational set already seen in the branch.

## 14. Final reporting format

End with exactly one primary classification:

```text
GENERAL-MELLIN-NUMERATOR-FUNCTION-RANK-FOUND
FINITE-JET-COMBINATION-EXTRACTION-API-GAP
MATRIX-KERNEL-TRIVIALITY-API-GAP
FUNCTION-RANK-INFORMATION-OBSTRUCTION
```

If `FOUND`, state explicitly:

```text
The zero-independent symmetric Mellin numerator family is function-level
linearly independent on every finite family of nonzero pairwise-distinct
squared coordinates.
```

Then state:

```text
Next unresolved Gap: GENERAL-FINITE-MELLIN-EVALUATION-BRIDGE-GAP
GWSS-001M-C1E: not started
GWSS-001M-C2: not started
GWSS-002: not authorized / not started
```
