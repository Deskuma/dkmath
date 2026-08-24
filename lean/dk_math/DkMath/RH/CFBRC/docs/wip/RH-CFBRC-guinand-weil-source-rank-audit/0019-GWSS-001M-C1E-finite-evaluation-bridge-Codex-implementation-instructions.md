# GWSS-001M-C1E finite evaluation bridge — Codex implementation instructions

Date: 2026-08-21

Repository: `Deskuma/dkmath`

Branch: `wip/RH-CFBRC-guinand-weil-source-rank-audit-260820-v0`

## 0. Mission

Continue after the successful function-rank closure in `0018`.

Implement and audit only:

```text
GWSS-001M-C1E-A  finite evaluation-point existence for the symmetric numerator family
GWSS-001M-C1E-B  determinant-nonzero consequences: all τ_i ≠ 0 and pairwise distinct
GWSS-001M-C1E-C  exact row-scaling transfer from numerator evaluation to bare Mellin kernel evaluation
```

Do **not** start:

```text
GWSS-001M-C2  actual Xi-window full-rank transfer
GWSS-002      off-critical witness construction
GWSS-003      arithmetic control
GWSS-004      classical Guinand-Weil infrastructure
```

The immediate purpose is to close:

```text
GENERAL-FINITE-MELLIN-EVALUATION-BRIDGE-GAP
```

using only the already-proved zero-independent function-rank theorem plus compact finite-dimensional determinant induction.

## 1. Mandatory orientation before editing

Before any edit, report:

```text
current branch
current HEAD
working-tree status
Lean toolchain
0017 and 0018 read
PascalCenteredXiMellinNumeratorFunctionRankAudit.lean read
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
GWSS-001M-C1E
```

Trusted frontier:

```text
GENERAL-MELLIN-NUMERATOR-JET-FOUND
GENERAL-FINITE-ORBIT-JET-COEFFICIENT-RANK-FOUND
GENERAL-MELLIN-NUMERATOR-FUNCTION-RANK-FOUND
```

Load-bearing firewall:

```text
NO RH assumption
NO classical Weil positivity
NO Li criterion
NO fixed-Xi defect-vanishing provider
NO T -> infinity horizontal decay
NO unrelated limit exchange
NO prime-side sign assumption
NO carrier-dependent selector as independent source
NO actual Xi-window representative selection in this assignment
```

## 2. Main target

For arbitrary finite centered coordinates:

```text
z : Fin n -> ℂ
```

with:

```text
∀ j, z j ^ 2 ≠ 0
Pairwise (fun i j => z i ^ 2 ≠ z j ^ 2)
```

prove existence of real evaluation parameters:

```text
τ : Fin n -> ℝ
```

such that the symmetric-numerator evaluation matrix has nonzero determinant:

```text
det (fun i j => mellinSymmetricNumerator (τ i) (z j)) ≠ 0
```

Preferred public theorem shape:

```lean
theorem exists_mellinSymmetricNumerator_evaluation_det_ne_zero
    {n : ℕ} {z : Fin n → ℂ}
    (hq : ∀ j, z j ^ 2 ≠ 0)
    (hpair : Pairwise (fun i j => z i ^ 2 ≠ z j ^ 2)) :
    ∃ τ : Fin n → ℝ,
      (fun i j => mellinSymmetricNumerator (τ i) (z j) :
        Matrix (Fin n) (Fin n) ℂ).det ≠ 0 := by
  ...
```

Binder syntax may be adjusted for Lean readability.

## 3. Required strategy — induction on n

Do not build a generic interpolation library.

Use direct induction on `n`.

### Base case n = 0

The empty evaluation matrix has determinant `1`.

Choose the unique empty `τ : Fin 0 -> ℝ`.

Use the pinned determinant API for `Fin 0` / `IsEmpty` if convenient.

### Successor case n+1

Assume:

```text
z : Fin (n+1) -> ℂ
```

Restrict to the first `n` coordinates:

```text
z0 : Fin n -> ℂ := fun j => z j.castSucc
```

or the equivalent indexing that makes the final coordinate the new column.

The hypotheses descend immediately:

```text
∀ j, z0 j ^ 2 ≠ 0
Pairwise distinct squared coordinates on z0
```

By the induction hypothesis choose:

```text
τ0 : Fin n -> ℝ
```

such that the `n × n` numerator evaluation matrix on `z0` has nonzero determinant.

Now form an `(n+1) × (n+1)` matrix whose first `n` rows are the old evaluations and whose final row is evaluated at a variable real parameter `t`.

A suggested definition is:

```text
E(t) i j :=
  if h : i.val < n then
    mellinSymmetricNumerator (τ0 ⟨i.val, h⟩) (z j)
  else
    mellinSymmetricNumerator t (z j)
```

but prefer `Fin.lastCases`, `Fin.cases`, `Fin.castSucc`, or another cleaner pinned `Fin` API if available.

The key is that deleting the final row and final column recovers exactly the old `n × n` evaluation matrix, up to an explicitly proved reindexing equivalence if needed.

## 4. Cofactor contradiction

Let:

```text
D(t) := det (E(t))
```

Suppose for contradiction:

```text
∀ t : ℝ, D(t) = 0
```

Expand `D(t)` along the variable final row using pinned Mathlib:

```lean
Matrix.det_succ_row
```

The pinned `v4.32.2` determinant API provides:

```lean
theorem det_succ_row {n : ℕ}
    (A : Matrix (Fin n.succ) (Fin n.succ) R)
    (i : Fin n.succ) :
    det A =
      ∑ j : Fin n.succ,
        (-1) ^ (i + j : ℕ) * A i j *
          det (A.submatrix i.succAbove j.succAbove)
```

Use `i = Fin.last n` (or an equivalent final-row index).

After expansion, `D(t)` has the form:

```text
∑ j, c j * mellinSymmetricNumerator t (z j)
```

where the cofactor coefficients `c j : ℂ` are independent of `t`.

You may define:

```text
cofactor j :=
  signFactor(j) * det (fixed minor deleting final row and column j)
```

or inline the expression if manageable.

From `∀ t, D(t)=0`, obtain:

```text
∀ t,
  ∑ j, c j * mellinSymmetricNumerator t (z j) = 0
```

Then apply the already-proved C1L theorem:

```lean
mellinSymmetricNumerator_combination_eq_zero_imp_coeff_zero
```

with the full `(n+1)` family `z`.

This yields:

```text
∀ j, c j = 0
```

## 5. The distinguished cofactor must be nonzero

Choose the cofactor associated with the final column `j = Fin.last n`.

Deleting:

```text
final row
final column
```

must recover the old `n × n` evaluation matrix from the induction hypothesis, perhaps after a trivial `Fin.succAbove` / reindex identification.

Therefore that cofactor is:

```text
nonzero sign × old determinant
```

and hence is nonzero.

This contradicts the conclusion that all cofactors vanish.

Thus:

```text
∃ t : ℝ, D(t) ≠ 0
```

Extend `τ0` by this `t` to obtain:

```text
τ : Fin (n+1) -> ℝ
```

with full determinant nonzero.

### Important discipline

Do not reprove function rank.

Do not reprove a second Vandermonde theorem.

Do not use analytic continuation or an identity theorem here.

The contradiction must flow through the existing C1L theorem.

## 6. Nonzero evaluation parameters are automatic

Once:

```text
det (fun i j => mellinSymmetricNumerator (τ i) (z j)) ≠ 0
```

is known, prove:

```text
∀ i, τ i ≠ 0
```

using:

```lean
mellinSymmetricNumerator_zero
```

If `τ i = 0`, the entire row is zero, so the determinant is zero.

Use a compact pinned matrix theorem if convenient, for example a row-zero determinant result.

Do not perturb evaluation points off zero. No perturbation is needed.

Preferred theorem shape:

```lean
theorem evaluation_det_ne_zero_imp_parameters_ne_zero
    ... :
    ∀ i, τ i ≠ 0 := by
  ...
```

## 7. Pairwise distinct evaluation parameters are automatic

From the same determinant-nonzero hypothesis prove:

```text
Function.Injective τ
```

or equivalently:

```text
Pairwise (fun i j => τ i ≠ τ j)
```

If `i ≠ j` but `τ i = τ j`, the two evaluation rows are identical.

Pinned Mathlib provides:

```lean
Matrix.det_zero_of_row_eq
```

with the semantic form:

```text
repeated row -> determinant = 0
```

Use it rather than proving row alternation again.

This injectivity is useful but subordinate to determinant nonvanishing.

## 8. Transfer to the bare Mellin kernel

For all selected evaluation points, `τ i ≠ 0`.

Use the existing exact identity:

```lean
mellinSymmetricNumerator_eq_kernel_mul
```

which states for nonzero `τ`:

```text
mellinSymmetricNumerator τ z
  = (τ : ℂ)^2 * complexExpSecondDifferenceKernel τ z
```

Therefore the numerator evaluation matrix is obtained from the bare-kernel evaluation matrix by nonzero row scaling.

Prove an exact determinant relation, semantically:

```text
det numeratorMatrix
  = (∏ i, (τ i : ℂ)^2) * det kernelMatrix
```

You may implement this by:

```text
Matrix.diagonal rowScale * kernelMatrix
```

and `Matrix.det_mul`, `Matrix.det_diagonal`, or by a direct row-scaling theorem if shorter.

Since every row scale is nonzero and numerator determinant is nonzero, conclude:

```text
det kernelMatrix ≠ 0
```

Preferred public theorem shape:

```lean
theorem exists_complexExpSecondDifferenceKernel_evaluation_det_ne_zero
    {n : ℕ} {z : Fin n → ℂ}
    (hq : ∀ j, z j ^ 2 ≠ 0)
    (hpair : Pairwise (fun i j => z i ^ 2 ≠ z j ^ 2)) :
    ∃ τ : Fin n → ℝ,
      (∀ i, τ i ≠ 0) ∧
      Function.Injective τ ∧
      (fun i j => complexExpSecondDifferenceKernel (τ i) (z j) :
        Matrix (Fin n) (Fin n) ℂ).det ≠ 0 := by
  ...
```

The exact conjunction order may be changed.

## 9. Zero-independent family firewall

The theorem quantifies over arbitrary `z : Fin n -> ℂ` subject only to:

```text
squared coordinates nonzero
squared coordinates pairwise distinct
```

The selected `τ` values may depend on this arbitrary finite family `z` because this is an existence theorem for evaluation coordinates, but no Xi-zero-specific carrier or selector may enter.

Do not use:

```text
pascalCenteredXiZeroDiskFinset
actual Xi representative choice
prime-side arithmetic data
RH or an RH-equivalent provider
```

in C1E.

## 10. Scope boundary for C2

Even after the general kernel evaluation theorem is proved, stop.

Do **not** in the same assignment:

```text
construct the actual squared-orbit carrier
choose representatives from the Xi window
apply spectral-factor nonzero column scaling in arbitrary rank
claim actual Xi-window full rank
construct an off-critical witness
```

Those belong to C2 and later.

## 11. Stop conditions

Stop and report precisely only if one of these occurs:

```text
A. successor induction cannot recover the old determinant as the distinguished minor because of a concrete Fin reindex API gap
B. det_succ_row / cofactor normalization cannot be connected to C1L without a large new determinant library
C. nonzero-row-scaling transfer to the bare kernel hits a concrete Matrix API gap
D. a genuine mathematical obstruction appears
```

If stopping, classify with exactly one of:

```text
FINITE-EVALUATION-FIN-REINDEX-API-GAP
FINITE-EVALUATION-COFACTOR-API-GAP
BARE-KERNEL-ROW-SCALING-API-GAP
FINITE-EVALUATION-INFORMATION-OBSTRUCTION
```

Before stopping for A-C, attempt one compact local helper. Do not label routine `Fin` bookkeeping as an information obstruction.

## 12. Success classification

If the general bare-kernel finite evaluation theorem is proved, classify:

```text
GENERAL-FINITE-NONZERO-TAU-MELLIN-RANK-FOUND
```

This means:

```text
For every finite family of nonzero pairwise-distinct squared coordinates,
there exist finitely many real, nonzero, pairwise-distinct dilation parameters
whose bare Mellin-kernel evaluation matrix is invertible.
```

After success, the next unresolved Gap becomes:

```text
ACTUAL-XI-WINDOW-FULL-MELLIN-RANK-TRANSFER-GAP
```

At that point C2 may be authorized in the next assignment.

GWSS-002 remains unauthorized until C2 itself is closed.

## 13. Suggested files

Prefer a focused module:

```text
DkMath/RH/CFBRC/PascalCenteredXiMellinFiniteEvaluationRankAudit.lean
```

and report:

```text
docs/wip/RH-CFBRC-guinand-weil-source-rank-audit/
0020-GWSS-001M-C1E-finite-evaluation-rank-report.md
```

Module docstring must state clearly:

```text
- evaluation parameters are existence witnesses for an arbitrary finite family
- no Xi zero carrier is used
- numerator is used first so τ = 0 is automatically excluded by determinant nonvanishing
- bare kernel follows by exact row scaling
```

## 14. Verification

At minimum run:

```text
lake build DkMath.RH.CFBRC.PascalCenteredXiMellinFiniteEvaluationRankAudit
git diff --check
```

Inspect axioms for the load-bearing theorems, at least:

```text
#print axioms exists_mellinSymmetricNumerator_evaluation_det_ne_zero
#print axioms exists_complexExpSecondDifferenceKernel_evaluation_det_ne_zero
```

Requirements:

```text
NO sorry
NO admit
NO new axiom
NO native_decide as a proof shortcut
```

Expected axiom footprint is only the standard foundational set already seen on this branch.

## 15. Final reporting format

Report:

```text
global objective
current stage
load-bearing boundary
finite numerator evaluation existence status
τ ≠ 0 status
τ injective / pairwise-distinct status
bare-kernel row-scaling transfer status
primary classification
next unresolved Gap
C2 authorization status
GWSS-002 authorization status
verification
```

End with exactly one primary classification:

```text
GENERAL-FINITE-NONZERO-TAU-MELLIN-RANK-FOUND
FINITE-EVALUATION-FIN-REINDEX-API-GAP
FINITE-EVALUATION-COFACTOR-API-GAP
BARE-KERNEL-ROW-SCALING-API-GAP
FINITE-EVALUATION-INFORMATION-OBSTRUCTION
```

If `FOUND`, state explicitly:

```text
GWSS-001M-C1E is closed.
Next unresolved Gap: ACTUAL-XI-WINDOW-FULL-MELLIN-RANK-TRANSFER-GAP
GWSS-001M-C2: authorized for the next bounded assignment, not started here.
GWSS-002: not authorized / not started.
```
