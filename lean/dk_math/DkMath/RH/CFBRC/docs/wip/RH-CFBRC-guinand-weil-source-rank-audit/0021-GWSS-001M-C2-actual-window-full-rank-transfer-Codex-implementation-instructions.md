# GWSS-001M-C2 actual Xi-window full Mellin rank transfer — Codex implementation instructions

Date: 2026-08-21

Repository: `Deskuma/dkmath`

Branch: `wip/RH-CFBRC-guinand-weil-source-rank-audit-260820-v0`

## 0. Mission

Continue the GWSS Mellin source-rank route after the successful C1E finite-evaluation theorem.

Implement and audit only:

```text
GWSS-001M-C2-A  actual Xi squared-orbit carrier and representatives
GWSS-001M-C2-B  apply C1E bare-kernel full rank to those representatives
GWSS-001M-C2-C  transfer to the canonical Mellin second-difference family by spectral-factor column scaling
GWSS-001M-C2-D  aggregate the actual Xi zero moment by squared orbit and expose the resulting full-rank source matrix
```

Do **not** start:

```text
GWSS-002       off-critical witness construction
GWSS-003       arithmetic sign / upper-control audit
GWSS-004       classical Guinand-Weil infrastructure
RH deduction
```

The purpose of C2 is not to prove another rank theorem. C1E already gives full finite rank for any finite family of nonzero pairwise-distinct squared coordinates. C2 must only transfer that theorem to the **actual finite centered-Xi zero window**, modulo the unavoidable even-weight identification `z ↔ -z`, and then connect the evaluation matrix to the actual zero-side weighted moment.

Current trusted frontier:

```text
GWSS-001M-C1J
  GENERAL-MELLIN-NUMERATOR-JET-FOUND

GWSS-001M-C1L
  GENERAL-MELLIN-NUMERATOR-FUNCTION-RANK-FOUND

GWSS-001M-C1E
  GENERAL-FINITE-NONZERO-TAU-MELLIN-RANK-FOUND

current missing bridge
  ACTUAL-XI-WINDOW-FULL-MELLIN-RANK-TRANSFER-GAP
```

If C2 closes including the orbit-moment aggregation, the intended classification is:

```text
MELLIN-FAMILY-ACTUAL-WINDOW-FULL-RANK-FOUND
```

Only after that classification may GWSS-002 be authorized in a later assignment.

## 1. Mandatory orientation before editing

Before any edit, report:

```text
current branch
current HEAD
working-tree status
Lean toolchain
0018, 0019, 0020 read
PascalCenteredXiActualWindowVariableWeightRankTransfer.lean read
PascalCenteredXiMellinLowRankAudit.lean read
PascalCenteredXiMellinFiniteEvaluationRankAudit.lean read
PascalCenteredXiMellinArithmeticSpecialization.lean read
global objective
current GWSS stage
load-bearing provider boundary
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
GWSS-001M-C2
```

Load-bearing firewall:

```text
NO RH assumption
NO classical Weil positivity
NO Li criterion
NO functional-equation transport promoted as new source rank
NO fixed-Xi defect-vanishing provider
NO T -> infinity horizontal decay
NO unrelated limit exchange
NO prime-side sign assumption
NO support-dependent selector promoted as the analytic family
NO claim of full rank on z and -z separately
```

The canonical analytic family remains the independently prescribed Mellin family:

```text
(ε, τ) -> pascalCenteredXiMellinSecondDifferenceWeight ε τ
```

The actual zero carrier may be used only to define the finite coordinate space on which this already-prescribed family is evaluated.

## 2. Mathematical target

Let:

```text
S_R := pascalCenteredXiZeroDiskFinset R
Q_R := image (fun z => z^2) S_R
```

The correct finite coordinate space is `Q_R`, not `S_R`, because every canonical Mellin weight is even in the centered variable.

For every `q ∈ Q_R`, choose one representative:

```text
rep_R(q) ∈ S_R
rep_R(q)^2 = q
```

C1E must then be applied to a finite enumeration of these representatives. Since distinct elements of `Q_R` are distinct squares and every actual centered-Xi zero has nonzero square, the C1E hypotheses are automatic.

The resulting nonzero and injective real parameters `τ_i` give:

```text
det [ complexExpSecondDifferenceKernel (τ_i) (rep_R(q_j)) ] ≠ 0
```

For sufficiently small positive `ε`, the existing theorem

```text
eventually_pascalCenteredXiMellinSpectralWeight_ne_zero_on_actual_window R
```

makes every spectral factor at every representative nonzero. Using

```text
pascalCenteredXiMellinSecondDifferenceWeight_eq_kernel_mul
```

this turns the actual Mellin matrix into a nonzero column scaling of the bare-kernel matrix, hence its determinant is nonzero.

Finally, group the actual zero moment by squared orbit so that the vector of Mellin moments is exactly the full-rank evaluation matrix applied to the vector of orbit masses.

## 3. C2-A — squared-orbit carrier

### A1. Define the actual squared-orbit carrier

Prefer a named definition:

```lean
noncomputable def pascalCenteredXiSquaredOrbitFinset (R : ℝ) : Finset ℂ :=
  (pascalCenteredXiZeroDiskFinset R).image (fun z => z ^ 2)
```

Equivalent naming is acceptable.

Prove the expected membership characterization:

```lean
q ∈ pascalCenteredXiSquaredOrbitFinset R
  ↔ ∃ z ∈ pascalCenteredXiZeroDiskFinset R, z ^ 2 = q
```

Reuse `Finset.mem_image`; do not introduce a quotient type for `z ~ -z` unless absolutely necessary.

### A2. Every actual squared orbit is nonzero

Use the existing theorem:

```text
pascalCenteredXiZeroDiskFinset_sq_ne_zero
```

Prove:

```lean
q ∈ pascalCenteredXiSquaredOrbitFinset R -> q ≠ 0
```

No RH or critical-line assumption is allowed.

### A3. Choose representatives

For `q` in the subtype of the squared-orbit finset, define or obtain a representative:

```text
rep R q : ℂ
```

with public or local lemmas:

```text
rep R q ∈ pascalCenteredXiZeroDiskFinset R
(rep R q)^2 = q.1
```

Classical choice is acceptable and expected.

Do not interpret the representative choice as new analytic information. It is only a finite coordinate presentation of the squared-orbit carrier.

## 4. C2-A2 — finite enumeration

C1E is currently stated over `Fin n`. Transport the squared-orbit subtype to `Fin` by the smallest available finite-type equivalence.

Preferred approaches include:

```text
Fintype.equivFin
Finset.card
an explicit equivalence between Fin Q.card and the subtype Q
```

Do not generalize the entire C1E module to arbitrary finite index types unless a tiny wrapper is clearly shorter than reindexing.

Construct:

```text
n_R : ℕ
q_R : Fin n_R -> ℂ
z_R : Fin n_R -> ℂ
```

such that:

```text
z_R j ∈ S_R
(z_R j)^2 = q_R j
q_R is injective
∀ j, (z_R j)^2 ≠ 0
Pairwise (fun i j => (z_R i)^2 ≠ (z_R j)^2)
```

Handle the empty-window case uniformly; C1E already supports `n = 0`.

## 5. C2-B — actual squared-orbit bare-kernel rank

Apply:

```text
exists_complexExpSecondDifferenceKernel_evaluation_det_ne_zero
```

from C1E to `z_R`.

Obtain:

```text
τ_R : Fin n_R -> ℝ
∀ i, τ_R i ≠ 0
Function.Injective τ_R
```

and:

```text
det K_R ≠ 0
```

where:

```text
K_R i j := complexExpSecondDifferenceKernel (τ_R i) (z_R j)
```

This step must be a theorem application plus finite-carrier bookkeeping. Do not reprove any jet, function-rank, Vandermonde, or finite-evaluation theorem.

A suitable public theorem may expose all of these witnesses for each `R`.

## 6. C2-C — spectral column scaling to the canonical Mellin family

Use the already-proved eventual theorem:

```lean
eventually_pascalCenteredXiMellinSpectralWeight_ne_zero_on_actual_window R
```

This says that for all sufficiently small positive `ε`, every actual zero in `S_R` has nonzero spectral factor.

Because every representative `z_R j` belongs to `S_R`, deduce eventually:

```text
∀ j,
centeredMellinSpectralWeight
  (centeredMellinBoxApprox ε) (z_R j) ≠ 0
```

### C1. Prefer an eventual full-rank theorem

Avoid choosing one arbitrary `ε` unless needed. The strongest clean target is:

```lean
∃ τ : Fin n_R → ℝ,
  (∀ i, τ i ≠ 0) ∧
  Function.Injective τ ∧
  ∀ᶠ ε : ℝ in nhdsWithin 0 (Set.Ioi 0),
    Matrix.det
      ((fun i j =>
        pascalCenteredXiMellinSecondDifferenceWeight ε (τ i) (z_R j)) :
        Matrix (Fin n_R) (Fin n_R) ℂ) ≠ 0
```

Equivalent packaging is acceptable.

### C2. Exact matrix factorization

For every nonzero `τ_i`, use:

```text
pascalCenteredXiMellinSecondDifferenceWeight_eq_kernel_mul
```

with the exact factorization:

```text
H_ε = K_R * diagonal(S_ε)
```

or the transpose-equivalent column-scaling orientation, where:

```text
S_ε(j) := centeredMellinSpectralWeight
  (centeredMellinBoxApprox ε) (z_R j)
```

Then:

```text
det H_ε = det K_R * ∏ j, S_ε(j)
```

up to the exact matrix multiplication orientation chosen in Lean.

The proof must use exact finite determinant identities only. Do not replace `S_ε` by `1`; do not exchange the `ε -> 0+` limit with any other limit.

### C3. Optional existential positive-ε corollary

If compact, derive:

```text
∃ ε > 0, det H_ε ≠ 0
```

from the eventual theorem and the nontriviality of `nhdsWithin 0 (Set.Ioi 0)`.

This corollary is useful but not required if the eventual full-rank theorem is already public and clear.

## 7. C2-D — squared-orbit mass aggregation

This part is required for full source-rank closure, because the explicit formula observes the actual weighted zero moment, not merely an abstract evaluation matrix.

### D1. Define orbit mass

For a squared coordinate `q`, define the multiplicity-weighted mass:

```lean
noncomputable def pascalCenteredXiSquaredOrbitMass (R : ℝ) (q : ℂ) : ℂ :=
  ∑ z ∈ (pascalCenteredXiZeroDiskFinset R).filter (fun z => z ^ 2 = q),
    (pascalCenteredXiZeroMultiplicity z : ℂ)
```

This should agree with the right-hand side already used by:

```text
pascalCenteredXiZeroDiskWeightedMoment_actualSquaredOrbitSelector
```

Do not assume the orbit consists of exactly two points; the filtered finite sum is the canonical definition.

### D2. Even-weight fiber constancy

Prove the minimal lemma needed to show that the canonical Mellin weight is constant on equal-square fibers.

Mathematically, over `ℂ`:

```text
a^2 = b^2 -> a = b or a = -b
```

and the canonical Mellin weight is even for positive `ε`.

You may instead prove constancy directly from the kernel/spectral formulas if that is shorter, but do not use any zero-specific symmetry theorem as a new provider.

Target semantic statement:

```text
a^2 = b^2 ->
pascalCenteredXiMellinSecondDifferenceWeight ε τ a =
pascalCenteredXiMellinSecondDifferenceWeight ε τ b
```

for the admissible parameter regime needed in the aggregation theorem.

### D3. Regroup the actual zero moment

Prove a finite fiberwise decomposition of:

```text
pascalCenteredXiZeroDiskWeightedMoment
  (pascalCenteredXiMellinSecondDifferenceWeight ε τ) R
```

into the squared-orbit carrier:

```text
∑ q in Q_R,
  pascalCenteredXiSquaredOrbitMass R q *
    pascalCenteredXiMellinSecondDifferenceWeight ε τ (rep_R q)
```

up to multiplication order.

Prefer existing `Finset` image/fiberwise sum APIs if available. A compact local finite-sum lemma is acceptable. Do not build a general quotient-sum library.

### D4. Vector/matrix source equation

For the selected `τ_R`, package the collection of actual Mellin moments as a vector indexed by evaluation row:

```text
momentVec i :=
  pascalCenteredXiZeroDiskWeightedMoment
    (pascalCenteredXiMellinSecondDifferenceWeight ε (τ_R i)) R
```

and the orbit masses as:

```text
massVec j := pascalCenteredXiSquaredOrbitMass R (q_R j)
```

Prove the exact finite equation:

```text
momentVec = H_ε *ᵥ massVec
```

or the transpose-equivalent orientation, depending on the chosen matrix convention.

The matrix in this equation must be the same full-rank canonical Mellin evaluation matrix from C2-C.

### D5. Rank consequence

For sufficiently small positive `ε`, `det H_ε ≠ 0`. Therefore the map from squared-orbit masses to the finite vector of Mellin zero moments is injective.

A useful theorem shape is:

```text
H_ε *ᵥ m₁ = H_ε *ᵥ m₂ -> m₁ = m₂
```

or simply a statement that `H_ε.mulVec` has trivial kernel.

Do not construct an off-critical selector or witness yet. That belongs to GWSS-002.

## 8. What “actual-window full rank” means

C2 must explicitly document that full rank is **modulo squared orbit**.

It does **not** mean that an even Mellin family separates `z` from `-z`.

The correct statement is:

```text
one coordinate per distinct q = z^2
```

The C2 source matrix is full rank on this finite squared-orbit coordinate space.

This is not a defect: even weights are structurally incapable of separating the two points in one `±` orbit, and the zero moment naturally aggregates their multiplicities.

## 9. Stop conditions

Stop and classify precisely if one of these occurs:

```text
A. ACTUAL-SQUARED-ORBIT-ENUMERATION-API-GAP
B. ACTUAL-MELLIN-SPECTRAL-COLUMN-SCALING-GAP
C. ACTUAL-SQUARED-ORBIT-MOMENT-AGGREGATION-GAP
D. ACTUAL-XI-WINDOW-RANK-INFORMATION-OBSTRUCTION
```

Rules:

- A finite-type reindexing inconvenience is an API gap, not an information obstruction.
- A `Finset` image/fiberwise sum inconvenience is an aggregation API gap, not an information obstruction.
- If C2-B/C full evaluation rank is proved but D aggregation is blocked, report that distinction explicitly and **do not** authorize GWSS-002 yet.
- Do not weaken the carrier back to individual zeros just to avoid the squared-orbit bookkeeping.

## 10. Success classification

Full success requires:

```text
actual squared-orbit carrier constructed
representatives lie in the actual Xi window
all squared coordinates nonzero and distinct
C1E bare-kernel full rank applied
canonical Mellin evaluation matrix eventually full rank for ε -> 0+
actual zero moment regrouped by squared orbit
moment vector = full-rank evaluation matrix × orbit-mass vector
```

Then classify exactly:

```text
MELLIN-FAMILY-ACTUAL-WINDOW-FULL-RANK-FOUND
```

At that point GWSS-001 source-rank is closed.

The next unresolved Gap becomes:

```text
OFF-CRITICAL-MELLIN-WITNESS-GAP
```

and GWSS-002 may be authorized only in the next assignment.

## 11. Provider firewall after C2 success

Even after C2 closes, do not claim RH or contradiction.

C2 proves only that the zero-independent Mellin family has enough finite rank to recover the squared-orbit mass vector of each fixed finite actual Xi window from finitely many zero-side moments.

The next stage must still construct a useful off-critical witness and then confront the arithmetic side.

The known hard stage remains later:

```text
explicit formula RHS
  ordinary zeta / von Mangoldt term
  archimedean term
  elementary term
  top-horizontal term
```

The current repository has `X -> ∞` convergence at fixed finite residue window, but no authorized `T -> ∞` top-horizontal disappearance theorem.

Do not jump to GWSS-003 in this assignment.

## 12. Required outputs

Prefer a focused module such as:

```text
DkMath/RH/CFBRC/PascalCenteredXiMellinActualWindowFullRankAudit.lean
```

and report:

```text
docs/wip/RH-CFBRC-guinand-weil-source-rank-audit/
0022-GWSS-001M-C2-actual-window-full-rank-report.md
```

The report must state:

```text
global objective
current GWSS stage
load-bearing provider boundary
squared-orbit carrier status
representative/enumeration status
C1E transfer status
spectral column-scaling status
orbit-mass aggregation status
moment-vector matrix equation status
primary classification
next unresolved Gap
GWSS-002 authorization status
verification
```

## 13. Verification

At minimum run the focused build for the new module and:

```text
git diff --check
```

Inspect axioms of the load-bearing public theorems, especially:

```text
actual squared-orbit bare-kernel rank theorem
actual canonical Mellin full-rank theorem
actual zero-moment squared-orbit decomposition theorem
moment-vector matrix equation / injectivity theorem
```

Requirements:

```text
NO sorry
NO admit
NO new axiom
NO native_decide as a proof escape
```

The axiom footprint should remain the standard foundational set already seen on this branch.

## 14. Final reporting format

End with exactly one primary classification:

```text
MELLIN-FAMILY-ACTUAL-WINDOW-FULL-RANK-FOUND
ACTUAL-SQUARED-ORBIT-ENUMERATION-API-GAP
ACTUAL-MELLIN-SPECTRAL-COLUMN-SCALING-GAP
ACTUAL-SQUARED-ORBIT-MOMENT-AGGREGATION-GAP
ACTUAL-XI-WINDOW-RANK-INFORMATION-OBSTRUCTION
```

If `FOUND`, state explicitly:

```text
For every fixed finite actual centered-Xi zero window, the canonical
zero-independent Mellin second-difference family is full rank on the finite
space of distinct squared orbits, and the actual weighted zero moments are
the corresponding full-rank matrix transform of the squared-orbit mass vector.
```

Then state:

```text
GWSS-001 source-rank: CLOSED
Next unresolved Gap: OFF-CRITICAL-MELLIN-WITNESS-GAP
GWSS-002: authorized for the next bounded assignment, not started here
GWSS-003: not authorized
```
