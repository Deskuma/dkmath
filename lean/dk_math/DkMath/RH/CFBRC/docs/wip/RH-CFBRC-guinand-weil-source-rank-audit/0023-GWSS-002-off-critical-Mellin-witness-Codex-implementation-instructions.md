# GWSS-002 off-critical Mellin witness — Codex implementation instructions

Date: 2026-08-21

Repository: `Deskuma/dkmath`

Branch: `wip/RH-CFBRC-guinand-weil-source-rank-audit-260820-v0`

## 0. Mission

Continue the GWSS route after C2 closed the actual-window source-rank problem.

Implement and audit only:

```text
GWSS-002-A  off-critical geometry on the squared-orbit carrier
GWSS-002-B  occupied squared-orbit mass is nonzero
GWSS-002-C  dual coordinate extraction from the full-rank Mellin moment matrix
GWSS-002-D  target-orbit off-critical scalar witness
GWSS-002-E  package the scalar witness as one admissible finite Mellin weight
```

Do **not** start:

```text
GWSS-003  arithmetic sign / upper-control audit
GWSS-004  classical Guinand--Weil infrastructure
T -> infinity horizontal-term removal
Weil positivity
Li criterion
RH deduction
```

Current trusted frontier:

```text
GWSS-001M-C2
  MELLIN-FAMILY-ACTUAL-WINDOW-FULL-RANK-FOUND
  GWSS-001 source-rank CLOSED

current missing bridge
  OFF-CRITICAL-MELLIN-WITNESS-GAP
```

The goal of this assignment is a **one-way witness theorem** of the form:

```text
off-critical squared orbit in an actual finite Xi window
  -> exists one admissible finite linear combination of the canonical Mellin weights
  -> its actual zero-side weighted moment is certified nonzero.
```

This is not a positivity theorem and must not become one.

If the bounded assignment succeeds, classify:

```text
OFF-CRITICAL-MELLIN-WITNESS-FOUND
```

Then the next unresolved Gap becomes:

```text
MELLIN-WITNESS-ARITHMETIC-CONTROL-GAP
```

Only then may GWSS-003 be authorized in a later assignment.

## 1. Mandatory orientation before editing

Before any edit, report:

```text
current branch
current HEAD
working-tree status
Lean toolchain
0000 roadmap GWSS-002/GWSS-003 sections read
0021 and 0022 read
PascalCenteredXiMellinActualWindowFullRankAudit.lean read
PascalCenteredXiMellinArithmeticSpecialization.lean read
multiplicity definition / positivity API audited
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
GWSS-002
```

Load-bearing provider boundary:

```text
The independent analytic source is still the already-prescribed canonical
Mellin second-difference family from GWSS-001/C2.

A carrier-dependent finite linear combination may be synthesized now as an
existential witness, but it MUST NOT be counted as a new independent source.
```

Forbidden providers:

```text
RH
classical Weil positivity
Li criterion
functional-equation reflection as a new source
criticalMirror / conjugation as a new source
fixed-Xi defect vanishing
unproved T -> infinity horizontal decay
unproved limit exchange
prime-side sign assumptions
reverse Cauchy--Schwarz / reverse triangle / Gram positivity
```

## 2. Why the witness must isolate one orbit

For a centered zero

```text
z = δ + i γ
q = z^2
```

we have

```text
q.im = 2 * δ * γ.
```

Actual nontrivial zeta zeros already satisfy `γ ≠ 0`.  Hence on the actual
centered-Xi carrier:

```text
δ = 0  <->  q.im = 0.
```

Therefore an off-critical squared orbit is exactly a carrier coordinate with
nonzero imaginary part.

However, do **not** use the global scalar

```text
sum_q q.im * mass(q)
```

as the primary witness.  Different squared orbits can cancel, in particular
if conjugate-related coordinates occur.  The C2 full-rank theorem exists
precisely so that one target squared orbit can be extracted first.

Preferred architecture:

```text
target orbit q0
  -> extract mass(q0) from the Mellin moment vector
  -> multiply by q0.im
  -> off-critical q0 gives q0.im != 0
  -> occupied orbit gives mass(q0) != 0
  -> detector != 0
```

No global cancellation argument is needed.

## 3. GWSS-002-A — squared-orbit off-critical geometry

### A1. Exact square-imaginary-part identity

Expose a small theorem, preferably independent of Xi:

```lean
theorem complex_sq_im_eq_two_mul_re_mul_im (z : ℂ) :
    (z ^ 2).im = 2 * z.re * z.im := by
  ...
```

Use existing Complex multiplication APIs or `ring` after reducing real/imaginary parts.

Equivalent normalization is acceptable.

### A2. Actual centered-Xi zero has nonzero imaginary coordinate

Reuse the existing unconditional theorem chain behind:

```text
pascalCenteredXiZeroDiskFinset_ne_zero
nontrivialRiemannZetaZero_im_ne_zero
```

but prove the exact statement actually needed:

```lean
theorem pascalCenteredXiZeroDiskFinset_im_ne_zero
    {R : ℝ} {z : ℂ}
    (hz : z ∈ pascalCenteredXiZeroDiskFinset R) :
    z.im ≠ 0 := by
  ...
```

Do not infer this merely from `z ≠ 0`; use the nontrivial-zeta-zero theorem.

### A3. Critical-line/off-critical equivalence in squared coordinates

For actual window points, prove:

```lean
theorem pascalCenteredXiZeroDiskFinset_re_eq_zero_iff_sq_im_eq_zero
    {R : ℝ} {z : ℂ}
    (hz : z ∈ pascalCenteredXiZeroDiskFinset R) :
    z.re = 0 ↔ (z ^ 2).im = 0 := by
  ...
```

and/or the directly useful nonzero form:

```lean
theorem pascalCenteredXiZeroDiskFinset_re_ne_zero_iff_sq_im_ne_zero
    {R : ℝ} {z : ℂ}
    (hz : z ∈ pascalCenteredXiZeroDiskFinset R) :
    z.re ≠ 0 ↔ (z ^ 2).im ≠ 0 := by
  ...
```

This is the intended geometry bridge.  Do not use RH, criticalMirror, or the
functional equation.

### A4. Optional squared-orbit predicate

If useful for theorem readability, define a small predicate such as:

```lean
def PascalCenteredXiSquaredOrbitOffCritical (R : ℝ) (q : ℂ) : Prop :=
  q ∈ pascalCenteredXiSquaredOrbitFinset R ∧ q.im ≠ 0
```

Do not introduce a larger geometry framework.

## 4. GWSS-002-B — occupied squared-orbit mass is nonzero

This is load-bearing for a nonzero zero-side witness.

Recall:

```lean
pascalCenteredXiSquaredOrbitMass R q
```

is the complex cast of the finite sum of zero multiplicities in the fiber
`z^2 = q`.

For every occupied orbit, prove:

```lean
theorem pascalCenteredXiSquaredOrbitMass_ne_zero
    {R : ℝ} {q : ℂ}
    (hq : q ∈ pascalCenteredXiSquaredOrbitFinset R) :
    pascalCenteredXiSquaredOrbitMass R q ≠ 0 := by
  ...
```

### B1. Mandatory multiplicity audit

Before proving this theorem, locate the exact definition of:

```text
pascalCenteredXiZeroMultiplicity
```

and the existing theorem/API showing that a point in the actual zero carrier
has positive/nonzero multiplicity.

Prefer to reuse an existing theorem.

If the current API only exposes multiplicity as a natural-number count,
prove a short local bridge:

```text
z in actual zero window -> 0 < multiplicity(z)
```

then show the finite fiber mass contains at least one positive summand and all
summands are nonnegative naturals before casting to `ℂ`.

A clean alternative is to define a private or public natural orbit mass,
prove it positive, and prove that the existing complex orbit mass is its cast.

Do **not** argue informally that multiplicities are positive.  This point must
be formalized.

### B2. Stop rule for multiplicity

If no theorem or short derivation connects carrier membership to positive
multiplicity, stop and classify precisely:

```text
ACTUAL-ORBIT-MASS-NONZERO-API-GAP
```

Do not replace it with an axiom or an assumed positivity hypothesis in the
main witness theorem.

## 5. GWSS-002-C — dual coordinate extraction from full rank

C2 gives, for suitable fixed `R ε τ`, the exact source equation:

```text
momentVec = H *ᵥ massVec
```

where:

```text
H = pascalCenteredXiMellinEvaluationMatrix R ε τ
```

and determinant nonvanishing implies `H.mulVec` is injective.

For the witness we need more than injectivity: for any target orbit index
`j0`, construct a finite row functional on the moment vector that returns the
single coordinate `massVec j0`.

### C1. Preferred finite-linear-algebra theorem

For a square complex matrix `H` with `H.det ≠ 0`, prove a focused helper of
semantic strength:

```lean
theorem exists_row_coefficients_extract_mulVec_coordinate
    {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ)
    (hdet : H.det ≠ 0) (j0 : Fin n) :
    ∃ c : Fin n → ℂ,
      ∀ m : Fin n → ℂ,
        ∑ i, c i * (H *ᵥ m) i = m j0 := by
  ...
```

Equivalent matrix notation is acceptable.

### C2. Preferred proof route

Use the pinned finite matrix inverse / nonsingular inverse API.

Conceptually:

```text
c^T = e_j0^T * H^{-1}
```

or equivalently solve:

```text
H^T * c = e_j0.
```

Then:

```text
c^T * (H m) = e_j0^T m = m_j0.
```

Search pinned Mathlib for the smallest useful API around:

```text
Matrix.nonsingInv
Matrix.mul_nonsing_inv
Matrix.nonsing_inv_mul
Matrix.transpose
Matrix.mulVec
Matrix.vecMul
Matrix.det_transpose
```

Do not build a general dual-space library.

### C3. Acceptable fallback

If inverse row notation is awkward, define the coefficient vector directly
from entries of `Matrix.nonsingInv H` and prove the finite sum identity by
`Matrix.mul_apply` / `Matrix.mulVec` calculations.

This is a finite algebra task.  An API inconvenience here is not an
information obstruction.

### C4. Apply to the C2 source equation

Package a theorem for the actual window:

```lean
theorem exists_pascalCenteredXiMellinMoment_coordinate_extractor
    {R ε : ℝ}
    {τ : Fin (pascalCenteredXiSquaredOrbitIndexCard R) → ℝ}
    (hε : 0 < ε)
    (hdet : (pascalCenteredXiMellinEvaluationMatrix R ε τ).det ≠ 0)
    (j0 : Fin (pascalCenteredXiSquaredOrbitIndexCard R)) :
    ∃ c : Fin (pascalCenteredXiSquaredOrbitIndexCard R) → ℂ,
      ∑ i, c i * pascalCenteredXiMellinMomentVec R ε τ i =
        pascalCenteredXiSquaredOrbitMassVec R j0 := by
  ...
```

Mandatory dependency:

```text
C2 momentVec = H *ᵥ massVec
+ finite inverse coordinate extractor
```

Do not use the carrier-dependent polynomial selector from GWSS-001T as the
primary proof.  The point of GWSS-002 is to use the already-certified canonical
Mellin basis.

## 6. GWSS-002-D — off-critical target-orbit scalar detector

Let target index `j0` have squared coordinate:

```text
q0 := pascalCenteredXiSquaredOrbitCoordinate R j0
```

Define or expose the target scalar detector:

```text
(q0.im : ℂ) * pascalCenteredXiSquaredOrbitMassVec R j0
```

Given:

```text
q0.im ≠ 0
```

and the orbit-mass nonzero theorem, prove this scalar is nonzero.

Then scale the coordinate-extractor coefficients by `(q0.im : ℂ)` to obtain:

```lean
∃ c,
  (∑ i, c i * pascalCenteredXiMellinMomentVec R ε τ i) =
    (q0.im : ℂ) * pascalCenteredXiSquaredOrbitMassVec R j0
```

with a final `≠ 0` conclusion under the off-critical hypothesis.

A suitable load-bearing theorem shape is:

```lean
theorem exists_nonzero_pascalCenteredXiMellin_offCritical_detector
    {R ε : ℝ}
    {τ : Fin (pascalCenteredXiSquaredOrbitIndexCard R) → ℝ}
    (hε : 0 < ε)
    (hdet : (pascalCenteredXiMellinEvaluationMatrix R ε τ).det ≠ 0)
    (j0 : Fin (pascalCenteredXiSquaredOrbitIndexCard R))
    (hoff : (pascalCenteredXiSquaredOrbitCoordinate R j0).im ≠ 0) :
    ∃ c : Fin (pascalCenteredXiSquaredOrbitIndexCard R) → ℂ,
      (∑ i, c i * pascalCenteredXiMellinMomentVec R ε τ i) ≠ 0 := by
  ...
```

Stronger exact-value conclusion is preferred if convenient.

The target coordinate must be isolated **before** multiplying by `q0.im`.
Do not use a global imaginary-part sum.

## 7. GWSS-002-E — package as one admissible Mellin witness weight

The roadmap asks for an admissible weight, not only an abstract scalar
combination of recorded moments.

Given extractor/detector coefficients `c`, define the finite synthesized weight:

```lean
noncomputable def pascalCenteredXiMellinWitnessWeight
    (ε : ℝ)
    (τ : Fin n → ℝ)
    (c : Fin n → ℂ) : ℂ → ℂ :=
  fun z => ∑ i, c i * pascalCenteredXiMellinSecondDifferenceWeight ε (τ i) z
```

Use the actual C2 index cardinality directly if that gives cleaner types.

### E1. Admissibility

For `hε : 0 < ε`, prove the finite combination is:

```text
Differentiable ℂ
PascalCenteredEvenWeight
```

using the already-proved admissibility of each canonical Mellin weight and
finite-sum closure.

Do not add a new analytic test-function theory.

### E2. Moment linearity

Prove exactly:

```text
pascalCenteredXiZeroDiskWeightedMoment witnessWeight R
  = sum_i c_i * pascalCenteredXiMellinMomentVec R ε τ i
```

up to the chosen multiplication-order normalization.

This should be a finite-sum linearity/reindexing argument only.

### E3. Final witness theorem

Combine C2-C/D/E into a theorem of semantic strength:

```text
off-critical actual squared orbit
  -> exists ε > 0, τ, c, h,
       h is a finite linear combination of canonical Mellin weights,
       h is differentiable and even,
       pascalCenteredXiZeroDiskWeightedMoment h R != 0.
```

There are two acceptable packaging levels.

#### Preferred global-existence wrapper

Use:

```text
eventually_pascalCenteredXiActualWindow_mellin_evaluation_det_ne_zero R
```

to obtain `τ`, then choose one sufficiently small positive `ε` with determinant
nonzero, and package the witness.

The filter is `nhdsWithin 0 (Set.Ioi 0)`.  Any chosen `ε` must explicitly
satisfy `0 < ε`; do not silently infer it from an eventual proposition without
proving membership in the filter set.

#### Acceptable bounded local theorem

If the only obstruction is selecting one `ε` from the eventual theorem in the
pinned API, first close the stronger local theorem parameterized by:

```text
hε : 0 < ε
hdet : H.det != 0
```

Then attempt a short selection wrapper.

If the wrapper alone is blocked, classify the remaining issue as:

```text
POSITIVE-EPSILON-SELECTION-API-GAP
```

Do not call that an information obstruction.

## 8. Source-rank firewall for the synthesized witness

This point is mandatory in module and report documentation.

The final witness coefficient vector `c` may depend on:

```text
the finite actual window R
the chosen target orbit j0
the selected finite Mellin evaluation matrix
```

Therefore the synthesized witness weight is **carrier/target dependent**.

That is acceptable in GWSS-002 because it is an existential witness built
inside the span of the already independent canonical Mellin family.

It is **not** a new source-rank provider.

State explicitly:

```text
Independent source:
  canonical Mellin family from GWSS-001/C2

Synthesized witness:
  target-dependent finite linear combination of that family
```

Do not claim `c` itself is zero-derived independent information.

## 9. Fixed quadratic defect comparison

Do not reopen a full source-rank comparison; GWSS-001 already closed it.

For GWSS-002 it is sufficient that the witness isolates one squared-orbit
coordinate through the C2 invertible Mellin matrix and certifies

```text
q0.im * mass(q0) != 0.
```

This target-coordinate information is not being inferred from the fixed
quadratic defect alone; it is read from the full-rank Mellin source already
certified in C2.

Do not add a second abstract countermodel unless a concrete Lean dependency
requires it.

## 10. Stop conditions

Stop and report precisely if one of these occurs:

```text
A. actual carrier membership cannot be connected to positive zero multiplicity
   -> ACTUAL-ORBIT-MASS-NONZERO-API-GAP

B. finite inverse cannot be turned into a target-coordinate extractor without
   a genuinely large matrix development
   -> MELLIN-DUAL-COORDINATE-EXTRACTOR-API-GAP

C. one positive epsilon cannot be selected from the existing eventual full-rank theorem
   while the local hε/hdet theorem is complete
   -> POSITIVE-EPSILON-SELECTION-API-GAP

D. the off-critical geometry q.im != 0 cannot be obtained from actual centered
   zero data without importing RH/functional-equation assumptions
   -> OFF-CRITICAL-SQUARED-ORBIT-GEOMETRY-GAP

E. an actual target orbit can be isolated only by introducing a new unproved
   positivity or sign theorem
   -> OFF-CRITICAL-WITNESS-INFORMATION-OBSTRUCTION
```

Do not label routine Matrix/Finset/filter API friction as an information obstruction.

## 11. Success classification

The primary success classification is:

```text
OFF-CRITICAL-MELLIN-WITNESS-FOUND
```

Use it only if the final result establishes, for an off-critical actual squared
orbit, an admissible finite Mellin witness with certified nonzero actual
zero-side weighted moment.

A matrix-coordinate theorem without an admissible witness weight is useful
partial progress but does not yet earn the full classification.

After success, state:

```text
GWSS-002: CLOSED
Next unresolved Gap: MELLIN-WITNESS-ARITHMETIC-CONTROL-GAP
GWSS-003: authorized for the next bounded assignment
GWSS-004: not authorized
```

## 12. Why GWSS-003 is still forbidden here

Do not substitute the finite explicit formula into the witness and begin
estimating its right-hand side in this assignment.

The arithmetic formula contains:

```text
prime / von-Mangoldt term
archimedean term
elementary term
top-horizontal term
```

The top-horizontal term remains present.  No `T -> infinity` disappearance
has been proved merely because the witness is now available.

This assignment ends once the zero-side off-critical witness exists.

## 13. Required module/report outputs

Prefer a focused module such as:

```text
DkMath/RH/CFBRC/PascalCenteredXiMellinOffCriticalWitnessAudit.lean
```

and report:

```text
docs/wip/RH-CFBRC-guinand-weil-source-rank-audit/
0024-GWSS-002-off-critical-Mellin-witness-report.md
```

The report must include:

```text
global objective
current GWSS stage
load-bearing provider boundary
squared-orbit geometry status
orbit-mass nonzero status
dual coordinate extraction status
admissible witness-weight status
primary classification
next unresolved Gap
GWSS-003 authorization status
verification
```

## 14. Verification

At minimum run:

```text
lake build DkMath.RH.CFBRC.PascalCenteredXiMellinOffCriticalWitnessAudit
git diff --check
```

Also inspect `#print axioms` for the principal public theorems, especially:

```text
actual orbit mass nonzero
coordinate extractor
off-critical detector
final admissible witness theorem
```

Requirements:

```text
NO sorry
NO admit
NO new axiom
NO native_decide as a proof shortcut
```

The expected axiom footprint is the standard foundational set already present
in the branch (`propext`, `Classical.choice`, `Quot.sound`) unless an existing
upstream theorem legitimately carries something else; report any change.

## 15. Final reporting format

End with exactly one primary classification from:

```text
OFF-CRITICAL-MELLIN-WITNESS-FOUND
ACTUAL-ORBIT-MASS-NONZERO-API-GAP
MELLIN-DUAL-COORDINATE-EXTRACTOR-API-GAP
POSITIVE-EPSILON-SELECTION-API-GAP
OFF-CRITICAL-SQUARED-ORBIT-GEOMETRY-GAP
OFF-CRITICAL-WITNESS-INFORMATION-OBSTRUCTION
```

If `FOUND`, state explicitly:

```text
An off-critical squared orbit in a fixed actual centered-Xi window admits an
admissible target-dependent finite linear combination of the zero-independent
canonical Mellin family whose actual zero-side weighted moment is nonzero.
```

Then state:

```text
GWSS-002: CLOSED
Next unresolved Gap: MELLIN-WITNESS-ARITHMETIC-CONTROL-GAP
GWSS-003: authorized next but not started
GWSS-004: not authorized
```
