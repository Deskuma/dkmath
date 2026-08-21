# GWSS-003C target-specific quantitative homogeneity audit — Codex implementation instructions

Date: 2026-08-21

Repository: `Deskuma/dkmath`

Branch: `wip/RH-CFBRC-guinand-weil-source-rank-audit-260820-v0`

## 0. Mission

Continue only from the verified GWSS-003B frontier.

Trusted state:

```text
GWSS-001 source rank                         CLOSED
GWSS-002 off-critical Mellin witness         CLOSED
GWSS-003A finite arithmetic identity         FOUND
GWSS-003B universal complex-linear phase     NOGO
finite prime vertical norm majorant          FOUND
real/conjugation witness compatibility       API GAP
current primary missing provider             TARGET-SPECIFIC-QUANTITATIVE-CONTROL-REQUIRED
```

Implement only the next bounded stage:

```text
GWSS-003C-0  correct the 0030 report classification hierarchy if still needed
GWSS-003C-1  expose an unscaled target-orbit mass extractor witness
GWSS-003C-2  prove that the off-critical detector witness is target-imaginary-part scalar scaling of that mass witness
GWSS-003C-3  transport this scaling through zero moment, finite arithmetic RHS, and the four arithmetic surfaces
GWSS-003C-4  formalize the first-order homogeneity cancellation for norm/majorant inequalities
GWSS-003C-5  decide whether ordinary linear/norm quantitative control can ever force `q0.im = 0`
GWSS-003C-6  identify the exact next provider class without starting it
```

Do **not** start:

```text
GWSS-004 classical Guinand--Weil infrastructure
Weil positivity
Li criterion
T -> infinity
new zero-avoidance-height theory
new Xi growth theory
new source family
new interpolation family
DkReal shrinking-window uniqueness
RiemannHypothesis deduction
```

This stage is a **homogeneity / information-content audit**, not a request for many new bounds.

## 1. Mandatory orientation before editing

Before any edit, report:

```text
current branch
current HEAD
working-tree status
Lean toolchain
0029 instructions read
0030 report read
PascalCenteredXiMellinOffCriticalWitnessAudit.lean read
PascalCenteredXiMellinWitnessArithmeticControlAudit.lean read
PascalCenteredXiMellinWitnessPhaseNoGoAudit.lean read
PascalCenteredXiPrimeRightEdgeTransport.lean read
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
GWSS-003C
```

Load-bearing boundary:

```text
The current off-critical witness is target-dependent.
Its coefficients are obtained by taking a coordinate extractor for one
actual squared orbit and multiplying that extractor by the real scalar
`q0.im`, where q0 is the selected squared coordinate.

The finite arithmetic RHS is already proved complex-linear in the weight.
Therefore any quantitative theorem that is only first-order homogeneous in
that same weight may scale by exactly the same `|q0.im|` factor.

The task is to determine whether this scaling is merely a proof artifact or a
formal structural obstruction.
```

Forbidden shortcuts:

```text
RH
classical Weil positivity
Li criterion
functional-equation reflection as new information
conjugation as a new independent source
fixed-Xi defect vanishing
unproved horizontal decay
unproved limit exchange
reverse triangle / reverse Cauchy-Schwarz
assuming inverse-matrix conditioning
assuming `q0.im` is uniformly separated from zero
calling an identity or homogeneous rescaling a new arithmetic provider
```

## 2. Correct 0030 classification hierarchy if necessary

The 0029 instructions required exactly one primary classification.
If the current 0030 report still lists the three labels

```text
UNIVERSAL-COMPLEX-LINEAR-PHASE-PROVIDER-NOGO
CONJUGATION-SYMMETRY-API-GAP
TARGET-SPECIFIC-QUANTITATIVE-CONTROL-REQUIRED
```

as co-primary, make a **report-only** correction before or together with the 003C report:

```text
Primary classification:
TARGET-SPECIFIC-QUANTITATIVE-CONTROL-REQUIRED

Secondary findings:
UNIVERSAL-COMPLEX-LINEAR-PHASE-PROVIDER-NOGO
CONJUGATION-SYMMETRY-API-GAP
```

Do not change any Lean theorem merely for this documentation correction.

## 3. Structural fact to audit

The current GWSS-002D construction proceeds schematically as follows.

For an invertible actual-window Mellin evaluation matrix `H` and target index `j0`, first obtain a coefficient row `c0` such that

```text
sum_i c0_i * moment_i = mass(j0).
```

Then define the off-critical coefficients by multiplying by the target squared-coordinate imaginary part:

```text
qIm := ((q0.im : ℝ) : ℂ)
c_i := qIm * c0_i.
```

Hence

```text
sum_i c_i * moment_i = qIm * mass(j0).
```

The principal question of GWSS-003C is whether the corresponding synthesized weights satisfy the exact function identity

```text
h_off = qIm * h_mass
```

and therefore, for every complex-linear arithmetic functional `F`,

```text
F(h_off) = qIm * F(h_mass).
```

If so, the off-critical displacement enters the current detector only as an overall target-dependent scalar.

Do not assume this conclusion. Prove the relevant identities in Lean.

## 4. GWSS-003C-1 — unscaled mass extractor witness

### C1. Expose an admissible unscaled mass extractor

Reuse the existing theorem

```text
exists_pascalCenteredXiMellinMoment_coordinate_extractor
```

or the lowest-level reusable extractor theorem available in
`PascalCenteredXiMellinOffCriticalWitnessAudit.lean`.

For fixed:

```text
R
ε > 0
τ
hdet : det(mellinEvaluationMatrix R ε τ) != 0
j0
```

obtain coefficients `c0` whose synthesized witness has zero-side moment exactly equal to the target squared-orbit mass.

Preferred theorem shape:

```lean
theorem exists_pascalCenteredXiMellinMassWitness_of_full_rank_target
    {R ε : ℝ} (hε : 0 < ε)
    {τ : Fin (pascalCenteredXiSquaredOrbitIndexCard R) → ℝ}
    (hdet : (pascalCenteredXiMellinEvaluationMatrix R ε τ).det ≠ 0)
    (j0 : Fin (pascalCenteredXiSquaredOrbitIndexCard R)) :
    ∃ c0 : Fin (pascalCenteredXiSquaredOrbitIndexCard R) → ℂ,
      Differentiable ℂ (pascalCenteredXiMellinWitnessWeight ε τ c0) ∧
      PascalCenteredEvenWeight (pascalCenteredXiMellinWitnessWeight ε τ c0) ∧
      pascalCenteredXiZeroDiskWeightedMoment
          (pascalCenteredXiMellinWitnessWeight ε τ c0) R =
        pascalCenteredXiSquaredOrbitMassVec R j0 := by
  ...
```

Equivalent packaging is acceptable.

Do not introduce a new selector family if existing inverse-matrix extraction already proves this.

### C2. Keep occupancy and off-critical information separate

The unscaled `c0`/`h_mass` must not use `q0.im ≠ 0`.

This is important: `h_mass` is an occupancy/mass extractor, not an off-critical detector.

## 5. GWSS-003C-2 — exact scalar factorization of the off-critical witness

### D1. Coefficient scaling identity

For

```text
qIm : ℂ := (pascalCenteredXiSquaredOrbitCoordinate R j0).im
c : Fin n → ℂ := fun i => qIm * c0 i
```

prove the exact function identity

```text
pascalCenteredXiMellinWitnessWeight ε τ c
  = fun z => qIm * pascalCenteredXiMellinWitnessWeight ε τ c0 z.
```

Preferred public or private helper:

```lean
theorem pascalCenteredXiMellinWitnessWeight_scaled_coefficients
    (a : ℂ) (ε : ℝ) (τ : Fin n → ℝ) (c0 : Fin n → ℂ) :
    pascalCenteredXiMellinWitnessWeight ε τ (fun i => a * c0 i) =
      fun z => a * pascalCenteredXiMellinWitnessWeight ε τ c0 z := by
  ...
```

This should be finite-sum algebra only.

### D2. Detector reconstruction

Package a theorem that, for an off-critical target, returns both:

```text
h_mass
h_off
h_off = qIm * h_mass
zeroMoment(h_mass) = mass(q0)
zeroMoment(h_off) = qIm * mass(q0)
```

The existing global GWSS-002D theorem may remain unchanged. A new comparison theorem is enough.

Do not reimplement the full existence proof if the needed witnesses can be obtained from existing theorems.

## 6. GWSS-003C-3 — arithmetic scaling transport

Use the already-proved

```text
pascalCenteredXiFiniteArithmeticRHS_const_mul
```

and, where useful, direct component scalar-linearity to record:

```text
finiteArithmeticRHS(h_off, W)
  = qIm * finiteArithmeticRHS(h_mass, W).
```

At minimum also audit the same exact scalar factor for:

```text
ordinary-zeta right-edge integral
archimedean right-edge integral
elementary right-edge integral
top-horizontal contribution
finite prime-cutoff integral / integrand if compact
```

Do not spend the assignment creating a general complex-linear functional framework.

A small generic helper is acceptable only if it shortens the focused proof.

### E1. Normalized exact identity

Because an off-critical target has `qIm != 0`, prove the most useful normalized statement obtained by cancelling the scalar from the finite explicit formula.

Schematic target:

```text
F(h_off) = qIm * F(h_mass)
F(h_off) = -(2*pi*i) * qIm * mass(q0)
qIm != 0
--------------------------------------------
F(h_mass) = -(2*pi*i) * mass(q0)
```

This normalized identity is expected to show that cancelling the off-critical scalar removes all horizontal displacement information and leaves the ordinary occupied-orbit mass identity.

Do not call this normalized identity a contradiction or a new provider.

## 7. GWSS-003C-4 — first-order norm homogeneity cancellation

This is the main quantitative audit.

### F1. Generic scalar norm cancellation

Prove a compact generic complex/real lemma showing that for `a != 0`, first-order homogeneous norm inequalities cancel the same scalar factor.

Possible shapes:

```lean
theorem norm_mul_le_norm_mul_iff_of_ne_zero
    {a w : ℂ} {B : ℝ} (ha : a ≠ 0) ... :
    ‖a * w‖ ≤ ‖a‖ * B ↔ ‖w‖ ≤ B := by
  ...
```

or an inequality implication sufficient for the audit.

Do not over-generalize if Mathlib API friction appears. A specialized theorem for `qIm : ℂ` is enough.

### F2. Apply to the prime-side majorant

The existing finite prime transport gives a genuine arithmetic majorant of the shape

```text
||primeCutoffIntegrand(h, sigma, X, t)||
  <= ||h(centeredRightEdge)|| * M(sigma).
```

For `h_off = qIm * h_mass`, expose that both sides carry the same factor `|qIm|`.

Preferred semantic conclusion:

```text
prime majorant applied to h_off
is exactly the qIm-scaled version of the same majorant applied to h_mass.
```

It is enough to prove this pointwise for the weight norm and/or the integrand norm if the full inequality rewrite is awkward.

### F3. Audit the other finite terms

Because the ordinary-zeta, archimedean, elementary, and top-horizontal observables are linear in `h`, their norms are first-order homogeneous under scalar multiplication.

Record the exact norm scaling or enough algebra to conclude that a bound built only from:

```text
triangle inequality
componentwise norm bounds
sum_i |c_i| bounds
basis-weight norm bounds
linear integral norm bounds
```

will inherit the same `|qIm|` factor when the coefficients are obtained by multiplying `c0` by `qIm`.

Do not claim a universal theorem about every imaginable inequality. Limit the conclusion to the audited first-order homogeneous family.

## 8. GWSS-003C-5 — decide whether target-specific quantitative control can force off-critical exclusion

This section is mandatory.

### G1. Distinguish three types of quantitative provider

Audit separately:

```text
Type H1: first-order homogeneous bounds
  B(a*h) = |a| * B(h)

Type H0: nonhomogeneous absolute bounds
  B(a*h) <= C independent of |a|

Type HS: strictly sublinear / vanishing-scale bounds
  B(a*h) = o(|a|) or an asymptotic bound that tends to zero faster
```

For the current detector construction, determine which types could in principle force `q0.im = 0`.

Expected logical distinctions to verify, not assume:

```text
H1:
  scalar cancels; no direct information on whether q0.im is zero.

H0:
  at best gives a finite upper bound on |q0.im| unless the independent bound
  can itself be forced to zero.

HS / justified vanishing sequence:
  could in principle contradict a fixed nonzero detector, but requires new
  analytic information not currently present.
```

### G2. Important finite-identity sanity check

For the normalized mass witness `h_mass`, the exact finite explicit formula is already true:

```text
finiteArithmeticRHS(h_mass, W)
  = -(2*pi*i) * mass(q0).
```

Since an occupied orbit has nonzero positive multiplicity mass, no valid theorem can unconditionally prove a strict upper bound on that exact same finite RHS that is smaller than its exact norm for the same data.

Therefore do not search for a false inequality of the form

```text
||finiteArithmeticRHS(h_mass, W)|| < 2*pi*||mass(q0)||.
```

The only meaningful future route must add genuinely new structure, such as:

```text
an additional parameter/limit where an independent arithmetic bound tends to zero
nonlinear positivity or a quadratic form not equivalent to scalar rescaling
restricted real/conjugation structure with a surviving detector
another independent arithmetic observable
```

Do not implement any of those in GWSS-003C.

### G3. Strong possible stop conclusion

If the formalized scaling shows that the present off-critical factor enters only as an overall scalar and every currently available quantitative control is first-order homogeneous, a legitimate classification is:

```text
OFF-CRITICAL-SCALAR-HOMOGENEITY-OBSTRUCTION
```

This would mean:

```text
The present linear Mellin witness + linear finite explicit formula cannot
extract `q0.im = 0` from ordinary homogeneous norm control, because the
horizontal displacement factor cancels exactly.
```

This is stronger and more precise than a generic coefficient-control gap.

Do not use this classification unless the exact factorization is proved.

## 9. GWSS-003C-6 — decide next provider class

End with exactly one primary classification from:

```text
OFF-CRITICAL-SCALAR-HOMOGENEITY-OBSTRUCTION
TARGET-SPECIFIC-QUANTITATIVE-CONTROL-STILL-OPEN
NONHOMOGENEOUS-VANISHING-CONTROL-REQUIRED
REAL-STRUCTURE-ROUTE-REMAINS-OPEN
NONLINEAR-POSITIVITY-PROVIDER-DECISION-REQUIRED
GWSS-003C-IMPLEMENTATION-API-GAP
```

Secondary findings may include:

```text
unscaled mass witness: FOUND / GAP
off-critical witness scalar factorization: FOUND / GAP
arithmetic RHS scalar factorization: FOUND / GAP
prime-majorant first-order homogeneity: FOUND / GAP
top-horizontal scalar homogeneity: FOUND / GAP
homogeneous bound cancellation: FOUND / GAP
```

### Authorization rule

GWSS-004 remains unauthorized unless GWSS-003C closes the ordinary linear/homogeneous quantitative route and identifies a precise nonlinear/classical positivity fragment as the minimal remaining provider.

If the result is merely that a nonhomogeneous vanishing estimate is still plausible, stay within GWSS-003 and name that exact theorem instead.

## 10. Preferred focused Lean output

Prefer one focused module:

```text
DkMath/RH/CFBRC/PascalCenteredXiMellinWitnessQuantitativeHomogeneityAudit.lean
```

The module should be compact and algebraic. Reuse existing APIs rather than duplicating GWSS-002/003A/003B.

Required report:

```text
docs/wip/RH-CFBRC-guinand-weil-source-rank-audit/
0032-GWSS-003C-target-specific-quantitative-homogeneity-audit-report.md
```

If 0030 classification wording is corrected, keep that edit report-only and minimal.

## 11. Verification

At minimum run:

```text
lake build DkMath.RH.CFBRC.PascalCenteredXiMellinWitnessQuantitativeHomogeneityAudit
git diff --check
```

Inspect `#print axioms` for every load-bearing theorem.

Requirements:

```text
NO sorry
NO admit
NO native_decide proof shortcut
NO new axiom
```

Expected axiom footprint remains:

```text
propext
Classical.choice
Quot.sound
```

Report any deviation.

## 12. Mandatory report orientation

The 0032 report must state explicitly:

```text
global objective
current GWSS stage
load-bearing provider boundary
0030 primary/secondary classification hierarchy
unscaled mass witness status
off-critical scalar-factor status
finite arithmetic RHS scaling status
four-term component scaling status
finite prime majorant scaling status
first-order homogeneous norm cancellation status
whether any current quantitative bound can force q0.im = 0
primary classification
next unresolved Gap
GWSS-004 authorization status
verification
```

## 13. Route-drift firewall

Stop if the implementation begins expanding into:

```text
large coefficient-condition-number theory
large Gamma estimates
new zeta growth theory
new horizontal zero-avoidance sequence
T -> infinity
full Guinand-Weil theorem
full Weil criterion
Li coefficients
new DkReal development
```

without first changing the primary classification.

The purpose of GWSS-003C is to answer one narrow question:

```text
Does the current target-dependent off-critical factor survive independent
first-order quantitative control, or does it cancel by exact homogeneity?
```
