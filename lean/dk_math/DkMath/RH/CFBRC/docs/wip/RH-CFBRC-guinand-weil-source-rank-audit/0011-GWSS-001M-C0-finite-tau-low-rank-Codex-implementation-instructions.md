# GWSS-001M-C0 finite-τ low-rank lift — Codex implementation instructions

Date: 2026-08-21

Repository: `Deskuma/dkmath`

Branch: `wip/RH-CFBRC-guinand-weil-source-rank-audit-260820-v0`

## 0. Mission

Continue the GWSS Mellin source-rank route after the successful low-jet actual-window audit.

Implement and audit only:

```text
GWSS-001M-C0-A  2-orbit bare-kernel finite-τ separation
GWSS-001M-C0-B  3-orbit bare-kernel finite-τ separation
GWSS-001M-C0-C  fixed-ε Mellin spectral-factor rank preservation
GWSS-001M-C0-D  actual Xi-window low-rank finite-τ corollaries
```

Do **not** start:

```text
GWSS-001M-C1  general n-orbit Vandermonde framework
GWSS-001M-C2  arbitrary finite Xi-window full-rank theorem
GWSS-002     off-critical witness family
GWSS-003     arithmetic sign / upper-control audit
```

The purpose of this assignment is to lift the already-proved local Mellin jet rank for two and three squared orbits to actual finite nonzero dilation parameters.

## 1. Mandatory orientation before editing

Before any edit, report:

```text
current branch
current HEAD
working-tree status
Lean toolchain
0007 through 0010 read
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
GWSS-001M-C0
```

Trusted frontier:

```text
GWSS-001T-A
  ACTUAL-WINDOW-EVEN-POLYNOMIAL-ORBIT-SEPARATION-FOUND

GWSS-001M-A
  exact Mellin jets z², z⁴/12, z⁶/360 FOUND

GWSS-001M-B0
  ACTUAL-WINDOW-QZERO-OBSTRUCTION-DISCHARGED

GWSS-001M-B1/B2
  MELLIN-LOW-JET-ACTUAL-WINDOW-RANK-FOUND
```

Next unresolved Gap:

```text
FINITE-TAU-EVALUATION-SEPARATION-GAP
```

## 2. Load-bearing firewall

Do not introduce or use as providers:

```text
RH
classical Weil positivity
Li criterion
fixed-Xi defect vanishing
prime-side sign after cancellation
T -> infinity horizontal decay
zero-avoidance height sequence not already proved
limit exchange
reverse Cauchy-Schwarz
actual-carrier-dependent polynomial selector as an independent source
```

The family being audited here is the already-existing zero-configuration-independent Mellin family

```text
(ε, τ) |-> pascalCenteredXiMellinSecondDifferenceWeight ε τ
```

Parameter choices may be made existentially after a finite zero configuration is given, but the functional form itself must remain the pre-existing Mellin family. Do not construct a new weight by inserting the actual zero carrier into its coefficients.

## 3. Required source modules

Inspect and reuse the exact checked-out declarations in at least:

```text
DkMath.RH.CFBRC.PascalCenteredXiMellinFiniteJetRankAudit
DkMath.RH.CFBRC.PascalCenteredXiMellinLowRankAudit
DkMath.RH.CFBRC.PascalCenteredXiActualWindowVariableWeightRankTransfer
DkMath.RH.CFBRC.PascalCenteredXiMellinArithmeticSpecialization
```

Important existing declarations include:

```text
tendsto_complexExpSecondDifferenceKernel_quadraticJet
tendsto_complexExpSecondDifferenceKernel_quarticJet
tendsto_complexExpSecondDifferenceKernel_sexticJet

twoOrbitMellinJetDeterminant_eq
twoOrbitMellinJetDeterminant_ne_zero
threeOrbitMellinJetDeterminant_eq
threeOrbitMellinJetDeterminant_ne_zero

pascalCenteredXiZeroDiskFinset_sq_ne_zero
eventually_pascalCenteredXiMellinSpectralWeight_ne_zero_on_actual_window
pascalCenteredXiMellinSecondDifferenceWeight_eq_kernel_mul
```

Verify exact theorem names and hypotheses from source before coding.

## 4. Suggested focused module

If a new module is needed, prefer:

```text
DkMath.RH.CFBRC.PascalCenteredXiMellinFiniteTauLowRankAudit
```

Do not create multiple helper modules unless a real dependency boundary forces it.

## 5. C0-A — 2-orbit bare-kernel finite-τ lift

Let

```text
K τ z := complexExpSecondDifferenceKernel τ z
q₁ := z₁²
q₂ := z₂²
```

Use only nonzero dilation values generated from one real parameter:

```text
τ₁ := t
τ₂ := 2t
```

Work on the punctured filter around `t = 0` so both dilation values are nonzero.

Define or reason with the scalar 2-by-2 evaluation determinant

```text
Δ₂(t; z₁,z₂)
  := K t z₁ * K (2t) z₂
     - K t z₂ * K (2t) z₁.
```

The required normalized limit is schematically

```text
Δ₂(t; z₁,z₂) / t²
  -> 3 * D₂(q₁,q₂)
```

where

```text
D₂(q₁,q₂)
  := q₁ * (q₂² / 12) - q₂ * (q₁² / 12).
```

Use the already-proved quadratic and quartic jet theorems. Do not reprove the Taylor expansion from scratch.

Preferred theorem shape:

```text
Tendsto
  (fun t => Δ₂(t; z₁,z₂) / (t : ℂ)^2)
  (nhdsWithin 0 ({0}ᶜ))
  (nhds (3 * D₂(q₁,q₂)))
```

Then prove the finite-parameter consequence:

```text
q₁ ≠ 0
q₂ ≠ 0
q₁ ≠ q₂

implies

∀ᶠ t in nhdsWithin 0 ({0}ᶜ),
  Δ₂(t; z₁,z₂) ≠ 0.
```

An equivalent explicit existence theorem is acceptable, but an eventual theorem is preferred because it records genuine local separation and avoids an arbitrary numerical choice of `t`.

Do not count only the normalized quotient as success. The unnormalized finite evaluation determinant itself must be shown nonzero for sufficiently small nonzero `t`.

## 6. C0-B — 3-orbit bare-kernel finite-τ lift

Use the three nonzero dilation values

```text
τ₁ := t
τ₂ := 2t
τ₃ := 3t
```

and define the direct scalar 3-by-3 evaluation determinant. A `Matrix` framework is optional; direct scalar expansion is acceptable and may be simpler.

The target is a normalized limit of the form

```text
Δ₃(t; z₁,z₂,z₃) / t⁶
  -> 120 * D₃(q₁,q₂,q₃)
```

where `D₃` is exactly the low-jet determinant already formalized in `PascalCenteredXiMellinLowRankAudit`.

The coefficient `120` comes from the dilation-square Vandermonde for

```text
1², 2², 3²
```

and must be proved, not inserted heuristically.

### 6.1 Preferred row-operation route

Avoid a large generic determinant framework unless Lean source strongly favors it.

A practical scalar route is:

```text
row₂ <- row₂ - row₁
row₃ <- row₃ - row₁
```

The two changed rows are order `t²`. Divide them by `t²`.

Their leading quartic-jet coefficients are proportional with factors `3` and `8`. Then use

```text
row₃ <- row₃ - (8/3) row₂
```

and divide the resulting row by another `t²`.

The surviving sextic coefficient is `40`, so the total coefficient is

```text
3 * 40 = 120.
```

This route is recommended because it mirrors the actual low-rank information and avoids building a general `n × n` determinant layer prematurely.

### 6.2 Required finite-parameter consequence

From

```text
q₁, q₂, q₃ nonzero
pairwise distinct q₁, q₂, q₃
```

prove

```text
∀ᶠ t in nhdsWithin 0 ({0}ᶜ),
  Δ₃(t; z₁,z₂,z₃) ≠ 0.
```

Again, the unnormalized finite evaluation determinant must eventually be nonzero.

## 7. Do not confuse jet rank with finite-τ rank

The stage succeeds only if actual finite parameter values are obtained through an eventual or existential theorem.

The following is insufficient by itself:

```text
normalized determinant tends to a nonzero limit
```

The implementation must also conclude:

```text
finite nonzero t values exist, and indeed sufficiently small nonzero t work.
```

Use the punctured-neighborhood hypothesis to discharge denominators such as `(t : ℂ)^2` and `(t : ℂ)^6`.

## 8. C0-C — fixed-ε Mellin spectral-factor rank preservation

For nonzero `τ`, the existing factorization has the form

```text
pascalCenteredXiMellinSecondDifferenceWeight ε τ z
  = K τ z * Sε(z)
```

with

```text
Sε(z)
  := centeredMellinSpectralWeight (centeredMellinBoxApprox ε) z.
```

For fixed `ε`, the spectral factor is independent of `τ` and therefore scales columns of the evaluation matrix.

### 8.1 Two-orbit scaling

Prove an exact scalar identity expressing the actual Mellin 2-orbit evaluation determinant as

```text
Sε(z₁) * Sε(z₂) * Δ₂(t; z₁,z₂)
```

for punctured `t`.

Then show that if

```text
Sε(z₁) ≠ 0
Sε(z₂) ≠ 0
```

and the bare determinant is nonzero, the actual Mellin determinant is nonzero.

### 8.2 Three-orbit scaling

Likewise prove exact column scaling by

```text
Sε(z₁) * Sε(z₂) * Sε(z₃).
```

Do not replace the spectral factor by `1`.

Do not take `ε -> 0` inside any determinant unless an exact theorem is separately proved. The existing finite-window simultaneous nonvanishing theorem is sufficient for this stage.

## 9. C0-D — actual Xi-window low-rank corollaries

Use the existing theorem

```text
eventually_pascalCenteredXiMellinSpectralWeight_ne_zero_on_actual_window
```

rather than reproving finite intersection of pointwise limits.

For actual Xi zero-window points with distinct squared orbits, aim for nested eventual statements of the form

```text
∀ᶠ ε in nhdsWithin 0 (Set.Ioi 0),
  ∀ᶠ t in nhdsWithin 0 ({0}ᶜ),
    actual Mellin 2-orbit determinant at (t, 2t) ≠ 0
```

and analogously for three orbits with `(t, 2t, 3t)`.

This formulation is preferred because it simultaneously records:

```text
positive small ε exist
nonzero small finite τ values exist
the Mellin family itself separates the selected squared orbits
```

If extracting an explicit existential `ε` from the filter is awkward, do not turn that into a mathematical obstruction. A correct nested-eventual theorem is already a finite-parameter separation theorem.

## 10. Actual-window hypotheses

For the 2-orbit actual Xi corollary, require only:

```text
z₁ ∈ pascalCenteredXiZeroDiskFinset R
z₂ ∈ pascalCenteredXiZeroDiskFinset R
z₁² ≠ z₂²
```

Do not add `z₁ ≠ z₂` unless Lean needs it only as an immediately derived local fact.

For the 3-orbit corollary require only actual-window membership and pairwise distinct squared coordinates.

Use `pascalCenteredXiZeroDiskFinset_sq_ne_zero` for the nonzero coordinate hypotheses.

## 11. Independence interpretation

A successful C0 theorem means something stronger than the old carrier-dependent polynomial selector route:

```text
pre-existing Mellin family
  -> finite nonzero parameter values
  -> actual Xi squared-orbit separation for rank 2 / 3
```

This counts as genuine low-rank source-rank evidence because the functional family was not synthesized from the actual carrier.

However, low-rank separation does **not** yet isolate one orbit inside an arbitrary finite window with many squared orbits.

Therefore do not authorize GWSS-002 from a rank-2 or rank-3 theorem alone.

## 12. No general Vandermonde in this assignment

Do not start a theorem indexed by arbitrary `n`, `Fin n`, arbitrary finite orbit sets, or a general determinant library unless an unavoidable existing API forces a tiny helper abstraction.

The next stage after a successful C0 is expected to ask whether the pattern extends to the full finite squared-orbit carrier.

The bounded purpose now is to verify that the jet information really lifts to finite Mellin parameters before generalizing.

## 13. Classification

Choose exactly one primary classification:

```text
FINITE-TAU-LOW-RANK-SEPARATION-FOUND
FINITE-TAU-LOW-RANK-SEPARATION-API-GAP
FINITE-TAU-LOW-RANK-SEPARATION-OBSTRUCTION
```

Use `FOUND` only if both of the following are present:

```text
bare-kernel finite-τ separation for rank 2 and rank 3
actual Mellin-weight finite-τ separation after nonzero spectral-factor scaling
```

If the bare kernel succeeds but the spectral-factor transfer is merely unimplemented, use `API-GAP`, not `FOUND`.

If a genuine mathematical counterexample prevents the finite-τ lift, use `OBSTRUCTION` and state the exact counterexample.

## 14. Next Gap after success

If the classification is

```text
FINITE-TAU-LOW-RANK-SEPARATION-FOUND
```

then the next unresolved Gap becomes

```text
GENERAL-FINITE-ORBIT-MELLIN-RANK-GAP
```

Do not start that next stage automatically.

GWSS-002 remains unapproved until a theorem handles the full finite squared-orbit content needed for an actual off-critical witness.

## 15. Suggested report

Create:

```text
0012-GWSS-001M-C0-finite-tau-low-rank-report.md
```

The report must begin with:

```text
Global objective:
Current GWSS stage:
Load-bearing boundary:
Next unresolved Gap:
```

Then record separately:

```text
C0-A 2-orbit bare-kernel result
C0-B 3-orbit bare-kernel result
C0-C spectral-factor scaling result
C0-D actual-window result
primary classification
GWSS-002 authorization status
```

## 16. Verification

For every new or changed Lean module run the focused build, for example:

```text
lake build DkMath.RH.CFBRC.PascalCenteredXiMellinFiniteTauLowRankAudit
```

Also run:

```text
git diff --check
```

Check for new:

```text
sorry
admit
axiom
```

Use `#print axioms` on the new load-bearing normalized-limit, eventual-nonzero, and actual-window separation theorems.

If no public aggregation import changes, a root `DkMath.RH` build is not mandatory for this bounded assignment.

## 17. Stop conditions

Stop and report instead of expanding scope if the work begins turning into:

```text
general arbitrary-n determinant infrastructure
classical Weil positivity
T -> infinity contour work
prime-side sign search
new carrier-dependent interpolation weights
an unproved exchange of ε and τ limits
an assumption that Sε(z) is exactly 1
```

No GWSS-002 implementation is authorized in this assignment.
