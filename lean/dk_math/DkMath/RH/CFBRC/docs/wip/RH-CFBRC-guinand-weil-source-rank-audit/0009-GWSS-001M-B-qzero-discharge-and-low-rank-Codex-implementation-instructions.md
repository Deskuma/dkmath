# GWSS-001M-B q=0 discharge and low-rank Mellin jet audit — Codex implementation instructions

Date: 2026-08-21

Repository: `Deskuma/dkmath`

Branch: `wip/RH-CFBRC-guinand-weil-source-rank-audit-260820-v0`

## 0. Mission

Continue the bounded Mellin-rank audit after `0008-GWSS-001M-Mellin-finite-jet-rank-report.md`.

Implement and audit only:

```text
GWSS-001M-B0  discharge q = 0 on the actual Xi zero window
GWSS-001M-B1  exact 2-orbit jet-rank certificate
GWSS-001M-B2  exact 3-orbit jet-rank certificate
```

Do **not** start:

```text
GWSS-001M-C  general n-orbit Vandermonde theorem
GWSS-001M-D  finite nonzero τ evaluation-matrix separation
GWSS-002     off-critical witness construction
```

The purpose of this assignment is to decide whether the obstruction reported in 0008 is only a generic bare-kernel null coordinate or a genuine obstruction on the actual centered Xi zero carrier.

## 1. Mandatory orientation before editing

Before any edit, report:

```text
current branch
current HEAD
working-tree status
Lean toolchain
0007 and 0008 read
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
GWSS-001M-B
```

Load-bearing boundary:

```text
NO RH assumption
NO classical Weil positivity
NO Li criterion
NO fixed-Xi defect vanishing provider
NO T -> infinity horizontal decay provider
NO limit exchange
NO prime-side sign assumption
NO treating a carrier-dependent interpolation selector as an independent witness
```

## 2. Important correction to the 0008 stop condition

The following generic theorem from the new Mellin jet module is correct and must be preserved:

```text
complexExpSecondDifferenceKernel τ 0 = 0
pascalCenteredXiMellinSecondDifferenceWeight ε τ 0 = 0
```

Therefore the bare Mellin family has a genuine null coordinate at centered `z = 0`.

However, do **not** conclude from this alone that the actual Xi zero window has a rank obstruction.

The repository already contains an unconditional real-axis exclusion for nontrivial zeta zeros.

Inspect and reuse the checked-out source declarations rather than re-proving them from scratch:

```text
DkMath.RH.CFBRC.StandardZetaRealAxisClosure
DkMath.RH.Weave.Analytic.EtaRealAxisPositivity
DkMath.RH.CFBRC.PascalCenteredXiGlobalZeroDiskBridge
```

Expected relevant theorem names in the current tree include:

```text
nontrivialRiemannZetaZero_im_ne_zero
riemannZeta_ne_zero_of_real_mem_openCriticalInterval
mem_pascalCenteredXiZeros_iff_nontrivial_shift
mem_pascalCenteredXiZeroDiskFinset_iff
```

Verify exact names and types in the checkout before using them.

## 3. GWSS-001M-B0 — actual-window zero-coordinate discharge

### 3.1 Target fact

For every actual centered Xi zero in a finite disk, prove that the centered coordinate is nonzero and hence its squared coordinate is nonzero.

Preferred target shapes are:

```lean
theorem pascalCenteredXiZeroDiskFinset_ne_zero
    {R : ℝ} {z : ℂ}
    (hz : z ∈ pascalCenteredXiZeroDiskFinset R) :
    z ≠ 0 := by
  ...
```

and

```lean
theorem pascalCenteredXiZeroDiskFinset_sq_ne_zero
    {R : ℝ} {z : ℂ}
    (hz : z ∈ pascalCenteredXiZeroDiskFinset R) :
    z ^ 2 ≠ 0 := by
  ...
```

Names may be adjusted to local naming conventions.

### 3.2 Preferred proof route

Use the existing actual zero classification:

```text
z ∈ pascalCenteredXiZeroDiskFinset R
  -> z ∈ pascalCenteredXiZeros
  -> NontrivialRiemannZetaZero (criticalLineCenter + z)
  -> (criticalLineCenter + z).im ≠ 0
  -> z.im ≠ 0
  -> z ≠ 0
  -> z ^ 2 ≠ 0
```

The theorem `nontrivialRiemannZetaZero_im_ne_zero` is unconditional and is based on the existing eta real-axis positivity route. Reuse it. Do not introduce RH.

### 3.3 Required classification after B0

Choose exactly one:

```text
ACTUAL-WINDOW-QZERO-OBSTRUCTION-DISCHARGED
ACTUAL-WINDOW-QZERO-EXCLUSION-API-GAP
ACTUAL-WINDOW-QZERO-OBSTRUCTION-CONFIRMED
```

Proceed to B1 only if the first classification is obtained.

If B0 succeeds, the 0008 label `MELLIN-FAMILY-RANK-OBSTRUCTION` must be treated as a generic bare-kernel obstruction, not as the final actual-window classification.

Do not delete the generic zero-coordinate theorems from the jet module.

## 4. Squared-orbit coordinates

For the low-rank certificates, write

```text
q₁ = z₁ ^ 2
q₂ = z₂ ^ 2
q₃ = z₃ ^ 2
```

The orbit relation is the existing squared relation:

```text
zᵢ ^ 2 = zⱼ ^ 2
```

Do not assume or require a quotient carrier.

The low-rank theorem hypotheses should make the required distinctions explicit:

```text
zᵢ are actual Xi-window points
qᵢ ≠ 0 from B0
qᵢ ≠ qⱼ for distinct squared orbits
```

Do not strengthen this to `zᵢ ≠ zⱼ` when only squared-orbit distinction matters.

## 5. GWSS-001M-B1 — exact 2-orbit jet rank

The finite jets proved in `PascalCenteredXiMellinFiniteJetRankAudit.lean` are:

```text
quadratic coefficient      z ^ 2
quartic correction         z ^ 4 / 12
sextic correction          z ^ 6 / 360
```

For two distinct actual squared orbits, the first two jet coordinates give the matrix

```text
[ q₁        q₂      ]
[ q₁² / 12 q₂² / 12]
```

The determinant is schematically

```text
(q₁ * q₂ * (q₂ - q₁)) / 12
```

### 5.1 Required Lean certificate

Implement a small exact algebraic theorem proving nonvanishing of the 2-orbit determinant from:

```text
q₁ ≠ 0
q₂ ≠ 0
q₁ ≠ q₂
```

Prefer a direct scalar determinant formula over introducing a general matrix/determinant layer unless Mathlib already makes the direct matrix theorem trivial.

A valid theorem can be purely algebraic in `q₁ q₂ : ℂ`, followed by an actual-window corollary using B0.

Suggested structure:

```text
abstract scalar determinant theorem
  -> actual Xi-window two-orbit corollary
```

### 5.2 What B1 does and does not prove

B1 proves that the **jet coefficient vectors** distinguish two nonzero squared orbits.

It does **not** yet prove the existence of two finite nonzero dilation values `τ₁`, `τ₂` whose actual Mellin evaluation matrix is invertible.

Do not silently identify jet rank with finite evaluation rank.

## 6. GWSS-001M-B2 — exact 3-orbit jet rank

Proceed only if B1 succeeds cleanly.

For three distinct actual squared orbits, use the first three jet coordinates:

```text
[ q₁          q₂          q₃          ]
[ q₁² / 12   q₂² / 12   q₃² / 12   ]
[ q₁³ / 360  q₂³ / 360  q₃³ / 360  ]
```

Its determinant is a nonzero scalar multiple of

```text
q₁ * q₂ * q₃
  * (q₂ - q₁)
  * (q₃ - q₁)
  * (q₃ - q₂)
```

### 6.1 Preferred implementation discipline

First prove the algebraic factorization in a focused theorem.

Then derive nonvanishing under:

```text
q₁ ≠ 0
q₂ ≠ 0
q₃ ≠ 0
q₁ ≠ q₂
q₁ ≠ q₃
q₂ ≠ q₃
```

Then produce an actual Xi-window corollary using B0.

Do not generalize to arbitrary `n` in this assignment.

The purpose of the 3-orbit certificate is to verify that the expected Vandermonde pattern survives Lean formalization before a general theorem is authorized.

## 7. Spectral-factor firewall

The actual Mellin family contains the extra centered Mellin spectral factor

```text
centeredMellinSpectralWeight (centeredMellinBoxApprox ε) z
```

The earlier GWSS-001T theorem proves eventual simultaneous nonvanishing of this factor on every fixed finite actual Xi window.

Do not yet fold this factor into the low-rank jet determinant unless doing so is a trivial nonzero diagonal scaling corollary.

If such a corollary is added, label it exactly as rank preservation under nonzero pointwise scaling. Do not claim finite-`τ` Mellin evaluation separation.

## 8. Important distinction: source rank vs independent witness

The actual-window polynomial selector from GWSS-001T-A depends on

```text
pascalCenteredXiZeroDiskFinset R
```

itself. Therefore it proves evaluation-map rank but is not an independently prescribed off-critical witness.

The Mellin family is different: its parameters `ε` and `τ` are defined independently of the unknown zero configuration.

The purpose of GWSS-001M is to determine whether this pre-existing family has enough local parameter rank.

Preserve this distinction in docstrings and reports.

## 9. Stop conditions

Stop immediately and report if any of the following occurs:

```text
B0 requires RH or an RH-equivalent theorem
2-orbit determinant needs an unproved zero-coordinate assumption after B0
3-orbit factorization does not match the expected Vandermonde structure
the implementation starts proving arbitrary n-dimensional determinant theory
jet rank is being silently promoted to finite-τ evaluation rank
horizontal decay or prime-side sign enters the proof
```

A focused API mismatch is a valid result. Do not compensate by introducing a broad new analytic layer.

## 10. Required classification

At the end of this assignment classify the bounded stage with exactly one primary result:

```text
MELLIN-LOW-JET-ACTUAL-WINDOW-RANK-FOUND
MELLIN-LOW-JET-RANK-UNRESOLVED
MELLIN-LOW-JET-RANK-OBSTRUCTION
```

For `FOUND`, all of the following must hold:

```text
actual Xi q = 0 excluded unconditionally
2-orbit jet determinant nonzero theorem proved
3-orbit jet determinant nonzero theorem proved
no RH-equivalent provider introduced
```

Even if `FOUND`, do **not** classify the whole Mellin family as full actual-window rank yet.

The next unresolved Gap must then be named:

```text
FINITE-TAU-EVALUATION-SEPARATION-GAP
```

or, if the evidence warrants it,

```text
GENERAL-VANDERMONDE-RANK-GAP
```

## 11. GWSS-002 remains forbidden

Do not begin off-critical witness construction in this assignment.

Authorization for GWSS-002 requires a later theorem showing that the zero-independent Mellin family itself, at finite admissible parameter values or an equivalent exact source family, supplies the needed actual-window separation.

Local jet rank is strong evidence but is not yet that theorem.

## 12. Verification

For each modified or added Lean module run:

```text
lake build <focused module>
```

Run:

```text
git diff --check
```

Check for new:

```text
sorry
admit
axiom
```

Use `#print axioms` on the new load-bearing B0/B1/B2 theorems.

If the public `DkMath.RH` import surface is unchanged, a root build is not mandatory for this bounded task. If the public import surface changes, run the relevant root build.

## 13. Report

Create:

```text
0010-GWSS-001M-B-qzero-discharge-low-rank-report.md
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
B0 q=0 actual-window classification
B1 two-orbit jet-rank result
B2 three-orbit jet-rank result
primary bounded-stage classification
GWSS-002 authorization status
```

Also explicitly state that the generic bare-kernel `z = 0` nullspace theorem remains true even if the actual Xi carrier excludes that coordinate.
