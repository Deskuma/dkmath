# IPSM-030 — CS1–CS5 closeout and CS6/CS7 smoothing-envelope roadmap

Date: 2026-08-14

Repository: `Deskuma/dkmath`

Branch: `wip/RH-CFBRC-prime-side-sign-mechanism-260813-v0`

Status: CS1–CS5 Green / CS6–CS7 next checkpoint / no sign claim / no RH claim

## 0. Review result

The IPSM-029 common-source implementation is Green.

The current module now supplies:

```text
Mellin quadratic common-source weight                  GREEN
radial common-source weight                            GREEN
arithmetic defect endpoint as one finite source sum    GREEN
pointwise defect-weight limit                          GREEN
vanishing-envelope order adapter                       GREEN
critical-axis exact residual                           OPEN
quantitative O(ε²) smoothing remainder                 OPEN
independent arithmetic upper envelope                  OPEN
```

The current exact endpoint representation is especially important:

```text
ArithmeticDefectEndpoint(ε,W)
  = finite centered-Xi source moment of CommonSourceDefectWeight(ε,·).
```

For every fixed source point `z`, the weight converges to the zero-side defect density:

$$
\operatorname{CommonDefectWeight}_\varepsilon(z)\longrightarrow 2(\operatorname{Re}z)^2.
$$

This confirms that the common-source reduction is genuine rather than a renaming layer.

## 1. Critical firewall before CS6/CS7

Do not try to prove that the full fixed-`ε` endpoint defect is `O(ε²)`.

Only the smoothing remainder around the limiting density is automatically small.

Define conceptually:

$$
R_\varepsilon(z):=\operatorname{CommonDefectWeight}_\varepsilon(z)-2(\operatorname{Re}z)^2.
$$

Then the correct decomposition is:

$$
\operatorname{CommonDefectWeight}_\varepsilon(z)=2(\operatorname{Re}z)^2+R_\varepsilon(z).
$$

The first term is the genuine off-critical defect density. It does not vanish merely because the Mellin box shrinks.

Therefore an `O(ε²)` theorem for `R_ε` is an approximation theorem, not a sign theorem.

## 2. CS6-A — exact critical-axis Mellin multiplier

Add an explicit sinc import if needed:

```lean
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
```

For a critical-axis point

```lean
z = (y : ℂ) * Complex.I
```

and `0 < ε`, target:

```lean
theorem pascalCenteredXiPrimeSideQuadraticization_mellinMultiplier_I_mul
    {ε y : ℝ} (hε : 0 < ε) :
    centeredMellinSpectralWeight
        (centeredMellinBoxApprox ε)
        ((y : ℂ) * Complex.I) =
      (Real.sinc (ε * y) : ℂ) := by
  ...
```

Use the already proved logarithmic-average formula rather than unfolding the Mellin transform from scratch.

The mathematical identity is:

$$
\frac{1}{2\varepsilon}\int_{-\varepsilon}^{\varepsilon}e^{ity}\,dt=\operatorname{sinc}(\varepsilon y).
$$

The `Real.sinc` totalization handles `y = 0`; do not introduce a fake `y ≠ 0` hypothesis into the public theorem.

## 3. CS6-B — exact critical-axis defect residual

From CS6-A, prove:

```lean
theorem pascalCenteredXiPrimeSideQuadraticization_commonSourceDefectWeight_I_mul
    {ε y : ℝ} (hε : 0 < ε) :
    pascalCenteredXiPrimeSideQuadraticizationCommonSourceDefectWeight
        ε ((y : ℂ) * Complex.I) =
      y ^ 2 * (1 - Real.sinc (ε * y)) := by
  ...
```

This is the exact finite-`ε` critical-axis smoothing residual.

Since Mathlib has `Real.sinc_le_one`, derive the safe nonnegativity theorem:

```lean
theorem pascalCenteredXiPrimeSideQuadraticization_commonSourceDefectWeight_I_mul_nonneg
    {ε y : ℝ} (hε : 0 < ε) :
    0 ≤ pascalCenteredXiPrimeSideQuadraticizationCommonSourceDefectWeight
      ε ((y : ℂ) * Complex.I) := by
  ...
```

This theorem is not a radial-comparison provider. It only records that a finite Mellin box leaves a nonnegative residual even at a critical-axis source point.

Do not infer a whole-disk sign statement from this unless every source point has already been proved critical; that would reintroduce the RH frontier.

## 4. CS7-A — define the smoothing remainder weight

Define:

```lean
noncomputable def pascalCenteredXiPrimeSideQuadraticizationCommonSourceSmoothingRemainderWeight
    (ε : ℝ) (z : ℂ) : ℝ :=
  pascalCenteredXiPrimeSideQuadraticizationCommonSourceDefectWeight ε z -
    2 * z.re ^ 2
```

Then prove the exact algebraic decomposition:

```lean
theorem pascalCenteredXiPrimeSideQuadraticization_commonSourceDefectWeight_eq_limitDensity_add_remainder
    (ε : ℝ) (z : ℂ) :
    pascalCenteredXiPrimeSideQuadraticizationCommonSourceDefectWeight ε z =
      2 * z.re ^ 2 +
        pascalCenteredXiPrimeSideQuadraticizationCommonSourceSmoothingRemainderWeight ε z := by
  ...
```

This named remainder is the quantity that should receive the `O(ε²)` estimate.

## 5. CS7-B — pointwise quadratic smoothing bound

Use the symmetric logarithmic average and cancel the linear exponential term before estimating.

For `0 < ε` and

```text
ε * ‖z‖ ≤ 1
```

target a concrete bound of the form:

```lean
theorem pascalCenteredXiPrimeSideQuadraticization_commonSourceSmoothingRemainderWeight_abs_le
    {ε : ℝ} (hε : 0 < ε) (z : ℂ)
    (hsmall : ε * ‖z‖ ≤ 1) :
    |pascalCenteredXiPrimeSideQuadraticizationCommonSourceSmoothingRemainderWeight ε z| ≤
      (ε ^ 2 / 3) * ‖z‖ ^ 4 := by
  ...
```

The constant `1/3` is a convenient target, not a required sharp constant.

Recommended route:

```text
Hε(z) - 1
  = normalized integral of (exp(tz) - 1 - tz)
    because the symmetric average of tz is zero

‖exp(tz) - 1 - tz‖ ≤ ‖tz‖²
    when ‖tz‖ ≤ 1

average(t²) over [-ε,ε]
  = ε² / 3
```

Mathlib currently exposes the useful bound under the name:

```lean
Complex.norm_exp_sub_one_sub_id_le
```

Verify the exact pinned signature before committing the proof.

Do not use a first-order bound `‖exp(tz)-1‖ ≤ C‖tz‖`; that loses the symmetric cancellation and only gives `O(ε)`.

## 6. CS7-C — uniform bounded-disk envelope

For every source point in the finite zero disk, `‖z‖ ≤ R`.

Therefore, under a small-box hypothesis such as

```text
0 < ε
ε * R ≤ 1
```

target:

```lean
theorem pascalCenteredXiPrimeSideQuadraticization_commonSourceSmoothingRemainderWeight_abs_le_of_mem_disk
    {ε R : ℝ} (hε : 0 < ε) (hsmall : ε * R ≤ 1)
    {z : ℂ} (hz : z ∈ pascalCenteredXiZeroDiskFinset R) :
    |pascalCenteredXiPrimeSideQuadraticizationCommonSourceSmoothingRemainderWeight ε z| ≤
      (ε ^ 2 / 3) * R ^ 4 := by
  ...
```

Handle the sign/radius hypotheses using the existing zero-disk membership API rather than assuming `R ≥ 0` independently when it is already available from the transport window.

## 7. CS7-D — finite-radius total smoothing envelope

Define a source-count-based envelope, for example:

```lean
noncomputable def pascalCenteredXiPrimeSideQuadraticizationCommonSourceSmoothingEnvelope
    (ε R : ℝ) : ℝ :=
  (ε ^ 2 / 3) * R ^ 4 *
    (pascalCenteredXiZeroDiskMultiplicity R : ℝ)
```

Then prove an endpoint-vs-limit-defect estimate on a safe transport window:

```lean
theorem pascalCenteredXiMellinQuadraticArithmeticDefectEndpoint_sub_fixedDefect_abs_le_smoothingEnvelope
    {ε : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow)
    (hsmall : ε * W.R ≤ 1) :
    |pascalCenteredXiMellinQuadraticArithmeticDefectEndpoint ε W -
      pascalCenteredXiFixedSecondMomentDefectFunctional W.R| ≤
      pascalCenteredXiPrimeSideQuadraticizationCommonSourceSmoothingEnvelope ε W.R := by
  ...
```

The proof should be a finite `Finset` estimate over the common source.

This is the quantitative strengthening of the already Green qualitative endpoint limit.

## 8. CS7-E — envelope vanishes

For fixed `R`, prove:

```lean
theorem tendsto_pascalCenteredXiPrimeSideQuadraticizationCommonSourceSmoothingEnvelope_zero
    (R : ℝ) :
    Tendsto
      (fun ε : ℝ =>
        pascalCenteredXiPrimeSideQuadraticizationCommonSourceSmoothingEnvelope ε R)
      (𝓝[>] 0) (nhds 0) := by
  ...
```

This should be elementary because the source disk is finite and all `R`-dependent factors are constant.

## 9. What CS7 does and does not prove

A successful CS7 gives:

```text
ArithmeticDefectEndpoint(ε,W)
  = FixedXiDefect(W.R) + smoothing remainder

|smoothing remainder|
  ≤ O_W(ε²)
```

It does not give:

```text
ArithmeticDefectEndpoint(ε,W) ≤ O_W(ε²)
```

unless an additional independent theorem controls the fixed defect component.

That distinction is load-bearing.

If one silently replaces the first estimate by the second, the desired sign has simply been assumed through the missing fixed-defect term.

## 10. CS8 — independent arithmetic upper-envelope frontier

After CS6/CS7 are Green, resume the actual sign search.

The desired provider has the form:

```lean
structure PascalCenteredXiPrimeSideArithmeticVanishingUpperEnvelopeProvider
    (W : PascalCenteredXiResidueTransportWindow) where
  envelope : ℝ → ℝ
  envelope_tendsto_zero : Tendsto envelope (𝓝[>] 0) (nhds 0)
  endpoint_eventually_le :
    ∀ᶠ ε : ℝ in 𝓝[>] 0,
      pascalCenteredXiMellinQuadraticArithmeticDefectEndpoint ε W ≤ envelope ε
```

But do not instantiate this structure with the smoothing envelope from CS7 unless the missing fixed-defect term has independently been controlled.

The existing Green adapter then gives:

```text
FixedXiDefect(W.R) ≤ 0.
```

Together with the independently Green zero-side nonnegativity, that would force equality at the selected safe radius.

## 11. Independent-provider routes to re-audit after CS7

Only source-derived routes are acceptable:

```text
A. finite von Mangoldt cancellation / domination
B. prime-side completion square whose remainder is exactly controlled
C. CF2D same-source inequality with the common weighted moment
D. a direct arithmetic bound on ArithmeticDefectEndpoint
```

The following are forbidden as providers:

```text
- zero-side FixedXiDefect nonnegativity
- anti-mirror energy
- RH-equivalent defect vanishing
- ordered-limit conclusions used backwards
- the CS7 smoothing envelope by itself
- synthetic addition of the radial term into a shifted energy
```

## 12. Acceptance checklist

```text
[ ] CS1–CS5 remain unchanged and Green
[ ] critical-axis multiplier is exact sinc, totalized at y=0
[ ] critical-axis finite-ε residual is named explicitly
[ ] critical-axis residual nonnegativity is proved without RH
[ ] smoothing remainder is defined relative to 2*(Re z)^2
[ ] symmetric cancellation is used before the exponential estimate
[ ] pointwise remainder receives an O(ε²) bound
[ ] finite zero-disk receives a uniform O(ε²) bound
[ ] total smoothing envelope tends to zero
[ ] endpoint-minus-fixed-defect quantitative estimate is proved
[ ] smoothing estimate is not mislabeled as the arithmetic sign provider
[ ] independent arithmetic upper envelope remains a separate frontier
[ ] no fixed-positive-ε sign theorem is claimed
[ ] no limit exchange
[ ] no RH consequence
```

## 13. Expected closeout

If CS6/CS7 are Green but no independent arithmetic upper-envelope provider is found, close this phase as:

```text
common source                                GREEN
critical-axis sinc residual                  GREEN
finite-radius O(ε²) smoothing control        GREEN
endpoint = fixed defect + vanishing error    GREEN
independent arithmetic upper envelope        OPEN
```

That is a materially sharper frontier than the previous radial-comparison gap: it separates the harmless Mellin smoothing error from the true sign-carrying fixed defect component.
