# IPSM-029 — Common source-variable bridge audit

Date: 2026-08-14

Repository: `Deskuma/dkmath`

Branch: `wip/RH-CFBRC-prime-side-sign-mechanism-260813-v0`

Status: Q3-F obstruction closeout / common-source audit / no sign claim / no RH claim

## 0. Current checkpoint

The Q3 finite radial layer is Green.

Current exact surface:

```text
ScalarSurface = π * normalizedArithmetic.re            GREEN
π * Radial <= ScalarSurface iff ArithmeticDefect <= 0 GREEN
safe-radius Radial >= 0                                GREEN
independent arithmetic-to-radial provider              OPEN
```

The four Q3-F routes currently have no independent provider:

```text
CF2D / whole-feature common projection                 NOT FOUND
outer-count / finite arithmetic domination             NOT FOUND
source-derived completion square                       NOT FOUND
finite/eventual arithmetic defect nonpositivity        NOT FOUND
```

This is an obstruction closeout, not an impossibility theorem.

Keep `PascalCenteredXiPrimeSideQuadraticizationRadialComparisonGap`.

## 1. Main audit correction: the common source already exists at moment level

Do not begin by forcing the following three objects to be pointwise identical:

```text
CF2D centered-zero state
WholeBoxFeature(v)
fixed-Xi OuterCount(r)
```

They use different parameter spaces and represent different stages of the construction.

The existing canonical common source is instead:

```lean
pascalCenteredXiZeroDiskWeightedMoment
    (h : ℂ → ℂ) (R : ℝ)
```

Conceptually, at a safe finite radius this is the atomic centered-Xi source

$$
\mu_R=\sum_{a\in Z_R}m_a\,\delta_a.
$$

and the weighted moment is

$$
M_R(h)=\sum_{a\in Z_R}m_a h(a).
$$

This source already underlies both the holomorphic Mellin endpoint and the radial second moment.

The right abstraction level for IPSM-029 is therefore **common source functional**, not necessarily common pointwise carrier.

## 2. Existing Mellin endpoint is already a common-source weighted moment

The existing theorem

```lean
pascalCenteredXiMellinSecondDifferenceZeroMoment_tau_zero_eq
```

identifies the quadratic Mellin zero moment with

```lean
pascalCenteredXiZeroDiskWeightedMoment
  (fun z =>
    z ^ 2 * centeredMellinSpectralWeight
      (centeredMellinBoxApprox ε) z)
  W.R
```

Define a named weight only if it improves theorem readability:

```lean
noncomputable def pascalCenteredXiPrimeSideQuadraticizationMellinZeroWeight
    (ε : ℝ) (z : ℂ) : ℂ :=
  z ^ 2 * centeredMellinSpectralWeight
    (centeredMellinBoxApprox ε) z
```

Then expose a lightweight adapter:

```lean
pascalCenteredXiMellinQuadraticZeroMoment ε W =
  pascalCenteredXiZeroDiskWeightedMoment
    (pascalCenteredXiPrimeSideQuadraticizationMellinZeroWeight ε)
    W.R
```

Do not duplicate the existing XDP-020 proof.

## 3. Put the radial observable on the same atomic source

Define the complex-valued radial weight:

```lean
noncomputable def pascalCenteredXiPrimeSideQuadraticizationRadialWeight
    (z : ℂ) : ℂ :=
  (Complex.normSq z : ℂ)
```

Target:

```lean
theorem pascalCenteredXiZeroDiskWeightedMoment_radialWeight_eq
    (R : ℝ) :
    pascalCenteredXiZeroDiskWeightedMoment
      pascalCenteredXiPrimeSideQuadraticizationRadialWeight R =
      (pascalCenteredXiZeroDiskRadialSecondMoment R : ℂ) := by
  ...
```

This should be finite-sum algebra only.

Then, at a safe radius, transport through existing bridges:

```text
zero-disk radial moment
= window radial second moment
= CF2D q2 radial mass
= fixed radial second-moment functional.
```

The CF2D component is therefore not a new source. It is a coordinate realization of the same radial weight.

## 4. Expose the common-source endpoint defect

Let

```text
Q_R   := radial weighted moment
Mε,R  := Mellin quadratic weighted moment
```

The normalized arithmetic endpoint satisfies

```text
NormalizedArithmeticEndpoint ε W = -Mε,R.
```

Hence the arithmetic defect endpoint is exactly

$$
D_\varepsilon(W)=Q_R+\operatorname{Re}M_{\varepsilon,R}.
$$

Define the pointwise real defect weight:

```lean
noncomputable def pascalCenteredXiPrimeSideQuadraticizationCommonSourceDefectWeight
    (ε : ℝ) (z : ℂ) : ℝ :=
  Complex.normSq z +
    (pascalCenteredXiPrimeSideQuadraticizationMellinZeroWeight ε z).re
```

Target the finite-source theorem:

```lean
theorem pascalCenteredXiMellinQuadraticArithmeticDefectEndpoint_eq_commonSourceMoment
    {ε : ℝ}
    (W : PascalCenteredXiResidueTransportWindow) :
    pascalCenteredXiMellinQuadraticArithmeticDefectEndpoint ε W =
      ∑ a ∈ pascalCenteredXiZeroDiskFinset W.R,
        (pascalCenteredXiZeroMultiplicity a : ℝ) *
          pascalCenteredXiPrimeSideQuadraticizationCommonSourceDefectWeight ε a := by
  ...
```

Use the existing safe-radius radial bridge and the existing Mellin zero-moment identity.

This theorem is an audit identity only. It is not a sign theorem.

## 5. The epsilon-zero limit of the pointwise defect weight

The approximate identity already proves

```lean
tendsto_centeredMellinSpectralWeight_centeredMellinBoxApprox_one
```

and therefore

```lean
tendsto_centeredMellinBoxApprox_quadraticWeight
```

for every fixed `z`.

Hence the common-source defect weight should satisfy

$$
\operatorname{DefectWeight}_\varepsilon(z)\longrightarrow |z|^2+\operatorname{Re}(z^2)=2(\operatorname{Re}z)^2.
$$

Target:

```lean
theorem tendsto_pascalCenteredXiPrimeSideQuadraticizationCommonSourceDefectWeight
    (z : ℂ) :
    Tendsto
      (fun ε : ℝ =>
        pascalCenteredXiPrimeSideQuadraticizationCommonSourceDefectWeight ε z)
      (𝓝[>] 0)
      (nhds (2 * z.re ^ 2)) := by
  ...
```

The last algebra step is pure complex-coordinate algebra.

Summing this finite source recovers the existing fixed-defect limit and the `2 * horizontalEnergy` theorem.

## 6. Important audit: exact finite-epsilon nonpositivity may be too strong

The centered Mellin box is an approximate identity, not the exact constant weight `1` at positive `ε`.

For a pure critical-axis point `z = I * y`, the spectral weight is the symmetric exponential average

$$
H_\varepsilon(iy)=\frac{1}{2\varepsilon}\int_{-\varepsilon}^{\varepsilon}e^{ity}\,dt.
$$

For `y ≠ 0`, this is the usual sinc factor.

Consequently the common-source point defect becomes

$$
\operatorname{DefectWeight}_\varepsilon(iy)=y^2\left(1-\frac{\sin(\varepsilon y)}{\varepsilon y}\right).
$$

This is nonnegative, and is strictly positive whenever `ε y ≠ 0`.

Therefore a universal pointwise theorem

```text
DefectWeight ε z <= 0
```

cannot be the correct source inequality at fixed positive `ε`.

This does not by itself disprove every possible finite arithmetic inequality, because the finite-X arithmetic approximant is not yet the endpoint. It does show that the endpoint contract `ArithmeticDefectEndpoint ε W <= 0` is stronger than the natural smoothing geometry and should not be treated as the only admissible sign mechanism.

If the sinc theorem is cheap in the pinned Mathlib API, formalize it as an audit theorem. Otherwise keep it as a documented analytic warning and proceed with the weaker contract below.

## 7. Replace exact finite sign by a vanishing-slack comparison contract

The correct order-theoretic target may be

$$
D_\varepsilon(W)\le r_\varepsilon(W),\qquad r_\varepsilon(W)\longrightarrow0,
$$

rather than `Dε <= 0` for every sufficiently small positive `ε`.

This contract is compatible with a positive Mellin smoothing residual on the critical axis while still forcing the fixed defect to be nonpositive in the limit.

Add a generic adapter:

```lean
theorem pascalCenteredXiFixedDefect_nonpos_of_endpoint_le_vanishingEnvelope
    (W : PascalCenteredXiResidueTransportWindow)
    (r : ℝ → ℝ)
    (hr : Tendsto r (𝓝[>] 0) (nhds 0))
    (hupper : ∀ᶠ ε : ℝ in 𝓝[>] 0,
      pascalCenteredXiMellinQuadraticArithmeticDefectEndpoint ε W ≤ r ε) :
    pascalCenteredXiFixedSecondMomentDefectFunctional W.R ≤ 0 := by
  ...
```

This is only an order-limit adapter. It does not provide `r`.

Optionally add the finite-X version only if it is genuinely useful:

```text
finite approximant <= envelope_X,ε
X -> infinity
endpoint <= envelope_ε
epsilon -> 0
fixed defect <= 0
```

Preserve the established order `X -> infinity` first, then `ε -> 0+`.

## 8. Second-order smoothing error is the natural next analytic quantity

The symmetric log-average cancels the first-order term in `ε`.

Therefore the natural source estimate to investigate is quadratic slack:

$$
\left|H_\varepsilon(z)-1\right|\le C(R)\varepsilon^2
$$

for `|z| <= R`, with an explicit finite-radius constant.

A robust proof route uses the rescaled representation

$$
H_\varepsilon(z)=\frac12\int_{-1}^{1}e^{\varepsilon u z}\,du
$$

and the cancellation of the odd linear term.

This should yield a bound of the shape

$$
\left|z^2(H_\varepsilon(z)-1)\right|\le C_R\varepsilon^2
$$

on the fixed zero disk.

Do not claim that this bound alone proves RH. Its role is to identify the unavoidable Mellin smoothing slack and to formulate the arithmetic-to-radial comparison at the correct scale.

## 9. Functional-level common source via fixed Xi log derivative

There is also a second common-source layer:

```lean
pascalCenteredXiNegLogDeriv : ℂ → ℂ
```

The radial observable uses its unweighted circle integrals through

```text
OuterCount(r)
-> layer cake in r
-> radial q2 mass.
```

The holomorphic/Mellin endpoint uses its weighted outer contour through

```text
h(z) * pascalCenteredXiNegLogDeriv(z)
-> weighted zero-disk moment.
```

Thus both are already functionals of the same fixed Xi log-derivative source, but with different geometries:

```text
radial: family of nested unweighted circles + layer cake
Mellin: one weighted outer contour
```

A direct theorem converting the radial layer cake into the Mellin whole feature would be genuinely new. Do not hide this by a structure field.

If attempted later, use a separate named bridge/gap.

## 10. What IPSM-029 should establish before further provider search

Preferred implementation order:

```text
CS1  name the Mellin zero weight
CS2  express radial as the same ZeroDiskWeightedMoment source
CS3  express endpoint defect as one finite common-source weighted sum
CS4  prove pointwise epsilon -> 0 defect-weight limit = 2 * re^2
CS5  add vanishing-envelope order adapter
CS6  audit/optionally prove critical-axis sinc residual
CS7  audit an O(epsilon^2) smoothing envelope
```

Only after CS1-CS5 should Q3 provider search resume.

## 11. Classification after common-source closeout

If CS1-CS5 are Green, the frontier becomes more precise:

```text
common centered-Xi atomic source                     GREEN
radial weight on that source                         GREEN
Mellin quadratic weight on that source               GREEN
endpoint defect as one weighted source moment         GREEN
fixed-defect limit of that moment                     GREEN
vanishing-slack transport adapter                     GREEN
independent arithmetic upper envelope                 OPEN
```

The new main question is not merely

```text
Can Radial be compared to ScalarSurface?
```

but rather

```text
Can the prime-side finite arithmetic source produce an upper envelope
for the common-source defect whose ordered limit is zero?
```

That formulation allows the Mellin regularization bias instead of demanding an unnaturally exact finite sign.

## 12. Firewall

Do not use the zero-side theorem

```text
fixed defect >= 0
```

as a provider for the prime-side upper envelope.

Do not use

```text
fixed defect = 2 * horizontalEnergy
```

or the all-safe-radius RH equivalence to derive the finite arithmetic estimate.

Do not replace `X -> infinity` then `ε -> 0+` by a joint or reversed limit.

Do not define a synthetic completion square whose positivity already contains the radial comparison.

Do not claim that common-source representation proves the comparison.

Do not claim RH.

A Green IPSM-029 should expose the exact common source and the correct asymptotic comparison contract; the independent prime-side upper envelope remains the load-bearing mathematical gap.