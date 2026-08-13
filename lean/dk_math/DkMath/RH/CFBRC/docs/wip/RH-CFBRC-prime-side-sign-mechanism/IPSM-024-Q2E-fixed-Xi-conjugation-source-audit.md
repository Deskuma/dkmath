# IPSM-024 — Q2-E fixed-Xi conjugation source audit

Date: 2026-08-14

Repository: `Deskuma/dkmath`

Branch: `wip/RH-CFBRC-prime-side-sign-mechanism-260813-v0`

Status: Q2-A–D Green / Q2-E source-conjugation checkpoint / no sign claim / no RH claim

## 0. Review result

Q2-A–D are Green in `PascalCenteredXiPrimeSideQuadraticizationAudit.lean`.

The current implementation supplies:

```text
top fixed-Xi amplitude interval integrability          GREEN
top box kernel / feature                               GREEN
finite horizontal×box rectangle IntegrableOn           GREEN
Fubini swap                                             GREEN
HorizontalBase = normalized top aggregate              GREEN
TopNode(1-x) = -conj(TopNode(x))                        GREEN
fixed-Xi kernel/logDeriv conjugation                    OPEN
```

The `HorizontalConjugationGap` marker is currently correct: the preceding finite-source and Fubini results do not by themselves provide conjugation.

## 1. Exact pinned Mathlib fact

The active `lake-manifest.json` pins Mathlib to `v4.32.2`, rev:

```text
905b95818eb32af7874a58b427f50c1711a5e96c
```

At this exact revision, `Mathlib.NumberTheory.Harmonic.ZetaAsymp` contains:

```lean
@[simp]
theorem riemannZeta_conj (s : ℂ) :
    riemannZeta (conj s) = conj (riemannZeta s)
```

Therefore add the explicit import required to expose this theorem:

```lean
import Mathlib.NumberTheory.Harmonic.ZetaAsymp
```

Do not rely on upstream `main` APIs beyond the pinned revision.

## 2. Do not start by proving `completedRiemannZeta₀_conj`

A direct global conjugation theorem for `completedRiemannZeta₀` is not required for Q2-E.

The safer route is:

```text
riemannZeta_conj                         [Mathlib, global]
Gammaℝ conjugation                       [already proved locally]
        ↓
completedRiemannZeta conjugation on Re(s) > 1
        ↓
pascalRiemannXiKernel conjugation on Re(s) > 1
        ↓
identity principle for the entire fixed kernel
        ↓
pascalRiemannXiKernel conjugation globally
        ↓
centered kernel conjugation
        ↓
derivative conjugation
        ↓
totalized logDeriv conjugation
```

This avoids special-value algebra at `s = 0, 1` and avoids any RH input.

## 3. Q2-E1 — completed-zeta conjugation on the safe right half-plane

Use the already available project theorem

```lean
gammaR_ne_zero_of_pos_re
```

and the already Green theorem

```lean
pascalXiArchimedeanGammaR_conj
```

together with Mathlib:

```lean
riemannZeta_def_of_ne_zero
riemannZeta_conj
```

Target a local/helper theorem of the shape:

```lean
theorem completedRiemannZeta_conj_of_one_lt_re
    {s : ℂ} (hs : 1 < s.re) :
    completedRiemannZeta (starRingEnd ℂ s) =
      starRingEnd ℂ (completedRiemannZeta s) := by
  ...
```

For `1 < s.re`, both `s` and `conj s` are nonzero and `Gammaℝ` is nonzero, so `riemannZeta_def_of_ne_zero` may be algebraically rearranged to

```text
completedRiemannZeta s = Gammaℝ s * riemannZeta s
```

and similarly at `conj s`.

Then conjugation follows from `riemannZeta_conj`, `pascalXiArchimedeanGammaR_conj`, and `map_mul`.

Keep this theorem restricted to the safe half-plane. There is no need to solve Mathlib's totalized completed-zeta values globally.

## 4. Q2-E2 — fixed Xi kernel conjugation on the safe half-plane

Use the existing source identity:

```lean
pascalRiemannXiKernel_eq_mul_completedRiemannZeta
```

For `1 < s.re`, prove:

```lean
theorem pascalRiemannXiKernel_conj_of_one_lt_re
    {s : ℂ} (hs : 1 < s.re) :
    pascalRiemannXiKernel (starRingEnd ℂ s) =
      starRingEnd ℂ (pascalRiemannXiKernel s) := by
  ...
```

All required nonzero hypotheses follow from the real-part bound.

This is still only a local right-half-plane theorem.

## 5. Q2-E3 — analytic continuation to the entire fixed kernel

The project already has:

```lean
differentiable_pascalRiemannXiKernel :
  Differentiable ℂ pascalRiemannXiKernel
```

Define conceptually:

```text
g(s) = conj(pascalRiemannXiKernel(conj s)).
```

Use the same mechanism already used by Mathlib's own `riemannZeta_conj` proof:

```lean
differentiableAt_conj_conj_iff
DifferentiableOn.analyticOnNhd
AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq
```

Both `g` and `pascalRiemannXiKernel` are analytic on `Set.univ`, and Q2-E2 gives equality on the open set `1 < Re(s)` containing `s = 2`.

Target the global theorem:

```lean
theorem pascalRiemannXiKernel_conj (s : ℂ) :
    pascalRiemannXiKernel (starRingEnd ℂ s) =
      starRingEnd ℂ (pascalRiemannXiKernel s) := by
  ...
```

This step is analytic continuation of an independently proved right-half-plane identity. It is not a zero-symmetry or RH argument.

## 6. Q2-E4 — centered kernel conjugation

Use that `criticalLineCenter = 1/2` is real.

Target:

```lean
theorem pascalCenteredRiemannXiKernel_conj (z : ℂ) :
    pascalCenteredRiemannXiKernel (starRingEnd ℂ z) =
      starRingEnd ℂ (pascalCenteredRiemannXiKernel z) := by
  ...
```

This should be an algebraic wrapper around `pascalRiemannXiKernel_conj`.

## 7. Q2-E5 — derivative and totalized logDeriv conjugation

Do not add nonvanishing assumptions.

The existing D4 proof already demonstrates the pinned API pattern with:

```lean
deriv_conj_conj
logDeriv_apply
```

Repeat that pattern for `pascalCenteredRiemannXiKernel`.

First derive:

```text
deriv pascalCenteredRiemannXiKernel (conj z)
= conj (deriv pascalCenteredRiemannXiKernel z).
```

Then target:

```lean
theorem pascalCenteredXiNegLogDeriv_conj (z : ℂ) :
    pascalCenteredXiNegLogDeriv (starRingEnd ℂ z) =
      starRingEnd ℂ (pascalCenteredXiNegLogDeriv z) := by
  ...
```

Because Mathlib's `logDeriv` is totalized, no kernel-nonzero hypothesis is needed for this algebraic conjugation identity.

## 8. Q2-E6 — validate on the actual top amplitude

After Q2-E5 is Green, immediately prove the source theorem needed by Q2-F:

```lean
theorem pascalCenteredXiPrimeSideQuadraticizationTopAmplitude_one_sub_eq_neg_conj
    (W : PascalCenteredXiResidueTransportWindow) (x : ℝ) :
    pascalCenteredXiPrimeSideQuadraticizationTopAmplitude W (1 - x) =
      -starRingEnd ℂ
        (pascalCenteredXiPrimeSideQuadraticizationTopAmplitude W x) := by
  ...
```

Use exactly:

```text
TopNode(1-x) = -conj(TopNode(x))
fixed-Xi negLogDeriv oddness
fixed-Xi negLogDeriv conjugation
```

Do not use the completed functional-equation reflection again here; the centered oddness theorem is already the correct source law.

## 9. Placement recommendation

Two acceptable implementations exist.

Preferred reusable placement:

```text
PascalCanonicalXiFixedObservableBridge.lean
  - import ZetaAsymp
  - pascalRiemannXiKernel_conj
  - pascalCenteredRiemannXiKernel_conj
  - pascalCenteredXiNegLogDeriv_conj
```

If moving the already-local `Gammaℝ` conjugation theorem would create unnecessary churn, a first implementation may keep the new conjugation chain in `PascalCenteredXiPrimeSideQuadraticizationAudit.lean` and refactor it later.

Do not create an import cycle merely to improve theorem placement.

## 10. Acceptance checklist

```text
[ ] uses Mathlib v4.32.2 pinned API
[ ] imports ZetaAsymp explicitly
[ ] riemannZeta_conj is used as an existing theorem, not reproved
[ ] completed-zeta conjugation is required only on Re(s) > 1
[ ] fixed-kernel right-half-plane conjugation is source-derived
[ ] global fixed-kernel conjugation uses identity principle
[ ] centered kernel conjugation is exact
[ ] derivative conjugation uses deriv_conj_conj
[ ] logDeriv conjugation has no fake nonzero hypothesis/provider
[ ] TopAmplitude(1-x) = -conj(TopAmplitude(x)) closes from actual source
[ ] HorizontalConjugationGap is removed or superseded only after these theorems compile
[ ] no horizontal sign claim
[ ] no whole ordering claim
[ ] radial comparison remains separate
[ ] no limit exchange
[ ] no RH consequence
```

## 11. Next checkpoint after Q2-E

If Q2-E is Green, proceed to Q2-G with the exact expected reflection:

```text
TopBoxFeature(1-x, v)
= -conj(TopBoxFeature(x, -v)).
```

The `v -> -v` reflection is mandatory.

Only after this theorem is compiled should the aggregate/deorientation/symmetrization layer be attempted.
