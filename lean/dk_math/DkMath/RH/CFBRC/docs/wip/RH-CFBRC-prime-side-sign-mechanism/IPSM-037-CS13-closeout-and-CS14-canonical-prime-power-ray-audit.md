# IPSM-037 — CS13 closeout and CS14 canonical prime-power ray audit

## 0. Status

CS13 is Green-B.

The new module `PascalCenteredXiPrimeSideModeKernelPhaseAudit.lean` has exposed the source-derived one-mode phase without introducing a sign theorem, an infinite tail/integral exchange, or an RH consequence.

The next phase is not to force the pending nonzero-frequency primitive. The next phase is to canonicalize the already finite von-Mangoldt mode ledger by prime-power rays.

## 1. CS13 closeout

The following surfaces are now available.

1. The centered right-edge node is affine:

$$z_W(t)=(\sigma_W-1/2)+it.$$

2. The quadratic Mellin box weight has the exact boundary-difference form:

$$q_\varepsilon(z)=\frac{z}{2\varepsilon}\left(e^{\varepsilon z}-e^{-\varepsilon z}\right).$$

3. For every positive natural mode `n`, the source mode admits the exact phase transport

$$q_\varepsilon(z)n^{-(1/2+z)}=n^{-1/2}\frac{z}{2\varepsilon}\left(e^{(\varepsilon-\log n)z}-e^{(-\varepsilon-\log n)z}\right).$$

4. The real affine exponential coordinate is exact:

$$\Re\left((a+it)e^{r(a+it)}\right)=e^{ar}\left(a\cos(rt)-t\sin(rt)\right).$$

5. The CS12 mode kernel is exactly the CS13 boundary phase kernel.

6. The zero-frequency primitive is safe and exact:

$$J(a,0,T)=aT.$$

The nonzero-frequency closed form remains a named gap. This is acceptable: CS14 does not require it.

## 2. Why CS14 should reindex before finishing the trigonometric primitive

CS12 currently exposes the finite weighted mode ledger in the form

$$\sum_{n\le X}\Lambda(n)K_{\varepsilon,W}(n).$$

The repository already proves that the canonical DkMath prime-power shadow coefficient is exactly the classical von Mangoldt coefficient, and that the finite PHZ support can be transported bijectively between natural prime-power labels and unique `(prime, exponent)` labels.

Therefore the next structural reduction is finite and algebraic. It does not require an infinite Dirichlet-series rearrangement and it does not require evaluation of the CS13 nonzero-frequency primitive.

## 3. Existing Core to reuse

Reuse the existing theorems and definitions from `PascalPrimePowerCanonicalFold` and `PascalVonMangoldtLSeriesBridge`.

Important existing surfaces include:

* `canonicalPrimePowerSupportUpTo`
* `pascalPrimePowerPairSupportUpTo`
* `primePowerPairLabel`
* `primePowerShadow_spec`
* `canonicalPrimePowerShadowCost_eq_log_of_witness`
* `primePowerPairLabel_injOn`
* `image_primePowerPairLabel_support_eq_canonicalSupport`
* `pascalPrimePowerPHZFiniteUpTo_eq_pairSupport_sum`
* `pascalPrimePowerPHZFiniteUpTo_eq_canonical`
* `canonicalPrimePowerShadowCost_eq_vonMangoldt`

Do not create a second prime-power uniqueness layer.

## 4. New module

Create a chained module

`DkMath.RH.CFBRC.PascalCenteredXiPrimeSidePrimePowerRayAudit`

with

```lean
import DkMath.RH.CFBRC.PascalCenteredXiPrimeSideModeKernelPhaseAudit
```

and add it to the public `DkMath.RH` import list after the CS13 module.

## 5. CS14-A — restrict the finite mode ledger to canonical prime powers

First prove a kernel-valued analogue of the existing PHZ canonical fold.

Desired theorem shape:

```lean
theorem pascalCenteredXiPrimeSideFiniteModeSum_eq_canonicalPrimePowerSupport
    {ε : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) :
    (∑ n ∈ Finset.range (X + 1),
      (ArithmeticFunction.vonMangoldt n : ℝ) *
        pascalCenteredXiPrimeSideFiniteModeKernel ε W n) =
    ∑ q ∈ canonicalPrimePowerSupportUpTo X,
      canonicalPrimePowerShadowCost q *
        pascalCenteredXiPrimeSideFiniteModeKernel ε W q := by
  ...
```

The exact theorem name may be adjusted, but the content should be this finite support restriction.

This theorem is not a sign theorem. It only removes modes whose von-Mangoldt coefficient is zero.

## 6. CS14-B — reindex canonical labels by unique `(p,k)` support

Use the existing image and injectivity theorems to obtain an exact pair-support expression.

Desired mathematical surface:

$$\sum_{q\le X}\Lambda(q)K(q)=\sum_{(p,j)\in\mathcal P_X}(\log p)K(p^{j+1}).$$

A possible Lean theorem shape is:

```lean
theorem pascalCenteredXiPrimeSideCanonicalModeSum_eq_pairSupport
    {ε : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) :
    (∑ q ∈ canonicalPrimePowerSupportUpTo X,
      canonicalPrimePowerShadowCost q *
        pascalCenteredXiPrimeSideFiniteModeKernel ε W q) =
    ∑ pk ∈ pascalPrimePowerPairSupportUpTo X,
      Real.log (pk.1 : ℝ) *
        pascalCenteredXiPrimeSideFiniteModeKernel ε W
          (pk.1 ^ (pk.2 + 1)) := by
  ...
```

This should be proved by the existing canonical support bijection rather than by fresh factorization arguments.

## 7. CS14-C — group the pair support by base prime

Define the finite ray kernel for one base prime.

A robust definition that avoids introducing a maximum-exponent API is:

```lean
noncomputable def pascalCenteredXiPrimeSideFinitePrimePowerRayKernel
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow)
    (X p : ℕ) : ℝ :=
  ∑ k ∈ Finset.range X,
    if p ^ (k + 1) ≤ X then
      pascalCenteredXiPrimeSideFiniteModeKernel ε W (p ^ (k + 1))
    else 0
```

Then target an exact finite grouping theorem of the form

$$\sum_{n\le X}\Lambda(n)K(n)=\sum_{p\le X\atop p\ \mathrm{prime}}(\log p)\,\mathcal R_{\varepsilon,W,X}(p).$$

Prefer reusing `pascalPrimeCoordinateSupportUpTo X` rather than defining another finite prime set.

A theorem shape may be:

```lean
theorem pascalCenteredXiPrimeSideFiniteModeSum_eq_primePowerRays
    {ε : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) :
    (∑ n ∈ Finset.range (X + 1),
      (ArithmeticFunction.vonMangoldt n : ℝ) *
        pascalCenteredXiPrimeSideFiniteModeKernel ε W n) =
    ∑ p ∈ pascalPrimeCoordinateSupportUpTo X,
      Real.log (p : ℝ) *
        pascalCenteredXiPrimeSideFinitePrimePowerRayKernel ε W X p := by
  ...
```

The exact finite-index convention may differ by an innocuous `k`/`k+1` choice. Keep positive exponents only.

## 8. CS14-D — expose the phase lattice on one prime ray

For a prime `p` and positive exponent `j`, prove the elementary phase identity

$$\log(p^j)=j\log p.$$

Use the pinned Mathlib API if available; otherwise prove it from positivity of a prime and the real logarithm power law. Do not create a custom logarithm theory.

With

$$a=\sigma_W-1/2,\qquad \ell_p=\log p,$$

the CS13 two boundary frequencies become

$$r_+(j)=\varepsilon-j\ell_p,$$

and

$$r_-(j)=-\varepsilon-j\ell_p.$$

Hence increasing the exponent by one translates both phase frequencies by exactly `-log p`.

Target a named theorem recording this equal-spacing property, even if no sign theorem follows.

## 9. CS14-E — expose geometric damping, but do not overcommit

The same substitution gives a second structural fact. In the CS13 transported mode, the factor

$$p^{-j/2}e^{-aj\log p}$$

collapses mathematically to

$$p^{-j\sigma_W}.$$

This means a fixed-base prime-power ray is not merely an equally spaced phase lattice. It is an equally spaced phase lattice with geometric damping.

There are two acceptable implementation levels.

Level 1: prove only the exact complex-power identity needed to show that the `p^j` mode is the `j`-th power of the base `p` mode. Existing `eulerPrimePowerMode_eq_primePower_cpow_neg` may already provide the cleanest route.

Level 2: if the pinned APIs make it clean, expose the real damping factor explicitly as `p^{-j σ}`.

Do not spend a large amount of proof engineering merely to obtain the cosmetic real-power form. The structural ray grouping is more important.

## 10. CS14-F — finite geometric compression is optional but high-value

After CS14-C/D, inspect whether one fixed prime ray can be compressed before integration.

At a fixed right-edge point `s`, write

$$q_p(s)=p^{-s}.$$

Then the positive-exponent ray has the finite geometric form

$$\sum_{j=1}^{m}q_p(s)^j.$$

Because the Mellin weight is common to all exponents on that same right-edge point, a finite prime ray can potentially be compressed to a finite geometric quotient before taking the half-window real projection.

This would expose the local Euler-factor structure directly:

$$\sum_{j=1}^{m}q^j=q\frac{1-q^m}{1-q}.$$

Treat this as an optional CS14-F theorem only if it is genuinely finite and source-derived. Do not introduce an infinite geometric sum or exchange an infinite ray with the interval integral in this phase.

## 11. Why this route is promising

For one fixed prime `p`, the ray now has three aligned properties:

1. The coefficient is constant across powers:

$$\Lambda(p^j)=\log p.$$

2. The phase frequencies form an arithmetic lattice with spacing `log p`.

3. The analytic amplitude is geometrically damped along the exponent direction.

This is a much more structured object than unrelated natural modes. If a cancellation mechanism exists, the prime-power ray is a natural place to search for it.

## 12. Sign firewall

Do not infer any of the following merely from the ray rewrite:

* `FiniteModeKernel ε W (p^j) ≥ 0`
* `FinitePrimePowerRayKernel ε W X p ≥ 0`
* `FiniteTailProjection ε W X ≥ 0`
* finite defect nonpositivity
* an independent vanishing upper envelope
* RH

The coefficient `log p > 0` only transfers a ray sign if a ray sign has independently been proved.

## 13. Infinite-series firewall

This phase remains finite.

Do not use or assert:

* interchange of an infinite prime-power ray with the half-window integral;
* rearrangement of the full infinite von-Mangoldt series into prime rays;
* an infinite Euler-product logarithmic derivative inside the CS12/CS13 integral;
* a joint `X, ε` limit;
* reversal of the existing ordered limits.

Absolute convergence in `σ > 1` may make a later infinite-ray theorem possible, but it is not part of CS14 unless separately audited.

## 14. CS13 nonzero-frequency gap

Do not make the CS13 nonzero-frequency primitive a prerequisite for CS14.

The ray structure is already visible at the source level through `p^j`, `log(p^j)`, and the complex exponential phase. A closed `sin/cos` primitive may be useful later for quantitative bounds, but forcing it now risks spending effort on a representation that ray compression may supersede.

## 15. CF2D trigonometric corollary remains deferred

The optional rewrite of `Real.cos`/`Real.sin` through `realTrigKernelFamily.cfcos`/`cfsin` remains deferred until the prime-side sign mechanism is closed or a concrete q2 shortcut becomes visible.

Do not import CF2D real trigonometry into the CS14 arithmetic proof merely for notation.

## 16. Green criteria for CS14

CS14 may be called Green-B if all of the following hold:

1. The CS12 finite mode ledger is restricted exactly to canonical prime-power support.
2. The canonical support is reindexed exactly by the existing unique `(p,k)` pair support.
3. The finite ledger is grouped exactly into base-prime rays with common `log p` coefficient.
4. The phase lattice `log(p^j)=j log p` is exposed source-derived.
5. No sign theorem is manufactured from coefficient positivity.
6. No infinite ray/integral exchange is introduced.
7. Any missing ray sign or cancellation provider is recorded as a named gap.

If finite geometric compression also closes cleanly, record it as an additional Green result, not as a sign theorem.

## 17. Expected next frontier

After CS14, inspect the fixed-base ray itself.

The strongest next question is not whether every mode kernel has one sign. It is whether the damped phase lattice on one primitive base `p` admits an exact local cancellation, geometric compression, monotone remainder, or q2/rotation interpretation that controls the signed ray projection.

Only after that local mechanism is understood should the argument return to summing over different primes and to the independent finite-cutoff anchor required by CS8/CS9.
