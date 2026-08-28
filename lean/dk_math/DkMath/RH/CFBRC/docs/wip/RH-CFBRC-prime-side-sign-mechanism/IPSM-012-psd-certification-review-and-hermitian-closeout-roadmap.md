# IPSM-012 — PSD certification review and Hermitian closeout roadmap

Date: 2026-08-14

Repository: `Deskuma/dkmath`

Branch: `wip/RH-CFBRC-prime-side-sign-mechanism-260813-v0`

Status: implementation review / Gate 4B.2 PSD certification / no RH claim

---

## 0. Review result

The fixed-`ε` generic Mellin Gram layer is now PSD-certified in the finite-family quadratic-form sense.

Current classification:

```text
pointwise Gram expansion
  GREEN

pairwise kernel integral identity
  GREEN

finite double-sum / interval-integral exchange
  GREEN

kernel quadratic form = normalized common integral
  GREEN

kernel quadratic form = feature-map energy
  GREEN

quadratic-form reality
  GREEN

fixed-ε finite-family PSD certification
  GREEN

pointwise Hermitian kernel symmetry
  OPEN

prime-side source quadraticization bridge
  NOT STARTED
```

This checkpoint does not imply positivity of the prime-side scalar excess.

---

## 1. PSD certification is genuinely closed

The load-bearing theorem is now:

```lean
mellinQuadraticBoxGramQuadraticForm_eq_energy
```

It identifies the complex kernel-generated quadratic form with the real feature-map energy cast into `ℂ`.

The implementation then derives:

```lean
mellinQuadraticBoxGramQuadraticForm_im_eq_zero
mellinQuadraticBoxGramQuadraticForm_re_eq_energy
mellinQuadraticBoxGramQuadraticForm_re_nonneg
```

Thus for every finite family `z : Fin n → ℂ` and coefficient family `c : Fin n → ℂ`, at every fixed `ε > 0`, the kernel-generated quadratic form is real and nonnegative.

This is exactly the finite-family PSD certificate required by IPSM-008 through IPSM-011.

The generic object may therefore be upgraded from

```text
Gram-kernel candidate
```

to

```text
fixed-ε finite-family PSD-certified Mellin Gram structure
```

without any prime-side claim.

---

## 2. The integration algebra is now audit-complete

The implementation correctly introduced the two generic linearity helpers

```lean
intervalIntegral_sum_univ_eq_sum_intervalIntegral
sum_intervalIntegral_univ_eq_intervalIntegral_sum
```

and used them twice to move the inner and outer `Finset.univ` sums through the interval integral.

The pairwise theorem

```lean
mellinQuadraticBoxGram_pair_eq_integral
```

is reused as the atomic bridge from each kernel matrix entry to the normalized interval integral.

No infinite sum, Fubini theorem, dominated convergence, limit exchange, or asymptotic argument enters this proof.

The normalization `(2 * ε)⁻¹` appears exactly once.

---

## 3. Preferred final generic closeout: direct Hermitian symmetry

PSD certification is complete even before a separate pointwise symmetry theorem, but the generic kernel API should still expose Hermitian symmetry explicitly.

Target theorem:

```lean
mellinQuadraticBoxGramKernel_conj_symm
    {ε : ℝ} (hε : 0 < ε) (z w : ℂ) :
    mellinQuadraticBoxGramKernel ε w z =
      starRingEnd ℂ (mellinQuadraticBoxGramKernel ε z w)
```

The natural route is through the scalar multiplier conjugation law.

Suggested intermediate theorem:

```lean
mellinQuadraticBoxMultiplier_conj
    {ε : ℝ} (hε : 0 < ε) (u : ℂ) :
    mellinQuadraticBoxMultiplier ε (starRingEnd ℂ u) =
      starRingEnd ℂ (mellinQuadraticBoxMultiplier ε u)
```

Conceptually this is immediate from the real-normalized logarithmic average:

$$
H_\varepsilon(\overline u)=\overline{H_\varepsilon(u)}.
$$

For real `t`, conjugation sends the exponential feature to the corresponding conjugated parameter:

$$
\overline{e^{tu}}=e^{t\overline u}.
$$

The remaining proof obligation is only the installed Mathlib API for commuting complex conjugation with the finite interval integral.

Do not use any RH-specific mirror theorem here.  This belongs entirely in `DkMath.Analysis.MellinQuadraticGramKernel`.

---

## 4. Safe proof routes for the multiplier conjugation law

### Route A — direct interval-integral conjugation

Rewrite both sides using:

```lean
mellinQuadraticBoxMultiplier_eq_logAverage hε
```

Then:

1. use that the normalization scalar is real;
2. commute conjugation through the interval integral;
3. use `Complex.exp_conj` / the available equivalent theorem;
4. simplify conjugation of the real parameter `t`.

This is the preferred mathematical proof.

### Route B — real/imaginary extensionality

If the interval-integral conjugation API is awkward, prove the two complex numbers equal by `Complex.ext` after expressing real and imaginary parts of the integral.

Use this only as an API fallback; do not change the theorem statement.

### Route C — derive symmetry from the feature kernel integral directly

Instead of proving a separate multiplier theorem first, expand both kernel sides with

```lean
mellinQuadraticBoxGramKernel_eq_logAverage_integral hε
```

and prove conjugate symmetry at the integral level.

This is acceptable, but the separate multiplier conjugation theorem is reusable and therefore preferred.

---

## 5. Hermitian kernel theorem after multiplier conjugation

After the multiplier law, the kernel symmetry should be finite algebra:

```text
Kε(w,z)
  = w * conj(z) * Hε(w + conj(z))

conj(Kε(z,w))
  = conj(z) * w * conj(Hε(z + conj(w)))
  = w * conj(z) * Hε(w + conj(z))
```

No positivity argument is needed for this theorem.

The pointwise Hermitian law and the already-proved PSD quadratic form should remain two separate APIs:

```text
Hermitian symmetry
  structural kernel identity

PSD certification
  finite-family nonnegative quadratic-form identity
```

---

## 6. Gate 4B.2 closeout condition

Gate 4B.2 may be marked fully closed when the following are all Green:

```text
1. pointwise expansion
2. pairwise integral identity
3. double finite-sum / interval-integral exchange
4. quadratic form = feature energy
5. quadratic-form reality
6. finite-family PSD
7. direct pointwise Hermitian kernel symmetry
```

Items 1–6 are already Green.

Only item 7 remains.

---

## 7. Gate 4B.3 must remain logically separate

The generic PSD-certified Mellin kernel does not yet control the prime-side finite scalar excess.

The prime-side object remains the affine explicit-formula surface already isolated in Gate 3A–4A.

Therefore the following inference remains forbidden:

```text
fixed-ε Mellin Gram kernel is PSD
  therefore
prime-side scalar excess is nonnegative
```

A new source-derived quadraticization theorem is still required.

The next prime-side question is not whether the generic kernel is positive; that is now settled.

The next question is whether the actual prime-side source can be represented, paired, differentiated, integrated by parts, or otherwise transformed into a quadratic form generated by this PSD kernel without inserting the desired sign as an assumption.

---

## 8. Gate 4B.3 entry audit after Hermitian closeout

Once Hermitian symmetry is Green, start a new RH-specific module rather than adding more generic wrappers to the analysis file.

Suggested module:

```text
DkMath.RH.CFBRC.PascalCenteredXiPrimeSideQuadraticizationAudit
```

First checkpoint should expose only exact representation candidates.

Suggested questions:

```text
A. Can the finite prime-cutoff coefficients be embedded as a finite feature family?

B. Can the right-edge integration variable produce the same exponential feature map as the Mellin Gram kernel?

C. Can the archimedean, elementary, and top-horizontal corrections be represented inside the same quadratic form rather than discarded?

D. Does a source-derived adjoint/conjugate coefficient family exist at finite X?

E. Can the radial comparison term be identified with a diagonal or boundary term of that quadratic form?
```

Do not define a provider whose field is equivalent to the desired scalar-excess nonnegativity.

---

## 9. Expected branch status after the next checkpoint

```text
Gate 3B algebraic route
  CLOSED

Gate 4A full-source mirror audit
  GREEN

Gate 4B.2 fixed-ε Mellin Gram construction
  PSD CERTIFIED
  Hermitian symmetry pending one theorem family

Gate 4B.3 prime-side quadraticization
  BLOCKED until Hermitian closeout

prime-side independent sign provider
  OPEN
```

---

## 10. Non-goals

IPSM-012 introduces no claim of:

```text
prime-side scalar excess nonnegativity
finite arithmetic defect nonpositivity
finite-cutoff conjugate provider
source-derived quadraticization
limit exchange
joint limit
T -> infinity
fixed defect vanishing
Riemann Hypothesis
```
