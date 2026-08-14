# IPSM-010 — Pointwise Gram expansion review and integrated identity roadmap

Date: 2026-08-13

Repository: `Deskuma/dkmath`

Branch: `wip/RH-CFBRC-prime-side-sign-mechanism-260813-v0`

Status: implementation review / Gate 4B PSD-certification roadmap / no RH claim

---

## 0. Review result

The current implementation in

```text
DkMath.Analysis.MellinQuadraticGramKernel
```

has now closed the pointwise algebra needed for the fixed-`ε` Gram argument.

Current classification:

```text
mellinQuadraticBoxGramKernel
  GREEN

mellinQuadraticBoxGramEnergy
  GREEN

mellinQuadraticBoxGramEnergy_nonneg
  GREEN

mellinQuadraticBoxGramQuadraticForm
  GREEN

mellinQuadraticBoxGram_feature_normSq_eq_double_sum
  GREEN

quadratic form = integrated feature energy
  OPEN

kernel PSD certification
  OPEN

Hermitian symmetry
  OPEN

prime-side quadraticization bridge
  NOT STARTED
```

No positivity theorem for the prime-side scalar excess is implied by this checkpoint.

---

## 1. Pointwise expansion is correctly oriented

The kernel-generated quadratic form is

```lean
noncomputable def mellinQuadraticBoxGramQuadraticForm
    {n : ℕ} (ε : ℝ) (z : Fin n → ℂ) (c : Fin n → ℂ) : ℂ :=
  ∑ i, ∑ j,
    c i * starRingEnd ℂ (c j) *
      mellinQuadraticBoxGramKernel ε (z i) (z j)
```

The coefficient orientation is the one produced by the feature map

```text
j ↦ c j * (z j * exp(t * z j)).
```

The new theorem

```lean
mellinQuadraticBoxGram_feature_normSq_eq_double_sum
```

proves exactly the pointwise identity obtained by expanding the norm square.  In mathematical notation:

$$
\left|\sum_j c_j z_j e^{t z_j}\right|^2=\sum_i\sum_j c_i\overline{c_j}z_i\overline{z_j}e^{t(z_i+\overline{z_j})}.
$$

This closes the previously open finite-sum/conjugation orientation question.

In particular, there is no detected reversal of `c i * conj(c j)` and no detected reversal of the kernel arguments.

---

## 2. The remaining equality is an integration/normalization problem

At fixed `ε > 0`, the kernel already has the exact logarithmic-average representation

$$
K_\varepsilon(z,w)=z\overline w\,(2\varepsilon)^{-1}\int_{-\varepsilon}^{\varepsilon}e^{t(z+\overline w)}\,dt.
$$

The feature-map energy is

$$
E_\varepsilon(z,c)=(2\varepsilon)^{-1}\int_{-\varepsilon}^{\varepsilon}\left|\sum_j c_jz_je^{tz_j}\right|^2\,dt.
$$

Thus no new analytic estimate is required for the next checkpoint.  Only fixed finite sums, continuous exponential functions, a finite interval, and linearity of the interval integral are involved.

There is no limit, dominated-convergence theorem, Fubini theorem, or infinite series in this identity.

---

## 3. Recommended proof architecture

Do not prove the final equality by repeatedly unfolding both definitions in one large tactic block.

Introduce or locally use the common complex double-sum integrand

```text
G(t) :=
  ∑ i, ∑ j,
    c i * conj(c j) * z i * conj(z j) *
      exp(t * (z i + conj(z j))).
```

Then close the proof in three independent steps.

### Step A — feature energy to the common integrand

Use

```lean
mellinQuadraticBoxGram_feature_normSq_eq_double_sum
```

pointwise under the interval integral.

Target shape:

```text
(GramEnergy ε z c : ℂ)
  = ((2 * ε)⁻¹ : ℂ) * ∫ t in (-ε)..ε, G t
```

The existing energy is real-valued, so the cast to `ℂ` should be made explicit at this layer.

### Step B — kernel quadratic form to the same common integral

Expand each kernel term with

```lean
mellinQuadraticBoxGramKernel_eq_logAverage_integral
```

and move the finite sums through the interval integral.

Target shape:

```text
GramQuadraticForm ε z c
  = ((2 * ε)⁻¹ : ℂ) * ∫ t in (-ε)..ε, G t
```

This isolates all interval-integral linearity and constant-factor normalization in one theorem.

### Step C — exact equality

Combine Step A and Step B.

Preferred final theorem surface:

```lean
mellinQuadraticBoxGramQuadraticForm_eq_energy
    {n : ℕ} {ε : ℝ} (hε : 0 < ε)
    (z : Fin n → ℂ) (c : Fin n → ℂ) :
    mellinQuadraticBoxGramQuadraticForm ε z c =
      (mellinQuadraticBoxGramEnergy ε z c : ℂ)
```

If direct cast normalization is awkward in the installed Mathlib API, a safe intermediate split is:

```text
(GramQuadraticForm ε z c).re = GramEnergy ε z c
(GramQuadraticForm ε z c).im = 0
```

followed by `Complex.ext`.

Do not weaken the mathematical statement merely to avoid the cast; either route represents the same fixed-`ε` identity.

---

## 4. Integrability obligations should remain elementary

Every summand in `G` is a finite product of constants and

```text
t ↦ Complex.exp ((t : ℂ) * a)
```

for a fixed complex `a`.

Therefore each summand is continuous in `t`, each finite sum is continuous, and hence the common integrand is interval-integrable on the finite interval.

Recommended discipline:

```text
prove continuity / interval-integrability once
then use finite-sum linearity
```

rather than generating separate integrability obligations inside every `rw` of the double sum.

The exact installed Mathlib lemma names for finite-sum interval-integral linearity should be chosen by compilation.  Do not guess an API name into a permanent theorem if the compiler selects a different route.

---

## 5. Normalization audit

The factor `(2 * ε)⁻¹` appears exactly once on both sides.

On the feature side it is outside the interval integral by definition of

```lean
mellinQuadraticBoxGramEnergy.
```

On the kernel side it is inside

```lean
mellinQuadraticBoxMultiplier ε (...)
```

and becomes the same outer scalar after the finite sums and interval integral are exchanged.

For `ε > 0`, the real and complex casts of this scalar agree canonically.  This is a type-normalization issue, not an additional mathematical hypothesis.

No second factor of `(2 * ε)⁻¹` should be introduced.

---

## 6. PSD certification after the exact identity

Once

```text
GramQuadraticForm = (GramEnergy : ℂ)
```

is Green, PSD should be a corollary of the already-proved theorem

```lean
mellinQuadraticBoxGramEnergy_nonneg
```

rather than a second independent integral proof.

Suggested theorem surface:

```lean
mellinQuadraticBoxGramQuadraticForm_re_nonneg
    {n : ℕ} {ε : ℝ} (hε : 0 < ε)
    (z : Fin n → ℂ) (c : Fin n → ℂ) :
    0 ≤ (mellinQuadraticBoxGramQuadraticForm ε z c).re
```

and, if useful:

```lean
mellinQuadraticBoxGramQuadraticForm_im_eq_zero
```

Together these formally certify that the finite kernel matrix is positive semidefinite in the intended quadratic-form sense.

This is the correct point at which the project may upgrade the status from

```text
Gram-kernel candidate
```

to

```text
PSD-certified fixed-ε Gram kernel.
```

---

## 7. Hermitian symmetry remains logically separate

PSD certification of every finite quadratic form gives the intended positivity surface, but the pointwise kernel identity

$$
K_\varepsilon(w,z)=\overline{K_\varepsilon(z,w)}
$$

should preferably still be proved explicitly from the logarithmic-average representation.

The missing scalar identity is the conjugation law for the multiplier:

$$
H_\varepsilon(\overline u)=\overline{H_\varepsilon(u)}.
$$

For real `t` and positive real normalization, this follows from conjugating the exponential log-average.  It is independent of the prime-side problem and belongs in the generic analysis module.

Do not use the prime-side mirror theorem to prove this generic Mellin-kernel symmetry.

---

## 8. Prime-side boundary remains unchanged

Even after the generic kernel becomes PSD-certified, the existing prime-side finite scalar excess remains a linear/affine explicit-formula surface.

The theorem still missing is a source-derived quadraticization bridge that identifies or controls that scalar excess by the new Hermitian energy.

Therefore the following implication is still forbidden unless a new theorem supplies the bridge:

```text
Mellin Gram kernel is PSD
  therefore
prime-side scalar excess >= 0
```

The current branch does not justify this implication.

---

## 9. Next checkpoint

```text
Gate 4B.2a
  common double-sum integrand / interval-integrability

Gate 4B.2b
  feature energy = normalized integral of common integrand

Gate 4B.2c
  kernel quadratic form = normalized integral of common integrand

Gate 4B.2d
  quadratic form = feature energy
  -> reality
  -> PSD certification

Gate 4B.2e
  direct Hermitian kernel symmetry

Gate 4B.3
  prime-side source quadraticization audit
```

The current pointwise expansion is Green.  The next work is finite-dimensional integration algebra, not a new sign assumption.

---

## 10. Non-goals

IPSM-010 introduces no claim of:

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
