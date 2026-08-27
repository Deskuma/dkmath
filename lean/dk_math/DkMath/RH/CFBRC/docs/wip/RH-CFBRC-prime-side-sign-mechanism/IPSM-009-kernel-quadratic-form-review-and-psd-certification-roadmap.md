# IPSM-009 — Kernel quadratic-form review and PSD certification roadmap

Date: 2026-08-13

Repository: `Deskuma/dkmath`

Branch: `wip/RH-CFBRC-prime-side-sign-mechanism-260813-v0`

Status: Gate 4B positive-kernel certification / no prime-side sign claim / no RH claim

---

## 0. Review result

The new definition

```lean
mellinQuadraticBoxGramQuadraticForm
```

is a correct kernel-generated finite quadratic-form surface for the coefficient convention already used by

```lean
mellinQuadraticBoxGramEnergy
```

The current state is therefore:

```text
fixed-epsilon log-average multiplier        GREEN
one-variable quadratic weight               GREEN
Hermitian Gram-kernel candidate              GREEN
positive feature-map energy                  GREEN
kernel-generated finite quadratic form       GREEN as a definition
quadratic-form = feature-map energy           OPEN
kernel PSD theorem                            OPEN
kernel Hermitian symmetry                     OPEN
prime-side scalar-excess quadraticization     OPEN
```

No PSD theorem should be claimed until the exact quadratic-form/energy identity is closed.

---

## 1. Coefficient orientation audit

The feature map used by the existing positive energy is

```text
phi_t(j) = z_j * exp(t z_j)
```

with coefficient-weighted sum

```text
S_t = sum_j c_j * phi_t(j).
```

Expanding its squared norm gives coefficient order

```text
c_i * conj(c_j)
```

and kernel factor

```text
z_i * conj(z_j) * exp(t * (z_i + conj(z_j))).
```

This is exactly the orientation encoded by

```lean
∑ i, ∑ j,
  c i * starRingEnd ℂ (c j) *
    mellinQuadraticBoxGramKernel ε (z i) (z j)
```

Therefore the new quadratic form does not have a conjugation-direction bug.

---

## 2. Exact identity target

The desired fixed-`ε` identity is conceptually

$$
Q_{\varepsilon}(z,c)=E_{\varepsilon}(z,c).
$$

However the implemented codomains differ:

```text
mellinQuadraticBoxGramQuadraticForm : ℂ
mellinQuadraticBoxGramEnergy        : ℝ
```

So the implementation should choose one of the following theorem surfaces.

### Preferred strong surface

```lean
mellinQuadraticBoxGramQuadraticForm_eq_energy
    {n : ℕ} {ε : ℝ} (hε : 0 < ε)
    (z : Fin n → ℂ) (c : Fin n → ℂ) :
    mellinQuadraticBoxGramQuadraticForm ε z c =
      (mellinQuadraticBoxGramEnergy ε z c : ℂ)
```

This single theorem immediately certifies that the quadratic form is real and nonnegative through the already Green energy theorem.

### Safe fallback surface

If real-to-complex interval-integral coercion becomes API-heavy, split the result into:

```lean
mellinQuadraticBoxGramQuadraticForm_re_eq_energy
mellinQuadraticBoxGramQuadraticForm_im_eq_zero
```

Then recover the strong complex equality by `Complex.ext` later.

The proof should not introduce a new positivity assumption.

---

## 3. Required algebra under the integral

The load-bearing pointwise expansion is

$$
\left|\sum_j c_j z_j e^{t z_j}\right|^2=\sum_i\sum_j c_i\overline{c_j}z_i\overline{z_j}e^{t(z_i+\overline{z_j})}.
$$

For real `t`, the proof must use an exact conjugation identity of the form

```text
conj(exp((t : ℂ) * z)) = exp((t : ℂ) * conj(z)).
```

Then distributivity converts `normSq` of the finite sum into the double finite sum.

This is the mathematical core.  Finite-sum and interval-integral interchange are bookkeeping around this identity.

---

## 4. Integral/sum exchange checkpoint

The kernel definition already supplies the log-average integral for each pair `(i,j)`.

The quadratic-form/energy proof therefore needs only finite linearity:

```text
pairwise kernel integral
  -> finite sum over j
  -> finite sum over i
  -> one interval integral of the double sum
  -> pointwise normSq expansion
```

No dominated convergence, infinite sum interchange, `ε → 0`, or cutoff limit is involved.

The implementation should keep this theorem entirely inside the fixed-`ε`, finite-`Fin n` analysis layer.

---

## 5. PSD certification

Once the exact identity is Green, the PSD theorem should be derived rather than reproved from scratch.

Recommended surface:

```lean
mellinQuadraticBoxGramQuadraticForm_re_nonneg
    {n : ℕ} {ε : ℝ} (hε : 0 < ε)
    (z : Fin n → ℂ) (c : Fin n → ℂ) :
    0 ≤ (mellinQuadraticBoxGramQuadraticForm ε z c).re
```

If the strong complex equality is available, also expose:

```lean
mellinQuadraticBoxGramQuadraticForm_im_eq_zero
```

This is the actual finite-family PSD certificate for the kernel candidate.

Do not call the kernel PSD merely because the separate feature-map energy is nonnegative; the exact bridge is the certification step.

---

## 6. Hermitian symmetry

After or alongside PSD certification, prove the kernel-level symmetry

$$
K_{\varepsilon}(z,w)=\overline{K_{\varepsilon}(w,z)}.
$$

The missing analytic ingredient is the multiplier conjugation identity

$$
H_{\varepsilon}(\overline{u})=\overline{H_{\varepsilon}(u)}.
$$

For the centered Mellin box this should follow from the existing real symmetric log-average because `t` is real.

Suggested theorem layering:

```text
multiplier_conj
  -> GramKernel_conj_swap
  -> quadratic form reality
```

Quadratic-form reality may also follow independently from the energy identity; retaining both routes is useful as an internal consistency audit.

---

## 7. Important separation from the one-variable quadratic weight

Even after PSD certification, the following remain distinct theorem surfaces:

$$
q_{\varepsilon}(z)=z^2H_{\varepsilon}(z).
$$

$$
K_{\varepsilon}(z,z)=|z|^2H_{\varepsilon}(z+\overline z).
$$

The PSD result therefore does not by itself imply positivity of the current one-variable explicit-formula weight.

This mismatch is intentional and must remain explicit.

---

## 8. Gate 4B checkpoint after PSD closure

Only after the generic kernel is formally PSD should the RH/CFBRC layer attempt source quadraticization.

The next question is not whether a positive Gram form exists; after this checkpoint it will.

The next question is whether the prime-side scalar excess can be represented by, or bounded below by, a source-derived instance of that Gram form without assuming the desired sign.

Conceptually the missing bridge remains

```text
linear explicit-formula source
  -> source-derived paired / adjoint family
  -> Hermitian quadratic form
  -> current scalar excess
```

No such bridge is currently proved.

---

## 9. Non-goals

IPSM-009 does not claim:

```text
prime-side scalar excess nonnegativity
finite arithmetic defect nonpositivity
finite prime-cutoff conjugate provider
source quadraticization
limit exchange
joint limit
T -> infinity
fixed defect vanishing
Riemann Hypothesis
```

---

## 10. Next checkpoint

```text
Gate 4B.2a
  kernel quadratic form = feature-map energy

Gate 4B.2b
  quadratic-form reality and PSD

Gate 4B.2c
  kernel Hermitian symmetry

Gate 4B.3
  prime-side source quadraticization bridge
  OR named bridge obstruction
```

The generic positive-kernel layer should be fully certified before any new RH-specific positivity argument is attempted.
