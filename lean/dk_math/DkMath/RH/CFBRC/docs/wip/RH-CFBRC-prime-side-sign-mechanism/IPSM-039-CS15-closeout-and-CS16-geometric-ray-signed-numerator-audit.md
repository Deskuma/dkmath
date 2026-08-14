# IPSM-039 — CS15 closeout and CS16 geometric-ray signed-numerator audit

## Status

CS15 is accepted as **Green-B**.

The finite prime-power ray has now been reduced to a finite complex geometric source without introducing an infinite ray, a sum/integral exchange, a sign theorem, or an RH consequence.

Verified CS15 ingredients:

- finite exponent support and downward closure;
- exact transport of the `p^(k+1)` mode to powers of the fixed ratio `q_p(s)`;
- finite complex ray amplitude before real projection;
- recovery of the CS14 real ray kernel by finite interval integration;
- denominator-free finite geometric compression;
- phase-spacing compatibility and adjacent-mode transport;
- explicit named gap for the missing signed-ray cancellation provider.

The next task is not to expand the ray back into many trigonometric modes.  The next task is to exploit the finite geometric compression itself.

---

## CS16 objective

For one prime `p`, one finite cutoff `X`, and one right-edge point

```text
s(t) = W.rectangle.σ + t * I,
q(t) = p ^ (-s(t)),
```

the finite ray is a finite geometric sum in `q(t)`.

The central CS16 goal is to separate its signed real projection into:

1. a **strictly positive denominator**; and
2. a **finite signed numerator** carrying the remaining phase information.

This is a finite source transformation.  It must not introduce an infinite Euler factor.

---

## CS16-A — remove the conditional support equality

CS15 currently has a theorem of the form

```lean
..._eq_geometricCore_of_support_eq_range
```

with an explicit hypothesis that the exponent support equals `Finset.range m`.

For prime `p`, the support is finite, contained in `Finset.range X`, and downward closed.  Package that fact into an actual ray-length object.

Suggested API shape:

```lean
noncomputable def pascalCenteredXiPrimeSidePrimePowerRayLength
    (X p : ℕ) : ℕ :=
  (pascalCenteredXiPrimeSidePrimePowerExponentSupportUpTo X p).card
```

or another definition that minimizes proof friction.

Target theorem:

```lean
pascalCenteredXiPrimeSidePrimePowerExponentSupportUpTo X p =
  Finset.range (pascalCenteredXiPrimeSidePrimePowerRayLength X p)
```

under `hp : Nat.Prime p`.

Any equivalent finite-prefix theorem is acceptable.  Do not rebuild prime-power uniqueness; reuse CS14/CS15 support facts.

This gate is important because all later geometric compression should be unconditional once `p` is known prime.

---

## CS16-B — right-edge ratio lies strictly inside the unit disk

For

```text
q_p(t) = pascalCenteredXiPrimeSidePrimeRatio p
  (pascalSymmetricRectangleRightEdge W.rectangle.σ t),
```

prove the source-derived modulus statement or a sufficient inequality implying

```text
‖q_p(t)‖ < 1.
```

The residue transport rectangle already carries

```text
W.rectangle.hσ : 1 < W.rectangle.σ.
```

Together with `hp.one_lt`, this should force strict contraction of the prime ratio on the complete right edge.

Prefer an exact modulus theorem if convenient, conceptually

```text
‖q_p(t)‖ = p ^ (-W.rectangle.σ).
```

If Mathlib's complex-`cpow` normalization makes that exact statement awkward, a directly proved strict inequality is enough for the subsequent gates.

Required consequences:

```text
q_p(t) ≠ 1
1 - q_p(t) ≠ 0
0 < Complex.normSq (1 - q_p(t))
```

No limit is involved.

---

## CS16-C — unconditional finite geometric amplitude

Using CS16-A, rewrite the finite complex ray amplitude pointwise as

```text
weight(t) * finiteGeometricRayCore (q_p(t)) m
```

with the canonical finite ray length `m`.

Then transport the denominator-free CS15 identity to the full weighted amplitude:

```text
(1 - q_p(t)) * RayAmplitude(t)
  = weight(t) * (q_p(t) - q_p(t)^(m+1)).
```

This theorem should be exact and pointwise.

Do not divide yet.

---

## CS16-D — rationalized positive-denominator identity

Now use `1 - q_p(t) ≠ 0` to obtain the quotient form, but immediately rationalize the complex denominator with conjugation.

The preferred mathematical identity is

$$
\operatorname{Re}\!\left(
  h(t)\frac{q(t)-q(t)^{m+1}}{1-q(t)}
\right)
=
\frac{
  \operatorname{Re}\!\left(
    h(t)(q(t)-q(t)^{m+1})\overline{(1-q(t))}
  \right)
}{|1-q(t)|^2}.
$$

In repository notation, prefer `Complex.normSq (1 - q)` or the exact pinned equivalent.

Define a named finite signed numerator, for example:

```lean
noncomputable def pascalCenteredXiPrimeSideFiniteGeometricRaySignedNumerator
    ... (t : ℝ) : ℝ :=
  Complex.re
    (weight(t) *
      (q(t) - q(t) ^ (m + 1)) *
      starRingEnd ℂ (1 - q(t)))
```

and a named denominator if that improves readability.

Target exact identity:

```text
RayAmplitude(t).re
  = SignedNumerator(t) / Complex.normSq (1 - q(t)).
```

The exact multiplication order may be adjusted for Lean.

---

## CS16-E — pointwise sign equivalence

Because the denominator is strictly positive, prove both directional adapters:

```text
0 ≤ RayAmplitude(t).re ↔ 0 ≤ SignedNumerator(t)
RayAmplitude(t).re ≤ 0 ↔ SignedNumerator(t) ≤ 0.
```

This is only a **pointwise sign reduction**.  It is not yet an integrated ray sign theorem.

Do not silently move from a pointwise equivalence to an interval-integral sign theorem without a pointwise sign provider.

---

## CS16-F — four-mode endpoint expansion

Expand the rationalized geometric numerator before applying the Mellin weight.

Algebraically,

$$
(q-q^{m+1})\overline{(1-q)}
=
q-|q|^2-q^{m+1}+|q|^2q^m.
$$

Use the exact repository identity `q * conj q = Complex.normSq q` or its pinned equivalent.

This is strategically important: an entire finite prime-power ray is reduced to a small endpoint-mode ledger rather than re-expanded into all intermediate exponents.

Target a theorem expressing the signed numerator through at most these endpoint modes:

```text
q,
1 weighted by normSq q,
q^m,
q^(m+1).
```

It is acceptable to keep `Complex.normSq q` cast into `ℂ` explicitly.

Do not infer a sign from this expansion.

---

## CS16-G — right-edge denominator geometry

Optionally expose

$$
|1-q|^2
=
1-2\operatorname{Re}(q)+|q|^2.
$$

Since `q = p^{-σ-it}`, this can later be read as a positive oscillatory denominator.

A stronger lower bound such as

$$
|1-q|\ge 1-|q|>0
$$

or a squared version is useful if it is easy to certify in Lean, but it is not required for Green-B.

Do not import CF2D merely to rename this quantity.  The later `q2` reinterpretation remains optional.  The present gate should first close in ordinary complex analysis.

---

## CS16-H — integrated signed-ray frontier

After the positive-denominator identity is available, define the corresponding finite signed numerator integrand/kernel if useful.

The desired future signed-ray theorem would require something like

```text
∀ t ∈ [0,T], 0 ≤ SignedNumerator(t)
```

or a genuinely integrated cancellation theorem.

If neither is source-derived, record a named frontier such as

```lean
inductive PascalCenteredXiPrimeSideGeometricRaySignedNumeratorGap : Prop
  | noIndependentSignedNumeratorProvider :
      PascalCenteredXiPrimeSideGeometricRaySignedNumeratorGap
```

A gap is the correct result if the numerator remains oscillatory.

---

## Important firewall — tail direction is still not an endpoint anchor

Even if CS16 eventually proves a sign for every finite prime-power ray, that by itself controls the **direction of the cutoff error**.

It does not automatically prove the absolute sign of

```text
pascalCenteredXiMellinQuadraticArithmeticDefectEndpoint ε W.
```

The earlier distinction remains mandatory:

```text
signed tail / block direction
+
independent finite-cutoff anchor or vanishing upper envelope
```

are logically different ingredients.

Do not use fixed-defect nonnegativity, horizontal-energy nonnegativity, or the RH-equivalent fixed-defect vanishing theorem as the missing arithmetic anchor.

---

## Why this route is preferred

CS13 exposed many oscillatory natural modes.

CS14 grouped them into prime-power rays.

CS15 compressed each ray into one finite geometric source.

CS16 should now exploit that compression instead of undoing it.

The key reduction is

```text
many p^k modes
→ one geometric quotient
→ positive norm-square denominator
→ finite endpoint signed numerator.
```

If a cancellation mechanism exists at the prime-ray level, this is the smallest currently authorized surface on which it should become visible.

---

## Green criteria

CS16 is Green-B if it closes all of the following without synthetic sign assumptions:

1. exponent support is canonically a finite prefix;
2. the right-edge prime ratio is strictly inside the unit disk;
3. finite ray amplitude is exactly the geometric core with canonical length;
4. denominator-free weighted compression is exact;
5. rationalized real projection has strictly positive `normSq` denominator;
6. pointwise sign is reduced exactly to a named finite numerator;
7. the numerator is expanded to the finite endpoint-mode ledger;
8. any still-missing signed provider is left as a named gap.

No infinite ray, no infinite sum/integral exchange, no fixed-ε RH sign theorem, and no RH conclusion are authorized in this checkpoint.
