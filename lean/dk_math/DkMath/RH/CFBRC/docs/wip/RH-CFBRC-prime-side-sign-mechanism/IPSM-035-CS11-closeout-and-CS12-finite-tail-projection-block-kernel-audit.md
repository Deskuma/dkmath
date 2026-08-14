# IPSM-035 — CS11 closeout and CS12 finite-tail projection / block-kernel audit

## Status

CS11 is accepted **Green-B**.

The implementation in `PascalCenteredXiPrimeSideSignedTailPairingAudit.lean` establishes, at fixed positive `ε`, fixed finite residue window `W`, and finite cutoff `X`:

- an exact raw finite residual integral;
- conjugation of the Mellin quadratic weight, finite PHZ source, and ordinary-zeta negative logarithmic derivative;
- anti-conjugation of the oriented residual integrand under `t ↦ -t`;
- `PrimeCutoffResidual.re = 0`;
- the exact half-interval identity for `PrimeCutoffResidual.im`;
- the positive-convention finite prime tail `ordinary-zeta − PHZ`;
- a named frontier for the missing independent signed-tail provider.

No infinite tail/integral exchange, fixed-`ε` sign theorem, limit exchange, or RH conclusion is present.

The module split remains healthy: the old quadraticization module stays frozen, and CS11 is a new downstream import-chain module.

---

## 1. Exact consequence already available from CS10 + CS11

Let

```text
R_{ε,W,X} := PrimeCutoffResidual(ε,W,X)
```

and let the positive-convention prime tail be

```text
Tail_{W,X}(t) := OrdinaryZetaNegLogDeriv(s_t) - PHZ_X(s_t).
```

CS11 gives

$$R_{ε,W,X}.\operatorname{im}=2\int_0^T \operatorname{Re}(\operatorname{RawDifference}_{ε,W,X}(t))\,dt.$$

The raw difference is

$$\operatorname{RawDifference}_{ε,W,X}(t)=-h_ε(z_t)\,\operatorname{Tail}_{W,X}(t),$$

where

```text
h_ε(z) := pascalCenteredXiMellinSecondDifferenceWeight ε 0 z.
```

CS10 gives

$$D_{ε,W,X}-D_{ε,W,\infty}=-\frac{R_{ε,W,X}.\operatorname{im}}{\pi}.$$

Therefore the next theorem should combine the already proved identities into the exact signed half-interval formula

$$D_{ε,W,X}-D_{ε,W,\infty}=\frac{2}{\pi}\int_0^T\operatorname{Re}\!\left(h_ε(z_t)\operatorname{Tail}_{W,X}(t)\right)dt.$$

This is source-derived algebra. It must be proved before introducing any new provider.

---

## 2. CS12-A — name the finite signed tail projection

Create a new downstream module, recommended name:

```text
DkMath.RH.CFBRC.PascalCenteredXiPrimeSideFiniteTailProjectionAudit
```

Import only the CS11 module plus genuinely needed Mathlib support.

Recommended definition:

```lean
noncomputable def pascalCenteredXiPrimeSideFiniteTailProjection
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) : ℝ :=
  ∫ t in (0 : ℝ)..W.rectangle.T,
    (pascalCenteredXiMellinSecondDifferenceWeight ε 0
      (pascalOrdinaryToCentered
        (pascalSymmetricRectangleRightEdge W.rectangle.σ t)) *
      pascalCenteredXiPrimeSideFinitePrimeTail W X t).re
```

Target theorem:

```lean
pascalCenteredXiMellinQuadraticArithmeticDefectApproximant_sub_endpoint_eq_tailProjection
```

with exact shape

$$D_{ε,W,X}-D_{ε,W,\infty}=\frac{2}{\pi}\,P_{ε,W,X}.$$

The constant and sign must be checked by Lean from the existing CS10-D and CS11 identities; do not repair them informally if the actual normalization differs.

---

## 3. CS12-B — classify what the signed projection actually proves

Because `π > 0`, the exact identity should yield order adapters such as

$$0\le P_{ε,W,X}\iff D_{ε,W,\infty}\le D_{ε,W,X}.$$

and, if useful,

$$P_{ε,W,X}\le0\iff D_{ε,W,X}\le D_{ε,W,\infty}.$$

This is only a **convergence-direction classification**.

### Firewall

Do **not** infer

```text
P_{ε,W,X} ≥ 0
→ D_{ε,W,∞} ≤ 0
```

without an independent finite-cutoff anchor such as

```text
D_{ε,W,X} ≤ 0
```

or a vanishing upper bound for that finite cutoff.

A sign for the tail projection tells whether the finite cutoff lies above or below its endpoint. It does not determine the absolute sign of the endpoint.

This firewall should be recorded in module comments and in the closeout theorem naming.

---

## 4. CS12-C — finite block decomposition before any infinite-tail interchange

Do not yet rewrite `Tail_{W,X}` as an infinite sum inside the integral.

Instead introduce a **finite block** between cutoffs `X` and `Y`.

A low-risk definition is the difference of existing PHZ partial sums:

```lean
noncomputable def pascalCenteredXiPrimeSideFinitePrimeBlock
    (W : PascalCenteredXiResidueTransportWindow)
    (X Y : ℕ) (t : ℝ) : ℂ :=
  pascalPrimePowerPHZFiniteUpTo Y
      (pascalSymmetricRectangleRightEdge W.rectangle.σ t) -
    pascalPrimePowerPHZFiniteUpTo X
      (pascalSymmetricRectangleRightEdge W.rectangle.σ t)
```

Then source algebra gives

$$\operatorname{Tail}_{W,X}(t)-\operatorname{Tail}_{W,Y}(t)=\operatorname{Block}_{W,X,Y}(t).$$

No summability or sum/integral interchange is required for this identity.

Define the corresponding finite block projection and prove

$$P_{ε,W,X}-P_{ε,W,Y}=B_{ε,W,X,Y}.$$

This converts the remaining signed problem into finite increments first.

---

## 5. CS12-D — expose the von Mangoldt mode kernel on finite blocks

For a finite block, it is safe to use the existing finite von Mangoldt representation and `intervalIntegral.integral_finsetSum` after proving the required finite integrability certificates.

Define a mode kernel without hiding the positive arithmetic coefficient. A suitable semantic target is

$$K_{ε,W}(n)=\int_0^T\operatorname{Re}\!\left(h_ε(z_t)\,(n^{-s_t})\right)dt.$$

Then a finite block should have the form

$$B_{ε,W,X,Y}=\sum_{X<n\le Y}\Lambda(n)\,K_{ε,W}(n),$$

up to the exact repository cutoff convention (`range (X+1)`, endpoint inclusions, and the `n=0` totalization). Lean must determine the exact finite-index statement.

The coefficient side is nonnegative:

$$\Lambda(n)\ge0.$$

But this alone gives no block sign. The oscillatory kernel `K_{ε,W}(n)` carries the sign question.

Do not replace `K` by its norm. A norm bound destroys exactly the cancellation information CS10–CS11 isolated.

---

## 6. Optional explicit phase normalization

Only after the finite mode-kernel theorem is Green, audit an explicit phase form on the ordinary right edge

$$s_t=\sigma+it,\qquad z_t=(\sigma-\tfrac12)+it.$$

For positive natural `n`, the Dirichlet monomial has the expected oscillatory structure

$$n^{-s_t}=n^{-\sigma}e^{-it\log n}.$$

A future theorem may therefore isolate

$$K_{ε,W}(n)=n^{-\sigma}\int_0^T\operatorname{Re}\!\left(h_ε(z_t)e^{-it\log n}\right)dt.$$

Only introduce this if the required `Complex.cpow` normalization can be proved from existing Mathlib APIs without fragile branch assumptions.

No trigonometric rewrite is required merely for cosmetic purposes.

---

## 7. CS12-E — anchor audit

The endpoint-sign problem now has two logically different ingredients:

```text
A. direction:
   signed finite tail/block projection
   → finite cutoff lies above/below endpoint

B. anchor:
   an independently proved finite-cutoff upper bound
   → finite cutoff lies at/below a vanishing barrier
```

Only their correct combination can produce the CS8 upper-envelope target.

A useful adapter to consider is the following semantic shape:

```text
0 ≤ P_{ε,W,X}
∧ D_{ε,W,X} ≤ r(ε)
→ D_{ε,W,∞} ≤ r(ε)
```

If later this is made eventual in `ε` with `r(ε) → 0`, then it feeds the already classified CS9 envelope contract.

Do not package the conjunction itself as an unexplained provider. The source of both the direction inequality and the anchor inequality must remain explicit.

---

## 8. Search order for the independent mechanism

After CS12-A through CS12-D are Green, inspect these routes in order:

1. **single-mode kernel sign** — likely false globally because of oscillation; test rather than assume;
2. **adjacent finite prime-power block cancellation** — pair/block structure may be the first natural sign unit;
3. **partial-summation / Abel transform of finite blocks** — preserve signed information;
4. **monotone or alternating block certificate** — only if source-derived;
5. **finite-cutoff anchor** — determine whether an already proved whole-surface/energy theorem controls some finite `X` without using the radial comparison target itself.

The last item is essential. Even a perfect direction theorem for the tail does not solve the absolute endpoint sign without an anchor.

---

## 9. Forbidden shortcuts

CS12 must not use any of the following as a prime-side signed provider:

- fixed-Xi defect nonnegativity;
- horizontal zero energy or anti-mirror energy;
- RH-equivalent defect vanishing;
- the CS9 envelope equivalence in the reverse direction;
- `X → ∞` convergence alone;
- an infinite tail/integral exchange without an independent certificate;
- a norm majorant as a substitute for signed cancellation;
- a synthetic completion square whose source identity is not already present.

No fixed-`ε` sign theorem, limit exchange, or RH consequence should be stated unless a genuinely independent source theorem is found.

---

## 10. Expected CS12 closeout

A successful algebraic closeout should look like

```text
CS12-A  defect error = exact finite tail projection            GREEN
CS12-B  projection sign ↔ cutoff/endpoint order               GREEN
CS12-C  finite cutoff difference = finite block projection     GREEN
CS12-D  finite block = Σ Λ(n) * signed mode kernel             GREEN
CS12-E  independent block sign / finite-cutoff anchor           OPEN or source-derived GREEN
```

If no independent sign or anchor is found, add a new named obstruction such as

```lean
inductive PascalCenteredXiPrimeSideFiniteBlockSignedAnchorGap : Prop
  | noIndependentFiniteBlockSignedAnchor :
      PascalCenteredXiPrimeSideFiniteBlockSignedAnchorGap
```

This is a frontier marker, not an impossibility theorem.

---

## 11. Architectural note

Continue the import-chain policy:

```text
...FiniteSourceCancellationAudit
→ ...SignedTailPairingAudit
→ ...FiniteTailProjectionAudit
→ future block/anchor module
```

Do not move old Green theorems merely to rebalance file size. New research phases should continue downstream unless a genuine refactor bug requires touching an earlier module.
