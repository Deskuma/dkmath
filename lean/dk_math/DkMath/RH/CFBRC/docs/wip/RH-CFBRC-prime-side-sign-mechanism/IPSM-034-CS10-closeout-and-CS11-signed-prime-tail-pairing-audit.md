# IPSM-034: CS10 closeout and CS11 signed prime-tail pairing audit

## Status

CS10 is Green through the exact finite-source cancellation layer.

The implemented chain is now:

```text
four-term finite arithmetic ledger
→ exact cancellation of archimedean / elementary / top-horizontal corrections
→ one complex prime cutoff residual
→ fixed-ε residual tends to zero as X → ∞
→ finite defect error is exactly the signed imaginary coordinate
```

The load-bearing identity is

```text
ArithmeticDefectApproximant - ArithmeticDefectEndpoint
  = -(PrimeCutoffResidual.im) / π.
```

No independent sign theorem is contained in this identity.  The remaining CS10-E--G gap is therefore correctly retained as a named source frontier.

## Verified source facts

`PascalCenteredXiPrimeSideFiniteSourceCancellationAudit.lean` defines

```lean
pascalCenteredXiPrimeSideFiniteCutoffResidual ε W X
```

as the finite prime-mode sum minus the ordinary-zeta right-edge integral.  The prime-mode sum is exactly the XDP-017 cutoff integral.

The exact four-term explicit formula shows that when the finite arithmetic approximant is compared with its fixed-ε Xi endpoint, the archimedean, elementary, and top-horizontal terms occur identically on both sides and cancel algebraically.  They are therefore not independent obstructions for the inner `X → ∞` error.

The XDP-017 transport theorem already gives the fixed-ε convergence of the cutoff integral to the ordinary-zeta right-edge integral, hence the named residual tends to zero with `X → ∞`.

## CS11 objective

Do not immediately introduce an infinite tail sum under the interval integral.  First expose the signed residual at the integrand level and exploit the exact symmetry of the finite vertical interval.

Create a new module:

```text
DkMath.RH.CFBRC.PascalCenteredXiPrimeSideSignedTailPairingAudit
```

with

```lean
import DkMath.RH.CFBRC.PascalCenteredXiPrimeSideFiniteSourceCancellationAudit
```

and add it to the public `DkMath.RH` import surface only after the module is Green.

## CS11-A: named raw cutoff-difference amplitude

Let

```text
s(t) := σ + i t
z(t) := s(t) - 1/2
hε(z) := z^2 * Hε(z)
```

using the existing repository definitions rather than new parallel mathematics.

Name the raw complex amplitude before the right-edge differential:

```lean
noncomputable def pascalCenteredXiPrimeSideFiniteCutoffRawDifference
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow)
    (X : ℕ) (t : ℝ) : ℂ :=
  pascalCenteredXiMellinSecondDifferenceWeight ε 0
      (pascalOrdinaryToCentered
        (pascalSymmetricRectangleRightEdge W.rectangle.σ t)) *
    (pascalPrimePowerPHZFiniteUpTo X
        (pascalSymmetricRectangleRightEdge W.rectangle.σ t) -
      pascalXiOrdinaryZetaNegLogDeriv
        (pascalSymmetricRectangleRightEdge W.rectangle.σ t))
```

Then prove the exact residual integral form

```text
PrimeCutoffResidual
  = ∫ t in -T..T, RawDifference(t) * I.
```

This theorem should use only the existing cutoff-integral adapter and definitions.  No `tsum` or sum/integral interchange is needed.

## CS11-B: conjugation of the Mellin quadratic weight on the vertical pair

For positive `ε`, prove the vertical-pair conjugation theorem for the actual `τ = 0` Mellin weight:

```text
hε(z(-t)) = conj(hε(z(t))).
```

Recommended source route:

1. `pascalOrdinaryToCentered (rightEdge σ (-t))` is the conjugate of the `t` node;
2. use the exact logarithmic-average representation of `centeredMellinSpectralWeight (centeredMellinBoxApprox ε)`;
3. conjugation passes through the finite interval integral;
4. `z^2` respects conjugation.

Do not introduce an abstract conjugation provider if this can be derived from the box definition.

## CS11-C: conjugation of the arithmetic cutoff difference

Prove, on `1 < σ`,

```text
PHZ_X(s(-t)) = conj(PHZ_X(s(t)))
```

and

```text
OrdinaryZetaNegLogDeriv(s(-t))
  = conj(OrdinaryZetaNegLogDeriv(s(t))).
```

For the finite PHZ term, the preferred proof is the finite von Mangoldt sum: the coefficients are real and the Dirichlet monomial conjugates under `t ↦ -t`.

For the ordinary-zeta limit term, prefer the convergent von Mangoldt L-series in `Re(s) > 1` or an already available pinned zeta-conjugation theorem.  Do not use any zero-side symmetry, RH statement, or completed-Xi zero theorem.

The target is

```text
RawDifference(-t) = conj(RawDifference(t)).
```

## CS11-D: anti-conjugation after the contour differential

Because the right-edge differential contributes `I`, the actual residual integrand should satisfy

```text
(RawDifference(-t) * I)
  = -conj(RawDifference(t) * I).
```

Use the symmetric interval to prove

```text
PrimeCutoffResidual = -conj(PrimeCutoffResidual)
```

and hence

```text
PrimeCutoffResidual.re = 0.
```

This is an important semantic result: the CS10-D imaginary projection then contains the whole residual, not merely one coordinate of an unrelated complex error.

If convenient, also record the equivalent pure-imaginary representation

```text
PrimeCutoffResidual
  = I * ((PrimeCutoffResidual.im : ℂ)).
```

with the exact orientation checked by Lean.

## CS11-E: half-interval signed real reduction

After CS11-D, derive a real half-interval representation before expanding an infinite tail.

Expected shape, with the exact sign checked by Lean:

```text
PrimeCutoffResidual.im
  = 2 * ∫ t in 0..T, (RawDifference t).re.
```

Consequently the finite defect error becomes a single signed real integral:

```text
ArithmeticDefectApproximant - ArithmeticDefectEndpoint
  = -(2 / π) * ∫ t in 0..T, (RawDifference t).re.
```

Do not hard-code this sign if Lean exposes the opposite orientation; the theorem surface, not the prose, is authoritative.

## CS11-F: positive-convention pointwise tail

Only after the finite symmetric pairing is Green, name the positive-convention tail

```text
PrimeTail_X(s)
  := OrdinaryZetaNegLogDeriv(s) - PHZ_X(s).
```

Then

```text
RawDifference(t) = -hε(z(t)) * PrimeTail_X(s(t)).
```

and the defect cutoff error should become a positive-convention signed tail projection.

At this stage do not yet claim

```text
PrimeTail_X(s) = ∑ n > X, Λ(n) n^{-s}
```

inside an integral unless the exact `HasSum`/`tsum` tail and interchange certificate have been proved.

## CS11-G: pointwise von Mangoldt tail and optional interchange

Audit the existing L-series API for an exact pointwise tail theorem in `Re(s) > 1`.

A desirable pointwise statement is

```text
PrimeTail_X(σ + i t)
  = ∑' n, indicator_{X < n} (Λ(n) * n^{-(σ+i t)}).
```

or an equivalent `HasSum` formulation.

If an integral/tail exchange is pursued, it must be justified independently.  The existing XDP-017 vertical majorant is a strong candidate because the von Mangoldt L-series is absolutely summable at the fixed real coordinate `σ > 1` and the interval in `t` is finite.

The exchange is optional for CS11 closeout.  Do not block CS11-D/E on it.

## CS11-H: one-mode signed projection audit

If CS11-G is obtained, isolate one tail mode before summing:

```text
Λ(n) * n^{-σ} * Re(hε(a + i t) * exp(-i t log n))
```

where

```text
a := σ - 1/2 > 0.
```

The coefficients `Λ(n) * n^{-σ}` are nonnegative.  Therefore any remaining sign problem sits in the real oscillatory projection kernel.

Audit, in this order:

1. exact conjugate pairing;
2. exact cosine/sine decomposition of the one-mode kernel;
3. whether the half-interval integral has a fixed sign;
4. if not, whether adjacent prime-power modes admit source-derived block cancellation;
5. only then consider a coarse absolute bound.

Do not infer a sign from coefficient nonnegativity alone: the Fourier phase is load-bearing.

## Important likely obstruction

The finite rectangle height `T` leaves a truncated Fourier-type integral.  Such kernels can be oscillatory.  Therefore a theorem of the form

```text
∀ n > X, 0 ≤ oneModeProjection n
```

must not be assumed or encoded as a provider without proof.

If the one-mode kernel is sign-indefinite, record that fact or a named gap and move to pair/block cancellation rather than hiding the oscillation under a norm bound.

## Firewall

CS11 must not use any of the following as a signed prime-tail provider:

- `pascalCenteredXiFixedSecondMomentDefectFunctional_nonneg`;
- finite horizontal zero energy;
- anti-mirror zero energy;
- `PascalCenteredXiFixedDefectVanishesOnSafeRadii`;
- `pascalCenteredXiFixedDefectVanishesOnSafeRadii_iff_riemannHypothesis`;
- the CS9 envelope equivalence in the provider direction;
- reversed or joint `X/ε` limits.

The following are allowed as source infrastructure:

- finite von Mangoldt identities;
- absolute convergence on `Re(s) > 1`;
- finite-interval dominated convergence already established in XDP-017;
- Mellin box logarithmic-average identities;
- conjugation identities derived from real coefficients / real integration intervals.

## CS11 closeout classification

Green-A would mean a genuine source-derived signed tail theorem is obtained.

Green-B is acceptable if the following are closed exactly:

```text
residual integral representation
→ vertical conjugate pairing
→ residual is pure imaginary
→ half-interval signed real reduction
→ positive-convention tail surface
→ precise remaining signed-kernel gap
```

A Green-B closeout must retain a named frontier such as

```lean
inductive PascalCenteredXiPrimeSideSignedTailPairingGap : Prop
  | noIndependentSignedTailProjectionProvider :
      PascalCenteredXiPrimeSideSignedTailPairingGap
```

if no independent sign provider is found.

## Scope

CS11 is still an inner finite-source audit.  It does not prove:

- a fixed-`ε` radial comparison;
- a vanishing upper envelope;
- fixed defect nonpositivity;
- limit exchange;
- RH.

The purpose is to reduce the remaining arithmetic question from a complex four-source ledger to the smallest honest signed oscillatory source surface that Lean can expose.