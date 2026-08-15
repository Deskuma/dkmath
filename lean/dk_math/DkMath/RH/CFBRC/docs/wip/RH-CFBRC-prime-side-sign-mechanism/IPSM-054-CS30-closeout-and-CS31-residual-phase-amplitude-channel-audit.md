# IPSM-054 — CS30 closeout and CS31 residual phase/amplitude channel audit

## 0. Status

Branch: `wip/RH-CFBRC-prime-side-sign-mechanism-260813-v1`

CS30 verdict: **Green-B**.

CS30 has now established, at fixed finite `ε`, residue window `W`, and cutoff `X`:

- a finite rectangle background scalar,
- the exact finite identity
  `G = π * (background - scalarMismatch)`,
- the exact mismatch-reach classification,
- a finite Euler log potential `A_X`,
- `A'_X = -PHZ_X`,
- the finite Euler compensator and its log derivative,
- the finite Euler-renormalized zeta residual,
- the exact residual negative-log-derivative identity,
- nonvanishing of the residual on a decomposition-safe top edge,
- the top zeta-cutoff mismatch as one finite weighted residual integral,
- no infinite Euler product, no infinite prime-series exchange, no endpoint sign, and no RH conclusion.

The remaining named frontier is an independent scalar-reach estimate.

## 1. First cleanup — discharge the finite PHZ integrability input

CS30 currently accepts the finite PHZ weighted top integrand as an explicit `IntervalIntegrable` hypothesis.

This is only a local finite technical obligation. Promote the continuity argument already present in the CS28 top-companion proof into public reusable theorems, for example:

```lean
theorem pascalCenteredXiPrimeSideFiniteArithmeticTopEdgePathIntegrand_continuous
    {ε : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) :
    Continuous
      (pascalCenteredXiPrimeSideFiniteArithmeticTopEdgePathIntegrand ε W X)
```

and

```lean
theorem pascalCenteredXiPrimeSideFiniteArithmeticTopEdgePathIntegrand_intervalIntegrable
    {ε : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) :
    IntervalIntegrable
      (pascalCenteredXiPrimeSideFiniteArithmeticTopEdgePathIntegrand ε W X)
      volume W.rectangle.σ (1 - W.rectangle.σ)
```

Then provide CS30 residual-integral adapters which no longer require callers to supply `hPHZ` manually.

Do not turn this into an infinite-series statement. The proof should remain a finite `Finset` continuity proof.

## 2. CS31-A — residual logarithmic-rate field

Define the top path

```text
s_T(u) = u + iT
```

and the finite residual logarithmic-rate field

```lean
noncomputable def pascalCenteredXiPrimeSideFiniteResidualLogRate
    (X : ℕ) (W : PascalCenteredXiResidueTransportWindow) (u : ℝ) : ℂ :=
  -logDeriv
    (fun z : ℂ =>
      pascalCenteredXiPrimeSideFiniteEulerRenormalizedZetaResidual X z)
    (pascalSymmetricRectangleTopEdge u W.rectangle.T)
```

Under the existing top factor-safety contract this is source-derived and finite.

Do not introduce `Complex.arg` at this stage.

## 3. CS31-B — two real channels

Define the two surviving real rate channels:

```lean
noncomputable def pascalCenteredXiPrimeSideFiniteResidualAmplitudeDecayRate ... : ℝ :=
  (pascalCenteredXiPrimeSideFiniteResidualLogRate X W u).re

noncomputable def pascalCenteredXiPrimeSideFiniteResidualPhaseDecayRate ... : ℝ :=
  (pascalCenteredXiPrimeSideFiniteResidualLogRate X W u).im
```

The naming convention is intentional. Since

```text
q = -R'/R,
```

its real part is the negative logarithmic-amplitude rate and its imaginary part is the negative unwrapped-phase rate.

Initially this semantic statement may remain separate from the algebraic definitions.

## 4. CS31-C — pointwise scalar-channel decomposition

Let

```text
h(u) = centered Mellin quadratic weight on the top edge,
q(u) = finite residual log rate.
```

Prove the exact real identity

```text
Im(h(u) * q(u))
  = Re(h(u)) * Im(q(u))
    + Im(h(u)) * Re(q(u)).
```

Package the two terms as named channel densities, e.g.

```lean
PhaseChannelDensity := h.re * q.im
AmplitudeChannelDensity := h.im * q.re
```

and prove

```text
ScalarResidualDensity
  = PhaseChannelDensity + AmplitudeChannelDensity.
```

This is a pure complex-algebra theorem and must not require a sign hypothesis.

## 5. CS31-D — exact scalar mismatch as two finite channel integrals

From CS30,

```text
MismatchScalar
  = Im (2 * ∫ h*q) / (2π).
```

Therefore prove the exact finite decomposition

```text
MismatchScalar
  = (1 / π) * ∫ PhaseChannelDensity
    + (1 / π) * ∫ AmplitudeChannelDensity.
```

Derive the required real interval-integrability from the already available complex interval-integrability whenever possible.

Keep the top orientation exactly as in CS28/CS30: `σ → 1 - σ`.

Do not silently reverse the interval.

## 6. CS31-E — semantic derivative bridge for the amplitude channel

On a safe top point, let

```text
R_X(u) = finite Euler-renormalized zeta residual at s_T(u).
```

Because `R_X(u) ≠ 0`, prove the local real derivative identity, if supported cleanly by the pinned Mathlib API:

```text
d/du log |R_X(u)|
  = Re(R'_X(u) / R_X(u))
  = -AmplitudeDecayRate(u).
```

Prefer `Real.log (Complex.abs ...)` or `Real.log ‖...‖` according to the most stable Mathlib theorem surface.

If this derivative bridge becomes disproportionately API-heavy, keep the algebraic two-channel result Green-B and leave this semantic bridge as a narrowly named frontier. Do not introduce an axiom/provider merely to name amplitude.

## 7. CS31-F — branch-free cumulative displacement variables

Avoid global `Complex.arg` initially.

Define branch-free cumulative rates by finite real interval integrals from a chosen top-edge basepoint, for example the right corner `u = σ`:

```text
AmplitudeDecayDisplacement(u)
  := ∫ v in σ..u, AmplitudeDecayRate(v)

PhaseDecayDisplacement(u)
  := ∫ v in σ..u, PhaseDecayRate(v)
```

If continuity is available, prove the corresponding FTC derivative statements.

The phase displacement is deliberately defined through the log-derivative rate rather than a principal-branch `arg`. This records winding continuously and avoids branch-cut artifacts.

Do **not** yet claim that it equals a principal argument difference.

## 8. Optional CS31-G — construct an actual logarithm lift only if economical

The safe top interval is contractible and the residual is nonzero there, so a continuous/differentiable logarithm lift exists mathematically.

However, do not make the whole CS31 depend on locating a fragile global-log API.

If useful, construct a source-level lift from the rate integral:

```text
L_X(u) := L_X(σ) - ∫ v in σ..u, q(v)
```

with a base value satisfying

```text
exp(L_X(σ)) = R_X(σ).
```

Then prove, if practical,

```text
exp(L_X(u)) = R_X(u).
```

This would identify

```text
Re L_X = log amplitude,
Im L_X = unwrapped phase
```

up to the chosen initial branch.

This section is optional. The exact two-channel mismatch decomposition is the primary deliverable.

## 9. CS31-H — reach classification in channel form

Combine CS30 reach with the new channel identity.

For zero-target radial contact, derive an exact equivalence of the form

```text
Background(ε,W,X)
  ≤ PhaseChannel(ε,W,X) + AmplitudeChannel(ε,W,X)
```

with the exact `1/π` normalization already absorbed consistently into the channel definitions or displayed explicitly.

Do not infer that either channel is individually nonnegative.

This theorem should make clear that a phase-only provider is stronger than necessary unless the amplitude channel is independently eliminated or controlled.

## 10. Strength countermodels

Add pure real countermodels showing at least:

1. phase channel alone may fail while amplitude channel supplies reach;
2. amplitude channel alone may fail while phase channel supplies reach;
3. neither individual channel sign follows from a lower bound on their sum.

These should be simple algebraic witnesses, not analytic claims about zeta.

Purpose: prevent future code from silently replacing the true two-channel reach problem by an unjustified phase-sign theorem.

## 11. Next analytic frontier

After CS31, the meaningful next question is not

```text
Is the residual mismatch small?
```

and not yet

```text
Is the phase channel positive?
```

The correct question becomes:

```text
Can the weighted phase + amplitude displacement reach the finite rectangle background cofinally?
```

Possible later mechanisms include:

- top-edge mirror pairing,
- integration by parts against the explicit Mellin weight,
- cancellation of the amplitude channel against archimedean/elementary background terms,
- a source-derived winding/phase-count relation for the renormalized residual.

None of these is assumed in CS31.

## 12. Required named frontier

If no independent channel reach theorem is obtained, retain a narrow marker such as:

```lean
inductive PascalCenteredXiPrimeSideFiniteResidualChannelReachGap : Prop
  | no_independent_phase_amplitude_reach_estimate
```

Do not delete the CS30 reach gap unless a theorem genuinely discharges it.

## 13. Validation

Run at least:

```text
lake env lean <new-CS31-file>
lake build DkMath.RH
git diff --check
```

No new `sorry`, `axiom`, or `native_decide`.

## 14. Research interpretation

CS25 removed the common quadratic carrier and exposed interaction.
CS27 turned that interaction into a holomorphic finite potential.
CS28 exposed the actual top mismatch.
CS29 reduced the relevant information to one scalar component.
CS30 compressed the mismatch into one finite Euler-renormalized zeta residual and corrected the sign logic from “mismatch smallness” to “mismatch reach.”

CS31 should now resolve that surviving scalar into its two genuinely distinct real mechanisms:

```text
weighted phase decay
+
weighted logarithmic-amplitude decay.
```

Only after this split is exact should one decide whether a later CF2D/ThreeElement interpretation is mathematically useful. The ordinary complex-analysis bridge remains primary.
