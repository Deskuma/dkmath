# IPSM-057 — CS33 closeout and CS34 interval-local residual regularity audit

## 0. Status

Branch: `wip/RH-CFBRC-prime-side-sign-mechanism-260813-v1`

CS33 verdict: **Yellow**.

The finite transport algebra is closed, but the principal weighted-displacement theorem still accepts residual-rate continuity as an external hypothesis.  The remaining issue is not a sign theorem and not an RH-strength provider.  It is a local analytic regularity gap needed to make the finite ledger source-derived on the safe top edge.

CS33 has proved, conditionally on the stated regularity hypotheses:

- branch-free phase endpoint transport,
- real and imaginary Mellin-weight derivative channels,
- finite phase/amplitude integration-by-parts ledgers,
- the exact weighted-displacement representation of the scalar top mismatch,
- the amplitude endpoint replacement by a `log (normSq residual)` endpoint difference,
- the multiplicative norm-square endpoint transport.

No sign, infinite prime expansion, limit exchange, or RH conclusion is present.

## 1. Critical correction: do not target global continuity

The current CS33 statements use hypotheses such as

```lean
Continuous (pascalCenteredXiPrimeSideFiniteResidualPhaseDecayRate X W)
Continuous (pascalCenteredXiPrimeSideFiniteResidualAmplitudeDecayRate X W)
```

These are stronger than the geometric source contract.

`IsPascalCenteredXiTopLogDerivDecompositionSafe W` only guarantees the relevant factor nonvanishing on the finite top interval

```text
u ∈ uIcc σ (1 - σ).
```

Outside that interval the ordinary zeta factor may have zeros.  Therefore CS34 must **not** attempt to prove global continuity of the totalized log derivative on all `ℝ`.

The correct target is interval-local regularity:

```text
∀ u ∈ uIcc σ (1 - σ), ContinuousAt rate u
```

or an equivalent `ContinuousOn` statement plus the local continuity facts required by the interval FTC / integration-by-parts API.

This weakening is mathematically important and should be reflected in theorem signatures.

## 2. CS34-A — local ordinary-zeta log-derivative regularity on the safe top

Let

```text
s(u) = u + i T.
```

From the top factor-safety contract, for every `u` in the top interval:

```text
s(u) ≠ 1,
riemannZeta (s(u)) ≠ 0.
```

Prove source-derived local continuity of

```lean
u ↦ pascalXiOrdinaryZetaNegLogDeriv (s u)
```

at each safe top point.

Preferred mathematical route:

1. use the local holomorphic / analytic regularity of `riemannZeta` away from `1`;
2. obtain continuity of its complex derivative locally;
3. combine with continuity and local nonvanishing of `riemannZeta`;
4. form the quotient defining the negative logarithmic derivative;
5. compose with the affine top-edge path.

Do not introduce a global zero-free strip.

If Mathlib's analytic API is more convenient than a theorem named directly for continuity of `deriv riemannZeta`, use it.  The theorem should record the mathematical local fact, not depend on a brittle implementation name.

## 3. CS34-B — residual log-rate local continuity

Use the already-proved CS30 pointwise identity on the safe top:

```text
ResidualLogRate_X(u)
  = OrdinaryZetaNegLogDeriv(s(u)) - PHZ_X(s(u)).
```

The finite PHZ top path is already continuous by CS31.

Derive:

```lean
∀ u ∈ uIcc σ (1 - σ),
  ContinuousAt
    (pascalCenteredXiPrimeSideFiniteResidualLogRate X W) u
```

and consequently local continuity of the two real channels:

```text
AmplitudeDecayRate = Re ResidualLogRate,
PhaseDecayRate     = Im ResidualLogRate.
```

Also prove `ContinuousOn` forms if useful for compact-interval integrability.

## 4. CS34-C — finite interval integrability automatically from local source regularity

On the safe top interval, discharge the routine finite integrability inputs needed downstream.

At minimum derive:

- interval integrability of the residual log rate;
- interval integrability of amplitude and phase rates;
- interval integrability of phase/amplitude channel densities after multiplication by the finite Mellin weight.

Prefer source-derived `ContinuousOn` / continuity arguments over adding new provider structures.

## 5. CS34-D — Mellin-weight derivative regularity

CS33 still accepts

```text
IntervalIntegrable (Re weightDerivative)
IntervalIntegrable (Im weightDerivative)
```

as explicit hypotheses.

These are expected to be routine because the Mellin second-difference weight is globally complex differentiable for `ε > 0` and the top path is affine.

Prove sufficient continuity or interval-integrability of

```text
u ↦ deriv (pascalCenteredXiMellinSecondDifferenceWeight ε 0) (centeredTop(u))
```

and hence of its real and imaginary parts.

If Mathlib's generic theorem "complex differentiable implies continuous derivative" is inconvenient, an explicit derivative formula is acceptable, but do not introduce unnecessary transcendental rewrites unless needed.

## 6. CS34-E — refactor displacement derivative lemmas to interval-local hypotheses

The current CS33 lemmas

```lean
...AmplitudeDisplacement_hasDerivAt_of_continuous
...PhaseDisplacement_hasDerivAt_of_continuous
```

use global `Continuous` hypotheses.

Provide interval-local variants whose hypotheses are only what the finite FTC actually needs on the safe interval.

Possible forms:

```lean
∀ u ∈ uIcc σ (1 - σ), ContinuousAt rate u
```

plus interval integrability, or a `ContinuousOn` theorem together with the local neighborhood continuity derived in CS34-A/B.

Do not weaken mathematical correctness merely to simplify theorem application at endpoints.  If the interval FTC API requires a slightly different statement at endpoints, record the exact sufficient local hypotheses.

## 7. CS34-F — source-derived phase endpoint transport

Reprove the CS33 branch-free phase endpoint theorem without external `hPhase : Continuous ...`:

```text
U_X(1-σ)
  = U_X(σ) * exp(-2 i Θ_X(1-σ)).
```

The only hypotheses should be the genuine source hypotheses, ideally:

- top decomposition safety;
- fixed finite `X`;
- no sign or reach assumption.

This is still a finite ODE transport identity, not a provider theorem.

## 8. CS34-G — source-derived weighted displacement ledger

Construct a theorem that recovers the CS33 scalar mismatch ledger with all routine finite regularity hypotheses discharged from source.

Target shape:

```text
TopMismatchScalar
  = [weight endpoint × phase displacement
     + weight endpoint × amplitude displacement
     - weight-variation integral] / π.
```

Use the existing CS33 theorem internally if convenient, after constructing its hypotheses automatically.

Then also expose the amplitude endpoint substitution:

```text
AmplitudeDisplacement(1-σ)
  = (log NormSqResidual(σ) - log NormSqResidual(1-σ)) / 2.
```

The resulting theorem should no longer accept arbitrary continuity/integrability certificates for residual rates or weight derivatives.

## 9. Optional top correction regularity cleanup

If the same local analytic work makes it inexpensive, also derive the top-edge weighted zeta integrability hypothesis currently carried from CS28/CS31.

Likewise, archimedean and elementary top integrability may be discharged from factor-safety if this is straightforward.

This is optional for CS34 if it materially expands scope.  Do not delay the residual-rate regularity closure solely to remove every older technical hypothesis.

## 10. Expected classification

### Green-B

The interval-local residual regularity is source-derived and the CS33 weighted-displacement ledger can be applied without external residual-rate continuity certificates.  The only substantive frontier left is an independent weighted-displacement / scalar-reach estimate.

### Yellow

Local zeta derivative continuity cannot be obtained from the presently imported Mathlib API without a new analytic bridge.  Record the exact missing local theorem and stop there.

### Red

Any implementation that:

- assumes a global zero-free top line,
- proves or assumes global continuity of the log derivative by ignoring zeros outside the finite safe interval,
- replaces local factor safety with RH-strength zero information,
- introduces infinite Euler products or prime-series continuation across the strip,
- assumes the desired reach inequality,
- or derives RH.

## 11. Named frontier after successful CS34

If CS34 closes the technical regularity layer, the continuity gap should be discharged or retired with an exact theorem dependency.

The surviving semantic frontier should be only the reach problem, for example the existing:

```lean
PascalCenteredXiPrimeSideFiniteResidualWeightedDisplacementReachGap
```

Do not create a new equivalent predicate and count it as progress.

## 12. Validation

Run at least:

```text
lake env lean <new-CS34-file>
lake build DkMath.RH
git diff --check
```

No new `sorry`, `axiom`, or `native_decide`.

## 13. Research interpretation

The chain has now reached:

```text
finite primes
→ interaction
→ holomorphic potential
→ finite rectangle
→ Euler-renormalized residual
→ phase + amplitude rates
→ branch-free polar transport
→ weighted endpoint displacement + weight-variation remainder.
```

CS34 is deliberately not another representation layer.  It should remove the last routine analytic certificate separating the exact finite ledger from its source.

After CS34, the research frontier should be genuinely sharp:

```text
Can the source-derived weighted displacement reach the finite rectangle background?
```

That is the next place where new mathematics, rather than adapter cleanup, is required.
