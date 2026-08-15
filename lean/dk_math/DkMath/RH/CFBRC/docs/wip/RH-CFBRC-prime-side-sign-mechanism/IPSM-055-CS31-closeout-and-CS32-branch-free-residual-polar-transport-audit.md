# IPSM-055 — CS31 closeout and CS32 branch-free residual polar-transport audit

## 0. Status

Branch: `wip/RH-CFBRC-prime-side-sign-mechanism-260813-v1`

CS31 verdict: **Green-B**.

CS31 has proved, at fixed finite `ε`, residue window `W`, and cutoff `X`:

- continuity and interval-integrability of the finite PHZ top path,
- automatic discharge of the CS30 finite `hPHZ` hypothesis,
- the exact residual log-rate
  `q_X(u) = -logDeriv R_X(u+iT)`,
- amplitude rate `A_X = Re q_X`,
- phase rate `P_X = Im q_X`,
- exact scalar-density splitting into phase and amplitude channels,
- exact scalar mismatch as the sum of the two channel integrals,
- channel-form radial-contact reach,
- branch-free cumulative amplitude/phase displacements based at `σ`,
- countermodels showing that no sign of either channel follows from the sign/reach of their sum.

The remaining semantic bridge is not a missing sign lemma.  It is the link from the rates/displacements back to the nonzero residual function itself.

## 1. CS32 objective

Build a **branch-free polar transport** for the finite Euler-renormalized zeta residual on the safe top edge.

Do not use:

- `Complex.arg`,
- a principal logarithm of the complex residual,
- a square-root normalization `R / |R|` unless it is independently justified,
- an infinite Euler product,
- any sign assumption for the phase or amplitude channel,
- the zero-side fixed defect or RH as a provider.

Use only the already-proved finite residual and its top-edge nonvanishing.

## 2. CS32-A — residual top path and nonvanishing

Introduce a short top-path abbreviation if useful:

```lean
F_X(u) := pascalCenteredXiPrimeSideFiniteEulerRenormalizedZetaResidual X
  (pascalSymmetricRectangleTopEdge u W.rectangle.T)
```

From `IsPascalCenteredXiTopLogDerivDecompositionSafe W`, prove on the full unoriented top interval

```text
u ∈ uIcc σ (1-σ) -> F_X(u) ≠ 0.
```

Also expose a path derivative theorem.  Since the top-edge path has derivative `1`, the derivative of `F_X` with respect to `u` should be the ordinary complex derivative of the residual at the same top-edge point.

Prefer a reusable `HasDerivAt` theorem.

## 3. CS32-B — amplitude carrier by `normSq`

Define the real amplitude carrier

```lean
N_X(u) := Complex.normSq (F_X(u)).
```

Prove on the safe top edge:

```text
0 < N_X(u).
```

Then prove the exact differential identity

```text
N_X'(u) = -2 * A_X(u) * N_X(u).
```

Equivalently, where convenient,

```text
A_X(u) = -(1/2) * N_X'(u) / N_X(u).
```

This should be derived from

```text
q_X(u) = -F_X'(u) / F_X(u)
```

and the elementary derivative of `normSq`; do not introduce a logarithm branch of `F_X`.

## 4. CS32-C — real logarithmic amplitude bridge

Because `N_X(u) > 0`, `Real.log (N_X(u))` is an ordinary real logarithm with no branch issue.

Prove

```text
(d/du) Real.log (N_X(u)) = -2 * A_X(u).
```

This discharges the CS31 amplitude semantic gap in a stronger and cleaner form than differentiating `log |F_X|` directly.

Then, under only the finite interval-integrability/continuity hypotheses actually required by the pinned FTC API, prove the endpoint displacement identity

```text
AmplitudeDisplacement_X(u)
  = -(1/2) * (Real.log (N_X(u)) - Real.log (N_X(σ))).
```

In particular at the top-left endpoint `1-σ`:

```text
AmplitudeDisplacement_X(1-σ)
  = (1/2) * (Real.log (N_X(σ)) - Real.log (N_X(1-σ))).
```

Respect the existing `σ -> 1-σ` orientation.

## 5. CS32-D — branch-free phase carrier

Define the unit phase carrier without `arg` and without a square root:

```lean
U_X(u) := F_X(u) / starRingEnd ℂ (F_X(u)).
```

On the safe top edge, prove:

```text
Complex.normSq (U_X(u)) = 1.
```

Then prove the exact differential transport equation

```text
U_X'(u) = (-2 * Complex.I * P_X(u)) * U_X(u).
```

The sign must be derived, not guessed.  With the current convention

```text
q_X = -F_X'/F_X,
P_X = Im q_X,
```

the expected sign is the one displayed above.

This is the branch-free phase analogue of the amplitude-carrier equation.

## 6. CS32-E — phase displacement transport

Reuse the CS31 branch-free displacement

```text
Theta_X(u) := integral from σ to u of P_X(v) dv.
```

Do not identify `Theta_X` with `Complex.arg F_X`.

If the required continuity/FTC hypotheses can be proved from the finite safe-top source, prove

```text
U_X(u) = U_X(σ) * Complex.exp (-2 * Complex.I * Theta_X(u)).
```

A robust route is to prove that

```text
u |-> U_X(u) * Complex.exp (2 * Complex.I * Theta_X(u))
```

has derivative zero on the safe interval and hence is constant.

If the available Mathlib interval-FTC API makes this disproportionately expensive, stop after the exact ODE and keep the endpoint transport as a named finite analytic gap.  Do not weaken it by assuming a phase branch.

## 7. CS32-F — paired carrier interpretation

Record the finite pair

```text
Amplitude carrier : N_X(u) > 0
Phase carrier     : U_X(u), normSq U_X(u) = 1
```

with transport laws

```text
N_X' = -2 A_X N_X,
U_X' = -2 i P_X U_X.
```

This is the exact branch-free polar decomposition of the **rates**, not a claim that the residual itself has been written with a globally chosen polar angle.

If useful, package the two equations into a small structure used only as an audit ledger.  Do not make the structure a provider hypothesis for the desired reach inequality.

## 8. CS32-G — strength firewall

Prove/record explicitly that these transport identities do **not** imply:

- `A_X >= 0`,
- `P_X >= 0`,
- either channel integral is nonnegative,
- the total scalar mismatch reaches the rectangle background,
- radial contact,
- endpoint defect sign,
- RH.

No provider may simply assume any of these conclusions.

## 9. Optional automatic regularity

CS31 still accepts several interval-integrability hypotheses for the residual-rate and channel densities.

If the existing safe-top/nonzero residual API is enough to prove continuity or interval-integrability of

```text
q_X,
A_X,
P_X,
phase-channel density,
amplitude-channel density,
```

then discharge those hypotheses here.

This is useful but secondary.  Do not create a large detour into analytic regularity if the pinned zeta derivative API makes it nonlocal; preserve a narrow named gap instead.

## 10. Expected theorem shapes

Names are suggestions only; preserve repository naming conventions.

```lean
theorem ...ResidualTopPath_ne_zero ...

theorem ...ResidualNormSq_pos ...

theorem ...ResidualNormSq_hasDerivAt ...

theorem ...AmplitudeRate_eq_neg_half_log_normSq_deriv ...

theorem ...AmplitudeDisplacement_eq_log_normSq_endpoint ...

theorem ...ResidualPhaseCarrier_normSq ...

theorem ...ResidualPhaseCarrier_hasDerivAt ...

theorem ...ResidualPhaseCarrier_eq_base_mul_exp_phaseDisplacement ...
```

Keep exact signs and factors `2` under audit.

## 11. Named frontier

If only the pointwise carrier equations close, a suitable remaining frontier is:

```lean
inductive PascalCenteredXiPrimeSideFiniteResidualPolarTransportGap : Prop
  | no_independent_phase_endpoint_transport_or_reach_estimate
```

If phase endpoint transport also closes, narrow the gap further to the actual unresolved weighted reach estimate.  Do not retain obsolete semantic gaps that are genuinely discharged by exact theorems.

## 12. Next step after CS32

Once the displacements are exact residual quantities, the next likely audit is **finite integration by parts** for the weighted channel integrals:

```text
∫ Re(h) * P
and
∫ Im(h) * A.
```

Using `Theta' = P` and `D' = A`, these can be rewritten as

```text
boundary displacement term
- integral(weight derivative * displacement).
```

That would separate the scalar mismatch into:

1. endpoint phase/amplitude displacement,
2. a finite weight-variation remainder.

Do not perform this integration-by-parts step in CS32 unless the carrier bridge closes cleanly first.

## 13. Verdict criteria

### Green

Both carrier ODEs and endpoint displacement transports close from the finite safe-top residual, with no new provider hypothesis.

### Green-B

The exact branch-free amplitude bridge and phase-carrier ODE close, while the independent weighted reach estimate remains a named gap.  This is the expected outcome.

### Yellow

Only definitions are added or the phase transport requires a hidden branch choice / stronger assumption not justified by the current source.

### Red

Any implementation that introduces `Complex.arg` as a global branch, assumes channel signs, uses an infinite Euler product, exchanges limits, imports the zero-side fixed-defect theorem as the provider, or concludes RH.

## 14. Validation

Run at least:

```text
lake env lean <new-CS32-file>
lake build DkMath.RH
git diff --check
```

No new `sorry`, `axiom`, or `native_decide`.

## 15. Research interpretation

CS25 removed the common carrier and exposed interaction only.
CS30 compressed the top mismatch into one finite Euler-renormalized residual.
CS31 split the residual scalar effect into amplitude and phase rates.

CS32 should now show that those rates are not arbitrary bookkeeping variables:

```text
residual
  -> normSq carrier + unit phase carrier
  -> amplitude rate + phase rate
  -> branch-free displacements.
```

The expected structure is therefore not a sign theorem but a finite transport law.  Only after that transport is exact should the project ask whether the weighted combined displacement reaches the finite rectangle background.
