# IPSM-056 — CS32 closeout and CS33 phase-endpoint / weighted-displacement audit

## 0. Status

Branch: `wip/RH-CFBRC-prime-side-sign-mechanism-260813-v1`

CS32 verdict: **Green-B**.

CS32 has now source-derived, on the safe finite top edge:

- the residual top path `F_X(u)` is nonzero,
- `F'_X = -q_X F_X`,
- the amplitude carrier `N_X = normSq F_X` is strictly positive,
- `N'_X = -2 A_X N_X`,
- `d/du log N_X = -2 A_X`,
- the full amplitude displacement is an endpoint log-ratio,
- the branch-free phase carrier `U_X = F_X / star F_X` has `normSq U_X = 1`,
- `U'_X = -2 i P_X U_X`,
- `U_X * star U_X = 1`.

No phase endpoint exponential identity, no channel sign, no reach provider, no infinite exchange, and no RH conclusion has been introduced.

## 1. CS33 objective

The next goal is not a sign theorem.

The goal is to finish the finite transport semantics of the CS31/CS32 channels and then move the scalar mismatch from a **rate integral** to an exact

```text
endpoint displacement + finite weight-variation remainder
```

representation.

This should be done without `Complex.arg`, without a logarithm branch for the complex residual, and without an infinite Euler product.

## 2. CS33-A — top-edge regularity of the residual rates

Before integrating the phase ODE, audit the minimum regularity required for

```lean
pascalCenteredXiPrimeSideFiniteResidualPhaseDecayRate X W
pascalCenteredXiPrimeSideFiniteResidualAmplitudeDecayRate X W
```

on the safe top interval.

Preferred result:

```text
ContinuousOn P_X [σ, 1-σ]
ContinuousOn A_X [σ, 1-σ]
```

or a stronger convenient finite statement.

Use only source-derived finite regularity:

- the top path `u ↦ u + iT`,
- finite PHZ continuity,
- ordinary zeta regularity away from `s = 1`,
- top factor-safety, especially `ζ(s) ≠ 0`,
- the finite Euler compensator.

If Mathlib does not expose the needed continuity of `deriv riemannZeta` in a directly reusable form, do not insert it as an axiom. Record the precise regularity gap and retain conditional downstream adapters.

## 3. CS33-B — derivative of the branch-free displacement functions

For the existing CS31 definitions

```text
D_X(u) = ∫_σ^u A_X(v) dv
Θ_X(u) = ∫_σ^u P_X(v) dv,
```

prove, under the regularity established in CS33-A,

```text
D'_X(u) = A_X(u),
Θ'_X(u) = P_X(u)
```

on the appropriate interior / interval form.

Keep the already-proved basepoint identities

```text
D_X(σ) = 0,
Θ_X(σ) = 0.
```

## 4. CS33-C — phase carrier conserved gauge

Define the gauge-corrected phase carrier

```text
C_X(u) := U_X(u) * exp(2 i Θ_X(u)).
```

Using

```text
U'_X = -2 i P_X U_X
```

and

```text
Θ'_X = P_X,
```

prove that `C'_X(u) = 0` on the safe top interval.

Then prove finite interval constancy and obtain

```text
U_X(u) = U_X(σ) * exp(-2 i Θ_X(u)).
```

In particular at the reflected endpoint `b = 1 - σ`:

```text
U_X(b) = U_X(σ) * exp(-2 i Θ_X(b)).
```

This is the desired branch-free phase endpoint transport.

Do not rewrite this with `Complex.arg`.

### Important semantic point

Because `U_X = F_X / conj(F_X)`, it carries twice the ordinary phase. Therefore the factor `2` in the exponential is structural, not a normalization accident.

## 5. CS33-D — amplitude endpoint transport remains source-derived

Retain the CS32 theorem

```text
D_X(b)
  = (log N_X(σ) - log N_X(b)) / 2.
```

Optionally add equivalent forms such as

```text
N_X(b) = N_X(σ) * exp(-2 D_X(b))
```

if they follow cleanly from real exponential/log identities and strict positivity of `N_X`.

No square root or complex logarithm is needed.

## 6. CS33-E — name the top Mellin weight channels

Let

```text
H_{ε,W}(u)
  := pascalCenteredXiMellinSecondDifferenceWeight ε 0
       (pascalOrdinaryToCentered
         (pascalSymmetricRectangleTopEdge u W.rectangle.T)).
```

Define or locally abbreviate

```text
wP(u) := Re H_{ε,W}(u),
wA(u) := Im H_{ε,W}(u).
```

Prove the real differentiability / interval regularity needed for integration by parts.

Prefer to expose derivatives as source-derived functions. If the current Mellin weight definition makes a clean explicit derivative formula available, prove it as a bonus; otherwise do not manufacture one merely for presentation.

## 7. CS33-F — phase-channel integration by parts

Starting from the exact CS31 phase channel

```text
∫_σ^b wP(u) P_X(u) du,
```

and `P_X = Θ'_X`, prove the finite identity

```text
∫_σ^b wP P_X
  = wP(b) * Θ_X(b)
    - ∫_σ^b wP'(u) * Θ_X(u) du,
```

where `b = 1 - σ` and the lower endpoint term vanishes because `Θ_X(σ) = 0`.

Use a generic integration-by-parts theorem or prove a small reusable finite lemma if that is cleaner in Lean.

## 8. CS33-G — amplitude-channel integration by parts

Likewise prove

```text
∫_σ^b wA A_X
  = wA(b) * D_X(b)
    - ∫_σ^b wA'(u) * D_X(u) du,
```

using `D_X(σ) = 0`.

Then substitute the CS32 endpoint theorem

```text
D_X(b)
  = (log N_X(σ) - log N_X(b)) / 2.
```

This turns the amplitude endpoint contribution into an explicit residual norm-square ratio.

## 9. CS33-H — exact scalar mismatch displacement ledger

Combine CS31 with CS33-F/G to prove an exact identity of the form

```text
MismatchScalar
  = (1 / π) * (
      wP(b) * Θ_X(b)
      + wA(b) * D_X(b)
      - ∫_σ^b (wP' * Θ_X + wA' * D_X))
```

with the exact repository normalization and parentheses checked by Lean.

Then provide a second form with the amplitude endpoint log-ratio substituted.

The expected conceptual decomposition is:

```text
scalar mismatch
  = phase endpoint displacement
    + amplitude endpoint displacement
    - finite weight-variation remainder.
```

This is an identity only. No sign is inferred.

## 10. CS33-I — reach classification in displacement form

Combine the CS30 reach theorem

```text
G <= 0  iff  Background <= MismatchScalar
```

with the CS33 displacement ledger.

The result should expose the exact finite provider frontier as a lower-bound problem for

```text
phase endpoint
+ amplitude endpoint
- weight-variation remainder.
```

Do not create a theorem that simply assumes this lower bound and calls it an independent provider. Conditional adapter lemmas are acceptable only when explicitly labeled as such.

## 11. Optional mirror audit

Only after the displacement ledger is exact, inspect whether the centered top-edge reflection

```text
u ↦ 1 - u
```

induces useful exact relations for

```text
H_{ε,W}, N_X, U_X, D_X, Θ_X.
```

Do not assume a residual functional equation. The finite Euler compensator does not automatically inherit the Xi functional equation.

Any mirror theorem must be proved from the actual residual definition.

## 12. Firewall

CS33 must not:

- use `Complex.arg`,
- choose a complex logarithm branch for `F_X`,
- assume `A_X >= 0` or `P_X >= 0`,
- infer either channel sign from their sum,
- assume the scalar mismatch is small or positive,
- assume the displacement ledger reaches the background,
- expand the top residual as an infinite prime series,
- exchange an infinite sum and an integral,
- use the zero-side fixed defect / horizontal energy as a prime-side provider,
- conclude RH.

## 13. Expected verdicts

### Green

The endpoint/displacement ledger yields a genuinely new source-derived lower bound or cancellation estimate beyond pure identities.

### Green-B

The phase endpoint exponential transport and the exact integration-by-parts displacement ledger close, but no independent reach estimate is obtained.

### Yellow

The polar ODE is exact, but a needed finite regularity / FTC bridge is unavailable in the current Mathlib API. Record the precise minimal regularity contract and keep all resulting lemmas conditional.

### Red

Any proof introduces a hidden phase branch, a channel sign assumption, an infinite top-edge prime expansion, or an RH-equivalent provider.

## 14. Named frontier

If only the finite identities close, keep a narrow named frontier such as

```lean
inductive PascalCenteredXiPrimeSideFiniteResidualWeightedDisplacementReachGap : Prop
  | no_independent_weighted_displacement_reach_estimate
```

If phase endpoint transport itself remains blocked by regularity, keep a separate technical gap rather than merging it with the reach gap.

## 15. Validation

Run at least:

```text
lake env lean <new-CS33-file>
lake build DkMath.RH
git diff --check
```

No new `sorry`, `axiom`, or `native_decide`.

## 16. Research interpretation

The prime-side chain has now reduced the finite radial-contact problem through the following exact transformations:

```text
finite radial deficit
→ common-carrier cancellation
→ interaction
→ finite phase boundary
→ holomorphic potential
→ finite top mismatch
→ Euler-renormalized zeta residual
→ phase/amplitude rates
→ branch-free polar carriers.
```

CS33 should perform the next compression:

```text
rate channels
→ endpoint displacements
  + finite weight-variation remainder.
```

Only after that compression is exact should a new sign/reach mechanism be sought.
