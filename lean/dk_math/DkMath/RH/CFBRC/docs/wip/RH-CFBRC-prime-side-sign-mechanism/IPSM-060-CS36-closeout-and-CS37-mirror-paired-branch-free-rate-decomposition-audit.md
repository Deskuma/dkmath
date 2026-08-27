# IPSM-060 — CS36 closeout and CS37 mirror-paired branch-free rate decomposition audit

## 0. Status

- Canonical branch: `wip/RH-CFBRC-prime-side-sign-mechanism-260813-v1`
- CS36 implementation: `DkMath.RH.CFBRC.PascalCenteredXiPrimeSideFiniteResidualMirrorPairedFunctionalEquationAudit`
- CS36 verdict: **Green-B**
- Meaning of Green-B here: the finite mirror-paired functional-equation representation is exact and source-derived, while no new reach inequality, cancellation theorem, sign provider, limit exchange, or RH conclusion has been obtained.

CS36 is therefore a genuine representation advance, not a closure of the remaining prime-side frontier.

---

## 1. CS36 facts now fixed by Lean

For the top-edge ordinary coordinate

` s(u) := pascalSymmetricRectangleTopEdge u W.rectangle.T `,

CS36 proves the mirror geometry

`conj(s(1-u)) = 1 - s(u)`.

The finite Euler log potential satisfies termwise conjugation, hence its compensator and the finite Euler-renormalized zeta residual have the corresponding conjugation laws.

Define the finite symmetric potential by

`A_X^sym(s) := A_X(s) + A_X(1-s)`.

Lean proves the exact mirror invariance

`A_X^sym(1-s) = A_X^sym(s)`.

The CS35 mirror pair has the exact finite factorization

`PairF_X(u) = ζ(s(u)) * ζ(1-s(u)) * exp(-A_X^sym(s(u)))`.

No infinite Euler product is used here. `A_X` is the finite prime-power potential already introduced in CS30.

For nonzero `s` and `1-s`, Lean also proves the installed completed-zeta fold

`ζ(s) * ζ(1-s) = completedRiemannZeta(s)^2 / (Γℝ(s) * Γℝ(1-s))`.

Thus the paired residual admits the exact completed representation

`PairF_X(u) = (completedRiemannZeta(s(u))^2 / (Γℝ(s(u)) * Γℝ(1-s(u)))) * exp(-A_X^sym(s(u)))`.

On the safe top interval, the paired residual remains nonzero. At the center `u = 1/2`, the CS35 representation remains consistent:

`PairF_X(1/2) = normSq(F_X(1/2))`,

and its real part is strictly positive.

The exponential compensator is nonzero pointwise.

### Strength firewall

The appearance of `completedRiemannZeta(s)^2` is a complex square identity only. It does **not** imply positivity or order.

CS36 does not prove:

- a sign for the paired rate;
- a sign for the scalar density;
- a reach estimate;
- cancellation with the rectangle background;
- an infinite Euler-product identity;
- any exchange of cutoff limits with contour or interval integrals;
- RH.

The explicit frontier remains

`PascalCenteredXiPrimeSideFiniteResidualMirrorFunctionalEquationReachGap.no_independent_paired_functional_equation_reach_estimate`.

---

## 2. Existing derivative source that CS37 must reuse

Do not rebuild the finite Euler derivative layer.

CS30 already proves:

1. `pascalCenteredXiPrimeSideFiniteEulerLogPotential_hasDerivAt`

   The finite Euler potential has derivative `-pascalPrimePowerPHZFiniteUpTo X s`.

2. `pascalCenteredXiPrimeSideFiniteEulerCompensator_hasDerivAt`

   The compensator derivative is the finite PHZ factor times the compensator.

3. `pascalCenteredXiPrimeSideFiniteEulerCompensator_logDeriv`

   The compensator log derivative is exactly the finite PHZ sum.

4. `pascalCenteredXiPrimeSideFiniteEulerRenormalizedZetaResidual_negLogDeriv`

   At a safe ordinary-zeta point,

   `-logDeriv(residual_X)(s) = pascalXiOrdinaryZetaNegLogDeriv(s) - pascalPrimePowerPHZFiniteUpTo X s`.

CS34 then upgrades the residual rate to interval-local continuity on the safe finite top interval.

Therefore CS37 should not introduce an abstract finite-prime derivative provider. The finite prime rate is already source-derived.

---

## 3. CS37 target

Suggested module:

`DkMath.RH.CFBRC.PascalCenteredXiPrimeSideFiniteResidualMirrorPairedBranchFreeRateAudit`

The goal is to differentiate the exact CS36 completed factorization and identify it with the exact CS35 mirror-pair ODE.

CS35 already supplies

`PairF_X'(u) = -PairQ_X(u) * PairF_X(u)`.

CS37 should obtain an exact branch-free decomposition of `PairQ_X` into the rates of the actual CS36 factors.

The desired structure is schematically

`paired residual rate = completed-zeta contribution + Gamma-pair contribution + finite symmetric Euler contribution`,

with all signs and chain-rule factors determined by Lean from the concrete definitions.

Do **not** hard-code a guessed final sign pattern before the derivative calculation is complete, especially because differentiation of the reflected argument `1-s(u)` contributes a minus sign.

---

## 4. CS37-A — branch-free product-rate algebra

Avoid `Complex.log` and all logarithm-branch arguments.

Work only with:

- `HasDerivAt` / `DifferentiableAt`;
- `deriv`;
- multiplication, inversion and division at proven nonzero points;
- the existing `logDeriv` definition where its nonzero hypotheses are explicit.

A small generic helper is acceptable if useful:

If a nonzero function satisfies `F' = -Q * F`, and the same `F` is represented as a finite product of differentiable nonzero factors, solve algebraically for `Q` from the product derivative.

This helper must be pure differential algebra; it must not contain a hidden sign or reach hypothesis.

---

## 5. CS37-B — use an inverse-Gamma product form

For differentiation, prefer rewriting the completed representation as a product

`completedRiemannZeta(s)^2 * (Γℝ(s))⁻¹ * (Γℝ(1-s))⁻¹ * exp(-A_X^sym(s))`.

This is preferable to differentiating a large quotient directly and avoids introducing a complex logarithm of `Γℝ`.

Before using division by any completed or Gamma factor, prove the required pointwise nonvanishing from the actual safe assumptions and the CS36 nonzero product where possible.

Do not add a new structure whose field simply assumes all desired factors are nonzero if those facts can be extracted from the existing safe product.

---

## 6. CS37-C — completed-zeta local rate

There is no pre-existing DkMath `CompletedZetaLogDerivBridge` on the current v1 branch. CS37 must construct the needed local rate from the installed Mathlib completed-zeta differentiability/analyticity facts and the exact CS36 factorization.

A local branch-free quantity of the form

`deriv completedRiemannZeta s / completedRiemannZeta s`

is acceptable only after `completedRiemannZeta s ≠ 0` is proved at the point under consideration.

Prefer theorem statements that carry the nonzero hypothesis explicitly rather than globalizing it.

The functional equation is already encoded at value level by CS36. CS37's task is the derivative/rate level, not to re-prove the functional equation.

---

## 7. CS37-D — symmetric finite Euler rate

Differentiate

`A_X^sym(s) = A_X(s) + A_X(1-s)`

using the CS30 finite Euler derivative theorem.

This should produce a completely finite reflected PHZ combination. Let Lean determine the exact reflected sign from the chain rule.

Then differentiate

`exp(-A_X^sym(s))`

and record its exact branch-free product rate.

This is the prime-side term that should later be compared with the CS35 paired rate channels.

No infinite prime sum or Euler-product passage is permitted.

---

## 8. CS37-E — identify with the CS35 paired rate

At a safe half-interval point, combine:

- CS35 `PairF' = -PairQ * PairF`;
- CS36 completed product representation;
- nonvanishing of `PairF`;
- the completed factor derivative;
- inverse-Gamma factor derivatives;
- the finite symmetric Euler derivative.

Cancel the common nonzero `PairF` and prove one exact theorem giving the paired rate in terms of those concrete factors.

This is the principal CS37 deliverable.

After the complex identity is proved, project it to real and imaginary channels only if the projections are useful and remain exact.

Recall the CS35 channel meanings:

- real paired-rate channel: amplitude-decay difference across the mirror;
- imaginary paired-rate channel: phase-decay sum across the mirror.

A real/imag theorem is valuable if it exposes a concrete cancellation or isolates a finite prime term. It is not required merely for cosmetic expansion.

---

## 9. CS37-F — compare with the rectangle correction ledger

Only **after** the exact paired-rate decomposition is proved, compare its Gamma / completed / elementary pieces with the already existing finite rectangle ledger.

Audit these existing source families:

- archimedean correction;
- elementary correction;
- top-horizontal / top-companion contribution;
- finite rectangle background.

There are exactly three acceptable outcomes:

1. **Exact cancellation found** — prove the cancellation theorem.
2. **Partial common structure found** — state the exact surviving remainder.
3. **No useful exact cancellation** — record this cleanly and retain the frontier.

Do not name a theorem `cancellation` unless an algebraic cancellation has actually been proved.

---

## 10. CS37-G — frontier and verdict rules

### Green-B

Use **Green-B** if CS37 obtains a concrete exact branch-free rate decomposition from the actual CS35/CS36/CS30 sources, even if no sign or reach estimate follows.

This is genuine source progress because the value-level functional-equation representation has been lifted to a differential/rate-level identity.

### Yellow

Use **Yellow** if CS37 only introduces an abstract differentiability/rate provider or a structure that assumes the desired decomposition without instantiating it from the concrete completed-zeta, Gamma and finite Euler factors.

### Green

A stronger **Green** requires an actual new load-bearing estimate or cancellation that reduces the remaining reach frontier without importing the zero-side/RH conclusion.

---

## 11. Hard firewalls

CS37 must not:

- infer positivity from `completedRiemannZeta(s)^2`;
- infer a sign from `Λ(n) ≥ 0`;
- assume monotonicity of the finite prime interaction;
- introduce an infinite Euler product;
- exchange `X → ∞` with an interval or contour integral;
- use the fixed-second-moment/RH equivalence as a prime-side provider;
- use an off-critical-zero exclusion theorem to prove the prime-side rate estimate;
- use `Complex.log` to define a global phase or logarithmic branch;
- assert Gamma/background cancellation before an exact identity proves it;
- hide the remaining reach estimate inside a provider structure;
- introduce a CF2D collision/assimilation provider before the ordinary complex rate identity is exact.

---

## 12. Conceptual interpretation after CS36

The finite mirror pair is no longer merely a conjugate pairing trick. It now has two simultaneously exact descriptions:

- **dynamical description:** center-normalized nonzero carrier governed by the CS35 paired ODE;
- **functional-equation description:** completed-zeta square times explicit Gamma and finite Euler compensator factors.

CS37 asks whether these two descriptions yield a useful exact decomposition of the rate.

This is precisely the correct place to test for a genuine source cancellation. If no cancellation appears, the negative result is still informative because it prevents replacing the remaining reach problem by another equivalent provider contract.
