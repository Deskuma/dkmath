# IPSM-043 — CS19 closeout and CS20 monotonicity-strength / terminal-ceiling audit

## Status

CS19 is accepted as **Green-B** on branch
`wip/RH-CFBRC-prime-side-sign-mechanism-260813-v1`.

The implementation now proves, at fixed positive `ε` and a fixed residue-transport window `W`:

1. the aggregate energy imbalance is exactly four times the finite von-Mangoldt mode sum;
2. cutoff differences of the imbalance are exactly four times finite prime-block projections;
3. tail-projection differences are exactly the same imbalance increments;
4. the finite tail projection tends to zero as `X → ∞` by transport from the already-authorized fixed-`ε` arithmetic approximant convergence;
5. monotonicity of the imbalance implies nonnegativity of every finite tail projection;
6. `F(0)=0`, so monotonicity also implies absolute nonnegativity of the imbalance;
7. no independent cutoff-monotonicity provider is asserted.

No infinite sum/integral exchange, endpoint sign theorem, fixed-defect RH argument, or RH conclusion is introduced.

---

## Why CS20 is a strength audit before attempting the provider

Write

```text
F(X) = pascalCenteredXiPrimeSideAggregateRayEnergyImbalance ε W X
P(X) = pascalCenteredXiPrimeSideFiniteTailProjection ε W X.
```

CS19 proves

$$
4(P(X)-P(Y))=F(Y)-F(X).
$$

It is tempting to attack `Monotone F` directly.  Before doing that, CS20 must determine how strong this condition really is.

Because `F(X)` is a cumulative natural-mode sum, an adjacent cutoff adds only the new natural label `X+1`.  Therefore the expected adjacent increment is

$$
F(X+1)-F(X)
=4\,\Lambda(X+1)K_{\varepsilon,W}(X+1).
$$

If this exact identity is proved, global cutoff monotonicity is essentially a per-mode nonnegativity requirement on every positive prime-power mode.  That would be much stronger than the aggregate cancellation mechanism that motivated CS17.

CS20 must therefore classify monotonicity rather than silently assume that it is the natural remaining provider.

---

## CS20-A — exact adjacent increment

Prove the one-step specialization of the CS19 block identity directly from the cumulative mode sum or by specializing the existing block theorem.

Suggested target shape:

```lean
F (X + 1) - F X =
  4 * (ArithmeticFunction.vonMangoldt (X + 1) : ℝ) *
    pascalCenteredXiPrimeSideFiniteModeKernel ε W (X + 1)
```

The exact associativity/parenthesization may be adjusted for Lean.

Also expose the corresponding adjacent block projection identity:

```lean
pascalCenteredXiPrimeSideFinitePrimeBlockProjection ε W X (X + 1) =
  (ArithmeticFunction.vonMangoldt (X + 1) : ℝ) *
    pascalCenteredXiPrimeSideFiniteModeKernel ε W (X + 1).
```

This is finite and algebraic.

---

## CS20-B — monotonicity versus adjacent increments

Package the standard natural-number fact that `Monotone F` is equivalent to nonnegativity of every adjacent increment.

An explicit induction proof is acceptable if the pinned Mathlib theorem name is inconvenient.

Target classification:

```text
Monotone F
↔ ∀ X, 0 ≤ F(X+1)-F(X)
↔ ∀ X, 0 ≤ Λ(X+1) * K(X+1).
```

Do not infer the final sign yet.

---

## CS20-C — prime-power specialization

Reuse the existing canonical prime-power / von-Mangoldt bridge.

For a positive prime-power label

```text
q = p^j,
Nat.Prime p,
0 < j,
```

we already have

```text
Λ(q) = log p
```

and `log p > 0`.

Therefore prove the local equivalence

```text
0 ≤ Λ(q) * K(q) ↔ 0 ≤ K(q)
```

for positive prime-power `q`.

For non-prime-power labels, prove or reuse `Λ(q)=0`, so the adjacent increment is zero.

The desired strength classification is conceptually

```text
Monotone F
↔ every positive prime-power mode kernel is nonnegative.
```

An equivalent witness-based statement is acceptable if quantifying over `IsPrimePowerLabel` is easier.

This theorem is important even if it shows that the CS19 monotonicity route is too strong.

---

## CS20-D — do not confuse aggregate cancellation with adjacent positivity

CS17 was deliberately designed to allow cancellation across prime-power rays through the aggregate energy ledger.

If CS20-C succeeds, full natural-cutoff monotonicity removes most of that freedom: at a prime-power cutoff the new term must itself have the correct sign.

This should be recorded explicitly as a strength result, not treated as a failure.

No theorem should claim that the mode kernel is nonnegative unless a genuinely source-derived proof is found.

If no such proof exists, keep a named gap such as

```lean
inductive PascalCenteredXiPrimeSideAdjacentPrimePowerModeSignGap : Prop
  | noIndependentPositivePrimePowerModeKernelProvider
```

or reuse the existing monotonicity gap with a theorem showing its equivalent strength.

---

## CS20-E — terminal imbalance exists without monotonicity

Now exploit the already-proved tail convergence instead of monotonicity.

CS19 gives

$$
4(P(X)-P(Y))=F(Y)-F(X)
$$

and

$$
P(Y)\to0.
$$

For each fixed `X`, prove

$$
F(Y)\to F(X)+4P(X).
$$

Then specialize to `X=0` and use `F(0)=0` to obtain a canonical terminal value.

Suggested definition:

```lean
noncomputable def pascalCenteredXiPrimeSideAggregateRayEnergyTerminal
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow) : ℝ :=
  4 * pascalCenteredXiPrimeSideFiniteTailProjection ε W 0
```

Target theorem:

```lean
Tendsto
  (pascalCenteredXiPrimeSideAggregateRayEnergyImbalance ε W)
  atTop
  (nhds (pascalCenteredXiPrimeSideAggregateRayEnergyTerminal ε W)).
```

This terminal value is defined from the already finite-source tail projection at cutoff zero.  It is not an infinite prime sum definition.

---

## CS20-F — exact terminal ceiling identity

Use uniqueness of limits, or an equivalent limit argument, to prove the exact identity for every finite cutoff:

$$
4P(X)=F_\infty-F(X).
$$

In repository notation:

```text
4 * FiniteTailProjection ε W X
  = AggregateRayEnergyTerminal ε W
      - AggregateRayEnergyImbalance ε W X.
```

This is the key CS20 reduction.

Then prove both sign adapters:

```text
0 ≤ P(X) ↔ F(X) ≤ F∞
P(X) ≤ 0 ↔ F∞ ≤ F(X).
```

The first equivalence is the desired **terminal ceiling** formulation.

---

## CS20-G — monotonicity is sufficient but not required

Recover the CS19 result as a corollary:

```text
Monotone F → ∀ X, F(X) ≤ F∞ → ∀ X, 0 ≤ P(X).
```

The important logical distinction is:

```text
full cutoff monotonicity
  ⇒ terminal ceiling
  ⇔ finite tail projection nonnegative.
```

The reverse implication from terminal ceiling to monotonicity must not be asserted.

The terminal ceiling permits oscillation below the limiting level and therefore preserves genuine aggregate cancellation.

---

## CS20-H — source frontier after the strength audit

If no independent theorem proves the terminal ceiling, record a new named frontier, for example:

```lean
inductive PascalCenteredXiPrimeSideAggregateTerminalCeilingGap : Prop
  | noIndependentAggregateTerminalCeilingProvider
```

This frontier is preferable to treating monotonicity as the only possible provider.

The future sign problem should then be stated as:

```text
for every finite cutoff X,
F(X) does not overshoot its source-derived terminal value F∞.
```

This is a strictly more flexible target than requiring every prime-power increment to be nonnegative.

---

## Optional CS20-I — identify the terminal source without changing its logic

If it is easy and source-derived, identify `F∞ = 4 P(0)` with the existing cutoff-zero right-edge source.

At cutoff zero, the finite PHZ contribution vanishes, so the tail is the ordinary-zeta right-edge negative log-derivative source.  Any such identification must reuse existing CS10/CS11/CS12 source identities.

Do not introduce a new infinite Euler product or interchange an infinite sum with the interval integral.

This optional identification may make the future terminal-ceiling problem more recognizable analytically.

---

## Firewall

CS20 must not use any of the following as a hidden sign provider:

1. fixed-Xi defect nonnegativity;
2. horizontal-energy nonnegativity;
3. the RH-equivalent fixed-defect vanishing theorem;
4. a per-mode sign assumption disguised as aggregate monotonicity;
5. an infinite prime-ray expansion without a certified interchange;
6. CF2D collision without the exact same-flow / same-filter / same-target assimilation hypotheses.

The CF2D bridge from CS18 remains a structural identification only.

---

## Green criteria

CS20 is Green-B if it closes all of the following:

1. exact adjacent cutoff increment;
2. monotonicity classification through adjacent increments;
3. prime-power specialization showing the strength of monotonicity;
4. fixed-`ε` convergence of `F(X)` to a named terminal value;
5. exact identity `4 P(X) = F∞ - F(X)`;
6. tail-sign iff terminal-ceiling equivalence;
7. monotonicity recorded only as a sufficient stronger condition;
8. any still-missing terminal-ceiling provider left as a named gap.

A result showing that full cutoff monotonicity is too strong is a successful audit outcome, not a failure.

No endpoint sign theorem or RH conclusion is authorized in this checkpoint.
