# IPSM-044 — CS20 closeout and CS21 good-cutoff / cofinal finite-anchor audit

## Status

CS20 is accepted as **Green-B**.

The natural-cutoff monotonicity route has now been classified exactly:

- the adjacent imbalance increment is the single new von-Mangoldt mode;
- monotonicity of the aggregate imbalance is equivalent to nonnegativity of every adjacent weighted mode;
- on prime powers, because `Λ(p^j) = log p > 0`, this is equivalent to nonnegativity of every prime-power mode kernel;
- therefore cutoff monotonicity is substantially stronger than the aggregate cancellation problem we intended to preserve;
- the weaker terminal identity is exact:

```text
4 * Pε,X = F∞(ε) - Fε(X),
```

and hence

```text
0 ≤ Pε,X ↔ Fε(X) ≤ F∞(ε).
```

The terminal ceiling remains only a reformulation of the tail sign.  It is not yet an independent provider.

The next checkpoint should weaken the provider surface again.  A universal sign for every cutoff is not logically necessary for the endpoint upper-envelope goal.

---

## CS21 objective

Return to the exact CS12 defect/tail identity

```text
Dε,X - Dε,∞ = (2 / π) * Pε,X.
```

The endpoint can therefore be bounded without knowing the sign of `Pε,X`:

```text
Dε,∞ ≤ Dε,X + (2 / π) * |Pε,X|.
```

For every fixed positive `ε`, CS19 already proves

```text
Pε,X → 0  as X → ∞.
```

Therefore the prime-side target does **not** require

```text
∀ X, 0 ≤ Pε,X
```

or monotonicity of the aggregate imbalance.  It is enough to find arbitrarily large finite cutoffs at which the finite arithmetic defect is suitably small.

The CS21 task is to formalize this weaker finite-cutoff anchor language and connect it exactly to the existing endpoint/upper-envelope API.

No new sign theorem is to be assumed.

---

## CS21-A — absolute residual adapter

From the existing exact identity, prove a reusable absolute-error inequality of the form

```lean
pascalCenteredXiMellinQuadraticArithmeticDefectEndpoint ε W ≤
  pascalCenteredXiMellinQuadraticArithmeticDefectApproximant ε W X +
    (2 / Real.pi) *
      |pascalCenteredXiPrimeSideFiniteTailProjection ε W X|
```

for `hε : 0 < ε`.

Also expose the symmetric absolute estimate if convenient:

```text
|Dε,X - Dε,∞| = (2 / π) * |Pε,X|
```

or the corresponding `≤` statement.

This is algebra only.

---

## CS21-B — eventual absolute residual smallness at fixed ε

Use the already proved

```text
Pε,X → 0
```

to show that for every `δ > 0`, eventually in `X`,

```text
|Pε,X| ≤ δ.
```

Prefer a theorem with an explicit eventual form rather than introducing a new limit.

A second adapter may use the defect sequence directly:

```text
|Dε,X - Dε,∞| ≤ δ
```

eventually, with the normalization handled exactly.

No uniformity in `ε` is claimed.

---

## CS21-C — cofinal finite-cutoff upper anchor

Define a fixed-`ε` contract which allows oscillation and only asks for small finite approximants arbitrarily far out in the cutoff.

A recommended robust form is

```lean
def PascalCenteredXiPrimeSideCofinalFiniteUpperAnchorAt
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow)
    (r : ℝ) : Prop :=
  ∀ δ : ℝ, 0 < δ → ∀ N : ℕ,
    ∃ X : ℕ, N ≤ X ∧
      pascalCenteredXiMellinQuadraticArithmeticDefectApproximant ε W X ≤ r + δ
```

The `+ δ` is intentional.  It avoids an artificial failure in the case where a convergent sequence approaches the limiting bound strictly from above.

Equivalent formulations using `Frequently` or `liminf` are acceptable if they produce cleaner Lean.

Do **not** define the contract using the endpoint itself.

---

## CS21-D — fixed-ε strength classification

Using only the existing convergence

```text
Dε,X → Dε,∞,
```

prove the exact classification

```text
CofinalFiniteUpperAnchorAt ε W r
  ↔ Dε,∞ ≤ r.
```

This is a strength audit, not an arithmetic provider.

The forward direction should use cofinal finite upper bounds plus convergence.
The reverse direction should use convergence and the `+ δ` slack.

This theorem is useful because it identifies the weakest cofinal finite-source target that still carries the endpoint upper bound.

---

## CS21-E — good-cutoff selector with residual tolerance

Define a more constructive one-cutoff package for later source work.  Conceptually, at one positive `ε` and tolerances `r, δ`, require a finite cutoff `X` with

```text
Dε,X ≤ r
|Pε,X| ≤ δ.
```

For example:

```lean
structure PascalCenteredXiPrimeSideGoodFiniteCutoff
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow)
    (r δ : ℝ) : Prop where
  X : ℕ
  approximant_upper :
    pascalCenteredXiMellinQuadraticArithmeticDefectApproximant ε W X ≤ r
  tail_abs_le :
    |pascalCenteredXiPrimeSideFiniteTailProjection ε W X| ≤ δ
```

Then prove the endpoint adapter

```text
Dε,∞ ≤ r + (2 / π) * δ.
```

This package permits the cutoff to depend on `ε` and permits all intermediate cutoffs to oscillate.

---

## CS21-F — vanishing good-cutoff family

Package the outer `ε → 0+` version only as an audit surface.

A suitable contract is the existence of functions

```text
r : ℝ → ℝ,
δ : ℝ → ℝ,
X : ℝ → ℕ
```

such that

```text
r(ε) → 0,
δ(ε) → 0,
```

and eventually for `ε → 0+`,

```text
Dε,X(ε) ≤ r(ε),
|Pε,X(ε)| ≤ δ(ε).
```

Prove that this implies the existing

```lean
PascalCenteredXiPrimeSideVanishingUpperEnvelopeAt W
```

with envelope

```text
r(ε) + (2 / π) * δ(ε).
```

Do not use zero-side fixed-defect nonnegativity in this implication.

---

## CS21-G — separate what is already free from what remains a provider

The absolute tail tolerance is not the main missing theorem:
for fixed positive `ε`, the existing cutoff convergence can make the tail as small as desired by taking `X` sufficiently large.

The genuinely new arithmetic obligation is therefore one of the following equivalent-strength source statements:

1. a cofinal family of finite approximants with a vanishing upper bound;
2. a good-cutoff selector whose finite approximant upper bound vanishes while its tail tolerance also vanishes;
3. another source-derived finite-cutoff estimate strong enough to instantiate one of the above.

Keep this obligation separate from the already solved cutoff convergence.

---

## CS21-H — finite source ledger for the anchor candidate

Expose the selected finite defect approximant at cutoff `X` through the existing finite arithmetic source ledger.

The source should remain visibly composed of

```text
finite von-Mangoldt prime modes
+ archimedean correction
+ elementary correction
+ top-horizontal correction
+ fixed radial term / normalization
```

using existing definitions and theorems.

The purpose is to identify which term could supply the independent finite upper estimate.  Do not drop correction terms and do not use the endpoint explicit formula to prove the finite anchor.

If useful, provide the `X = 0` correction-only specialization as an audit identity, but **do not assume it is small or sign-definite**.

---

## CS21-I — source frontier

If no independent finite upper estimate is obtained, close Green-B with a named gap such as

```lean
inductive PascalCenteredXiPrimeSideCofinalFiniteUpperAnchorGap : Prop
  | noIndependentCofinalFiniteUpperAnchorProvider
```

or an equivalent name matching the implemented API.

This gap is preferable to reintroducing the stronger universal tail-sign or mode-sign assumptions.

---

## Important firewall

Do not use any of the following as the finite arithmetic anchor:

- fixed-defect nonnegativity;
- horizontal zero energy nonnegativity;
- fixed-defect zero iff all zeros in the window are critical;
- any RH-equivalent theorem;
- the CS9 converse from fixed-defect nonpositivity;
- a synthetic provider that directly assumes the desired endpoint upper envelope.

CS9 already classifies the vanishing upper-envelope target as fixed-defect/RH strength.  CS21 must expose a genuinely finite prime-side source obligation rather than hiding that strength.

---

## Why this route is weaker than CS19/CS20

The old candidate asked for

```text
∀ X, Pε,X ≥ 0.
```

CS20 showed that a monotonicity route to this condition collapses to individual prime-power mode positivity.

CS21 instead permits

```text
Pε,X
```

to change sign arbitrarily.  It only asks for a sufficiently large finite cutoff at which:

```text
the finite arithmetic source is small,
and the already-convergent residual is small in absolute value.
```

Thus the authorized chain becomes

```text
finite source upper anchor at a good cutoff
+ absolute cutoff residual smallness
→ endpoint upper bound
→ vanishing upper envelope
```

without a universal signed-tail theorem.

---

## Green criteria

CS21 is Green-B if it closes all of the following without a synthetic source estimate:

1. exact/absolute defect-tail residual adapter;
2. fixed-`ε` eventual absolute tail smallness;
3. a cofinal finite upper-anchor contract;
4. fixed-`ε` equivalence between that contract and endpoint upper bound;
5. a good finite-cutoff package and endpoint adapter;
6. an outer vanishing good-cutoff family implies the existing vanishing upper-envelope contract;
7. the finite arithmetic source ledger remains explicit;
8. any missing independent finite upper estimate is left as a named gap.

No universal mode sign, no universal terminal ceiling, no infinite sum/integral exchange, no endpoint sign theorem, and no RH conclusion are authorized in this checkpoint.
