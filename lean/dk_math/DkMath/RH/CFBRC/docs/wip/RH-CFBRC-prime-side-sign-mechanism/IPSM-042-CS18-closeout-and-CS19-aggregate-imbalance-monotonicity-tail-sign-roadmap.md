# IPSM-042 — CS18 closeout and CS19 aggregate-imbalance monotonicity / tail-sign roadmap

## Status

CS18 is accepted as **Green-B** on branch `wip/RH-CFBRC-prime-side-sign-mechanism-260813-v1`.

Verified CS18 achievements:

- exact coordinate embedding `Complex → CF2D.Vec ℝ`;
- exact bridge `Complex.normSq = Vec.q2`;
- exact bridge from complex multiplication to `Vec.star`;
- CS17 polarization rewritten literally as a `q2` difference;
- normalized finite-ray state and `q2(z ± 1)` density formulas;
- Real/Imag two-channel decomposition through `cf2dPlusWhole`, `cf2dMinusWhole`, and `cf2dInteractionBeam`;
- finite complex powers transported to repeated `Vec.star`;
- aggregate q2 energies proved exactly equal to the pre-existing aggregate energies;
- collision applicability correctly stopped at a named gap because no same-flow / same-filter / same-target assimilation package is source-derived.

CS18 therefore proves that the prime-power ray structure is genuinely compatible with CF2D, but it does **not** manufacture the missing ordering provider.

---

## Logical refinement after CS18

The current CS17 gap is phrased as an absolute aggregate ordering at one cutoff `X`:

```text
AggregateMinusEnergy(X) ≤ AggregatePlusEnergy(X).
```

Equivalently, if

```text
F(X) := AggregatePlusEnergy(X) - AggregateMinusEnergy(X),
```

then the existing ledger gives

$$
F(X)=4\sum_{n\le X}\Lambda(n)K_{\varepsilon,W}(n).
$$

However, the signed-tail objective is more directly controlled by **cutoff increments** than by the absolute sign of `F(X)`.

From CS12/CS17 we have finite identities of the form

$$
P_X-P_Y=\operatorname{BlockProjection}_{X,Y},
$$

and

$$
4\operatorname{BlockProjection}_{X,Y}=F(Y)-F(X).
$$

Therefore

$$
4(P_X-P_Y)=F(Y)-F(X).
$$

This is the central CS19 bridge.

If `F` is nondecreasing in the cutoff, then `P_X ≥ P_Y`.  If independently the already-authorized fixed-`ε` cutoff convergence gives `P_Y → 0`, then

$$
P_X\ge0.
$$

That is exactly the signed finite-tail direction needed by the earlier CS11/CS12 route.

This is strictly more targeted than merely proving `F(X) ≥ 0`.

---

# CS19 objective

Build the finite cutoff-dynamical ledger

```text
aggregate q2 imbalance F(X)
→ finite block increment F(Y)-F(X)
→ tail projection difference P_X-P_Y
→ fixed-ε tail projection tends to zero
→ monotonicity provider implies P_X ≥ 0.
```

No infinite tail / integral exchange is needed.  The only limit allowed is the already authorized cutoff limit `X → ∞` at fixed positive `ε`.

---

## CS19-A — name the aggregate energy imbalance

Define a real-valued cutoff observable, conceptually

```lean
noncomputable def pascalCenteredXiPrimeSideAggregateRayEnergyImbalance
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow)
    (X : ℕ) : ℝ :=
  pascalCenteredXiPrimeSideAggregateRayPlusEnergy ε W X -
    pascalCenteredXiPrimeSideAggregateRayMinusEnergy ε W X
```

Optionally define the q2 synonym only if useful.  Do not duplicate the mathematical content: reuse CS18 exact equality.

Prove the exact existing ledger in named form:

```text
AggregateRayEnergyImbalance ε W X
  = 4 * finiteModeSum ε W X.
```

Also audit the canonical base cutoff (`X = 0` or the actual first empty-support cutoff selected by repository conventions).  If Lean proves the imbalance is exactly zero there, expose that theorem.  Do not assume it without checking the finite support convention.

---

## CS19-B — exact cutoff increment / block identity

Package CS17-F as a direct increment theorem:

$$
F(Y)-F(X)=4\operatorname{BlockProjection}_{X,Y}.
$$

Prefer a theorem whose orientation matches later monotonicity use:

```text
F X ≤ F Y ↔ 0 ≤ BlockProjection X Y
```

for arbitrary finite `X,Y` if algebraically valid; if a natural order hypothesis `X ≤ Y` is mathematically needed for interpretation, keep it explicit even if the equality itself does not require it.

Do not infer positivity.

---

## CS19-C — reconnect block projection to finite tail projection

Use CS12's exact finite identity, not an infinite Dirichlet tail.

Target:

$$
P_X-P_Y=\operatorname{BlockProjection}_{X,Y}.
$$

Then combine with CS19-B:

$$
4(P_X-P_Y)=F(Y)-F(X).
$$

Add exact order adapters, for example under `X ≤ Y` if desired:

```text
F X ≤ F Y ↔ P Y ≤ P X.
```

This is a finite theorem.

---

## CS19-D — fixed-ε tail projection tends to zero

The prime cutoff residual already tends to zero for each fixed `ε > 0`.
CS11/CS12 identify the defect error and tail projection exactly with that residual coordinate.

Transport those existing theorems to prove

```text
Tendsto (fun X => pascalCenteredXiPrimeSideFiniteTailProjection ε W X)
  atTop (nhds 0)
```

for fixed `ε > 0`.

Do not introduce an infinite tail representation to prove this.  It must be only a corollary of the existing finite cutoff residual convergence.

This theorem is important because it converts finite cutoff monotonicity into an actual one-sided tail sign.

---

## CS19-E — monotonic imbalance implies signed tail projection

Define or use Mathlib's monotonicity predicate on the cutoff observable.

Conceptual provider:

```text
Monotone (AggregateRayEnergyImbalance ε W)
```

or the weaker eventual / pairwise statement genuinely sufficient for each fixed `X`.

From CS19-C and CS19-D prove the adapter:

```text
Monotone F
→ ∀ X, 0 ≤ FiniteTailProjection ε W X.
```

The proof should be a standard order/limit argument:

1. monotonicity gives `P_X ≥ P_Y` for all sufficiently large `Y` (or all `Y ≥ X`);
2. `P_Y → 0`;
3. therefore `P_X ≥ 0`.

If Mathlib makes the direct limit-order theorem awkward, prove a small real-analysis helper locally.  Keep the assumptions explicit.

This theorem is an **adapter**, not a provider.

---

## CS19-F — relation to the current CS17 absolute-ordering gap

Record the logical relation carefully.

If the canonical base imbalance is zero and `F` is monotone, then

```text
0 ≤ F X
```

and hence the existing CS17 absolute aggregate ordering follows.

The converse is not available in general:

```text
∀ X, 0 ≤ F X
```

does not imply

```text
Monotone F.
```

This distinction should be theoremized or documented so that future code does not mistake the weaker absolute ordering for the signed-tail provider.

---

## CS19-G — source audit for monotonicity

Now inspect the finite source for a genuine provider of

```text
F X ≤ F Y  when X ≤ Y.
```

Equivalent finite formulations include:

```text
0 ≤ BlockProjection X Y
```

or

```text
P Y ≤ P X.
```

Audit candidate mechanisms in this order:

1. finite prime-power block grouping by base prime;
2. geometric-ray endpoint numerator for the **incremental block**, not the whole ray;
3. aggregate plus/minus q2 increment ordering;
4. finite summation-by-parts / telescoping across cutoff boundaries;
5. CF2D `q2_star` only where it gives an actual new inequality, not merely an equality rewrite.

Do not reuse the CS18 collision theorem unless a same-object, same-filter, same-target assimilation package is independently constructed from the prime-side cutoff flow.  At present it is not.

If no source-derived monotonicity provider appears, record a named gap such as

```lean
inductive PascalCenteredXiPrimeSideAggregateImbalanceMonotonicityGap : Prop
  | noIndependentCutoffMonotonicityProvider
```

This is the correct Green-B outcome if the increment remains oscillatory.

---

## Important firewall — signed tail direction is still not the endpoint anchor

Even a successful CS19 monotonicity theorem would give

$$
P_X\ge0,
$$

hence

$$
D_{\varepsilon,\infty}\le D_{\varepsilon,X}.
$$

That controls the direction from a finite cutoff to the endpoint.

It still does **not** give the absolute upper bound required for the endpoint defect.
An independent finite-cutoff anchor / vanishing upper envelope remains a separate obligation:

```text
signed tail direction
+
finite-cutoff anchor
→ endpoint upper envelope.
```

Do not use fixed-Xi defect nonnegativity, horizontal-energy positivity, or the RH-equivalent defect-vanishing theorem as that anchor.

CS20 should return to the finite-cutoff anchor only after CS19 has classified whether the signed-tail direction is genuinely available.

---

## Green criteria

CS19 is Green-B if it closes all source-derived adapters without assuming the desired sign:

1. named aggregate imbalance and exact mode-sum ledger;
2. exact cutoff-increment / block-projection identity;
3. exact tail-projection difference identity;
4. fixed-`ε` convergence of finite tail projection to zero;
5. proof that cutoff monotonicity would imply nonnegative finite tail projection;
6. explicit distinction between absolute aggregate ordering and cutoff monotonicity;
7. monotonicity provider either proved independently or retained as a named gap.

No infinite sum/integral exchange, endpoint sign theorem, fixed-defect RH argument, or RH conclusion is authorized here.
