# Codex Instruction 004

Theme: close the unconditional GN return bound and identify valuation excess with high-lift carriers

作業 branch:

```text
wip/ABC-GN-valuation-excess-260724-Codex
```

## 1. Review correction and current frontier

The current branch has Lean-checked implementations for:

```text
ABC-GN-004  exponent-exception / non-exceptional split
ABC-GN-005  exact log-rad-plus-excess identity
ABC-GN-006  conditional quality-to-excess interface
ABC-GN-007  local high-lift API
```

The code review accepts the new theorem surfaces in:

```text
DkMath/ABC/GNExceptionalSplit.lean
DkMath/ABC/GNValuationExcess.lean
DkMath/ABC/GNHighLift.lean
DkMath/ABC/GNQualityExcessBridge.lean
```

However, `report-004.md` is too pessimistic in treating both
`GNReturnLowerBound` and `GNSupportBudget` as equally open global obligations.

For an ABC triple `T.a + T.b = T.c`, the GN kernel is the difference quotient

```text
GN n T.a T.b = (T.c^n - T.b^n) / T.a
```

and contains the endpoint term `T.c^(n-1)`.  Therefore the next task is to
close, without an extra global hypothesis,

```text
T.c^(n-1) ≤ GN n T.a T.b
```

and hence

```text
(n-1) * log T.c ≤ log (GN n T.a T.b).
```

After this is proved, the genuine global obligation remaining in the
quality-to-excess route is the GN support budget.

## 2. Sources to inspect

Use only repository current source.

```text
lean/dk_math/DkMath/ABC/GNPowerLift.lean
lean/dk_math/DkMath/ABC/GNValuationSplit.lean
lean/dk_math/DkMath/ABC/GNValuationExcess.lean
lean/dk_math/DkMath/ABC/GNHighLift.lean
lean/dk_math/DkMath/ABC/GNQualityExcessBridge.lean
lean/dk_math/DkMath/Algebra/DiffPow.lean
lean/dk_math/DkMath/NumberTheory/Gcd/GN.lean
lean/dk_math/DkMath/CosmicFormula/CosmicFormulaBinom.lean
lean/dk_math/DkMath/ABC/RadLogBasic.lean
lean/dk_math/DkMath/ABC/AnalyticQualityBridge.lean
lean/dk_math/docs/dev/ABC-GN-valuation-excess-260724-v0/report-004.md
```

Relevant existing APIs include, but are not limited to:

```text
Triple.gnPowerLift_sum
Triple.powerDiff_eq_boundary_mul_GN
DkMath.Algebra.DiffPow.diffPowSum
DkMath.Algebra.DiffPow.pow_sub_pow_nat
DkMath.NumberTheory.Gcd.gn_sub_eq_sd_int
GN_eq_sum
log_GN_eq_log_rad_add_GNValuationExcess
padicValNat_le_iff_dvd
Real.log_le_log
Real.log_pow
```

Choose the lightest proof route.  Do not import a heavy research module merely
because it contains a theorem with a nearby statement.

## 3. Goal A: unconditional GN return in natural coordinates

Add the smallest natural-number theorem proving the endpoint lower bound.
A candidate surface is:

```lean
theorem Triple.pow_pred_c_le_GN
    (T : Triple) {n : ℕ}
    (hn : 1 ≤ n) (ha : 0 < T.a) :
    T.c ^ (n - 1) ≤ GN n T.a T.b := by
  ...
```

Adjust assumptions and naming to current style.  `T.hsum` may be used to
rewrite `T.c = T.a + T.b`.

Preferred mathematical routes:

```text
Route 1:
  identify GN with the finite difference-power sum
  and retain its i = 0 term T.c^(n-1)

Route 2:
  use a * GN + b^n = c^n
  prove b^n ≤ b * c^(n-1)
  rewrite c = a + b
  cancel the positive factor a
```

Do not use division on naturals if cancellation or a finite-sum proof is
cleaner.

If the same current-source representation makes it inexpensive, also prove
the calibration upper bound

```lean
GN n T.a T.b ≤ n * T.c ^ (n - 1)
```

but this upper bound is optional.  It must not delay the lower-bound theorem.

## 4. Goal B: discharge `GNReturnLowerBound`

From Goal A, prove the logarithmic return theorem under positive ABC
coordinates and `2 ≤ n`.

Candidate surfaces:

```lean
theorem Triple.log_c_mul_pred_le_log_GN
    (T : Triple) {n : ℕ}
    (hn : 2 ≤ n) (ha : 0 < T.a) (hb : 0 < T.b) :
    (((n - 1 : ℕ) : ℝ) * Real.log (T.c : ℝ)) ≤
      Real.log ((GN n T.a T.b : ℕ) : ℝ) := by
  ...
```

```lean
theorem Triple.gnReturnLowerBound_pred
    (T : Triple) {n : ℕ}
    (hn : 2 ≤ n) (ha : 0 < T.a) (hb : 0 < T.b) :
    GNReturnLowerBound T n ((n - 1 : ℕ) : ℝ) := by
  ...
```

Use exact current Mathlib theorem names for casts, powers, and logarithms.
Keep the lower bound non-strict.

## 5. Goal C: remove avoidable positivity hypotheses

Investigate whether positive `T.a` and `T.b` already imply

```lean
0 < Real.log (rad (T.a * T.b * T.c) : ℝ)
```

for an ABC triple.  If it closes with a small local proof, add a reusable
wrapper such as:

```lean
theorem Triple.log_rad_abc_pos
    (T : Triple) (ha : 0 < T.a) (hb : 0 < T.b) :
    0 < Real.log (rad (T.a * T.b * T.c) : ℝ) := by
  ...
```

A proof may pass through `1 < rad (a*b*c)` or a prime divisor of the positive
product.  Reuse existing radical lemmas where available.

If this requires a large unrelated radical refactor, do not perform it.
Keep the existing explicit `hrad` assumption and report the smallest missing
lemma shape.

## 6. Goal D: reduce the quality bridge to support budget only

Add a theorem specializing
`Triple.GNValuationExcess_gt_of_quality_gt` with

```text
κ = n - 1
hreturn = Triple.gnReturnLowerBound_pred
```

The resulting public theorem must not ask the caller for
`GNReturnLowerBound` or `0 < κ`.

Candidate conclusion:

```lean
((((n - 1 : ℕ) : ℝ) * (1 + ε) - σ) *
    Real.log (rad (T.a * T.b * T.c) : ℝ))
  < GNValuationExcess n T.a T.b
```

under high quality and `GNSupportBudget T n σ`.

If Goal C succeeds, remove the explicit radical-log positivity assumption as
well.  Otherwise retain only that one local analytic hypothesis.

### Affine support budget

Finite exceptional absorption will naturally introduce an additive constant.
Therefore add an affine interface if it keeps the theorem surface clean:

```lean
def GNSupportBudgetAffine
    (T : Triple) (n : ℕ) (σ C : ℝ) : Prop :=
  Real.log (rad (GN n T.a T.b) : ℝ) ≤
    σ * Real.log (rad (T.a * T.b * T.c) : ℝ) + C
```

and prove the corresponding excess lower bound

```text
(((n-1)*(1+ε)-σ) * log rad(abc)) - C < GNValuationExcess.
```

The existing `GNSupportBudget` should become the `C = 0` specialization or
remain as a compatibility wrapper.  Avoid duplicated proof bodies.

## 7. Goal E: identify excess with high-lift carriers

The current `valuationExcess` sum ranges over the entire factorization support,
but a support prime with valuation exactly one contributes zero.  Connect the
exact identity from `GNValuationExcess.lean` with the local high-lift API from
`GNHighLift.lean`.

A recommended placement is `DkMath/ABC/GNHighLift.lean`, since it already
imports `GNValuationExcess`.  Do not reverse this dependency and create an
import cycle.

Define a finite high-lift carrier set only if it improves reuse, for example:

```lean
noncomputable def highLiftSupport (m : ℕ) : Finset ℕ :=
  m.factorization.support.filter (fun q => q ^ 2 ∣ m)
```

or a GN-specialized equivalent.

Prove an exact restriction theorem of the form:

```lean
theorem valuationExcess_eq_sum_highLift
    {m : ℕ} (hm : m ≠ 0) :
    valuationExcess m =
      ∑ q ∈ highLiftSupport m,
        (((m.factorization q - 1 : ℕ) : ℝ) * Real.log (q : ℝ)) := by
  ...
```

Then add GN exceptional and non-exceptional specializations when they are thin:

```text
GNExceptionalValuationExcess
  = sum over exceptional high-lift carriers

GNNonExceptionalValuationExcess
  = sum over non-exceptional high-lift carriers
```

At minimum prove:

```lean
no GN high-lift prime -> GNValuationExcess = 0
```

If the converse

```lean
0 < GNValuationExcess -> exists a GNHighLiftPrime
```

closes without a large positivity detour, add it.  Otherwise record the exact
missing positivity lemma and stop there.

## 8. Quantifier and frontier audit

Do not state a uniform `GNSupportBudget` theorem without proving its exact
parameter dependencies.

The report must distinguish at least:

```text
fixed n versus varying n
σ depending on n versus absolute σ
additive constant C depending on n and ε
pointwise budget versus a theorem uniform over all positive ABC triples
```

The coefficient that matters is the net margin

```text
((n - 1) * (1 + ε) - σ)
```

not the existence of an arbitrary pointwise `σ`.

After Goals A–E, the honest global frontier should be stated as:

```text
unconditional GN return: closed
valuation excess carriers: exact finite high-lift support
remaining global obligation: a quantitatively useful affine GNSupportBudget
```

Do not claim that the support budget, high-lift rarity, finite exceptional
absorption, `K_ε`, or ABC has been proved.

## 9. Boundaries

Do not perform:

```text
abc_main_axiom modification or use
ABC final theorem claims
uniform high-lift rarity assumptions disguised as lemmas
false rad(GN) ≤ rad(abc) transport
probability / Janson / Borel-Cantelli refactors
primitive / Zsigmondy expansion unless a tiny existing wrapper is essential
FLT7 edits or imports
shared aggregator changes unless mathematically necessary
large renaming or repository-wide refactoring
```

Add no new `axiom`, `sorry`, or `native_decide`.

`DkMath/FLT/Seven/**`, FLT7 docs, and
`wip/FLT7-magic-core-260722-WiseWolf` are outside the task.

## 10. Local validation and report

Run local builds for every changed target module.  GitHub commit, push, PR,
and CI operations are not part of this instruction.

Because `report-004.md` already records the authorized rolling sprint, write
the result of this instruction to:

```text
lean/dk_math/docs/dev/ABC-GN-valuation-excess-260724-v0/report-005.md
```

Record:

```text
- exact theorem surfaces added
- proof route used for c^(n-1) ≤ GN
- whether GNReturnLowerBound was fully discharged
- whether radical-log positivity was internalized
- pure and affine support-budget theorem surfaces
- exact high-lift carrier identities
- quantifier dependencies left on GNSupportBudget
- local build results
- files changed
- confirmation that FLT7 and shared aggregators were untouched
- the single next mathematical obligation after this checkpoint
```

## 11. Stop conditions

```text
Outcome A:
  unconditional GN return is closed,
  quality-to-excess depends only on support budget,
  and valuation excess is exactly restricted to high-lift carriers.

Outcome B:
  GN return is closed and the reduced quality bridge is complete,
  but the high-lift finite-sum restriction needs one minimal factorization lemma.
  Record its exact statement.

Outcome C:
  the natural GN endpoint lower bound itself is blocked by a representation or
  cancellation gap.  Record the smallest missing theorem and do not hide it
  behind a new hypothesis.
```

After implementation, local validation, and `report-005.md`, return the result
to User and stop.  Do not start the support-budget proof automatically.
