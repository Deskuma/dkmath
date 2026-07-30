# Codex Instruction 005

Theme: finite exceptional support absorption and lifted-radical growth reduction

作業 branch:

```text
wip/ABC-GN-valuation-excess-260724-Codex
```

## 1. Current frontier

The previous checkpoint closed:

```text
unconditional GN return
positive ABC radical-log
pure / affine quality-to-excess bridge
exact high-lift carrier formula for valuation excess
```

The only remaining global input in the quality bridge is a quantitatively useful GN support budget.

Do not attack a false or unsupported statement such as

```text
rad (GN n a b) ≤ rad (a*b*c)
```

Instead separate the finite exponent-exceptional support from the genuinely new non-exceptional support.

The intended deterministic spine is:

```text
GN support
  = exceptional support q | n
    disjoint union
    non-exceptional support q ∤ n

exceptional support product | rad n
non-exceptional GN primes do not divide a*b*c

therefore
  log rad(GN)
    ≤ log rad(n) + log(nonExceptionalSupportProduct)
```

Then connect the non-exceptional product to radical growth of `T.gnPowerLift n`.

## 2. Sources to inspect

Use repository current source only.

```text
lean/dk_math/DkMath/ABC/GNPowerLift.lean
lean/dk_math/DkMath/ABC/GNExceptionalSplit.lean
lean/dk_math/DkMath/ABC/GNValuationExcess.lean
lean/dk_math/DkMath/ABC/GNHighLift.lean
lean/dk_math/DkMath/ABC/GNQualityExcessBridge.lean
lean/dk_math/DkMath/ABC/Rad.lean
lean/dk_math/DkMath/ABC/MassBridge.lean
lean/dk_math/DkMath/ABC/ValuationFlowBridge.lean
lean/dk_math/docs/dev/ABC-GN-valuation-excess-260724-v0/report-005.md
```

Relevant current APIs include:

```text
Triple.dvd_exp_of_dvd_boundary_of_dvd_GN
Triple.not_dvd_boundary_of_not_dvd_exp_of_dvd_GN
Triple.gnPowerLift_coprime
Triple.gnPowerLift
mem_support_factorization_iff
support_prod_log_eq_sum_log
rad_mul_coprime
rad_pow_eq_rad
prime_channel_family_prod_dvd_supportMass
supportMass_eq_abc_rad
GNSupportBudgetAffine
Triple.GNValuationExcess_gt_of_quality_gt_pred_affine
```

Choose the lightest dependency route.  Do not import large research modules merely for nearby vocabulary.

## 3. Recommended module

```text
lean/dk_math/DkMath/ABC/GNSupportReturn.lean
```

A nearby name is acceptable if current dependency structure strongly favors it.

## 4. Goal A: finite exceptional / non-exceptional support partition

Define finite support sets for a GN kernel, for example:

```lean
def GNExceptionalSupport (n a b : ℕ) : Finset ℕ :=
  (GN n a b).factorization.support.filter (fun q => q ∣ n)

def GNNonExceptionalSupport (n a b : ℕ) : Finset ℕ :=
  (GN n a b).factorization.support.filter (fun q => ¬ q ∣ n)
```

Define their squarefree products if useful:

```lean
def GNExceptionalSupportProduct (n a b : ℕ) : ℕ :=
  (GNExceptionalSupport n a b).prod id

def GNNonExceptionalSupportProduct (n a b : ℕ) : ℕ :=
  (GNNonExceptionalSupport n a b).prod id
```

Prove the exact support partition and radical product identity:

```text
GN support = exceptional ∪ non-exceptional
rad(GN) = exceptionalProduct * nonExceptionalProduct
```

Use a disjoint filtered partition; do not introduce multiplicity here.

## 5. Goal B: absorb all exceptional GN support into `rad n`

For `1 ≤ n`, prove every member of `GNExceptionalSupport n a b` is prime and divides `n`.  Then prove:

```lean
GNExceptionalSupportProduct n a b ∣ rad n
```

or an equivalent natural inequality.

The proof should use the finite prime-channel family API when it is lighter than rebuilding factorization arguments.

Derive the logarithmic exceptional bound:

```text
log(exceptionalProduct) ≤ log(rad n)
```

and the full support estimate:

```text
log(rad(GN n a b))
  ≤ log(rad n) + log(nonExceptionalProduct n a b)
```

Handle positivity and zero cases with the smallest honest assumptions.  In the main ABC use case, `2 ≤ n` and positive `a,b` are available.

## 6. Goal C: non-exceptional GN support is fresh relative to the original triple

For a positive ABC triple and `1 ≤ n`, prove that any

```text
q ∈ GNNonExceptionalSupport n T.a T.b
```

satisfies:

```text
Nat.Prime q
q ∣ GN n T.a T.b
¬ q ∣ T.a
¬ q ∣ T.b
¬ q ∣ T.c
¬ q ∣ T.a * T.b * T.c
```

Use:

```text
q ∤ n + q ∣ GN -> q ∤ T.a
```

for the boundary, and derive the `b,c` separation from the coprimality of the lifted triple.  Avoid re-proving the general gcd theory.

Package the result as one reusable theorem if that keeps later support proofs short.

## 7. Goal D: embed the fresh product into lifted radical growth

Let

```text
L := T.gnPowerLift n
```

Prove that the original ABC radical and the non-exceptional GN support product occur as disjoint support inside the lifted triple radical.  Preferred target:

```lean
rad (T.a * T.b * T.c) *
    GNNonExceptionalSupportProduct n T.a T.b ∣
  rad (L.a * L.b * L.c)
```

or the corresponding natural inequality.

An exact equality is welcome only if it follows cleanly.  Do not delay the divisibility/lower-bound bridge to force an exact formula.

Then derive the logarithmic growth inequality:

```text
log(rad(abc)) + log(nonExceptionalProduct)
  ≤ log(rad(lifted abc))
```

under the needed positivity assumptions.

## 8. Goal E: replace the full support budget by a lifted-radical-growth budget

Define an affine lifted-radical growth predicate, for example:

```lean
def GNLiftRadicalGrowthBudgetAffine
    (T : Triple) (n : ℕ) (σ C : ℝ) : Prop :=
  Real.log (rad ((T.gnPowerLift n).a *
      (T.gnPowerLift n).b * (T.gnPowerLift n).c) : ℝ) ≤
    (1 + σ) * Real.log (rad (T.a * T.b * T.c) : ℝ) + C
```

Also define a non-exceptional support budget if useful:

```lean
def GNNonExceptionalSupportBudgetAffine
    (T : Triple) (n : ℕ) (σ C : ℝ) : Prop :=
  Real.log (GNNonExceptionalSupportProduct n T.a T.b : ℝ) ≤
    σ * Real.log (rad (T.a * T.b * T.c) : ℝ) + C
```

Prove the deterministic chain:

```text
lifted-radical-growth budget
  -> non-exceptional support budget
  -> GNSupportBudgetAffine T n σ (C + log(rad n))
```

The exact arrangement of additive constants may be normalized algebraically, but the exceptional contribution must be explicit and depend only on `n` through `rad n` or a provably smaller term.

Finally compose with the existing quality bridge to obtain a theorem whose only global transport input is the lifted-radical-growth budget.  Its excess lower bound should visibly pay the exceptional constant `log(rad n)`.

## 9. Mathematical meaning and stopping boundary

This checkpoint should complete `ABC-GN-008` in the following precise sense:

```text
all q | n support is absorbed into a finite exponent constant;
all remaining support is fresh relative to the original ABC triple;
the remaining global obligation is renamed as lifted radical growth
or non-exceptional support growth.
```

Do not claim a uniform lifted-radical-growth theorem.

Do not begin:

```text
Hensel rarity theorems
p-adic logarithm formalization
uniform non-exceptional support bounds
K_epsilon construction
abc_main_axiom replacement
probability-layer refactoring
FLT7 integration
```

No new `axiom`, `sorry`, or `native_decide`.

## 10. Documentation correction

Update stale module comments in `GNQualityExcessBridge.lean` if inexpensive: the return lower bound is now unconditional, so the genuine remaining input is the support budget rather than two equally open estimates.  Do not refactor theorem names merely for prose consistency.

## 11. Public import

A direct import is sufficient:

```lean
import DkMath.ABC.GNSupportReturn
```

Do not modify a shared aggregator unless strictly required.  Record any such change in the report.

## 12. Local validation and report

Run local builds for the new module and directly affected modules.

Create:

```text
lean/dk_math/docs/dev/ABC-GN-valuation-excess-260724-v0/report-006.md
```

Record:

```text
- exact support definitions
- exceptional/non-exceptional partition theorem
- exceptional product -> rad n proof route
- freshness theorem relative to a*b*c
- lifted radical divisibility or inequality
- exact affine constant transport
- final quality-to-excess theorem surface
- remaining global mathematical obligation
- local build results
- FLT7/shared-area status
```

Do not commit, push, edit the PR, start CI, or inspect CI.  Return the result to the User and stop.

## 13. Outcomes

```text
Outcome A:
  exceptional absorption, freshness, lifted-radical bridge, and affine
  composition all close.

Outcome B:
  exceptional absorption and freshness close, but the lifted-radical product
  bridge needs one small missing radical/support lemma.  Implement the maximal
  theorem surface and name the exact missing lemma.

Outcome C:
  current source already contains a stronger equivalent bridge.  Add only the
  thinnest ABC wrapper and document the dependency.
```

In every outcome, stop after implementation, local validation, and `report-006.md`.
