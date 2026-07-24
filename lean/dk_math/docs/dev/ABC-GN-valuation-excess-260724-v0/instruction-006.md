# Codex Instruction 006

Theme: two-budget ABC closure — support growth plus valuation multiplicity

作業 branch:

```text
wip/ABC-GN-valuation-excess-260724-Codex
```

## 1. Current frontier

前 checkpoint では、次の deterministic support spine が完成した。

```text
GN support
  = exceptional support q | n
  ⊔ non-exceptional support q ∤ n

exceptional support product | rad n

non-exceptional support is fresh from a*b*c

rad(a*b*c) * nonExceptionalSupportProduct
  | rad((T.gnPowerLift n).a *
        (T.gnPowerLift n).b *
        (T.gnPowerLift n).c)

lifted radical growth budget (σ, Cs)
  -> GNSupportBudgetAffine T n σ (Cs + log(rad n))
```

既存層では、さらに次が Lean-confirmed である。

```text
c^(n-1) ≤ GN n a b

log GN
  = log(rad GN) + GNValuationExcess

GNValuationExcess
  = GNExceptionalValuationExcess
  + GNNonExceptionalValuationExcess
```

重要な correction:

```text
lifted-radical growth alone does not prove ABC.

It bounds prime support and therefore gives a lower bound on
GNValuationExcess under high quality.

A second upper budget on valuation multiplicity is required.
```

この checkpoint の役目は、一様 budget 自体を証明することではない。

```text
support budget
+
valuation-excess budget
  -> explicit K_epsilon ABC bound
```

という最終合成を Lean theorem surface として固定し、`abc_main_axiom` を置換するために本当に必要な一様契約を明示する。

## 2. Sources to inspect

repository current source だけを参照する。

```text
lean/dk_math/DkMath/ABC/GNPowerLift.lean
lean/dk_math/DkMath/ABC/GNValuationExcess.lean
lean/dk_math/DkMath/ABC/GNHighLift.lean
lean/dk_math/DkMath/ABC/GNQualityExcessBridge.lean
lean/dk_math/DkMath/ABC/GNSupportReturn.lean
lean/dk_math/DkMath/ABC/ABCMainTheorem.lean
lean/dk_math/DkMath/ABC/Triple.lean
lean/dk_math/DkMath/ABC/Rad.lean
lean/dk_math/docs/dev/ABC-GN-valuation-excess-260724-v0/report-006.md
```

current theorem names、仮定、namespace を確認し、存在しない名前を写経しない。

特に次の current API を再利用する。

```text
Triple.log_c_mul_pred_le_log_GN
Triple.log_GN_eq_log_rad_add_GNValuationExcess
GNValuationExcess_eq_exceptional_add_nonExceptional
Triple.GNSupportBudgetAffine_of_liftGrowth
GNLiftRadicalGrowthBudgetAffine
GNSupportBudgetAffine
Triple.log_rad_abc_pos
```

## 3. Recommended module

```text
lean/dk_math/DkMath/ABC/GNFinalBudgetBridge.lean
```

より自然な軽量配置が current dependency structure にある場合は変更してよい。

## 4. Goal A: valuation-excess upper-budget predicates

full valuation excess の affine upper budget を定義する。

```lean

def GNValuationExcessBudgetAffine
    (T : Triple) (n : ℕ) (τ D : ℝ) : Prop :=
  GNValuationExcess n T.a T.b ≤
    τ * Real.log (rad (T.a * T.b * T.c) : ℝ) + D
```

exceptional / non-exceptional 層についても定義する。

```lean

def GNExceptionalExcessBudgetAffine
    (T : Triple) (n : ℕ) (τ D : ℝ) : Prop :=
  GNExceptionalValuationExcess n T.a T.b ≤
    τ * Real.log (rad (T.a * T.b * T.c) : ℝ) + D


def GNNonExceptionalExcessBudgetAffine
    (T : Triple) (n : ℕ) (τ D : ℝ) : Prop :=
  GNNonExceptionalValuationExcess n T.a T.b ≤
    τ * Real.log (rad (T.a * T.b * T.c) : ℝ) + D
```

既存 exact partition から、次を証明する。

```text
exceptional budget (τe, De)
+
non-exceptional budget (τn, Dn)

-> full budget (τe + τn, De + Dn)
```

候補 theorem:

```lean

theorem GNValuationExcessBudgetAffine.of_split
    ...
```

命名は current style に合わせる。

ここでは finite exceptional prime support と valuation multiplicity を混同しない。

```text
exceptional support product | rad n
```

だけでは、exceptional valuation depth の一様上界は得られない。

## 5. Goal B: direct logarithmic height upper bound

support budget と excess budget を exact identity へ合流させる。

目標形:

```lean

theorem Triple.log_c_mul_pred_le_of_support_and_excessBudget
    (T : Triple) {n : ℕ} {σ Cs τ Ce : ℝ}
    (hn : 2 ≤ n) (ha : 0 < T.a) (hb : 0 < T.b)
    (hsupport : GNSupportBudgetAffine T n σ Cs)
    (hexcess : GNValuationExcessBudgetAffine T n τ Ce) :
    (((n - 1 : ℕ) : ℝ) * Real.log (T.c : ℝ)) ≤
      (σ + τ) *
        Real.log (rad (T.a * T.b * T.c) : ℝ) +
      (Cs + Ce) := by
  ...
```

証明経路:

```text
(n-1) log c ≤ log GN
log GN = log(rad GN) + valuation excess
log(rad GN) ≤ σ log R + Cs
valuation excess ≤ τ log R + Ce
```

`linarith` / `nlinarith` へ渡せる直線形を維持する。

## 6. Goal C: lifted-growth specialization

`GNSupportReturn.lean` の transport theorem を再利用し、

```text
GNLiftRadicalGrowthBudgetAffine T n σ Cs
GNValuationExcessBudgetAffine T n τ Ce
```

から、次を得る。

```text
(n-1) log c
  ≤ (σ + τ) log(rad(a*b*c))
    + Cs + Ce + log(rad n)
```

候補 theorem:

```lean

theorem Triple.log_c_mul_pred_le_of_liftGrowth_and_excessBudget
    ...
```

exceptional support constant `Real.log (rad n : ℝ)` を消さず、結論上に明示する。

## 7. Goal D: explicit pointwise ABC constant

次の margin 条件を仮定する。

```text
σ + τ ≤ (n-1) * (1+ε)
```

明示定数を定義する。

```lean

noncomputable def GNABCConstant
    (n : ℕ) (Cs Ce : ℝ) : ℝ :=
  max 1
    (Real.exp
      ((Cs + Ce + Real.log (rad n : ℝ)) /
        ((n - 1 : ℕ) : ℝ)))
```

current elaboration に適した括弧・cast へ調整してよい。
同値な、より扱いやすい明示定数へ変更してもよい。

ただし、

```text
K depends only on:
  n, Cs, Ce

K does not depend on:
  T.a, T.b, T.c
```

を保つ。

次の pointwise theorem を目標とする。

```lean

theorem Triple.abc_bound_of_liftGrowth_and_excessBudget
    (T : Triple) {n : ℕ} {ε σ Cs τ Ce : ℝ}
    (hn : 2 ≤ n)
    (ha : 0 < T.a) (hb : 0 < T.b)
    (hmargin :
      σ + τ ≤ ((n - 1 : ℕ) : ℝ) * (1 + ε))
    (hlift :
      GNLiftRadicalGrowthBudgetAffine T n σ Cs)
    (hexcess :
      GNValuationExcessBudgetAffine T n τ Ce) :
    (T.c : ℝ) ≤
      GNABCConstant n Cs Ce *
        (rad (T.a * T.b * T.c) : ℝ) ^ (1 + ε) := by
  ...
```

必要な補助事項:

```text
0 < T.c
0 < rad(a*b*c)
0 < (n-1 : ℝ)
Real.exp / Real.log
Real.rpow
```

既存 API で閉じるものを再証明しない。

`^ (1 + ε)` の elaboration が自然数冪として解釈されないよう、current ABC theorem surface と `Real.rpow` API を確認する。

## 8. Goal E: global final contract

一様契約を structure または Prop として固定する。

候補:

```lean

structure ABCGNFinalBudgetContract (ε : ℝ) where
  hε : 0 < ε
  n : ℕ
  hn : 2 ≤ n
  σ Cs τ Ce : ℝ
  margin :
    σ + τ ≤ ((n - 1 : ℕ) : ℝ) * (1 + ε)
  liftBudget :
    ∀ T : Triple, 0 < T.a → 0 < T.b →
      GNLiftRadicalGrowthBudgetAffine T n σ Cs
  excessBudget :
    ∀ T : Triple, 0 < T.a → 0 < T.b →
      GNValuationExcessBudgetAffine T n τ Ce
```

これから positive triple 版の global ABC theorem を証明する。

```lean

theorem abc_positive_of_GNFinalBudgetContract
    {ε : ℝ}
    (H : ABCGNFinalBudgetContract ε) :
    ∃ K : ℝ, 1 ≤ K ∧
      ∀ T : Triple,
        0 < T.a → 0 < T.b →
        (T.c : ℝ) ≤
          K * (rad (T.a * T.b * T.c) : ℝ) ^ (1 + ε) := by
  ...
```

自然に閉じる場合は `a = 0` / `b = 0` の coprime endpoint を処理し、現行 `abc_main_axiom` と同じ生引数 surface への bridge を追加してよい。

ただし、この checkpoint では `abc_main_axiom` 自体を削除・変更しない。

## 9. Goal F: audit the actual remaining mathematics

report では、次を明確に区別する。

```text
proved in Lean:
  support budget + valuation-excess budget
    -> explicit K_epsilon ABC bound

not proved:
  uniform lifted-radical growth budget
  uniform exceptional valuation-excess budget
  uniform non-exceptional valuation-excess budget
```

特に、

```text
finite exceptional prime support
```

と、

```text
uniformly bounded exceptional valuation multiplicity
```

を混同しない。

固定された有限個の prime であっても、valuation depth が一様定数になるとは限らない。

## 10. Mathematical meaning and stopping boundary

この checkpoint が Outcome A で閉じれば、`abc_main_axiom` の内容は次の三つの一様 budget へ還元される。

```text
uniform lifted-radical support growth
uniform exceptional valuation excess
uniform non-exceptional valuation excess
```

これは ABC 予想自体の証明ではない。

次を開始しない。

```text
Hensel rarity theorem
p-adic logarithm formalization
LTE の新規大規模構築
uniform high-lift exclusion
abc_main_axiom の削除
FLT7
確率・密度 route
```

新規 `axiom`、`sorry`、`native_decide` は追加しない。

## 11. Validation and report

対象 module をローカル build する。

次を作成する。

```text
lean/dk_math/docs/dev/ABC-GN-valuation-excess-260724-v0/report-007.md
```

report には最低限、次を記録する。

```text
- budget predicate の正確な定義
- exceptional / non-exceptional excess budget の合成
- support / excess 合成 theorem
- lifted-growth specialization
- 明示 K の式
- pointwise ABC theorem
- global contract theorem
- endpoint a=0 / b=0 を扱ったか
- 残る三つの一様 budget
- local build
- axiom audit
- FLT7 / aggregator の変更有無
```

## 12. Stop condition

```text
Outcome A:
  support budget と valuation-excess budget から
  明示 K_epsilon を持つ ABC bound が完成した。

Outcome B:
  logarithmic height bound は完成したが、
  Real.exp / Real.rpow の pointwise wrapper に最小 blocker が残った。

Outcome C:
  current source に同等の final contract が既にあり、
  最薄 wrapper と audit のみで閉じた。
```

実装・ローカル検証・`report-007.md` 作成後、User へ返して停止する。

commit、push、PR、CI、次 checkpoint への自動進行は行わない。
