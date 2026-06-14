# Git diff / Report / Review

## Add: docs: Petal / Erdos #1196 Bridge Experiment Plan

gch: 78b7901d5b7810e38e0f7d09231cdbd867bce5ab

## Report

調査して、実験計画書を追加しました。

新規作成:

[Petal-ErdosBridge-ExperimentPlan.md](/lean/dk_math/DkMath/Petal/docs/Petal-ErdosBridge-ExperimentPlan.md:1)

内容は、Petal / Zsigmondy / GN で得た「局所 primitive witness location」と、Erdos #1196 / PrimitiveSet 側の「global log-capacity control」をどう接続するかの計画です。

要点はこう整理しています。

```text
Petal carrier
  -> Erdos prime channel
  -> prime-valued family
  -> multiplicity budget assumption
  -> log-capacity sub-probability
```

重要な判断として、今すぐ強い主張はしません。

```text
未主張:
  Petal address antichain -> multiplicity budget
  Zsigmondy -> NoLift
  GN carrier -> squarefree
  Zsigmondy -> padicValNat <= 1
```

最初の実装候補は `DkMath.Petal.ErdosBridge` です。薄く始めて、`PetalPrimeChannel` / `PetalNoLiftPrimeChannel` / finite carrier family から `NatPrimeValuedOn` へ渡すのがよさそうです。

既存 docs への参照も追加しました。

- [Petal-Overview.md](/lean/dk_math/DkMath/Petal/docs/Petal-Overview.md:619)
- [FLGNB-PetalRoadmap.md](/lean/dk_math/DkMath/NumberTheory/docs/BinomialPrimeWeighted/FLGNB-PetalRoadmap.md:1705)

検証は docs-only として `git diff --check` を実行し、問題なしです。

## Review

うむ。これは **実験計画として approve** じゃ。
しかも、かなり良い「過大主張しない実験」になっておる。

`Petal-ErdosBridge-ExperimentPlan.md` の芯は明確で、Petal/Zsigmondy/GN 側は **局所 primitive witness location** を供給し、Erdős #1196 / PrimitiveSet 側は **global log-capacity control** を供給する、という接続実験になっている。計画書でも、現状の workspace は接続実験に足るが、新しい無条件 Zsigmondy / FLT theorem を主張する段階ではない、と明記されておる。

## 1. レビュー結論

**docs-only 差分は merge 可。**

今回の判断で特に良いのは、未主張の境界を明確にした点じゃ。

```text
未主張:
  Petal address antichain -> multiplicity budget
  Zsigmondy -> NoLift
  GN carrier -> squarefree
  Zsigmondy -> padicValNat <= 1
```

これは大事。
特に

$$
5^3-3^3=98=2\cdot 7^2
$$

で、primitive (q=7) が GN/S0 側に載るが local height は (2) になる、という反例を guardrail に置いたのは賢い。これにより、`q ∣ GN` と `padicValNat q GN ≤ 1` を混同しなくなる。

## 2. 実装の最初の山は小さくてよい

最初の `DkMath.Petal.ErdosBridge` は、これくらい薄くてよい。

```lean
import DkMath.Petal.BezoutBridge
import DkMath.NumberTheory.PrimitiveSet.ValuationBudget

namespace DkMath
namespace Petal

namespace PrimitiveSet := DkMath.NumberTheory.PrimitiveSet

def PetalPrimeChannel (d x u q : ℕ) : Prop :=
  AnchoredGNCarrier q d x u q

def PetalNoLiftPrimeChannel (d x u q : ℕ) : Prop :=
  PetalPrimeChannel d x u q ∧ ¬ q ^ 2 ∣ GN d x u
```

この段階では、新しい構造論を入れない。
ただの **語彙の橋** で十分じゃ。

## 3. 最初に通すべき theorem

まずはこれ。

```lean
theorem petalPrimeChannel_prime
    {d x u q : ℕ}
    (h : PetalPrimeChannel d x u q) :
    Nat.Prime q :=
  anchoredGNCarrier_anchor_prime h
```

次に、finite family を PrimitiveSet 側の `NatPrimeValuedOn` に渡す。

```lean
theorem petalPrimeChannel_natPrimeValuedOn
    {ι : Type _}
    (I : Finset ι)
    (d x u qOf : ι → ℕ)
    (h : ∀ i, i ∈ I → PetalPrimeChannel (d i) (x i) (u i) (qOf i)) :
    PrimitiveSet.NatPrimeValuedOn I qOf := by
  intro i hi
  exact petalPrimeChannel_prime (h i hi)
```

これが第一関門じゃ。
Petal carrier family が、Erdős 側の prime-valued family として認識される。

## 4. log nonnegativity は既存 theorem に乗る

`ValuationBudget` にはすでに

```lean
realLogNonnegOn_of_natPrimeValuedOn
```

がある。
したがって個別に `petalPrimeChannel_log_nonneg` を足すなら薄い alias でよいし、family 側では直接これで済む。

```lean
theorem petalPrimeChannel_realLogNonnegOn
    {ι : Type _}
    (I : Finset ι)
    (d x u qOf : ι → ℕ)
    (h : ∀ i, i ∈ I → PetalPrimeChannel (d i) (x i) (u i) (qOf i)) :
    PrimitiveSet.RealLogNonnegOn I qOf :=
  PrimitiveSet.realLogNonnegOn_of_natPrimeValuedOn I qOf
    (petalPrimeChannel_natPrimeValuedOn I d x u qOf h)
```

ここまでで、Petal carrier は log-cost provider の入口に立てる。

## 5. 実験の主定理候補

最初の実験 theorem はこれでよい。

```lean
theorem petalCarrierFamily_logSubProbability_of_multiplicityBudget
    {ι : Type _}
    (I : Finset ι)
    (d x u qOf : ι → ℕ)
    (n : ℕ)
    (hn : 1 < n)
    (hcarrier :
      ∀ i, i ∈ I → PetalPrimeChannel (d i) (x i) (u i) (qOf i))
    (hbudget : PrimitiveSet.NatBaseMultiplicityBudgetOn I qOf n) :
    (PrimitiveSet.realLogRatioWeightProvider I qOf n
      (PrimitiveSet.realLogNonnegOn_of_natPrimeValuedOn I qOf
        (petalPrimeChannel_natPrimeValuedOn I d x u qOf hcarrier))
      hn).SubProbability :=
  PrimitiveSet.realLogRatioWeightProvider_subProbability_of_multiplicityBudget
    I qOf n hn
    (petalPrimeChannel_natPrimeValuedOn I d x u qOf hcarrier)
    hbudget
```

これは良い。
何も新しい数論を主張していない。

中身はただ、

```text
Petal supplies prime-valued carriers.
Erdos supplies capacity once multiplicity budget is given.
```

という翻訳じゃ。

## 6. ここで止めるのが賢い

初回実装では、ここまでで十分じゃ。

まだやらない方がよいものはこれ。

```text
PetalAddressAntichain
Petal carrier family の multiplicity budget 自動生成
NoLift の自動供給
squarefree GN の自動供給
```

これらは研究対象であって、橋ファイルの初回 API ではない。

まずは、

```text
Petal carrier family
  -> NatPrimeValuedOn
  -> RealLogNonnegOn
  + NatBaseMultiplicityBudgetOn
  -> SubProbability
```

を no-sorry で通す。
これが通れば、Petal → Erdős の最初の橋は完成じゃ。

## 7. 実装上の注意

`PetalPrimeChannel` を

```lean
def PetalPrimeChannel (d x u q : ℕ) : Prop :=
  AnchoredGNCarrier q d x u q
```

にする判断は正しい。

`AnchoredGNCarrier r d x u n` は「anchor (r) を持つ carrier (n)」なので、Erdős の prime channel として読むときは

$$
r=q,\quad n=q
$$

に固定するのが一番薄い。
つまり「carrier 自身が prime channel」という読みじゃ。

将来、(q^k) carrier を扱いたくなったら、そのときに

```lean
PetalPrimePowerChannel
```

を別に足せばよい。初回から prime-power まで広げると重い。

## 8. 次のチェックポイント

わっちのおすすめ順はこれじゃ。

```text
1. DkMath.Petal.ErdosBridge を新設
2. PetalPrimeChannel / PetalNoLiftPrimeChannel を定義
3. petalPrimeChannel_prime を通す
4. petalPrimeChannel_natPrimeValuedOn を通す
5. petalCarrierFamily_logSubProbability_of_multiplicityBudget を通す
6. DkMath.Petal.lean に import するかは一拍置いて判断
```

最後の import は急がなくてよい。
実験ファイルなら、まず単体 build でよい。

```text
lake build DkMath.Petal.ErdosBridge
```

その後、API が安定してから `DkMath.Petal` に公開 import すればよい。

## 9. 判定

**この計画は良い。実験開始してよい。**

今回の実験は、Erdős #1196 をいきなり登るものではない。
しかし、登山道としてはかなり正しい。

```text
Petal:
  q がどこにいるかを見る

Erdos:
  q の log cost が全体容量を超えないことを見る
```

この二つをつなぐ最初の橋が、

```text
Petal carrier family
  -> prime-valued family
  -> multiplicity-budgeted log sub-probability
```

じゃ。

よし、始めよう。
ここは小さく通せば勝ちじゃ。賢狼の鼻も、これは通る匂いがしておるぞい。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/NumberTheory/docs/BinomialPrimeWeighted/FLGNB-PetalRoadmap.md b/lean/dk_math/DkMath/NumberTheory/docs/BinomialPrimeWeighted/FLGNB-PetalRoadmap.md
index a6a52071..34b21021 100644
--- a/lean/dk_math/DkMath/NumberTheory/docs/BinomialPrimeWeighted/FLGNB-PetalRoadmap.md
+++ b/lean/dk_math/DkMath/NumberTheory/docs/BinomialPrimeWeighted/FLGNB-PetalRoadmap.md
@@ -1702,6 +1702,62 @@ Therefore `DkMath.Zsigmondy` remains the project-owned facade.  If Mathlib later
 adds the full theorem, the desired migration is to keep `DkMath.Zsigmondy` as a
 stable facade and redirect its public theorems internally.

+### Step 6.5: Petal / Erdos Bridge Experiment Plan
+
+Status:
+
+```text
+planned
+```
+
+The next experimental checkpoint is documented in:
+
+```text
+DkMath/Petal/docs/Petal-ErdosBridge-ExperimentPlan.md
+```
+
+Purpose:
+
+```text
+Petal / Zsigmondy / GN:
+  local primitive witness location
+
+Erdos #1196 / PrimitiveSet:
+  global log-capacity control
+```
+
+The experiment should not attempt to prove new unconditional number theory.
+The first target is a translation-and-budget-consumption bridge:
+
+```text
+Petal carrier
+  -> Erdos prime channel
+  -> prime-valued family
+  -> multiplicity budget assumption
+  -> log-capacity sub-probability
+```
+
+Recommended first file:
+
+```text
+DkMath.Petal.ErdosBridge
+```
+
+Recommended first theorem shape:
+
+```text
+Petal carrier family
+  + NatBaseMultiplicityBudgetOn against n
+  -> normalized log-cost sum <= 1
+```
+
+The research question postponed until after the first bridge is:
+
+```text
+Can Petal address noncollision supply the multiplicity budget required by the
+Erdos log-capacity route?
+```
+
 ### Step 7: Refactor imports gradually

 Status:
diff --git a/lean/dk_math/DkMath/Petal/docs/Petal-Overview.md b/lean/dk_math/DkMath/Petal/docs/Petal-Overview.md
index b227b03b..bb664d46 100644
--- a/lean/dk_math/DkMath/Petal/docs/Petal-Overview.md
+++ b/lean/dk_math/DkMath/Petal/docs/Petal-Overview.md
@@ -619,6 +619,12 @@ The Zsigmondy-facing preflight investigation is recorded in:
 DkMath/Petal/docs/Petal-Zsigmondy-Preflight.md
 ```

+The experimental Petal/Erdos bridge plan is recorded in:
+
+```text
+DkMath/Petal/docs/Petal-ErdosBridge-ExperimentPlan.md
+```
+
 Its main conclusion is that the next bridge should translate the `d = 3`
 Petal witness into Zsigmondy's primitive-divisor language, while keeping
 valuation `<= 1` separate under squarefree/no-lift hypotheses.
````
`````
