# Git diff / Report / Review

## Add: DkMath.FLT.PrimeProvider.CosmicPetalBridgeGNNoWieferichValuation

gch: 897639bc58ec3cdf03c6d5738c9bec6ff194d1d2

## Report

進めました。今回は FLT 側の周辺整理として、honest valuation surface を `Research` から分離しました。

新設：

- [CosmicPetalBridgeGNNoWieferichValuation.lean](/lean/dk_math/DkMath/FLT/PrimeProvider/CosmicPetalBridgeGNNoWieferichValuation.lean)

ここへ no-sorry 確認済みの以下を移しました。

```lean
TriominoPrimitivePrimeFactorPadicValNatLeOneTarget
primitivePrimeFactorOfDiffPow_of_FLT_branch
triominoPrimitivePrimeFactorPadicValNatLeOneTarget_of_noLiftGNBridge
triominoPrimitivePrimeFactorPadicValNatLeOneTarget_of_squarefreeGNBridge
```

整理内容：

- `CosmicPetalBridgeGNNoWieferichResearch.lean`
  - research placeholder / fixed injection 側に縮小
  - honest valuation surface は import して使う側へ

- `TriominoSquarefreeGNBridgeProviderImpl.lean`
  - `Research` import を外し、新 `Valuation` import へ変更

- `CosmicPetalBridgeGN.lean`
  - public branch API が valuation target を使うため、新 `Valuation` を明示 import

- `PrimeProvider.lean`
  - 新 `Valuation` surface を aggregator に追加
  - `Research` の直 import は外しました

調査結果として、`CosmicPetalBridgeGNNoWieferichResearch` の直接 import は現在この 2 箇所だけです。

```text
CosmicPetalBridgeGNNoWieferichDefault
CosmicPetalBridgeGNDescentBQuarantine
```

どちらも fixed injection / quarantine の隔離点なので、現状の残り方として妥当です。

検証：

```sh
lake build DkMath.FLT.PrimeProvider.CosmicPetalBridgeGNNoWieferichValuation
lake build DkMath.FLT.PrimeProvider.CosmicPetalBridgeGNNoWieferichResearch
lake build DkMath.FLT.PrimeProvider.TriominoSquarefreeGNBridgeProviderImpl
lake build DkMath.FLT.PrimeProvider.CosmicPetalBridgeGN
lake build DkMath.FLT.PrimeProvider
git diff --check
```

すべて通っています。既存の research / branch 系 `sorry` 警告は継続です。

## Review

おお、これは **かなり良い分離** じゃ。採用でよい。
FLT 側も、ついに `Research` から honest valuation surface が外へ出た。

今回の変更で構造がこうなった。

```text
CosmicPetalBridgeGNNoWieferichValuation:
  no-sorry valuation surface
  FLT Branch-B -> PrimitiveBeam witness
  NoLift -> padicValNat <= 1
  Squarefree -> NoLift -> padicValNat <= 1

CosmicPetalBridgeGNNoWieferichResearch:
  legacy research core
  old placeholder / fixed injection / quarantine-facing abstractions
```

これは大きい。
前回までは「Research ファイルの中に honest route がある」状態だった。今回はそれを、公開可能な `Valuation` surface として切り出せた。

## レビュー結論

```text
897639bc...
  -> 採用可

honest valuation surface の Research 分離
  -> 成功

PrimeProvider aggregator の Research 直 import 削除
  -> 良い

TriominoSquarefreeGNBridgeProviderImpl の Research import 削除
  -> とても良い

Research import 残り 2 箇所
  -> Default / Quarantine なので妥当
```

## 一番良い点

`PrimeProvider.lean` から、

```lean
import DkMath.FLT.PrimeProvider.CosmicPetalBridgeGNNoWieferichResearch
```

が外れたのが大きい。

代わりに、

```lean
import DkMath.FLT.PrimeProvider.CosmicPetalBridgeGNNoWieferichValuation
```

になった。

つまり public aggregator は、もう旧 research valuation placeholder を直接背負わない。
これは DkMath 全体の本線 API としてかなり健全じゃ。

## `TriominoSquarefreeGNBridgeProviderImpl` の import 変更も重要

ここも良い。

```diff
-import DkMath.FLT.PrimeProvider.CosmicPetalBridgeGNNoWieferichResearch
+import DkMath.FLT.PrimeProvider.CosmicPetalBridgeGNNoWieferichValuation
```

Provider 実装が `Research` を直接 import していると、honest squarefree route のつもりでも研究債務を引きずる。
ここが `Valuation` に切り替わったことで、

```text
squarefree provider
  -> honest valuation target
  -> PrimitiveBeam NoLift route
```

という読みになる。

## `CosmicPetalBridgeGN.lean` の明示 import も妥当

```lean
import DkMath.FLT.PrimeProvider.CosmicPetalBridgeGNNoWieferichValuation
```

これは、public branch API が

```lean
TriominoPrimitivePrimeFactorPadicValNatLeOneTarget
```

を使う以上、明示 import するのが正しい。

ここで `Research` を経由しないのが大事じゃ。

## 新ファイルの中身

新設 `CosmicPetalBridgeGNNoWieferichValuation.lean` に移したものは、どれも honest surface として妥当。

```lean
TriominoPrimitivePrimeFactorPadicValNatLeOneTarget
primitivePrimeFactorOfDiffPow_of_FLT_branch
triominoPrimitivePrimeFactorPadicValNatLeOneTarget_of_noLiftGNBridge
triominoPrimitivePrimeFactorPadicValNatLeOneTarget_of_squarefreeGNBridge
```

特にこの二つが中核。

```lean
triominoPrimitivePrimeFactorPadicValNatLeOneTarget_of_noLiftGNBridge
triominoPrimitivePrimeFactorPadicValNatLeOneTarget_of_squarefreeGNBridge
```

これで FLT 側の読みは完全に、

```text
NoLift:
  本命 local multiplicity route

Squarefree:
  NoLift を作る十分条件 wrapper
```

になった。

## Research 側の縮小も良い

`CosmicPetalBridgeGNNoWieferichResearch.lean` は、今や

```lean
import DkMath.FLT.PrimeProvider.CosmicPetalBridgeGNNoWieferichValuation
import DkMath.NumberTheory.ZsigmondyCyclotomicResearch
```

になっている。

つまり、Research 側は honest target を使って旧 placeholder / fixed injection を包む側へ退いた。

これはよい。

```text
Research:
  valuation target の定義元ではない
  legacy injection / quarantine-facing wrapper
```

という状態になった。

## 残り Research import 2 箇所

調査結果：

```text
CosmicPetalBridgeGNNoWieferichDefault
CosmicPetalBridgeGNDescentBQuarantine
```

これは妥当じゃ。

`Default` は fixed injection / 研究既定値の注入点。
`Quarantine` は名前通り隔離点。

つまり、

```text
public aggregator:
  Research を直接 import しない

provider implementation:
  Research を直接 import しない

quarantine/default:
  Research を import してよい
```

という整理になった。かなり良い。

## 次に確認すると良いこと

この commit の後にやるなら、まずは `#print axioms` じゃな。

```lean
#print axioms DkMath.FLT.primitivePrimeFactorOfDiffPow_of_FLT_branch
#print axioms DkMath.FLT.triominoPrimitivePrimeFactorPadicValNatLeOneTarget_of_noLiftGNBridge
#print axioms DkMath.FLT.triominoPrimitivePrimeFactorPadicValNatLeOneTarget_of_squarefreeGNBridge
```

ここに `sorryAx` が出なければ、`Valuation` surface は本当に no-sorry surface として看板を出せる。

## 次の一手

次は docs closure を少し足すか、caller survey をもう一段進めるのが自然じゃ。

見るべきは、

```text
CosmicPetalBridgeGNNoWieferichResearch
```

を direct import している 2 箇所のうち、

```text
CosmicPetalBridgeGNNoWieferichDefault
```

が将来的に `Valuation` + 明示的な fixed injection に分解できるか。

ただし、これは急がなくてよい。
現状では `Default` と `Quarantine` が research を背負う設計は合理的じゃ。

## 判定

今回で、FLT 側の honest path はかなり閉じた。

```text
PrimitiveBeam:
  primitive witness + NoLift
  -> padicValNat <= 1

FLT Valuation:
  FLT Branch-B
  -> PrimitiveBeam witness
  -> PrimitiveBeam theorem

FLT Research:
  old placeholder / fixed injection / quarantine
```

ABC に続いて、FLT でも同じ整理が成立した。

```text
NoLift が本命。
Squarefree は十分条件。
Research placeholder は隔離。
```

うむ。これは良い。
`PrimeProvider` の public surface が `Research` から離れたのは、かなり大きな前進じゃ。

---

[DkMathTest: CosmicPetalBridgeGNNoWieferichResearch](/lean/dk_math/DkMathTest/FLT/PrimeProvider/CosmicPetalBridgeGNNoWieferichResearch.lean) - all OK: 2026/06/14  5:00

おお、確認完了じゃな。
これは **FLT honest valuation surface は no-sorry と見てよい**。

結果が全部これだけなら問題なし。

```text
[propext, Classical.choice, Quot.sound]
```

これは Lean/mathlib 通常依存で、`sorryAx` ではない。

確認できた対象：

```lean
DkMath.FLT.primitivePrimeFactorOfDiffPow_of_FLT_branch
DkMath.FLT.triominoPrimitivePrimeFactorPadicValNatLeOneTarget_of_noLiftGNBridge
DkMath.FLT.triominoPrimitivePrimeFactorPadicValNatLeOneTarget_of_squarefreeGNBridge
```

つまり、今回切り出した `CosmicPetalBridgeGNNoWieferichValuation` の中核は、

```text
no-sorry honest surface
```

として扱える。

## 状況判定

これで FLT 側も、かなり閉じた。

```text
FLT Branch-B primitive-prime inputs
  -> PrimitiveBeam.PrimitivePrimeFactorOfDiffPow
  -> NoLift GN
  -> padicValNat <= 1
```

squarefree 側も、

```text
Squarefree GN
  -> NoLift GN
  -> padicValNat <= 1
```

として no-sorry で通っている。

## 重要な意味

旧 research placeholder はまだ存在するが、もう honest valuation route の根ではない。

```text
Research:
  legacy / fixed injection / quarantine

Valuation:
  no-sorry public surface
```

この分離が `#print axioms` で裏取りできた。

## 次に記録するなら

Roadmap か `Petal-Zsigmondy-Preflight.md` に、短くこう書ける。

```text
FLT NoWieferich valuation surface was checked with `#print axioms`.
The three core theorems depend only on standard Lean/mathlib axioms:
`propext`, `Classical.choice`, and `Quot.sound`; no `sorryAx` appears.
```

うむ。
これで FLT 側は、少なくとも NoWieferich valuation bridge については安心して次の段に進める。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/FLT/PrimeProvider.lean b/lean/dk_math/DkMath/FLT/PrimeProvider.lean
index 31c84a33..9610b7b7 100644
--- a/lean/dk_math/DkMath/FLT/PrimeProvider.lean
+++ b/lean/dk_math/DkMath/FLT/PrimeProvider.lean
@@ -8,8 +8,8 @@ import DkMath.FLT.PrimeProviderCore
 import DkMath.FLT.PrimeProvider.CosmicPetalBridgeGNCore
 import DkMath.FLT.PrimeProvider.CosmicPetalBridgeGN
 import DkMath.FLT.PrimeProvider.CosmicPetalBridgeGNNoWieferich
+import DkMath.FLT.PrimeProvider.CosmicPetalBridgeGNNoWieferichValuation
 import DkMath.FLT.PrimeProvider.CosmicPetalBridgeGNNoWieferichDefault
-import DkMath.FLT.PrimeProvider.CosmicPetalBridgeGNNoWieferichResearch
 import DkMath.FLT.PrimeProvider.CosmicPetalBridgeGNDescentBQuarantine
 import DkMath.FLT.PrimeProvider.CosmicPetalBridgeGNDescentB
 import DkMath.FLT.PrimeProvider.TriominoCosmic
diff --git a/lean/dk_math/DkMath/FLT/PrimeProvider/CosmicPetalBridgeGN.lean b/lean/dk_math/DkMath/FLT/PrimeProvider/CosmicPetalBridgeGN.lean
index b501c315..696c43cb 100644
--- a/lean/dk_math/DkMath/FLT/PrimeProvider/CosmicPetalBridgeGN.lean
+++ b/lean/dk_math/DkMath/FLT/PrimeProvider/CosmicPetalBridgeGN.lean
@@ -5,6 +5,7 @@ Authors: D. and Wise Wolf.
 -/
 
 import DkMath.FLT.PrimeProvider.CosmicPetalBridgeGNCore
+import DkMath.FLT.PrimeProvider.CosmicPetalBridgeGNNoWieferichValuation
 import DkMath.FLT.PrimeProvider.CosmicPetalBridgeGNDescentB
 import DkMath.FLT.PrimeProvider.CosmicPetalBridgeGNDescentBQuarantine
 
diff --git a/lean/dk_math/DkMath/FLT/PrimeProvider/CosmicPetalBridgeGNNoWieferichResearch.lean b/lean/dk_math/DkMath/FLT/PrimeProvider/CosmicPetalBridgeGNNoWieferichResearch.lean
index 7786ee2e..930e98a6 100644
--- a/lean/dk_math/DkMath/FLT/PrimeProvider/CosmicPetalBridgeGNNoWieferichResearch.lean
+++ b/lean/dk_math/DkMath/FLT/PrimeProvider/CosmicPetalBridgeGNNoWieferichResearch.lean
@@ -4,8 +4,7 @@ Released under MIT license as described in the file LICENSE.
 Authors: D. and Wise Wolf.
 -/
 
-import DkMath.FLT.PrimeProvider.CosmicPetalBridgeGNNoWieferich
-import DkMath.NumberTheory.PrimitiveBeam
+import DkMath.FLT.PrimeProvider.CosmicPetalBridgeGNNoWieferichValuation
 import DkMath.NumberTheory.ZsigmondyCyclotomicResearch
 
 #print "file: DkMath.FLT.PrimeProvider.CosmicPetalBridgeGNNoWieferichResearch"
@@ -17,19 +16,6 @@ namespace DkMath.FLT
 
 open DkMath.CosmicFormulaBinom
 
-/--
-phase-15 で current research debt として残っている最小入力仕様。
-
-primitive-prime branch で
-`padicValNat q (z^p - y^p) ≤ 1`
-が一様に供給できれば、PrimeProvider / Kummer 側の glue は clean に閉じる。
--/
-abbrev TriominoPrimitivePrimeFactorPadicValNatLeOneTarget : Prop :=
-  ∀ {p x y z q : ℕ}, PrimeGe5CounterexamplePack p x y z →
-    ¬ p ∣ (z - y) →
-    Nat.Prime q → q ∣ (z ^ p - y ^ p) → ¬ q ∣ (z - y) →
-    padicValNat q (z ^ p - y ^ p) ≤ 1
-
 /--
 phase-15 の研究核（diff 版）:
 primitive prime divisor 文脈で `z^p - y^p` の `q`-進付値が高々 1 であることを示す。
@@ -74,39 +60,6 @@ theorem triominoWieferichShrinkKernelEqSeedTracePackB_kernel_padicValNat_diff_le
   intro p x y z q hpack hpB hqP hq_dvd_diff hq_not_dvd_gap
   exact hVal hpack hpB hqP hq_dvd_diff hq_not_dvd_gap
 
-/--
-Translate the FLT Branch-B primitive-prime inputs into the shared
-`PrimitiveBeam` primitive-factor predicate.
-
-This is the main handshake between the FLT NoWieferich branch and the newer
-`PrimitiveBeam` valuation route.
--/
-theorem primitivePrimeFactorOfDiffPow_of_FLT_branch
-    {p x y z q : ℕ}
-    (hpack : PrimeGe5CounterexamplePack p x y z)
-    (_hpB : ¬ p ∣ (z - y))
-    (hqP : Nat.Prime q)
-    (hq_dvd_diff : q ∣ (z ^ p - y ^ p))
-    (hq_not_dvd_gap : ¬ q ∣ (z - y)) :
-    DkMath.NumberTheory.PrimitiveBeam.PrimitivePrimeFactorOfDiffPow q z y p := by
-  refine ⟨hqP, hq_dvd_diff, ?_⟩
-  have hzy_coprime : Nat.Coprime z y := by
-    exact (coprime_right_of_add_pow_eq_pow hpack.hp hpack.hxy hpack.hEq).symm
-  intro k hk_pos hk_lt
-  exact
-    DkMath.NumberTheory.GcdNext.prime_exp_not_dvd_diff_imp_primitive
-      (a := z) (b := y) (d := p) (q := q)
-      hpack.hp
-      hpack.hp.one_lt
-      hqP
-      hzy_coprime
-      hpack.hyz_lt
-      hpack.y_pos
-      hq_dvd_diff
-      hq_not_dvd_gap
-      hk_pos
-      hk_lt
-
 /--
 `padicValNat q (GN p (z - y) y) ≤ 1` が供給できれば、
 `padicValNat q (z^p - y^p) ≤ 1` は no-`so#rry` で従う。
@@ -149,43 +102,6 @@ theorem triominoWieferichShrinkKernelEqSeedTracePackB_kernel_padicValNat_GN_le_o
   rw [← hEq]
   exact hdiff_le
 
-/--
-direct no-lift bridge (`¬ q^2 ∣ GN`) が供給されれば、
-primitive-prime branch の valuation target は no-`so#rry` で閉じる。
--/
-theorem triominoPrimitivePrimeFactorPadicValNatLeOneTarget_of_noLiftGNBridge
-    (hNoLift : TriominoNoLiftGNBridge) :
-    TriominoPrimitivePrimeFactorPadicValNatLeOneTarget := by
-  intro p x y z q hpack hpB hqP hq_dvd_diff hq_not_dvd_gap
-  have hPrim :
-      DkMath.NumberTheory.PrimitiveBeam.PrimitivePrimeFactorOfDiffPow q z y p :=
-    primitivePrimeFactorOfDiffPow_of_FLT_branch
-      hpack hpB hqP hq_dvd_diff hq_not_dvd_gap
-  have hGN_not_sq : ¬ q ^ 2 ∣ GN p (z - y) y :=
-    hNoLift hpack hpB hqP hq_dvd_diff hq_not_dvd_gap
-  exact
-    DkMath.NumberTheory.PrimitiveBeam.primitive_prime_padic_bound_diff_of_noLift_GN
-      hPrim
-      hpack.hp.pos
-      hpack.hp.one_lt
-      hpack.hyz_lt
-      hGN_not_sq
-
-/--
-squarefree bridge が供給されれば、primitive-prime branch の valuation target は
-NoLift bridge 経由で従う。
-
-This keeps the FLT-side hierarchy aligned with the ABC-side hierarchy:
-local NoLift is the main route, and full `GN` squarefreeness is a sufficient
-condition.
--/
-theorem triominoPrimitivePrimeFactorPadicValNatLeOneTarget_of_squarefreeGNBridge
-    (hSq : TriominoSquarefreeGNBridge) :
-    TriominoPrimitivePrimeFactorPadicValNatLeOneTarget := by
-  exact
-    triominoPrimitivePrimeFactorPadicValNatLeOneTarget_of_noLiftGNBridge
-      (triominoNoLiftGNBridge_of_squarefree_GN hSq)
-
 /--
 phase-15 の研究核:
 反例文脈で primitive prime divisor の `padicValNat` が高々 1 であることを示す。
diff --git a/lean/dk_math/DkMath/FLT/PrimeProvider/CosmicPetalBridgeGNNoWieferichValuation.lean b/lean/dk_math/DkMath/FLT/PrimeProvider/CosmicPetalBridgeGNNoWieferichValuation.lean
new file mode 100644
index 00000000..bf977ec5
--- /dev/null
+++ b/lean/dk_math/DkMath/FLT/PrimeProvider/CosmicPetalBridgeGNNoWieferichValuation.lean
@@ -0,0 +1,102 @@
+/-
+Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
+Released under MIT license as described in the file LICENSE.
+Authors: D. and Wise Wolf.
+-/
+
+import DkMath.FLT.PrimeProvider.CosmicPetalBridgeGNNoWieferich
+import DkMath.NumberTheory.PrimitiveBeam
+
+#print "file: DkMath.FLT.PrimeProvider.CosmicPetalBridgeGNNoWieferichValuation"
+
+set_option linter.style.longLine false
+set_option linter.style.emptyLine false
+
+namespace DkMath.FLT
+
+open DkMath.CosmicFormulaBinom
+
+/--
+phase-15 で current research debt として残っている最小入力仕様。
+
+primitive-prime branch で
+`padicValNat q (z^p - y^p) ≤ 1`
+が一様に供給できれば、PrimeProvider / Kummer 側の glue は clean に閉じる。
+-/
+abbrev TriominoPrimitivePrimeFactorPadicValNatLeOneTarget : Prop :=
+  ∀ {p x y z q : ℕ}, PrimeGe5CounterexamplePack p x y z →
+    ¬ p ∣ (z - y) →
+    Nat.Prime q → q ∣ (z ^ p - y ^ p) → ¬ q ∣ (z - y) →
+    padicValNat q (z ^ p - y ^ p) ≤ 1
+
+/--
+Translate the FLT Branch-B primitive-prime inputs into the shared
+`PrimitiveBeam` primitive-factor predicate.
+
+This is the main handshake between the FLT NoWieferich branch and the newer
+`PrimitiveBeam` valuation route.
+-/
+theorem primitivePrimeFactorOfDiffPow_of_FLT_branch
+    {p x y z q : ℕ}
+    (hpack : PrimeGe5CounterexamplePack p x y z)
+    (_hpB : ¬ p ∣ (z - y))
+    (hqP : Nat.Prime q)
+    (hq_dvd_diff : q ∣ (z ^ p - y ^ p))
+    (hq_not_dvd_gap : ¬ q ∣ (z - y)) :
+    DkMath.NumberTheory.PrimitiveBeam.PrimitivePrimeFactorOfDiffPow q z y p := by
+  refine ⟨hqP, hq_dvd_diff, ?_⟩
+  have hzy_coprime : Nat.Coprime z y := by
+    exact (coprime_right_of_add_pow_eq_pow hpack.hp hpack.hxy hpack.hEq).symm
+  intro k hk_pos hk_lt
+  exact
+    DkMath.NumberTheory.GcdNext.prime_exp_not_dvd_diff_imp_primitive
+      (a := z) (b := y) (d := p) (q := q)
+      hpack.hp
+      hpack.hp.one_lt
+      hqP
+      hzy_coprime
+      hpack.hyz_lt
+      hpack.y_pos
+      hq_dvd_diff
+      hq_not_dvd_gap
+      hk_pos
+      hk_lt
+
+/--
+direct no-lift bridge (`¬ q^2 ∣ GN`) が供給されれば、
+primitive-prime branch の valuation target は no-`so#rry` で閉じる.
+-/
+theorem triominoPrimitivePrimeFactorPadicValNatLeOneTarget_of_noLiftGNBridge
+    (hNoLift : TriominoNoLiftGNBridge) :
+    TriominoPrimitivePrimeFactorPadicValNatLeOneTarget := by
+  intro p x y z q hpack hpB hqP hq_dvd_diff hq_not_dvd_gap
+  have hPrim :
+      DkMath.NumberTheory.PrimitiveBeam.PrimitivePrimeFactorOfDiffPow q z y p :=
+    primitivePrimeFactorOfDiffPow_of_FLT_branch
+      hpack hpB hqP hq_dvd_diff hq_not_dvd_gap
+  have hGN_not_sq : ¬ q ^ 2 ∣ GN p (z - y) y :=
+    hNoLift hpack hpB hqP hq_dvd_diff hq_not_dvd_gap
+  exact
+    DkMath.NumberTheory.PrimitiveBeam.primitive_prime_padic_bound_diff_of_noLift_GN
+      hPrim
+      hpack.hp.pos
+      hpack.hp.one_lt
+      hpack.hyz_lt
+      hGN_not_sq
+
+/--
+squarefree bridge が供給されれば、primitive-prime branch の valuation target は
+NoLift bridge 経由で従う.
+
+This keeps the FLT-side hierarchy aligned with the ABC-side hierarchy:
+local NoLift is the main route, and full `GN` squarefreeness is a sufficient
+condition.
+-/
+theorem triominoPrimitivePrimeFactorPadicValNatLeOneTarget_of_squarefreeGNBridge
+    (hSq : TriominoSquarefreeGNBridge) :
+    TriominoPrimitivePrimeFactorPadicValNatLeOneTarget := by
+  exact
+    triominoPrimitivePrimeFactorPadicValNatLeOneTarget_of_noLiftGNBridge
+      (triominoNoLiftGNBridge_of_squarefree_GN hSq)
+
+end DkMath.FLT
diff --git a/lean/dk_math/DkMath/FLT/PrimeProvider/TriominoSquarefreeGNBridgeProviderImpl.lean b/lean/dk_math/DkMath/FLT/PrimeProvider/TriominoSquarefreeGNBridgeProviderImpl.lean
index 2e0c32e8..de71324c 100644
--- a/lean/dk_math/DkMath/FLT/PrimeProvider/TriominoSquarefreeGNBridgeProviderImpl.lean
+++ b/lean/dk_math/DkMath/FLT/PrimeProvider/TriominoSquarefreeGNBridgeProviderImpl.lean
@@ -5,7 +5,7 @@ Authors: D. and Wise Wolf.
 -/
 
 import DkMath.FLT.PrimeProvider.TriominoSquarefreeGNBridgeProvider
-import DkMath.FLT.PrimeProvider.CosmicPetalBridgeGNNoWieferichResearch
+import DkMath.FLT.PrimeProvider.CosmicPetalBridgeGNNoWieferichValuation
 
 #print "file: DkMath.FLT.TriominoSquarefreeGNBridgeProviderImpl"
 
diff --git a/lean/dk_math/DkMath/NumberTheory/docs/BinomialPrimeWeighted/FLGNB-PetalRoadmap.md b/lean/dk_math/DkMath/NumberTheory/docs/BinomialPrimeWeighted/FLGNB-PetalRoadmap.md
index 5939018c..1b7419d2 100644
--- a/lean/dk_math/DkMath/NumberTheory/docs/BinomialPrimeWeighted/FLGNB-PetalRoadmap.md
+++ b/lean/dk_math/DkMath/NumberTheory/docs/BinomialPrimeWeighted/FLGNB-PetalRoadmap.md
@@ -1538,9 +1538,9 @@ Status:
 implemented
 ```
 
-`DkMath.FLT.PrimeProvider.CosmicPetalBridgeGNNoWieferichResearch` now has a
-direct handshake from the FLT Branch-B primitive-prime inputs to the shared
-`PrimitiveBeam` predicate:
+`DkMath.FLT.PrimeProvider.CosmicPetalBridgeGNNoWieferichValuation` now holds the
+no-sorry valuation surface.  It provides the direct handshake from the FLT
+Branch-B primitive-prime inputs to the shared `PrimitiveBeam` predicate:
 
 ```lean
 primitivePrimeFactorOfDiffPow_of_FLT_branch
@@ -1595,13 +1595,43 @@ Squarefree:
   sufficient condition that produces NoLift
 
 Research placeholder:
-  still isolated in the old research core, not used by the honest NoLift target
+  isolated in CosmicPetalBridgeGNNoWieferichResearch
+  not used by the honest NoLift / squarefree valuation target
+```
+
+Import split:
+
+```text
+CosmicPetalBridgeGNNoWieferichValuation:
+  honest valuation target
+  PrimitiveBeam handoff
+  NoLift wrapper
+  squarefree-as-NoLift wrapper
+
+CosmicPetalBridgeGNNoWieferichResearch:
+  legacy research core
+  fixed injection / target abstraction around the old placeholder
+
+TriominoSquarefreeGNBridgeProviderImpl:
+  now imports the Valuation surface, not the Research file
+
+CosmicPetalBridgeGN:
+  imports the Valuation surface explicitly because its public branch API uses
+  TriominoPrimitivePrimeFactorPadicValNatLeOneTarget
+
+remaining direct Research imports:
+  CosmicPetalBridgeGNNoWieferichDefault
+  CosmicPetalBridgeGNDescentBQuarantine
 ```
 
 Expected validation:
 
 ```sh
+lake build DkMath.FLT.PrimeProvider.CosmicPetalBridgeGNNoWieferichValuation
 lake build DkMath.FLT.PrimeProvider.CosmicPetalBridgeGNNoWieferichResearch
+lake build DkMath.FLT.PrimeProvider.TriominoSquarefreeGNBridgeProviderImpl
+lake build DkMath.FLT.PrimeProvider.CosmicPetalBridgeGN
+lake build DkMath.FLT.PrimeProvider
 ```
 
 ### Step 7: Refactor imports gradually
````
`````
