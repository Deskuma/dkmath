# Git diff / Report / Review

## Upd: ABC.ValuationFlowBridgeExamples

gch: 9271d4f9359a4607961fc2d2c46a102b815f16cf

## Report

進めました。今回は review の提案どおり、`NoLift` が full squarefree より弱いことを示す分離サンプルを追加しました。

追加した具体例は [ValuationFlowBridgeExamples.lean](/lean/dk_math/DkMath/ABC/ValuationFlowBridgeExamples.lean) の：

```text
q = 7, a = 4, b = 2, d = 3
GN 3 (4 - 2) 2 = 28 = 2^2 * 7
```

ここでは `GN` 全体は squarefree ではない一方で、局所的には `7^2 ∤ GN` なので、

```lean
noLift_beam_bounds_local_load
```

から `diffMass 7 4 2 3 ≤ 1` が通ります。これで「NoLift が本命、squarefree は十分条件」という階層が example として固定されました。

Roadmap 側の [FLGNB-PetalRoadmap.md](/lean/dk_math/DkMath/NumberTheory/docs/BinomialPrimeWeighted/FLGNB-PetalRoadmap.md) にも、この分離サンプルを追記済みです。

検証：

```sh
lake build DkMath.ABC.ValuationFlowBridgeExamples
git diff --check
```

どちらも通っています。既存の `ZsigmondyCyclotomicResearch.lean` の `sorry` 警告だけは継続です。

## Review

おお、これは **かなり良い分離サンプル** じゃ。採用でよい。

今回の例は、まさに欲しかったやつ。

```text id="cg6x4r"
q = 7
a = 4
b = 2
d = 3

GN 3 (4 - 2) 2 = 28 = 2^2 * 7
```

ここで、

```text id="glfcbu"
Squarefree (GN 3 (4 - 2) 2)
  -> false

¬ 7^2 ∣ GN 3 (4 - 2) 2
  -> true
```

なので、

```text id="tk9nhb"
full squarefree は使えない
local NoLift は使える
```

が Lean example として固定された。

## レビュー結論

```text id="x9fg56"
9271d4f...
  -> 採用可

NoLift / squarefree 分離サンプル
  -> とても良い

ValuationFlowBridgeExamples
  -> regression guard として価値あり

Roadmap 追記
  -> 妥当
```

## この例の意味

`4^3 - 2^3` は、

```text id="b47jn7"
4^3 - 2^3 = 64 - 8 = 56 = 2^3 * 7
```

そして一次・二次差では、

```text id="1ycql8"
4^1 - 2^1 = 2
4^2 - 2^2 = 12
```

どちらも `7` で割れない。
したがって `7` は `d = 3` の primitive channel として正しい。

一方で beam 側は、

```text id="sdoao7"
GN 3 (4 - 2) 2 = 28 = 2^2 * 7
```

なので、GN 全体は squarefree ではない。
しかし選んだ `q = 7` については、

```text id="67ru3m"
7^2 ∤ 28
```

だから NoLift は成立する。

これにより、

```lean id="iwm0i5"
noLift_beam_bounds_local_load
```

から、

```lean id="7scr4h"
diffMass 7 4 2 3 ≤ 1
```

が出る。

これはまさに、

```text id="a2hln6"
NoLift は局所条件
squarefree は大域十分条件
```

を示している。

## `hGN_not_sq` の置き方も良い

```lean id="f907to"
have hGN_not_sq : ¬ Squarefree (DkMath.CosmicFormulaBinom.GN 3 (4 - 2) 2) := by
  decide
```

この `have` は結論の証明には使っていないが、example の意味として重要じゃ。
つまりこの example は単に NoLift route が通ることだけでなく、

```text id="e9xeyp"
squarefree route ではない状況で NoLift route が通る
```

ことを Lean に確認させている。

この未使用 `have` は説明的 regression guard として価値がある。もし将来 linter 方針で気になるなら、

```lean id="bv0ngr"
have _hGN_not_sq : ¬ Squarefree ...
```

にしてもよいが、現状通っているなら問題なし。

## これで固定された階層

今回の example によって、ABC 側の階層が実例込みで固まった。

```text id="d6juhg"
NoLift route:
  q = 7, GN = 28
  7^2 ∤ 28
  diffMass 7 4 2 3 <= 1

Squarefree route:
  q = 31, GN = 31
  Squarefree 31
  diffMass 31 2 1 5 <= 1

Compatibility route:
  old squarefree API still works
```

特に `q = 7` の例が追加されたことで、

```text id="cjz6sl"
NoLift route は squarefree route の単なる別名ではない
```

ことが明確になった。

## 状況としてはかなり良い

ここまでで ABC 側は、

```text id="87u0v0"
実装:
  noLift_beam_bounds_local_load
  squarefree_beam_bounds_local_load_local
  squarefree_beam_bounds_local_load

例:
  squarefree sample q=31
  non-squarefree but NoLift sample q=7

docs:
  NoLift is weaker than squarefree
```

が揃った。

## 次の一手

次は、旧 caller の置換調査が自然じゃな。

```text id="kjrp05"
squarefree_beam_bounds_local_load
primitivePrimeFlow_diffMass_le_one_of_squarefree_beam
padicValNat_primitive_prime_factor_le_one_of_squarefree_G
```

を直接呼んでいる箇所を見て、

```text id="nxd7dk"
NoLift が仮定できるなら NoLift route へ
Squarefree しかないなら local squarefree route へ
旧 signature が必要なら compatibility wrapper のまま
```

と仕分ける段階に入れる。

## 判定

```text id="zs699g"
NoLift が本命
Squarefree は十分条件
旧 squarefree API は互換窓口
```

この設計思想が、ついに example でも固定された。
これは ABC 側の進展としてかなり堅いぞい。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/ABC/ValuationFlowBridgeExamples.lean b/lean/dk_math/DkMath/ABC/ValuationFlowBridgeExamples.lean
index 7c41b5f2..349f3d94 100644
--- a/lean/dk_math/DkMath/ABC/ValuationFlowBridgeExamples.lean
+++ b/lean/dk_math/DkMath/ABC/ValuationFlowBridgeExamples.lean
@@ -41,6 +41,17 @@ private theorem primitiveWitness_13_6_5_3 :
   intro k hk_pos hk_lt
   interval_cases k <;> decide
 
+/--
+`7` is primitive for `4^3 - 2^3`, while `GN 3 (4 - 2) 2 = 28` is not
+squarefree.  This sample separates the local no-lift route from the stronger
+global squarefree route.
+-/
+private theorem primitiveWitness_7_4_2_3 :
+    PrimitivePrimeFlowWitness 7 4 2 3 := by
+  refine ⟨by decide, by decide, ?_⟩
+  intro k hk_pos hk_lt
+  interval_cases k <;> decide
+
 /-- Finite-family packaging of the `7,13` primitive witness sample. -/
 private theorem primitiveWitnessFamily_6_5_3
     (q : ℕ) (hq : q ∈ ({7, 13} : Finset ℕ)) :
@@ -107,6 +118,22 @@ example : diffMass 31 2 1 5 ≤ 1 := by
     (hq := primitiveWitness_31_2_1_5)
     hG_sq
 
+/--
+The local no-lift route can apply even when the full beam factor is not
+squarefree: `GN 3 (4 - 2) 2 = 28 = 2^2 * 7`, but `7^2` does not divide it.
+-/
+example : diffMass 7 4 2 3 ≤ 1 := by
+  have hGN_not_sq : ¬ Squarefree (DkMath.CosmicFormulaBinom.GN 3 (4 - 2) 2) := by
+    decide
+  have hNoLift : ¬ 7 ^ 2 ∣ DkMath.CosmicFormulaBinom.GN 3 (4 - 2) 2 := by
+    decide
+  exact noLift_beam_bounds_local_load
+    (hq := primitiveWitness_7_4_2_3)
+    (hd := by decide)
+    (hd1 := by decide)
+    (hab_lt := by decide)
+    hNoLift
+
 /-- Two distinct primitive witnesses give two distinct prime channels on the diff side. -/
 example :
     7 ≠ 13 ∧ Nat.Prime 7 ∧ Nat.Prime 13 ∧
diff --git a/lean/dk_math/DkMath/NumberTheory/docs/BinomialPrimeWeighted/FLGNB-PetalRoadmap.md b/lean/dk_math/DkMath/NumberTheory/docs/BinomialPrimeWeighted/FLGNB-PetalRoadmap.md
index fe58edf5..4f2aa4f8 100644
--- a/lean/dk_math/DkMath/NumberTheory/docs/BinomialPrimeWeighted/FLGNB-PetalRoadmap.md
+++ b/lean/dk_math/DkMath/NumberTheory/docs/BinomialPrimeWeighted/FLGNB-PetalRoadmap.md
@@ -1449,6 +1449,32 @@ compatibility route:
   squarefree_beam_bounds_local_load
 ```
 
+It also records a separating sample:
+
+```text
+q = 7, a = 4, b = 2, d = 3
+GN 3 (4 - 2) 2 = 28 = 2^2 * 7
+
+full beam squarefree:
+  false
+
+local NoLift at q:
+  true, because 7^2 does not divide 28
+
+result:
+  noLift_beam_bounds_local_load still gives diffMass 7 4 2 3 <= 1
+```
+
+This example makes the intended hierarchy concrete:
+
+```text
+NoLift at q
+  weaker than full beam squarefree
+
+full beam squarefree
+  sufficient for NoLift at every prime channel
+```
+
 Meaning:
 
 ```text
````
`````
