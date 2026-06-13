# Git diff / Report / Review

## Upd: ABC.ValuationFlowBridgeExamples

gch: a9ef15ff9b365483eb333c41af2590ebfba6c574

## Report

進めました。`ValuationFlowBridgeExamples` に、`q = 31, a = 2, b = 1, d = 5` の小サンプルで次の 3 ルートを固定しました。

- `noLift_beam_bounds_local_load`
- `squarefree_beam_bounds_local_load_local`
- 旧互換 `squarefree_beam_bounds_local_load`

旧互換サンプルは、新 API の `_hd_ge`, `_hb`, `_hab`, `_hpnd` に合わせて修正済みです。

Roadmap も Step 6.2 に追記して、examples が NoLift / local squarefree / compatibility の検証層であることを記録しました。

検証:

```sh
lake build DkMath.ABC.ValuationFlowBridgeExamples
git diff --check
```

どちらも通っています。既存の `ZsigmondyCyclotomicResearch.lean` の `sorry` 警告は継続ですが、今回追加・修正した pass 自体は no-sorry で通っています。

## Review

おお、これは **良い example 固定** じゃ。採用でよい。

今回の価値は、API 本体の追加というより、ABC 側の新しい三段構えが **小さな具体例で regression guard 化された** ことじゃな。

```text
q = 31
a = 2
b = 1
d = 5
GN 5 (2 - 1) 1 = 31
```

このサンプルで、

```lean
noLift_beam_bounds_local_load
squarefree_beam_bounds_local_load_local
squarefree_beam_bounds_local_load
```

の三ルートがすべて通るようになった。

## レビュー結論

```text
a9ef15ff...
  -> 採用可

ValuationFlowBridgeExamples
  -> NoLift / local squarefree / compatibility の三経路確認として良い

Roadmap 追記
  -> 妥当

Lean build
  -> 対象 build 成功なら十分
```

## 良い点

一番良いのは、旧互換 API だけでなく、新しい本命 API を example にしたことじゃ。

```lean
example : diffMass 31 2 1 5 ≤ 1 := by
  have hNoLift : ¬ 31 ^ 2 ∣ DkMath.CosmicFormulaBinom.GN 5 (2 - 1) 1 := by
    decide
  exact noLift_beam_bounds_local_load
    (hq := primitiveWitness_31_2_1_5)
    (hd := by decide)
    (hd1 := by decide)
    (hab_lt := by decide)
    hNoLift
```

これは、ABC 側の本命が

```text
NoLift beam
  -> local load <= 1
```

であることを具体例で固定している。

## squarefree route も良い

```lean
have hGN : DkMath.CosmicFormulaBinom.GN 5 (2 - 1) 1 = 31 := by
  decide
have hG_sq : Squarefree (DkMath.CosmicFormulaBinom.GN 5 (2 - 1) 1) := by
  simpa [hGN] using (show Squarefree 31 from (show Nat.Prime 31 by decide).squarefree)
```

ここで、

```text
GN 5 1 1 = 31
31 は prime
よって squarefree
```

を Lean に確認させている。
squarefree が NoLift の十分条件として働くルートの example として分かりやすい。

## 旧互換 route の修正も妥当

```lean
(_hd_ge := by decide)
(_hb := by decide)
(_hab := by decide)
(_hpnd := by decide)
```

これは、旧 API が compatibility wrapper になったことを example 側にも反映している。

つまり旧 API はまだ使えるが、内部的にはもう主要仮定ではない。
その意味で `_` prefix は良いシグナルじゃ。

## この example の意味

今回のサンプルは、ABC の local load 経路をこう固定している。

```text
Primitive witness:
  PrimitivePrimeFlowWitness 31 2 1 5

Beam:
  GN 5 (2 - 1) 1 = 31

NoLift:
  not 31^2 divides 31

Squarefree:
  Squarefree 31

Conclusion:
  diffMass 31 2 1 5 <= 1
```

非常に小さく、`decide` で閉じるので regression example として良い。

## 注意点

大きな問題はない。

あえて言うなら、`q = 31, a = 2, b = 1, d = 5` はかなり綺麗すぎるサンプルなので、将来的にはもう一つだけ **NoLift は成立するが GN 全体は squarefree ではない** サンプルがあると、NoLift route の意味がさらに強くなる。

例えば構造としては、

```text
GN d (a-b) b = q * r^2
q^2 ∤ GN
```

のようなケース。
この場合、

```text
Squarefree GN は失敗
NoLift q GN は成功
```

になるので、NoLift が squarefree より弱いことを example で示せる。

ただし今すぐ必要ではない。今回の三経路固定だけで十分価値がある。

## 現在の到達点

これで ABC 側も、実装・wrapper・example の三点が揃った。

```text
PrimitiveBeam:
  NoLift valuation theorem

ValuationFlow.Primitive:
  diffMass <= 1 wrapper

ABC.ValuationFlowBridge:
  local load <= 1 wrapper

ABC.ValuationFlowBridgeExamples:
  q=31 sampleで NoLift / squarefree / compatibility を固定
```

## 判定

```text
NoLift route:
  実装済み
  ABC wrapper 済み
  example 済み

local squarefree route:
  実装済み
  ABC wrapper 済み
  example 済み

旧 compatibility route:
  維持
  example 済み
```

うむ、かなり堅い。
これで ABC 側の新 route は「理論上つながった」だけでなく、具体サンプルで壊れにくくなった。次は旧 caller の置換調査、または NoLift が squarefree より弱いことを示す非 squarefree サンプル探索が自然じゃな。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/ABC/ValuationFlowBridgeExamples.lean b/lean/dk_math/DkMath/ABC/ValuationFlowBridgeExamples.lean
index 460208f2..7c41b5f2 100644
--- a/lean/dk_math/DkMath/ABC/ValuationFlowBridgeExamples.lean
+++ b/lean/dk_math/DkMath/ABC/ValuationFlowBridgeExamples.lean
@@ -68,6 +68,30 @@ example : diffMass 31 2 1 5 = beamMass 31 2 1 5 := by
     (by decide)
 
 /-- The squarefree beam sample `GN 5 1 1 = 31` yields local load at most `1`. -/
+example : diffMass 31 2 1 5 ≤ 1 := by
+  have hNoLift : ¬ 31 ^ 2 ∣ DkMath.CosmicFormulaBinom.GN 5 (2 - 1) 1 := by
+    decide
+  exact noLift_beam_bounds_local_load
+    (hq := primitiveWitness_31_2_1_5)
+    (hd := by decide)
+    (hd1 := by decide)
+    (hab_lt := by decide)
+    hNoLift
+
+/-- Squarefree `GN 5 1 1 = 31` is a sufficient condition for the same local load bound. -/
+example : diffMass 31 2 1 5 ≤ 1 := by
+  have hGN : DkMath.CosmicFormulaBinom.GN 5 (2 - 1) 1 = 31 := by
+    decide
+  have hG_sq : Squarefree (DkMath.CosmicFormulaBinom.GN 5 (2 - 1) 1) := by
+    simpa [hGN] using (show Squarefree 31 from (show Nat.Prime 31 by decide).squarefree)
+  exact squarefree_beam_bounds_local_load_local
+    (hq := primitiveWitness_31_2_1_5)
+    (hd := by decide)
+    (hd1 := by decide)
+    (hab_lt := by decide)
+    hG_sq
+
+/-- Compatibility sample for the older squarefree-beam API. -/
 example : diffMass 31 2 1 5 ≤ 1 := by
   have hGN : DkMath.CosmicFormulaBinom.GN 5 (2 - 1) 1 = 31 := by
     decide
@@ -75,11 +99,11 @@ example : diffMass 31 2 1 5 ≤ 1 := by
     simpa [hGN] using (show Squarefree 31 from (show Nat.Prime 31 by decide).squarefree)
   exact squarefree_beam_bounds_local_load
     (hd_prime := by decide)
-    (hd_ge := by decide)
+    (_hd_ge := by decide)
     (hab_lt := by decide)
-    (hb := by decide)
-    (hab := by decide)
-    (hpnd := by decide)
+    (_hb := by decide)
+    (_hab := by decide)
+    (_hpnd := by decide)
     (hq := primitiveWitness_31_2_1_5)
     hG_sq
 
diff --git a/lean/dk_math/DkMath/NumberTheory/docs/BinomialPrimeWeighted/FLGNB-PetalRoadmap.md b/lean/dk_math/DkMath/NumberTheory/docs/BinomialPrimeWeighted/FLGNB-PetalRoadmap.md
index 64820344..fe58edf5 100644
--- a/lean/dk_math/DkMath/NumberTheory/docs/BinomialPrimeWeighted/FLGNB-PetalRoadmap.md
+++ b/lean/dk_math/DkMath/NumberTheory/docs/BinomialPrimeWeighted/FLGNB-PetalRoadmap.md
@@ -1435,6 +1435,20 @@ squarefree_beam_bounds_local_load_local
 squarefree_beam_bounds_local_load
 ```
 
+`DkMath.ABC.ValuationFlowBridgeExamples` records the same API split on the
+small primitive sample `q = 31, a = 2, b = 1, d = 5`:
+
+```text
+NoLift route:
+  noLift_beam_bounds_local_load
+
+local squarefree route:
+  squarefree_beam_bounds_local_load_local
+
+compatibility route:
+  squarefree_beam_bounds_local_load
+```
+
 Meaning:
 
 ```text
@@ -1451,6 +1465,7 @@ Expected validation:
 ```sh
 lake build DkMath.NumberTheory.ValuationFlow.Primitive
 lake build DkMath.ABC.ValuationFlowBridge
+lake build DkMath.ABC.ValuationFlowBridgeExamples
 ```
 
 ### Step 7: Refactor imports gradually
````
`````
