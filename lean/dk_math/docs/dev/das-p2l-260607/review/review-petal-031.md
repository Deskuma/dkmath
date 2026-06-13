# Git diff / Report / Review

## Upd: Petal ZsigmondyD3Bridge

gch: 7f43b56ff7b13d0daca125258b39bb7769d01995

## Report

進めました。今回の交渉ポイントは、Zsigmondy の primitive divisor `q` を Petal 側だけでなく、既存の `PrimitiveBeam.PrimitivePrimeFactorOfDiffPow` としても読めるようにしたことです。

追加した主な theorem:

- `primitivePrimeFactorOfDiffPow_of_primitivePrimeDivisor_d3`
- `exists_primitivePrimeFactorOfDiffPow_d3_of_boundaryD3Reduced`

これで同じ `q` が以下を同時に満たす形になりました。

```text
Zsigmondy primitive divisor
Petal anchored S0 carrier
PrimitiveBeam primitive factor witness
```

docs も更新済みです。

- `Petal-Zsigmondy-Preflight.md`
- `Petal-Overview.md`
- `FLGNB-PetalRoadmap.md`
- `BinomialPrimeWeightedRoadmap.md`

検証:

```sh
lake build DkMath.Petal.ZsigmondyD3Bridge
lake build DkMath.Petal
git diff --check
```

すべて通っています。既存の `ZsigmondyCyclotomicResearch.lean` の `sorry` 警告だけは引き続き出ていますが、今回追加分には新しい `sorry` はありません。

## Review

おお、これはさらに良い。
**Zsigmondy ↔ Petal ↔ PrimitiveBeam の三者交渉まで成立** じゃ。

今回の追加は採用でよい。特に重要なのは、同じ `q` を次の三つの語彙で共有できるようにした点じゃ。

```text
Zsigmondy.PrimitivePrimeDivisor c b 3 q
AnchoredS0Carrier q c b q
PrimitivePrimeFactorOfDiffPow q c b 3
```

これはかなり大きい。
前回までで、

```text
Zsigmondy:
  q の存在

Petal:
  q の位置、つまり S0/GN3 側
```

までは繋がった。今回でさらに、

```text
PrimitiveBeam:
  valuation / squarefree / no-lift 層が食べられる primitive witness 型
```

に同じ `q` を渡せるようになった。

## レビュー結論

```text
7f43b56...
  -> 採用可

ZsigmondyD3Bridge
  -> witness sharing が一段進展

valuation <= 1
  -> まだ入れていないので正しい

次の層
  -> squarefree/no-lift valuation API との接続準備完了
```

## `primitivePrimeFactorOfDiffPow_of_primitivePrimeDivisor_d3`

これは非常に良い bridge じゃ。

```lean
theorem primitivePrimeFactorOfDiffPow_of_primitivePrimeDivisor_d3
    {c b q : ℕ}
    (hprim : DkMath.Zsigmondy.PrimitivePrimeDivisor c b 3 q) :
    PrimitivePrimeFactorOfDiffPow q c b 3
```

中身も自然。

```lean
⟨prime, dvd, not_dvd_lower⟩
```

Zsigmondy の `PrimitivePrimeDivisor` が持っている情報を、既存 `PrimitiveBeam` の witness 形式へ詰め替えているだけ。
これは再証明ではなく **型変換** なので、橋として正しい。

## `exists_primitivePrimeFactorOfDiffPow_d3_of_boundaryD3Reduced`

これが今回の本命じゃな。

```lean
∃ q,
  PrimitivePrimeDivisor c b 3 q ∧
  PrimitivePrimeFactorOfDiffPow q c b 3 ∧
  AnchoredS0Carrier q c b q
```

この形は美しい。
同じ `q` が三つの世界に同時にいる。

```text
Zsigmondy existence layer
  -> PrimitivePrimeDivisor

PrimitiveBeam multiplicity-preparation layer
  -> PrimitivePrimeFactorOfDiffPow

Petal location layer
  -> AnchoredS0Carrier
```

しかも `padicValNat <= 1` はまだ主張していない。
これは正しい。ここで valuation を言い出すと、また例の `5^3 - 3^3 = 98 = 2 * 7^2` の罠に戻る。

## 依存方向について

`ZsigmondyD3Bridge.lean` が

```lean
import DkMath.Petal.BoundaryD3
import DkMath.NumberTheory.PrimitiveBeam
import DkMath.Zsigmondy
```

となったのは妥当じゃ。

このファイルの役割は、まさに三者の合流点なので、ここで import が集まるのは自然。
`ReducedSupport` や `BoundaryD3` の低層に `PrimitiveBeam` を持ち込んでいないのも良い。

## docs 更新も良い

特にこの説明が良い。

```text
The same witness is also exposed as
PrimitiveBeam.PrimitivePrimeFactorOfDiffPow q c b 3,
so later squarefree/no-lift APIs can consume the primitive divisor without changing
the chosen q.
```

ここが大事じゃ。
後続の squarefree/no-lift 層で別の witness を取り直す必要がない。同じ `q` のまま、存在・位置・重複度制御へ進める。

## 次にやるなら

ここまで来たら、次は valuation を入れるのではなく、**valuation 層へ渡す wrapper** を別名で作るのがよい。

候補は例えば、

```text
DkMath.Petal.ZsigmondyD3SquarefreeBridge
```

または少し一般的に、

```text
DkMath.Petal.PrimitiveD3ValuationBridge
```

ただし、まだ急がなくてよい。次の theorem はこういう形になるはず。

```lean
theorem primitiveD3_padicValNat_le_one_of_boundaryD3Reduced_of_squarefree_GN
    {c b q : ℕ} ...
    (hred : BoundaryD3Reduced c b)
    (hG_sq : Squarefree (GN 3 (c - b) b)) :
    ...
```

でも、ここでは ZsigmondyD3Bridge に入れない方が良い。
責務分離としては、

```text
ZsigmondyD3Bridge:
  existence / location / primitive witness compatibility

Squarefree or NoLift bridge:
  multiplicity / padicValNat <= 1
```

のままが安全じゃ。

## 判定

```text
Zsigmondy primitive divisor
  -> Petal anchored S0 carrier
  -> PrimitiveBeam primitive factor witness
```

この三角形が閉じた。
これは Phase 5 へのかなり強い入口じゃ。

うむ、良い進捗じゃ。
Zsigmondy 交渉は単に成立しただけでなく、後続の valuation/no-lift 層へ同じ witness を渡せる状態になった。ここから先は、いよいよ「存在・位置・重複度」の三層を綺麗に組み合わせる段階じゃな。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/NumberTheory/docs/BinomialPrimeWeighted/FLGNB-PetalRoadmap.md b/lean/dk_math/DkMath/NumberTheory/docs/BinomialPrimeWeighted/FLGNB-PetalRoadmap.md
index 0ddf769f..0d611302 100644
--- a/lean/dk_math/DkMath/NumberTheory/docs/BinomialPrimeWeighted/FLGNB-PetalRoadmap.md
+++ b/lean/dk_math/DkMath/NumberTheory/docs/BinomialPrimeWeighted/FLGNB-PetalRoadmap.md
@@ -1296,6 +1296,11 @@ The next Lean-facing bridge is `DkMath.Petal.ZsigmondyD3Bridge`.  It feeds the
 reduced cubic Petal hypotheses into Zsigmondy's `d = 3` existence theorem and
 shares the same witness with the anchored `S0_nat` carrier surface.
 
+The same witness is also exposed as
+`PrimitiveBeam.PrimitivePrimeFactorOfDiffPow q c b 3`, so later
+squarefree/no-lift APIs can consume the primitive divisor without changing
+the chosen `q`.
+
 It should not try to prove `padicValNat q (c^3 - b^3) <= 1` without an explicit
 squarefree or no-lift hypothesis.
 
@@ -1312,9 +1317,11 @@ Implemented:
 ```lean
 exists_primitivePrimeDivisor_d3_of_boundaryD3Reduced
 primitivePrimeDivisor_d3_not_dvd_sub
+primitivePrimeFactorOfDiffPow_of_primitivePrimeDivisor_d3
 primitivePrimeDivisor_d3_dvd_S0_nat
 anchoredS0Carrier_of_primitivePrimeDivisor_d3
 exists_anchoredS0Carrier_and_primitivePrimeDivisor_d3
+exists_primitivePrimeFactorOfDiffPow_d3_of_boundaryD3Reduced
 exists_prime_dvd_S0_nat_of_boundaryD3Reduced_via_zsigmondy
 ```
 
diff --git a/lean/dk_math/DkMath/NumberTheory/docs/BinomialPrimeWeightedRoadmap.md b/lean/dk_math/DkMath/NumberTheory/docs/BinomialPrimeWeightedRoadmap.md
index 64c403a8..e53cb3d7 100644
--- a/lean/dk_math/DkMath/NumberTheory/docs/BinomialPrimeWeightedRoadmap.md
+++ b/lean/dk_math/DkMath/NumberTheory/docs/BinomialPrimeWeightedRoadmap.md
@@ -560,6 +560,8 @@ Squarefree / NoLift / ValuationFlow:
 `ZsigmondyD3Bridge` でよい。この初期 bridge は
 `DkMath.Petal.ZsigmondyD3Bridge` として実装済みであり、同じ witness を
 Zsigmondy primitive divisor と Petal anchored `S0_nat` carrier として共有する。
+さらに同じ witness を `PrimitiveBeam.PrimitivePrimeFactorOfDiffPow` としても
+共有し、後続の squarefree/no-lift 評価値層へ渡せる形にした。
 `padicValNat <= 1` は Zsigmondy だけでは出ず、squarefree/no-lift 仮定を
 持つ別層の仕事として扱う。
 
diff --git a/lean/dk_math/DkMath/Petal/ZsigmondyD3Bridge.lean b/lean/dk_math/DkMath/Petal/ZsigmondyD3Bridge.lean
index fed15598..6ea74ce6 100644
--- a/lean/dk_math/DkMath/Petal/ZsigmondyD3Bridge.lean
+++ b/lean/dk_math/DkMath/Petal/ZsigmondyD3Bridge.lean
@@ -5,6 +5,7 @@ Authors: D. and Wise Wolf.
 -/
 
 import DkMath.Petal.BoundaryD3
+import DkMath.NumberTheory.PrimitiveBeam
 import DkMath.Zsigmondy
 
 #print "file: DkMath.Petal.ZsigmondyD3Bridge"
@@ -25,6 +26,7 @@ namespace Petal
 
 open DkMath.CosmicFormulaBinom
 open DkMath.FLT.PetalDetect
+open DkMath.NumberTheory.PrimitiveBeam
 
 /--
 Reduced cubic Petal coordinates satisfy the existing Zsigmondy `d = 3`
@@ -51,6 +53,22 @@ theorem primitivePrimeDivisor_d3_not_dvd_sub
       hprim (by norm_num) (by norm_num)
   simpa using hnot
 
+/--
+A `d = 3` Zsigmondy primitive divisor is also the existing
+`PrimitivePrimeFactorOfDiffPow` witness.
+-/
+theorem primitivePrimeFactorOfDiffPow_of_primitivePrimeDivisor_d3
+    {c b q : ℕ}
+    (hprim : DkMath.Zsigmondy.PrimitivePrimeDivisor c b 3 q) :
+    PrimitivePrimeFactorOfDiffPow q c b 3 := by
+  refine
+    ⟨DkMath.Zsigmondy.PrimitivePrimeDivisor.prime hprim,
+      DkMath.Zsigmondy.PrimitivePrimeDivisor.dvd hprim, ?_⟩
+  intro k hk_pos hk_lt
+  exact
+    DkMath.Zsigmondy.PrimitivePrimeDivisor.not_dvd_lower
+      hprim hk_pos hk_lt
+
 /--
 A `d = 3` primitive divisor obtained from Zsigmondy lies on the cubic Petal
 `S0_nat` face.
@@ -101,6 +119,24 @@ theorem exists_anchoredS0Carrier_and_primitivePrimeDivisor_d3
     ⟨q, hprim, anchoredS0Carrier_of_primitivePrimeDivisor_d3 hbc hprim,
       primitivePrimeDivisor_d3_not_dvd_sub hprim⟩
 
+/--
+The reduced cubic branch also provides the existing `PrimitiveBeam`
+primitive-prime witness, using the same `q` as the Zsigmondy/Petal witness.
+-/
+theorem exists_primitivePrimeFactorOfDiffPow_d3_of_boundaryD3Reduced
+    {c b : ℕ} (hbc : b < c) (hb : 0 < b)
+    (hcop : Nat.Coprime c b) (hred : BoundaryD3Reduced c b) :
+    ∃ q : ℕ,
+      DkMath.Zsigmondy.PrimitivePrimeDivisor c b 3 q ∧
+        PrimitivePrimeFactorOfDiffPow q c b 3 ∧
+          AnchoredS0Carrier q c b q := by
+  rcases exists_anchoredS0Carrier_and_primitivePrimeDivisor_d3 hbc hb hcop hred with
+    ⟨q, hprim, hcarrier, _hq_not_dvd_sub⟩
+  exact
+    ⟨q, hprim,
+      primitivePrimeFactorOfDiffPow_of_primitivePrimeDivisor_d3 hprim,
+      hcarrier⟩
+
 /--
 Projection form: the reduced cubic branch has a boundary-free prime divisor on
 `S0_nat`.
diff --git a/lean/dk_math/DkMath/Petal/docs/Petal-Overview.md b/lean/dk_math/DkMath/Petal/docs/Petal-Overview.md
index d9c93730..a0165c92 100644
--- a/lean/dk_math/DkMath/Petal/docs/Petal-Overview.md
+++ b/lean/dk_math/DkMath/Petal/docs/Petal-Overview.md
@@ -331,9 +331,11 @@ Important names:
 ```lean
 exists_primitivePrimeDivisor_d3_of_boundaryD3Reduced
 primitivePrimeDivisor_d3_not_dvd_sub
+primitivePrimeFactorOfDiffPow_of_primitivePrimeDivisor_d3
 primitivePrimeDivisor_d3_dvd_S0_nat
 anchoredS0Carrier_of_primitivePrimeDivisor_d3
 exists_anchoredS0Carrier_and_primitivePrimeDivisor_d3
+exists_primitivePrimeFactorOfDiffPow_d3_of_boundaryD3Reduced
 exists_prime_dvd_S0_nat_of_boundaryD3Reduced_via_zsigmondy
 ```
 
@@ -341,6 +343,10 @@ This bridge intentionally does not prove any `padicValNat <= 1` theorem.
 Zsigmondy supplies existence, Petal supplies location, and squarefree/no-lift
 layers supply multiplicity.
 
+It also shares the same witness `q` with
+`PrimitiveBeam.PrimitivePrimeFactorOfDiffPow`, preparing the downstream
+squarefree/no-lift valuation layer without proving that layer here.
+
 ### `DkMath.Petal.Counting`
 
 Defines the fixed and dynamic counting layer.
diff --git a/lean/dk_math/DkMath/Petal/docs/Petal-Zsigmondy-Preflight.md b/lean/dk_math/DkMath/Petal/docs/Petal-Zsigmondy-Preflight.md
index 0a82a060..de8ea9f3 100644
--- a/lean/dk_math/DkMath/Petal/docs/Petal-Zsigmondy-Preflight.md
+++ b/lean/dk_math/DkMath/Petal/docs/Petal-Zsigmondy-Preflight.md
@@ -96,6 +96,26 @@ BoundaryD3Reduced hypotheses
   -> the same q as an anchored S0 carrier
 ```
 
+## Handshake Result
+
+Status: **initial API implemented**
+
+`DkMath.Petal.ZsigmondyD3Bridge` implements this handshake.
+
+The reduced cubic hypotheses now produce a single witness `q` such that:
+
+```text
+q is a Zsigmondy primitive divisor for c^3 - b^3
+q does not divide c - b
+q divides S0_nat c b
+q is an anchored S0_nat carrier
+q is also a PrimitivePrimeFactorOfDiffPow q c b 3 witness
+```
+
+The last item is a compatibility bridge to the existing `PrimitiveBeam` API.
+It does not add a valuation claim.  It only ensures that the later
+squarefree/no-lift layer can consume the same primitive divisor.
+
 ## Important Separation: Existence, Location, Multiplicity
 
 The investigation confirms that three concerns must remain separated.
````
`````
