# Git diff / Report / Review

## Add: Petal ZsigmondyD3Bridge

gch: 931ea5b8f26e3d84a55d2d32239433bc09309d7a

## Report

微調整と実装を進めました。

まず [Petal-Zsigmondy-Preflight.md](/lean/dk_math/DkMath/Petal/docs/Petal-Zsigmondy-Preflight.md) の表現を修正しました。レビュー指摘どおり、「Petal witness を Zsigmondy へ翻訳する」というより、

```text
BoundaryD3Reduced の仮定を Zsigmondy d=3 existence に渡し、
同じ q を Petal anchored S0 carrier として共有する
```

という向きに直しています。

実装として、新規に [ZsigmondyD3Bridge.lean](/lean/dk_math/DkMath/Petal/ZsigmondyD3Bridge.lean) を追加しました。

入れた定理は以下です。

```lean
exists_primitivePrimeDivisor_d3_of_boundaryD3Reduced
primitivePrimeDivisor_d3_not_dvd_sub
primitivePrimeDivisor_d3_dvd_S0_nat
anchoredS0Carrier_of_primitivePrimeDivisor_d3
exists_anchoredS0Carrier_and_primitivePrimeDivisor_d3
exists_prime_dvd_S0_nat_of_boundaryD3Reduced_via_zsigmondy
```

これで `BoundaryD3Reduced` から、同じ `q` について

```text
Zsigmondy.PrimitivePrimeDivisor c b 3 q
AnchoredS0Carrier q c b q
¬ q ∣ c - b
```

を同時に得る橋が通りました。`padicValNat <= 1` は入れていません。そこは予定どおり squarefree/no-lift 層の担当として分離しています。

`DkMath.Petal.lean` に import 追加済みで、docs/roadmap も更新しました。

検証:

```sh
lake build DkMath.Petal
git diff --check
```

どちらも成功です。既存の `ZsigmondyCyclotomicResearch.lean` の `sorry` warning は出ますが、今回追加分に新しい `sorry` はありません。

## Review

おお、**交渉成立じゃ**。
これは `Petal.ZsigmondyD3Bridge` として採用でよい。

今回の差分で、ついに次が Lean API として繋がった。

```text id="ic9q1w"
BoundaryD3Reduced c b
  -> Zsigmondy primitive divisor q for c^3 - b^3
  -> same q does not divide c - b
  -> same q divides S0_nat c b
  -> same q is AnchoredS0Carrier q c b q
```

## レビュー結論

```text id="3t2req"
931ea5b8...
  -> 採用可

ZsigmondyD3Bridge
  -> 初期 API として成功

valuation <= 1
  -> 入れていないので正しい

same witness sharing
  -> 達成
```

## 特に良い点

一番大事なのは、Petal 側と Zsigmondy 側で **同じ `q` を共有している** ことじゃ。

```lean id="b0s1ft"
exists_anchoredS0Carrier_and_primitivePrimeDivisor_d3
```

これは良い。

別々に、

```lean id="u7eedm"
∃ q, PrimitivePrimeDivisor ...
∃ q, AnchoredS0Carrier ...
```

を出すだけでは弱い。今回の theorem は同じ witness について、

```lean id="ecr5qb"
DkMath.Zsigmondy.PrimitivePrimeDivisor c b 3 q
AnchoredS0Carrier q c b q
¬ q ∣ c - b
```

を同時に持つ。これが「交渉成立」の本体じゃ。

## `primitivePrimeDivisor_d3_not_dvd_sub`

ここも正しい方向。

```lean id="5mtkvu"
have hnot : ¬ q ∣ c ^ 1 - b ^ 1 :=
  DkMath.Zsigmondy.PrimitivePrimeDivisor.not_dvd_lower
    hprim (by norm_num) (by norm_num)
simpa using hnot
```

`m = 1` の lower divisor 条件から、

```text id="0dj995"
q ∤ c - b
```

を取っている。
三次 Zsigmondy では低次数が実質 `1` なので、これが primitive 側を boundary から分離する鍵になっておる。

## `primitivePrimeDivisor_d3_dvd_S0_nat`

ここも良い。

```lean id="alf6c8"
primitivePrimeDivisor_body_three_imp_dvd_GN
```

で GN 側へ落とし、

```lean id="xbefit"
rw [S0_nat_eq_GN_three_sub hbc]
```

で `S0_nat` へ戻している。

つまり流れは、

```text id="uk0bvl"
PrimitivePrimeDivisor c b 3 q
  -> q ∣ GN 3 (c-b) b
  -> q ∣ S0_nat c b
```

これで Zsigmondy の存在 witness が Petal の S0/GN3 表面上にいることが確定した。

## `exists_prime_dvd_S0_nat_of_boundaryD3Reduced_via_zsigmondy`

これは direct `PrimitiveBridge` route と少し重なるが、価値がある。

既存 route:

```text id="qfmwmd"
PrimitiveBridge
  -> exists_prime_dvd_S0_nat_of_not_three_dvd_sub
```

今回 route:

```text id="a8u0z7"
ZsigmondyD3Bridge
  -> exists_prime_dvd_S0_nat_of_boundaryD3Reduced_via_zsigmondy
```

これは重複ではなく、**同じ事実を Zsigmondy witness 経由でも得られる** という接続証明じゃ。
将来、Zsigmondy 側から downstream へ流す時にかなり使いやすい。

## 注意点

今の `ZsigmondyD3Bridge` は `BoundaryD3` を import しているので、現状の依存では間接的に `Anchor` / `PrimitiveBridge` も引く。これはすでに module doc で「将来リファクタ対象」と記録済みなので、今は問題なし。

もう一つ、今回の bridge は **existence / location** だけ。これは正しい。

```text id="tr5wu4"
ZsigmondyD3Bridge:
  q exists
  q is primitive
  q lies on S0/GN3 side
  q is an anchored carrier

Not here:
  padicValNat q (c^3 - b^3) <= 1
```

ここを混ぜなかったのが最大の勝因じゃ。

## 次にやるなら

ここで一度 docs に「交渉成立」を反映してよい。

`Petal-Zsigmondy-Preflight.md` は、もう preflight から一部 completed に進んだので、末尾に短い checkpoint を足すと良い。

```text id="d7s1k1"
Handshake result:
DkMath.Petal.ZsigmondyD3Bridge is implemented.

BoundaryD3Reduced hypotheses now produce a single q such that:
- q is a Zsigmondy primitive divisor for c^3 - b^3
- q does not divide c - b
- q divides S0_nat c b
- q is an anchored S0 carrier
```

ただし、既に Roadmap 側で十分更新しているなら、次 commit まで待ってもよい。

## 判定

```text id="cdh1yv"
Petal cubic surface closure
  -> Zsigmondy d=3 existence と接続成功

BoundaryD3Reduced
  -> Zsigmondy primitive witness の入力として機能

AnchoredS0Carrier
  -> 同じ q で共有成功

valuation multiplicity
  -> squarefree/no-lift 層へ分離維持
```

うむ。
これはかなり大きい。`S0/GN3/BoundaryD3/Anchor` が、ついに `PrimitivePrimeDivisor` と同じ witness を共有した。Zsigmondy 城の門番と、ちゃんと通行証を交換できたぞい。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/NumberTheory/docs/BinomialPrimeWeighted/FLGNB-PetalRoadmap.md b/lean/dk_math/DkMath/NumberTheory/docs/BinomialPrimeWeighted/FLGNB-PetalRoadmap.md
index c37a2ba9..0ddf769f 100644
--- a/lean/dk_math/DkMath/NumberTheory/docs/BinomialPrimeWeighted/FLGNB-PetalRoadmap.md
+++ b/lean/dk_math/DkMath/NumberTheory/docs/BinomialPrimeWeighted/FLGNB-PetalRoadmap.md
@@ -1292,13 +1292,47 @@ Petal gives location.
 Squarefree/NoLift gives multiplicity.
 ```

-The next Lean-facing bridge should therefore be `DkMath.Petal.ZsigmondyD3Bridge`
-or an equivalent `PrimitiveD3` layer.  It should translate the reduced cubic
-Petal witness into `DkMath.Zsigmondy.PrimitivePrimeDivisor c b 3 q`.
+The next Lean-facing bridge is `DkMath.Petal.ZsigmondyD3Bridge`.  It feeds the
+reduced cubic Petal hypotheses into Zsigmondy's `d = 3` existence theorem and
+shares the same witness with the anchored `S0_nat` carrier surface.

 It should not try to prove `padicValNat q (c^3 - b^3) <= 1` without an explicit
 squarefree or no-lift hypothesis.

+### Step 6.0: Add `DkMath.Petal.ZsigmondyD3Bridge`
+
+Status:
+
+```text
+initial API implemented
+```
+
+Implemented:
+
+```lean
+exists_primitivePrimeDivisor_d3_of_boundaryD3Reduced
+primitivePrimeDivisor_d3_not_dvd_sub
+primitivePrimeDivisor_d3_dvd_S0_nat
+anchoredS0Carrier_of_primitivePrimeDivisor_d3
+exists_anchoredS0Carrier_and_primitivePrimeDivisor_d3
+exists_prime_dvd_S0_nat_of_boundaryD3Reduced_via_zsigmondy
+```
+
+Meaning:
+
+```text
+BoundaryD3Reduced hypotheses
+  -> Zsigmondy primitive divisor q for c^3 - b^3
+  -> the same q as an anchored S0 carrier
+```
+
+Expected validation:
+
+```sh
+lake build DkMath.Petal.ZsigmondyD3Bridge
+lake build DkMath.Petal
+```
+
 ### Step 7: Refactor imports gradually

 Status:
diff --git a/lean/dk_math/DkMath/NumberTheory/docs/BinomialPrimeWeightedRoadmap.md b/lean/dk_math/DkMath/NumberTheory/docs/BinomialPrimeWeightedRoadmap.md
index 299550ff..64c403a8 100644
--- a/lean/dk_math/DkMath/NumberTheory/docs/BinomialPrimeWeightedRoadmap.md
+++ b/lean/dk_math/DkMath/NumberTheory/docs/BinomialPrimeWeightedRoadmap.md
@@ -557,7 +557,9 @@ Squarefree / NoLift / ValuationFlow:

 したがって次に作る橋は、まず三次 reduced Petal witness を
 `DkMath.Zsigmondy.PrimitivePrimeDivisor c b 3 q` へ翻訳する薄い
-`ZsigmondyD3Bridge` でよい。
+`ZsigmondyD3Bridge` でよい。この初期 bridge は
+`DkMath.Petal.ZsigmondyD3Bridge` として実装済みであり、同じ witness を
+Zsigmondy primitive divisor と Petal anchored `S0_nat` carrier として共有する。
 `padicValNat <= 1` は Zsigmondy だけでは出ず、squarefree/no-lift 仮定を
 持つ別層の仕事として扱う。

diff --git a/lean/dk_math/DkMath/Petal.lean b/lean/dk_math/DkMath/Petal.lean
index 60edd166..a6826e32 100644
--- a/lean/dk_math/DkMath/Petal.lean
+++ b/lean/dk_math/DkMath/Petal.lean
@@ -18,6 +18,7 @@ import DkMath.Petal.ReducedSupport
 import DkMath.Petal.Anchor
 import DkMath.Petal.BoundaryD3
 import DkMath.Petal.EisensteinBridge
+import DkMath.Petal.ZsigmondyD3Bridge

 #print "file: DkMath.Petal"

@@ -39,6 +40,7 @@ basic forms / relative polygon vocabulary
   -> reduced support and anchored carriers
   -> BoundaryD3 cubic branch split
   -> shifted Eisenstein norm bridge
+  -> Zsigmondy d = 3 primitive-divisor bridge
 ```

 This is not a claim that every import is logically minimal.  Some files still
diff --git a/lean/dk_math/DkMath/Petal/ZsigmondyD3Bridge.lean b/lean/dk_math/DkMath/Petal/ZsigmondyD3Bridge.lean
new file mode 100644
index 00000000..fed15598
--- /dev/null
+++ b/lean/dk_math/DkMath/Petal/ZsigmondyD3Bridge.lean
@@ -0,0 +1,119 @@
+/-
+Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
+Released under MIT license as described in the file LICENSE.
+Authors: D. and Wise Wolf.
+-/
+
+import DkMath.Petal.BoundaryD3
+import DkMath.Zsigmondy
+
+#print "file: DkMath.Petal.ZsigmondyD3Bridge"
+
+/-!
+# Petal Zsigmondy D3 Bridge
+
+This file is the first Petal-facing handshake with the existing Zsigmondy
+primitive-divisor API.
+
+It intentionally proves only existence and location statements for the
+degree-three reduced branch.  It does not prove any `padicValNat <= 1` bound:
+that belongs to the squarefree/no-lift multiplicity layer.
+-/
+
+namespace DkMath
+namespace Petal
+
+open DkMath.CosmicFormulaBinom
+open DkMath.FLT.PetalDetect
+
+/--
+Reduced cubic Petal coordinates satisfy the existing Zsigmondy `d = 3`
+primitive-divisor existence theorem.
+-/
+theorem exists_primitivePrimeDivisor_d3_of_boundaryD3Reduced
+    {c b : ℕ} (hbc : b < c) (hb : 0 < b)
+    (hcop : Nat.Coprime c b) (hred : BoundaryD3Reduced c b) :
+    ∃ q : ℕ, DkMath.Zsigmondy.PrimitivePrimeDivisor c b 3 q := by
+  exact
+    DkMath.Zsigmondy.exists_primitivePrimeDivisor_prime_exp
+      (a := c) (b := b) (d := 3)
+      Nat.prime_three (by norm_num) hbc hb hcop hred
+
+/--
+A `d = 3` primitive divisor obtained from Zsigmondy does not divide the
+boundary gap.
+-/
+theorem primitivePrimeDivisor_d3_not_dvd_sub
+    {c b q : ℕ} (hprim : DkMath.Zsigmondy.PrimitivePrimeDivisor c b 3 q) :
+    ¬ q ∣ c - b := by
+  have hnot : ¬ q ∣ c ^ 1 - b ^ 1 :=
+    DkMath.Zsigmondy.PrimitivePrimeDivisor.not_dvd_lower
+      hprim (by norm_num) (by norm_num)
+  simpa using hnot
+
+/--
+A `d = 3` primitive divisor obtained from Zsigmondy lies on the cubic Petal
+`S0_nat` face.
+-/
+theorem primitivePrimeDivisor_d3_dvd_S0_nat
+    {c b q : ℕ} (hbc : b < c)
+    (hprim : DkMath.Zsigmondy.PrimitivePrimeDivisor c b 3 q) :
+    q ∣ S0_nat c b := by
+  have hx : 0 < c - b := Nat.sub_pos_of_lt hbc
+  have hprim_body :
+      DkMath.Zsigmondy.PrimitivePrimeDivisor (c - b + b) b 3 q := by
+    simpa [Nat.sub_add_cancel hbc.le] using hprim
+  have hq_dvd_GN :
+      q ∣ GN 3 (c - b) b := by
+    exact
+      (DkMath.Zsigmondy.primitivePrimeDivisor_body_three_imp_dvd_GN
+        (x := c - b) (u := b) hx hprim_body)
+  rw [S0_nat_eq_GN_three_sub hbc]
+  exact hq_dvd_GN
+
+/--
+The same `d = 3` Zsigmondy primitive divisor can be read as an anchored
+`S0_nat` carrier.
+-/
+theorem anchoredS0Carrier_of_primitivePrimeDivisor_d3
+    {c b q : ℕ} (hbc : b < c)
+    (hprim : DkMath.Zsigmondy.PrimitivePrimeDivisor c b 3 q) :
+    AnchoredS0Carrier q c b q := by
+  refine ⟨?_, ?_⟩
+  · exact hasPositiveAnchorPrime_self_of_prime
+      (DkMath.Zsigmondy.PrimitivePrimeDivisor.prime hprim)
+  · exact primitivePrimeDivisor_d3_dvd_S0_nat hbc hprim
+
+/--
+The reduced cubic branch yields a single witness that is simultaneously a
+Zsigmondy primitive divisor and a Petal anchored `S0_nat` carrier.
+-/
+theorem exists_anchoredS0Carrier_and_primitivePrimeDivisor_d3
+    {c b : ℕ} (hbc : b < c) (hb : 0 < b)
+    (hcop : Nat.Coprime c b) (hred : BoundaryD3Reduced c b) :
+    ∃ q : ℕ,
+      DkMath.Zsigmondy.PrimitivePrimeDivisor c b 3 q ∧
+        AnchoredS0Carrier q c b q ∧
+          ¬ q ∣ c - b := by
+  rcases exists_primitivePrimeDivisor_d3_of_boundaryD3Reduced hbc hb hcop hred with
+    ⟨q, hprim⟩
+  exact
+    ⟨q, hprim, anchoredS0Carrier_of_primitivePrimeDivisor_d3 hbc hprim,
+      primitivePrimeDivisor_d3_not_dvd_sub hprim⟩
+
+/--
+Projection form: the reduced cubic branch has a boundary-free prime divisor on
+`S0_nat`.
+-/
+theorem exists_prime_dvd_S0_nat_of_boundaryD3Reduced_via_zsigmondy
+    {c b : ℕ} (hbc : b < c) (hb : 0 < b)
+    (hcop : Nat.Coprime c b) (hred : BoundaryD3Reduced c b) :
+    ∃ q : ℕ, Nat.Prime q ∧ q ∣ S0_nat c b ∧ ¬ q ∣ c - b := by
+  rcases exists_anchoredS0Carrier_and_primitivePrimeDivisor_d3 hbc hb hcop hred with
+    ⟨q, hprim, hcarrier, hq_not_dvd_sub⟩
+  exact
+    ⟨q, DkMath.Zsigmondy.PrimitivePrimeDivisor.prime hprim,
+      anchoredS0Carrier_dvd_S0 hcarrier, hq_not_dvd_sub⟩
+
+end Petal
+end DkMath
diff --git a/lean/dk_math/DkMath/Petal/docs/Petal-Overview.md b/lean/dk_math/DkMath/Petal/docs/Petal-Overview.md
index 9cb68c2a..d9c93730 100644
--- a/lean/dk_math/DkMath/Petal/docs/Petal-Overview.md
+++ b/lean/dk_math/DkMath/Petal/docs/Petal-Overview.md
@@ -108,6 +108,7 @@ DkMath.Petal.ReducedSupport
 DkMath.Petal.Anchor
 DkMath.Petal.BoundaryD3
 DkMath.Petal.EisensteinBridge
+DkMath.Petal.ZsigmondyD3Bridge
 ```

 ### `DkMath.Petal.Basic`
@@ -320,6 +321,26 @@ arithmetic development.  Its role is to let later Petal/Zsigmondy-facing files
 import the Petal package surface instead of depending directly on the FLT file
 layout.

+### `DkMath.Petal.ZsigmondyD3Bridge`
+
+Shares the same `d = 3` Zsigmondy primitive-divisor witness with the Petal
+anchored `S0_nat` carrier surface.
+
+Important names:
+
+```lean
+exists_primitivePrimeDivisor_d3_of_boundaryD3Reduced
+primitivePrimeDivisor_d3_not_dvd_sub
+primitivePrimeDivisor_d3_dvd_S0_nat
+anchoredS0Carrier_of_primitivePrimeDivisor_d3
+exists_anchoredS0Carrier_and_primitivePrimeDivisor_d3
+exists_prime_dvd_S0_nat_of_boundaryD3Reduced_via_zsigmondy
+```
+
+This bridge intentionally does not prove any `padicValNat <= 1` theorem.
+Zsigmondy supplies existence, Petal supplies location, and squarefree/no-lift
+layers supply multiplicity.
+
 ### `DkMath.Petal.Counting`

 Defines the fixed and dynamic counting layer.
diff --git a/lean/dk_math/DkMath/Petal/docs/Petal-Zsigmondy-Preflight.md b/lean/dk_math/DkMath/Petal/docs/Petal-Zsigmondy-Preflight.md
index 505af458..0a82a060 100644
--- a/lean/dk_math/DkMath/Petal/docs/Petal-Zsigmondy-Preflight.md
+++ b/lean/dk_math/DkMath/Petal/docs/Petal-Zsigmondy-Preflight.md
@@ -26,8 +26,9 @@ BoundaryD3Reduced
 The next question is not yet "prove Zsigmondy".  The immediate question is:

 ```text
-Can the Petal anchored S0 witness be translated into the existing
-Zsigmondy primitive-divisor language?
+Can the reduced cubic Petal hypotheses be fed into the existing
+Zsigmondy d = 3 existence theorem, and can that same Zsigmondy witness be
+shared with the Petal anchored S0 carrier surface?
 ```

 ## Existing Zsigmondy Contract
@@ -90,8 +91,9 @@ theorem exists_anchoredS0Carrier_and_primitivePrimeDivisor_d3
 This is not a full Zsigmondy theorem.  It is the `d = 3` handshake:

 ```text
-Petal reduced cubic witness
-  -> primitive divisor witness for c^3 - b^3
+BoundaryD3Reduced hypotheses
+  -> Zsigmondy primitive divisor q for c^3 - b^3
+  -> the same q as an anchored S0 carrier
 ```

 ## Important Separation: Existence, Location, Multiplicity
````
`````
