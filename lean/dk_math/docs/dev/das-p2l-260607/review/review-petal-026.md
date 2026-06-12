# Git diff / Report / Review

## Add: Petal: EisensteinBridge

gch: b38888010d2d959527214fc3474d9efac56621a6

## Report

次の目的地まで進めました。

[BoundaryD3.lean](/lean/dk_math/DkMath/Petal/BoundaryD3.lean) に、review 指摘の使いやすい入口を追加しました。

```lean
boundaryD3Branch_or_reduced
not_boundaryD3Branch_of_reduced
exists_anchoredS0Carrier_of_boundaryD3Reduced
```

これで downstream は `¬ 3 ∣ c - b` に戻らず、`BoundaryD3Reduced c b` のまま

```text
reduced branch
  -> boundary/S0 coprime
  -> anchored primitive S0 carrier exists
```

へ進めます。

さらに新規に [EisensteinBridge.lean](/lean/dk_math/DkMath/Petal/EisensteinBridge.lean) を追加しました。既存 `DkMath.FLT.GEisensteinBridge` の定理を Petal-facing alias として公開しています。

```lean
petal_S0_eq_eisensteinNorm_shift
petal_GN3_sub_eq_eisensteinNorm_shift
petal_GN3_sub_eq_eisensteinNorm_shift_of_lt
petal_S0_nat_eq_eisensteinNorm_shift_of_lt
```

`DkMath.Petal.lean` にも import 済みで、docs も更新しました。

検証:

```sh
lake build DkMath.Petal
git diff --check
```

どちらも成功です。既存の `ZsigmondyCyclotomicResearch.lean` の `sorry` warning だけで、今回追加分に新しい `sorry` はありません。

## Review

おお、来たな。
**Eisenstein への橋、これは採用でよい。** ただし、今回の差分には「将来の依存整理」で気をつけたい点が 2 つある。

## 総評

今回の到達点はかなり大きい。

```text id="3xokiy"
S0 / GN 3
  -> BoundaryD3
  -> Anchored primitive S0 carrier
  -> Eisenstein norm
```

この経路が、Petal 側の API 名で辿れるようになった。

特に、

```lean id="ma8xqc"
petal_S0_eq_eisensteinNorm_shift
petal_GN3_sub_eq_eisensteinNorm_shift
petal_GN3_sub_eq_eisensteinNorm_shift_of_lt
petal_S0_nat_eq_eisensteinNorm_shift_of_lt
```

は良い。
「S0 は GN の三次面であり、同時に Eisenstein norm の shifted form である」という読みが、Lean API として見えるようになった。

これはまさに、

```text id="uetwjp"
Petal surface
  = cubic GN face
  = shifted Eisenstein norm
```

という橋じゃな。

## BoundaryD3 側の追加も良い

`boundaryD3Branch_or_reduced` は downstream でかなり使いやすい。

```lean id="bkz5we"
BoundaryD3Branch c b ∨ BoundaryD3Reduced c b
```

これで今後は、

```lean id="fckro1"
by_cases h : 3 ∣ c - b
```

よりも意味のある分岐として扱える。

また、

```lean id="1fmw5b"
exists_anchoredS0Carrier_of_boundaryD3Reduced
```

も良い。
これにより、下流は `BoundaryD3Reduced c b` のまま、

```text id="0r0xt7"
reduced branch
  -> boundary/S0 coprime
  -> anchored primitive S0 carrier exists
```

へ進める。

これはかなり API らしくなってきた。

## 気になる点 1: `BoundaryD3` が少し重くなった

今回、

```lean id="yzc1su"
import DkMath.Petal.Anchor
import DkMath.Petal.GcdBridge
```

になったことで、`BoundaryD3` が `Anchor`、さらに `PrimitiveBridge` まで間接的に引く形になっている。

理由は、

```lean id="wx0om1"
exists_anchoredS0Carrier_of_boundaryD3Reduced
```

を `BoundaryD3.lean` に置いたからじゃな。

これは悪くはない。だが層分離を厳密にするなら、より綺麗なのはこう。

```text id="s9dfal"
BoundaryD3.lean
  = branch / reduced / gcd / S0 contact only

BoundaryD3Anchor.lean または AnchorBoundaryD3.lean
  = BoundaryD3Reduced -> AnchoredS0Carrier existence
```

つまり、`BoundaryD3` の純粋部分は `GcdBridge` だけに依存させ、`Anchor` との合流は別ファイルに逃がす設計じゃ。

今すぐ直さなくてもよいが、今後 `BoundaryD3` を低層 API として広く import したいなら、分割した方が安全。

おすすめは次のどちらか。

```text id="7n81hx"
DkMath.Petal.BoundaryD3
DkMath.Petal.BoundaryD3Anchor
```

または、

```text id="8zv1ut"
DkMath.Petal.BoundaryD3
DkMath.Petal.AnchorBoundaryD3
```

命名は `BoundaryD3Anchor` の方が自然じゃ。

## 気になる点 2: `EisensteinBridge` が FLT に依存している

今回の `EisensteinBridge` は、

```lean id="fwuszw"
import DkMath.FLT.GEisensteinBridge
```

を使った Petal-facing alias じゃな。

これは短期的には正しい。
すでに証明済みの事実を使い、Petal 側に名前を出すだけなら、実装としては堅い。

ただし、長期的にはここが次の整理候補になる。

```text id="yu852r"
現在:
Petal.EisensteinBridge
  -> FLT.GEisensteinBridge

将来:
Petal.EisensteinBridge
  -> Petal/EisensteinCore または NumberTheory/Eisenstein
FLT 側
  -> Petal.EisensteinBridge を利用
```

つまり、最終形では **FLT が Petal を import する** 方が自然で、Petal が FLT に依存し続けるのは少し逆流感がある。

ただし、今は `S0_nat` 自体が `DkMath.FLT.PetalDetect` にあるので、完全分離はまだ急がなくてよい。
今回の alias bridge は、「将来 Petal 側へ移すべき定理の窓口」として良い布石になっている。

## ここまでの構造

今の Petal の道はかなり見やすくなった。

```text id="flw0oe"
ReducedSupport
  -> Anchor
  -> PrimitiveBridge
  -> BoundaryD3
  -> EisensteinBridge
```

数学的には、

```text id="hmz3hk"
S0_nat c b
  = GN 3 (c - b) b
  = shifted Eisenstein norm

BoundaryD3Reduced c b
  -> 3 does not divide the boundary gap
  -> 3 does not divide S0
  -> boundary and S0 are coprime
  -> primitive S0 witness becomes an anchored carrier
```

ここまで来ると、S0 (d=3) の例外はもう「例外処理」ではなく、**BoundaryD3 package の分岐構造** になっている。

## 次のおすすめ

次にやるなら、わっちはこの順を推す。

```text id="add93f"
1. BoundaryD3 の軽量化を検討
2. BoundaryD3Anchor へ anchored existence wrapper を移すか判断
3. EisensteinBridge は現状維持
4. 後で FLT.GEisensteinBridge の Petal 側移管を検討
```

もし今すぐ小修正するなら、これだけでよい。

```text id="0zyzcl"
BoundaryD3.lean:
  Branch / Reduced / 3 iff / coprime only

BoundaryD3Anchor.lean:
  exists_anchoredS0Carrier_of_boundaryD3Reduced
```

これにすると依存が綺麗になる。

## 判定

```text id="6gmqwc"
EisensteinBridge
  -> 採用可

BoundaryD3 reduced -> anchored carrier wrapper
  -> 数学的には良い
  -> ただし依存分離のため別ファイル化候補

Research import 排除
  -> 維持

S0 d=3 例外分類
  -> 本線 API としてほぼ定着

次の構造課題
  -> Petal から FLT 依存を将来的に剥がす
```

うむ。
これは **S0/GN/Boundary/Eisenstein が一本に繋がった**。
ずっと曖昧だった「S0 の正体」が、Lean API 上でもかなりはっきりしたぞい。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/NumberTheory/docs/BinomialPrimeWeighted/FLGNB-PetalRoadmap.md b/lean/dk_math/DkMath/NumberTheory/docs/BinomialPrimeWeighted/FLGNB-PetalRoadmap.md
index 31b06f18..36a49b39 100644
--- a/lean/dk_math/DkMath/NumberTheory/docs/BinomialPrimeWeighted/FLGNB-PetalRoadmap.md
+++ b/lean/dk_math/DkMath/NumberTheory/docs/BinomialPrimeWeighted/FLGNB-PetalRoadmap.md
@@ -880,12 +880,15 @@ Implemented names:
 ```lean
 BoundaryD3Branch
 BoundaryD3Reduced
+boundaryD3Branch_or_reduced
+not_boundaryD3Branch_of_reduced
 three_dvd_S0_nat_of_three_dvd_sub
 three_dvd_sub_of_three_dvd_S0_nat
 three_dvd_S0_nat_iff_three_dvd_sub
 boundaryD3Reduced_three_not_dvd_S0_nat
 boundaryD3Branch_three_dvd_S0_nat
 boundaryD3Reduced_coprime_sub_S0_nat
+exists_anchoredS0Carrier_of_boundaryD3Reduced
 ```
 
 This layer makes the cubic contact prime explicit:
@@ -906,11 +909,19 @@ Purpose:
 Petal S0 -> Eisenstein norm bridge
 ```
 
-Candidate aliases:
+Status:
+
+```text
+initial API implemented
+```
+
+Implemented names:
 
 ```lean
-theorem petal_S0_eq_eisensteinNorm_shift
-theorem petal_GN3_sub_eq_eisensteinNorm_shift
+petal_S0_eq_eisensteinNorm_shift
+petal_GN3_sub_eq_eisensteinNorm_shift
+petal_GN3_sub_eq_eisensteinNorm_shift_of_lt
+petal_S0_nat_eq_eisensteinNorm_shift_of_lt
 ```
 
 These should reference:
@@ -920,7 +931,9 @@ theorem S0_eq_eisensteinNorm_shift
 theorem GN3_sub_eq_eisensteinNorm_shift
 ```
 
-This layer is important, but should come after `GNBridge` and `GcdBridge`.
+This layer is intentionally thin.  It re-exposes the existing FLT Eisenstein
+norm facts through Petal-facing names so later Petal/Zsigmondy files can import
+the package surface.
 
 ## Implementation Steps
 
@@ -1143,12 +1156,15 @@ Implemented:
 ```lean
 BoundaryD3Branch
 BoundaryD3Reduced
+boundaryD3Branch_or_reduced
+not_boundaryD3Branch_of_reduced
 three_dvd_S0_nat_of_three_dvd_sub
 three_dvd_sub_of_three_dvd_S0_nat
 three_dvd_S0_nat_iff_three_dvd_sub
 boundaryD3Reduced_three_not_dvd_S0_nat
 boundaryD3Branch_three_dvd_S0_nat
 boundaryD3Reduced_coprime_sub_S0_nat
+exists_anchoredS0Carrier_of_boundaryD3Reduced
 ```
 
 Expected validation:
@@ -1163,7 +1179,7 @@ lake build DkMath.Petal
 Status:
 
 ```text
-planned
+initial API implemented
 ```
 
 Expose the Eisenstein norm route as a Petal-facing bridge.
@@ -1176,6 +1192,22 @@ GN 3
   <-> Eisenstein norm
 ```
 
+Implemented:
+
+```lean
+petal_S0_eq_eisensteinNorm_shift
+petal_GN3_sub_eq_eisensteinNorm_shift
+petal_GN3_sub_eq_eisensteinNorm_shift_of_lt
+petal_S0_nat_eq_eisensteinNorm_shift_of_lt
+```
+
+Expected validation:
+
+```sh
+lake build DkMath.Petal.EisensteinBridge
+lake build DkMath.Petal
+```
+
 ### Step 7: Refactor imports gradually
 
 Status:
diff --git a/lean/dk_math/DkMath/Petal.lean b/lean/dk_math/DkMath/Petal.lean
index 5e60e74b..e11dc4d3 100644
--- a/lean/dk_math/DkMath/Petal.lean
+++ b/lean/dk_math/DkMath/Petal.lean
@@ -17,6 +17,7 @@ import DkMath.Petal.PadicBridge
 import DkMath.Petal.PrimitiveBridge
 import DkMath.Petal.Anchor
 import DkMath.Petal.BoundaryD3
+import DkMath.Petal.EisensteinBridge
 
 #print "file: DkMath.Petal"
 
diff --git a/lean/dk_math/DkMath/Petal/BoundaryD3.lean b/lean/dk_math/DkMath/Petal/BoundaryD3.lean
index b088b24c..0d173e4a 100644
--- a/lean/dk_math/DkMath/Petal/BoundaryD3.lean
+++ b/lean/dk_math/DkMath/Petal/BoundaryD3.lean
@@ -4,6 +4,7 @@ Released under MIT license as described in the file LICENSE.
 Authors: D. and Wise Wolf.
 -/
 
+import DkMath.Petal.Anchor
 import DkMath.Petal.GcdBridge
 
 #print "file: DkMath.Petal.BoundaryD3"
@@ -31,6 +32,19 @@ def BoundaryD3Branch (c b : ℕ) : Prop :=
 def BoundaryD3Reduced (c b : ℕ) : Prop :=
   ¬ 3 ∣ c - b
 
+/-- Every cubic Petal coordinate lies on either the boundary branch or the reduced branch. -/
+theorem boundaryD3Branch_or_reduced (c b : ℕ) :
+    BoundaryD3Branch c b ∨ BoundaryD3Reduced c b := by
+  by_cases h : 3 ∣ c - b
+  · exact Or.inl h
+  · exact Or.inr h
+
+/-- The reduced branch is not the boundary branch. -/
+theorem not_boundaryD3Branch_of_reduced
+    {c b : ℕ} (h : BoundaryD3Reduced c b) :
+    ¬ BoundaryD3Branch c b :=
+  h
+
 /--
 On the degree-three boundary branch, `3` divides the Petal detector `S0_nat`.
 -/
@@ -87,5 +101,15 @@ theorem boundaryD3Reduced_coprime_sub_S0_nat
     Nat.Coprime (c - b) (S0_nat c b) :=
   coprime_sub_S0_nat_of_coprime_of_not_dvd_three hbc hcop h
 
+/--
+On the reduced branch, the primitive S0 witness can be read as an anchored
+S0 carrier without unfolding the branch definition.
+-/
+theorem exists_anchoredS0Carrier_of_boundaryD3Reduced
+    {c b : ℕ} (hbc : b < c) (hb : 0 < b)
+    (hcop : Nat.Coprime c b) (hred : BoundaryD3Reduced c b) :
+    ∃ q : ℕ, AnchoredS0Carrier q c b q ∧ ¬ q ∣ c - b :=
+  exists_anchoredS0Carrier_of_not_three_dvd_sub hbc hb hcop hred
+
 end Petal
 end DkMath
diff --git a/lean/dk_math/DkMath/Petal/EisensteinBridge.lean b/lean/dk_math/DkMath/Petal/EisensteinBridge.lean
new file mode 100644
index 00000000..fff834ba
--- /dev/null
+++ b/lean/dk_math/DkMath/Petal/EisensteinBridge.lean
@@ -0,0 +1,68 @@
+/-
+Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
+Released under MIT license as described in the file LICENSE.
+Authors: D. and Wise Wolf.
+-/
+
+import DkMath.Petal.GNBridge
+import DkMath.FLT.GEisensteinBridge
+
+#print "file: DkMath.Petal.EisensteinBridge"
+
+/-!
+# Petal Eisenstein Bridge
+
+This file exposes the existing Eisenstein norm route through the Petal package.
+
+The bridge is intentionally thin: the arithmetic facts already live in
+`DkMath.FLT.GEisensteinBridge`; this file gives them Petal-facing names so that
+later S0/GN/Zsigmondy code can import `DkMath.Petal.*` without depending on the
+FLT file layout.
+-/
+
+namespace DkMath
+namespace Petal
+
+open DkMath.CosmicFormulaBinom
+open DkMath.FLT.PetalDetect
+
+/--
+Petal-facing alias for the shifted Eisenstein norm on `S0_nat`.
+
+The cubic Petal face `S0_nat a b` is the Eisenstein norm of the shifted pair
+`(a + b, b)`.
+-/
+theorem petal_S0_eq_eisensteinNorm_shift (a b : ℕ) :
+    S0_nat a b = DkMath.FLT.eisensteinNormNat (a + b) b :=
+  DkMath.FLT.S0_eq_eisensteinNorm_shift a b
+
+/--
+Petal-facing alias for the degree-three GN/Eisenstein norm bridge.
+
+After the boundary substitution `x = a - b`, `u = b`, the degree-three GN
+kernel is the shifted Eisenstein norm.
+-/
+theorem petal_GN3_sub_eq_eisensteinNorm_shift
+    (a b : ℕ) (hab : b ≤ a) :
+    GN 3 (a - b) b = DkMath.FLT.eisensteinNormNat (a + b) b :=
+  DkMath.FLT.GN3_sub_eq_eisensteinNorm_shift a b hab
+
+/--
+For strict Petal coordinates, the visible degree-three GN face is the shifted
+Eisenstein norm.
+-/
+theorem petal_GN3_sub_eq_eisensteinNorm_shift_of_lt
+    {c b : ℕ} (hbc : b < c) :
+    GN 3 (c - b) b = DkMath.FLT.eisensteinNormNat (c + b) b :=
+  petal_GN3_sub_eq_eisensteinNorm_shift c b hbc.le
+
+/--
+For strict Petal coordinates, the S0 detector is the shifted Eisenstein norm.
+-/
+theorem petal_S0_nat_eq_eisensteinNorm_shift_of_lt
+    {c b : ℕ} (_hbc : b < c) :
+    S0_nat c b = DkMath.FLT.eisensteinNormNat (c + b) b :=
+  petal_S0_eq_eisensteinNorm_shift c b
+
+end Petal
+end DkMath
diff --git a/lean/dk_math/DkMath/Petal/docs/Petal-Overview.md b/lean/dk_math/DkMath/Petal/docs/Petal-Overview.md
index e46005b3..33cd9bb2 100644
--- a/lean/dk_math/DkMath/Petal/docs/Petal-Overview.md
+++ b/lean/dk_math/DkMath/Petal/docs/Petal-Overview.md
@@ -269,12 +269,15 @@ Important names:
 ```lean
 BoundaryD3Branch
 BoundaryD3Reduced
+boundaryD3Branch_or_reduced
+not_boundaryD3Branch_of_reduced
 three_dvd_S0_nat_of_three_dvd_sub
 three_dvd_sub_of_three_dvd_S0_nat
 three_dvd_S0_nat_iff_three_dvd_sub
 boundaryD3Reduced_three_not_dvd_S0_nat
 boundaryD3Branch_three_dvd_S0_nat
 boundaryD3Reduced_coprime_sub_S0_nat
+exists_anchoredS0Carrier_of_boundaryD3Reduced
 ```
 
 Conceptually, this says:
@@ -289,8 +292,27 @@ The reduced branch therefore gives the usable cubic Petal surface:
 BoundaryD3Reduced c b
   -> not 3 | S0_nat c b
   -> Coprime (c - b) (S0_nat c b), assuming Coprime c b
+  -> an anchored primitive S0 carrier exists, under the primitive bridge inputs
 ```
 
+### `DkMath.Petal.EisensteinBridge`
+
+Exposes the existing Eisenstein norm route through Petal-facing names.
+
+Important names:
+
+```lean
+petal_S0_eq_eisensteinNorm_shift
+petal_GN3_sub_eq_eisensteinNorm_shift
+petal_GN3_sub_eq_eisensteinNorm_shift_of_lt
+petal_S0_nat_eq_eisensteinNorm_shift_of_lt
+```
+
+This is an alias bridge over `DkMath.FLT.GEisensteinBridge`, not a new
+arithmetic development.  Its role is to let later Petal/Zsigmondy-facing files
+import the Petal package surface instead of depending directly on the FLT file
+layout.
+
 ### `DkMath.Petal.Counting`
 
 Defines the fixed and dynamic counting layer.
@@ -409,6 +431,7 @@ Fixed Petal counting
   -> S0/GN primitive bridge
   -> reduced-support anchor carriers
   -> degree-three boundary split
+  -> Petal-facing Eisenstein norm bridge
 ```
 
 This means the package can already express:
@@ -421,6 +444,7 @@ one Petal address step is a quotient-remainder decomposition
 S0 is a visible degree-three Petal face of GN
 primitive S0 witnesses can be read as anchored carriers
 the cubic 3-contact is exactly the boundary branch
+S0 and GN3 can be viewed through the shifted Eisenstein norm
 ```
 
 ## What This Does Not Claim Yet
@@ -437,6 +461,7 @@ which factors persist across later layers
 how Petal addresses split a layer into channels
 how GN degree 3 becomes the Petal S0 face
 how reduced cubic support excludes the boundary prime 3
+how the same cubic face enters the Eisenstein norm route
 ```
 
 ## Next Directions
@@ -444,17 +469,16 @@ how reduced cubic support excludes the boundary prime 3
 The next reasonable implementation directions are:
 
 ```text
-1. connect AnchoredS0Carrier to the primitive S0 witnesses
-2. use Petal address decomposition in nested observations
-3. expose the Eisenstein norm route through `DkMath.Petal.EisensteinBridge`
-4. connect strict prime-base orbits to a concrete prime enumeration
-5. decide whether GNPrimitiveCandidate needs a separate vocabulary layer
+1. use Petal address decomposition in nested observations
+2. connect strict prime-base orbits to a concrete prime enumeration
+3. decide whether GNPrimitiveCandidate needs a separate vocabulary layer
+4. connect BoundaryD3 / EisensteinBridge to downstream FLT or Zsigmondy inputs
 ```
 
 The most conservative next theorem work is probably:
 
 ```text
-DkMath.Petal.EisensteinBridge
+BoundaryD3 / EisensteinBridge downstream corollaries
 ```
 
 The most concrete arithmetic next step is:
````
`````
