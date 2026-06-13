# Git diff / Report / Review

## Upd: Petal: Closing process

gch: 2d4fc2f0ce3d0b581b045642314266f61ea6dfef

## Report

総括段階として、実装追加はせずに整理しました。

`DkMath.Petal` の import 順を物語順に整え、module doc にその意図を追記しました。

```text
basic forms / relative polygon vocabulary
  -> counting and address layers
  -> GN/GCD/p-adic/primitive bridges
  -> reduced support and anchored carriers
  -> BoundaryD3 cubic branch split
  -> shifted Eisenstein norm bridge
```

docs 側は以下を更新しました。

- [Petal-Overview.md](/lean/dk_math/DkMath/Petal/docs/Petal-Overview.md)
  - `Current Closed Surface` を追加
  - `Petal cubic surface closure` として、S0/GN3/BoundaryD3/Anchor/Eisenstein の閉じた範囲を明記
  - 未主張の範囲も整理

- [FLGNB-PetalRoadmap.md](/lean/dk_math/DkMath/NumberTheory/docs/BinomialPrimeWeighted/FLGNB-PetalRoadmap.md)
  - `Step 5.8: Petal cubic surface closure` を追加
  - 完了済み層、閉じた表面、延期項目を明記

- [BinomialPrimeWeightedRoadmap.md](/lean/dk_math/DkMath/NumberTheory/docs/BinomialPrimeWeightedRoadmap.md)
  - Phase 4.7 を現状に合わせて更新
  - Phase 5 へ渡す前段として、三次 Petal 表面が閉じたことを反映

検証:

```sh
lake build DkMath.Petal
git diff --check
```

どちらも成功です。既存の `ZsigmondyCyclotomicResearch.lean` の `sorry` warning のみで、今回の変更による新しい `sorry` はありません。

## Review

締まった。これは **Petal cubic surface closure checkpoint として採用でよい**。

今回の差分は、コード実装を増やすより重要な「どこまで閉じたか」を固定している。特に `Petal.lean` の import 順に物語を与えたのが良い。

```text
basic forms / relative polygon vocabulary
  -> counting and address layers
  -> GN/GCD/p-adic/primitive bridges
  -> reduced support and anchored carriers
  -> BoundaryD3 cubic branch split
  -> shifted Eisenstein norm bridge
```

これで `DkMath.Petal` が単なる集約 import ではなく、**三次 Petal 表面の公開 API** として読めるようになった。

## レビュー結論

```text
2d4fc2f0...
  -> 採用可

実装追加
  -> なし

整理内容
  -> 適切

Petal cubic surface
  -> 一旦 closure 扱いでよい
```

## 特に良い点

`Current Closed Surface` の追加は非常に良い。

```text
S0_nat c b
  = GN 3 (c - b) b
  = shifted Eisenstein norm
```

この一行で、今回の一連の実装の意味がかなり明確になる。

さらに、

```text
BoundaryD3Reduced
  -> 3 does not divide S0_nat
  -> Coprime (c - b) (S0_nat c b), assuming Coprime c b
  -> primitive S0 witness exists
  -> witness can be read as an anchored S0 carrier
```

この経路が docs に固定されたので、後で FLT / Zsigmondy 側から戻ってきた時に「何を使えばよいか」が分かる。

## 未主張の範囲も正しい

ここを明記したのも大事じゃ。

```text
general d boundary classification
full Zsigmondy theorem
FLT descent
complete Eisenstein refactor away from the FLT namespace
complete split of BoundaryD3 and BoundaryD3Anchor
concrete prime enumeration / standard primorial theorem
```

つまり、今回閉じたのは **一般 Petal 理論全体** ではなく、

```text
degree-three S0/GN3/BoundaryD3/Anchor/Eisenstein surface
```

じゃな。主張の境界が正確。

## BinomialPrimeWeightedRoadmap 側の更新も良い

Phase 4.7 から Phase 5 へ渡す前段として、

```text
S0/GN3/BoundaryD3/Anchor/Eisenstein cubic surface closure
```

を記録したのは正しい。

これで Zsigmondy へ向かう時に、いきなり原始素因子存在を殴るのではなく、

```text
どの因子がどの orbit / channel / GN face に保存されるか
```

を Petal API で追う、という位置づけが残る。

## ここで一区切りでよい

この checkpoint で、Petal は次の状態になった。

```text
Closed:
  S0 as GN3 face
  S0/GN gcd and p-adic bridge
  primitive S0 witness
  reduced support / anchored carrier
  BoundaryD3 branch split
  Eisenstein norm alias bridge

Deferred:
  general d
  Zsigmondy
  FLT descent
  neutral library promotion
  dependency cleanup
```

よって、ここで一旦 Petal は閉じてよい。

次に進むなら、Petal 内でさらに作り込むより、

```text
Phase 5 側から、この閉じた Petal cubic surface をどう使うか
```

へ移るのが自然じゃ。

うむ。良い締めじゃ。
S0 (d=3) の例外は、もう「揉めていた反例」ではなく、`BoundaryD3` によって名付けられた構造になった。これは大きい。

## Appendix

[Zsigmondy との交渉の行方](./note-petal-028.md)
[直近問題](./issue-petal-028.md)

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/NumberTheory/docs/BinomialPrimeWeighted/FLGNB-PetalRoadmap.md b/lean/dk_math/DkMath/NumberTheory/docs/BinomialPrimeWeighted/FLGNB-PetalRoadmap.md
index 36a49b39..32978520 100644
--- a/lean/dk_math/DkMath/NumberTheory/docs/BinomialPrimeWeighted/FLGNB-PetalRoadmap.md
+++ b/lean/dk_math/DkMath/NumberTheory/docs/BinomialPrimeWeighted/FLGNB-PetalRoadmap.md
@@ -1208,6 +1208,68 @@ lake build DkMath.Petal.EisensteinBridge
 lake build DkMath.Petal
 ```
 
+### Step 5.8: Petal cubic surface closure
+
+Status:
+
+```text
+completed
+```
+
+This checkpoint closes the current degree-three Petal surface:
+
+```text
+S0_nat c b
+  = GN 3 (c - b) b
+  = shifted Eisenstein norm
+```
+
+Completed package layers:
+
+```text
+DkMath.Petal.GNBridge
+DkMath.Petal.GcdBridge
+DkMath.Petal.PadicBridge
+DkMath.Petal.PrimitiveBridge
+DkMath.Petal.ReducedSupport
+DkMath.Petal.Anchor
+DkMath.Petal.BoundaryD3
+DkMath.Petal.EisensteinBridge
+```
+
+Closed surface:
+
+```text
+S0 / GN3 / BoundaryD3 / Anchor / Eisenstein
+```
+
+The main interpretation is:
+
+```text
+BoundaryD3Reduced
+  -> boundary and S0 are separated
+  -> primitive S0 witnesses can be read as anchored carriers
+  -> the same S0/GN3 face can be viewed as a shifted Eisenstein norm
+```
+
+Deferred:
+
+```text
+BoundaryD3Anchor split
+FLT namespace dependency refactor
+DkMath.Lib.* promotion of neutral Eisenstein and S0 facts
+general d boundary behavior
+full Zsigmondy bridge
+FLT descent
+```
+
+Validation:
+
+```sh
+lake build DkMath.Petal
+git diff --check
+```
+
 ### Step 7: Refactor imports gradually
 
 Status:
diff --git a/lean/dk_math/DkMath/NumberTheory/docs/BinomialPrimeWeightedRoadmap.md b/lean/dk_math/DkMath/NumberTheory/docs/BinomialPrimeWeightedRoadmap.md
index d344dc34..0901a240 100644
--- a/lean/dk_math/DkMath/NumberTheory/docs/BinomialPrimeWeightedRoadmap.md
+++ b/lean/dk_math/DkMath/NumberTheory/docs/BinomialPrimeWeightedRoadmap.md
@@ -426,6 +426,13 @@ DkMath.Petal
 DkMath.Petal.Counting
 DkMath.Petal.Address
 DkMath.Petal.GNBridge
+DkMath.Petal.GcdBridge
+DkMath.Petal.PadicBridge
+DkMath.Petal.PrimitiveBridge
+DkMath.Petal.ReducedSupport
+DkMath.Petal.Anchor
+DkMath.Petal.BoundaryD3
+DkMath.Petal.EisensteinBridge
 ```
 
 記録:
@@ -445,6 +452,8 @@ lean/dk_math/DkMath/NumberTheory/docs/BinomialPrimeWeighted/FLGNB-PetalRoadmap.m
   可除性構造として読む。
 - primitive prime divisor を追う前段として、
   「採用済み因子が後段 product に残る」ことを theorem 化する。
+- S0/GN3/BoundaryD3/Anchor/Eisenstein を、Phase 5 へ渡す三次 Petal 表面 API
+  として一旦閉じる。
 
 主な API:
 
@@ -483,6 +492,18 @@ theorem three_S0_nat_modEq_one_of_not_dvd_sub
 theorem three_not_dvd_S0_nat_of_not_dvd_sub
 ```
 
+S0/GN3 cubic surface closure:
+
+```lean
+theorem gcd_sub_S0_nat_eq_gcd_sub_three
+theorem padicValNat_cube_sub_eq_padicValNat_S0_nat_of_not_dvd_sub
+theorem exists_prime_dvd_S0_nat_of_not_three_dvd_sub
+theorem exists_anchoredS0Carrier_of_boundaryD3Reduced
+theorem three_dvd_S0_nat_iff_three_dvd_sub
+theorem petal_S0_eq_eisensteinNorm_shift
+theorem petal_GN3_sub_eq_eisensteinNorm_shift
+```
+
 意味:
 
 ```text
@@ -494,6 +515,7 @@ Petal Phase 4.7:
   factor persistence
   Petal quotient-remainder address
   GN degree-three Petal face
+  S0/GN3/BoundaryD3/Anchor/Eisenstein cubic surface closure
 
 Phase 5:
   primitive prime divisor / Zsigmondy bridge
@@ -503,6 +525,17 @@ Phase 5:
 Zsigmondy へ渡す前に、どの因子がどの orbit / channel / GN face に保存されるかを
 Lean 上で追うための道具である。
 
+現在の Phase 4.7 closure で閉じたのは、一般次数 `d` ではなく三次 `S0/GN3`
+表面である。未処理の項目は以下に残す:
+
+```text
+general d boundary classification
+full Zsigmondy theorem
+FLT descent
+DkMath.Lib.* promotion of neutral S0 / Eisenstein facts
+BoundaryD3Anchor split and final import-direction cleanup
+```
+
 ### Phase 5: Zsigmondy への接続準備
 
 目標:
diff --git a/lean/dk_math/DkMath/Petal.lean b/lean/dk_math/DkMath/Petal.lean
index e11dc4d3..60edd166 100644
--- a/lean/dk_math/DkMath/Petal.lean
+++ b/lean/dk_math/DkMath/Petal.lean
@@ -5,16 +5,16 @@ Authors: D. and Wise Wolf.
 -/
 
 import DkMath.Petal.Basic
-import DkMath.Petal.ReducedSupport
-import DkMath.Petal.Counting
-import DkMath.Petal.Address
 import DkMath.Petal.Forms
 import DkMath.Petal.RelPolygon
 import DkMath.Petal.CoreUnit
+import DkMath.Petal.Counting
+import DkMath.Petal.Address
 import DkMath.Petal.GNBridge
 import DkMath.Petal.GcdBridge
 import DkMath.Petal.PadicBridge
 import DkMath.Petal.PrimitiveBridge
+import DkMath.Petal.ReducedSupport
 import DkMath.Petal.Anchor
 import DkMath.Petal.BoundaryD3
 import DkMath.Petal.EisensteinBridge
@@ -29,6 +29,21 @@ Petal collects the relative polygon / `S0` / `GN` bridge surface.
 The first phase is intentionally thin: it exposes the existing FLT and
 UnitCycle theorem base through a stable package path, then adds focused bridge
 theorems that will support primitive-factor and Zsigmondy-facing work.
+
+The import order is arranged as the public story of the package:
+
+```text
+basic forms / relative polygon vocabulary
+  -> counting and address layers
+  -> GN/GCD/p-adic/primitive bridges
+  -> reduced support and anchored carriers
+  -> BoundaryD3 cubic branch split
+  -> shifted Eisenstein norm bridge
+```
+
+This is not a claim that every import is logically minimal.  Some files still
+carry temporary dependencies that are documented at their module headers and
+should be reconsidered during the planned `DkMath.Lib.*` promotion refactor.
 -/
 
 namespace DkMath
diff --git a/lean/dk_math/DkMath/Petal/docs/Petal-Overview.md b/lean/dk_math/DkMath/Petal/docs/Petal-Overview.md
index 33cd9bb2..02a3dbe6 100644
--- a/lean/dk_math/DkMath/Petal/docs/Petal-Overview.md
+++ b/lean/dk_math/DkMath/Petal/docs/Petal-Overview.md
@@ -98,9 +98,16 @@ DkMath.Petal.Basic
 DkMath.Petal.Forms
 DkMath.Petal.RelPolygon
 DkMath.Petal.CoreUnit
-DkMath.Petal.GNBridge
 DkMath.Petal.Counting
 DkMath.Petal.Address
+DkMath.Petal.GNBridge
+DkMath.Petal.GcdBridge
+DkMath.Petal.PadicBridge
+DkMath.Petal.PrimitiveBridge
+DkMath.Petal.ReducedSupport
+DkMath.Petal.Anchor
+DkMath.Petal.BoundaryD3
+DkMath.Petal.EisensteinBridge
 ```
 
 ### `DkMath.Petal.Basic`
@@ -447,32 +454,77 @@ the cubic 3-contact is exactly the boundary branch
 S0 and GN3 can be viewed through the shifted Eisenstein norm
 ```
 
+## Current Closed Surface
+
+The current closure checkpoint is:
+
+```text
+Petal cubic surface closure
+```
+
+At this checkpoint, `DkMath.Petal` can express the following degree-three
+surface without importing research files:
+
+```text
+S0_nat c b
+  = GN 3 (c - b) b
+  = shifted Eisenstein norm
+```
+
+It can also classify the cubic boundary contact:
+
+```text
+BoundaryD3Branch c b   := 3 | (c - b)
+BoundaryD3Reduced c b  := not 3 | (c - b)
+
+3 | S0_nat c b iff 3 | (c - b)
+```
+
+On the reduced branch, the package has the prepared route:
+
+```text
+BoundaryD3Reduced
+  -> 3 does not divide S0_nat
+  -> Coprime (c - b) (S0_nat c b), assuming Coprime c b
+  -> primitive S0 witness exists
+  -> witness can be read as an anchored S0 carrier
+```
+
+This closes the current S0/GN3/BoundaryD3/Anchor/Eisenstein surface as a
+usable API for later FLT and Zsigmondy-facing work.
+
 ## What This Does Not Claim Yet
 
 The package does not yet prove a standard primorial theorem using a concrete
 prime enumeration such as `nthPrime`.
 
-It also does not yet prove a Zsigmondy theorem.  Instead, it prepares the
-language needed for that bridge:
+It also does not yet prove:
 
 ```text
-where factors are stored
-which factors persist across later layers
-how Petal addresses split a layer into channels
-how GN degree 3 becomes the Petal S0 face
-how reduced cubic support excludes the boundary prime 3
-how the same cubic face enters the Eisenstein norm route
+general d boundary classification
+full Zsigmondy theorem
+FLT descent
+complete Eisenstein refactor away from the FLT namespace
+complete split of BoundaryD3 and BoundaryD3Anchor
+concrete prime enumeration / standard primorial theorem
 ```
 
+Instead, it prepares the language needed for those bridges: where factors are
+stored, which factors persist across later layers, how Petal addresses split a
+layer into channels, how GN degree 3 becomes the Petal S0 face, how reduced
+cubic support excludes the boundary prime `3`, and how the same cubic face
+enters the Eisenstein norm route.
+
 ## Next Directions
 
 The next reasonable implementation directions are:
 
 ```text
-1. use Petal address decomposition in nested observations
-2. connect strict prime-base orbits to a concrete prime enumeration
-3. decide whether GNPrimitiveCandidate needs a separate vocabulary layer
-4. connect BoundaryD3 / EisensteinBridge to downstream FLT or Zsigmondy inputs
+1. connect BoundaryD3 / EisensteinBridge to downstream FLT or Zsigmondy inputs
+2. use Petal address decomposition in nested observations
+3. connect strict prime-base orbits to a concrete prime enumeration
+4. decide whether GNPrimitiveCandidate needs a separate vocabulary layer
+5. perform the deferred `DkMath.Lib.*` promotion refactor
 ```
 
 The most conservative next theorem work is probably:
````
`````
