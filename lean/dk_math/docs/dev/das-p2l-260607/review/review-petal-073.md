# Git diff / Report / Review

## Upd: Petal.RangeFamily

gch: 3c4a9f296d4edc14bd31646c82811b0b433b2e81

## Report

進めました。

`DkMath.Petal.RangeFamily` に、`qOf` の注入性を実験側で扱いやすくする pairwise 入口を追加しました。

追加内容:

- `rangeLabel_injOn_of_pairwise_ne`
- `petal_range_two_pow_le_supportMass_GN_of_bodyPrimitivePrimeFactor_pairwise`
- `petal_range_two_pow_le_rad_GN_of_bodyPrimitivePrimeFactor_pairwise`
- `petal_range_two_pow_le_supportMass_GN_of_zsigmondyPrimitivePrimeDivisor_pairwise`
- `petal_range_two_pow_le_rad_GN_of_zsigmondyPrimitivePrimeDivisor_pairwise`

これで caller は `Set.InjOn qOf ↑(Finset.range k)` を直接組み立てずに、

```text
i < k, j < k, i != j -> qOf i != qOf j
```

という自然な非衝突条件から `2^k <= supportMass/rad(GN)` へ進めます。

docs も同期済みです。

検証:

```bash
lake build DkMath.Petal.RangeFamily
lake build DkMath.Petal
git diff --check -- ...
```

`DkMath.NumberTheory.ZsigmondyCyclotomicResearch` の既存 `sorry` warning は今回範囲外として残っています。

## Review

うむ。これは **RangeFamily が「実験で使いやすい入口」へ一段進んだ** という状況じゃ。
前回の `RangeFamily` は、`I = Finset.range k`, `mOf i = i + 1` という concrete family を固定して、`Set.InjOn qOf ↑(Finset.range k)` を受け取れば `2^k <= supportMass/rad(GN)` まで渡せる構造だった。今回の更新では、その `Set.InjOn` を直接作らずに、自然な pairwise 非衝突条件から入れるようになった。

## 1. 今回の核心

追加された最重要補題はこれ。

```lean
rangeLabel_injOn_of_pairwise_ne
```

これは、

```text
i < k, j < k, i ≠ j -> qOf i ≠ qOf j
```

から、

```lean
Set.InjOn qOf ↑(Finset.range k)
```

を作る補題じゃ。

つまり、Lean 的には `Set.InjOn` が欲しい。
しかし人間・実験側では、普通はこう考える。

```text
範囲 0,1,...,k-1 の中で、
異なる index には異なる label が割り当てられている
```

今回の補題は、この自然な言い方を Lean の `Set.InjOn` へ変換する橋になっている。

## 2. 何が使いやすくなったか

前回の endpoint はこうだった。

```text
qOf が range k 上で injective
PrimitiveBeam / Zsigmondy witness が各 i にある
  -> 2^k <= supportMass/rad(GN)
```

今回からは、caller はこう渡せる。

```text
i < k, j < k, i != j -> qOf i != qOf j
PrimitiveBeam / Zsigmondy witness が各 i にある
  -> 2^k <= supportMass/rad(GN)
```

これは実験実装ではかなり大きい。
`Set.InjOn` は Lean の内部形式としては綺麗だが、具体構成では pairwise な不等式の方が作りやすいからじゃ。

## 3. 追加された endpoint の意味

PrimitiveBeam 側にはこの 2 本。

```lean
petal_range_two_pow_le_supportMass_GN_of_bodyPrimitivePrimeFactor_pairwise
petal_range_two_pow_le_rad_GN_of_bodyPrimitivePrimeFactor_pairwise
```

意味は、

```text
range k 上で qOf が pairwise に異なる
各 qOf i が PrimitiveBeam witness
  -> 2^k <= supportMass(GN d x u)
  -> 2^k <= rad(GN d x u)
```

Zsigmondy 側にはこの 2 本。

```lean
petal_range_two_pow_le_supportMass_GN_of_zsigmondyPrimitivePrimeDivisor_pairwise
petal_range_two_pow_le_rad_GN_of_zsigmondyPrimitivePrimeDivisor_pairwise
```

意味は、

```text
range k 上で qOf が pairwise に異なる
各 qOf i が Zsigmondy primitive divisor
  -> 2^k <= supportMass(GN d (a - b) b)
  -> 2^k <= rad(GN d (a - b) b)
```

つまり、ABC 側の lower bound へ入るための label 非衝突条件が、より実験的な形になった。

## 4. 今回の進展の位置づけ

これまでの階段はこうだった。

```text
ABCBridge:
  PetalCarrierLabelMapData
    -> 2^card(I) <= rad(GN)

ABCBridge _of_card_eq:
  I.card = k
    -> 2^k <= rad(GN)

ABCBridge _of_card_le:
  k <= I.card
    -> 2^k <= rad(GN)

RangeFamily:
  I = range k, mOf i = i + 1
    -> qOf injective
    -> primitive witnesses
    -> 2^k <= rad(GN)

RangeFamily pairwise:
  i<k, j<k, i≠j -> qOf i≠qOf j
    -> primitive witnesses
    -> 2^k <= rad(GN)
```

今回で、一番 caller-facing な入口ができた。

## 5. トロミノ論法で見ると

今回の更新は、**Beam の非衝突条件を自然言語に近い形へ戻した** と見える。

```text
Core:
  GN surface

Beam:
  range k に並ぶ qOf 0, qOf 1, ..., qOf (k-1)

False を避ける条件:
  異なる Beam が同じ label を使わない

Gap:
  pairwise 非衝突を Set.InjOn に変換する橋

Big:
  2^k <= rad(GN)
```

前回までは、Lean が欲しい `Set.InjOn` を直接渡す必要があった。
今回は、人間が観測しやすい

```text
別 index なら別 label
```

という条件を渡せばよい。

これは「実験から定理へ」の導線としてかなり良い。

## 6. まだ残っている本丸

今回も、重要な算術部分はまだ明示仮定として残っている。

```text
各 qOf i が本当に primitive witness であること
各 qOf i が本当に Zsigmondy primitive divisor であること
qOf i たちが pairwise に異なること
GN が 0 でないこと
```

今回の補題は、これらを証明してくれるわけではない。

ただし、必要条件の形がずいぶん自然になった。

次の本丸は、

```text
qOf i を具体的にどう作るか
pairwise 非衝突をどう証明するか
primitive witness をどう供給するか
```

じゃ。

特に Zsigmondy route では、各 index に対して primitive divisor を選ぶために、choice / noncollision / uniqueness の整理が必要になる。ここはまだ本格的な数論側の作業。

## 7. 現在の全体地図

今の Petal → ABC route はかなり整った。

```text
Abstract:
  PetalCarrierLabelMapData
    -> 2^card(I) <= rad(GN)

Concrete range:
  I = range k, mOf i = i + 1
    -> 2^k <= rad(GN)

Experiment-facing:
  pairwise label separation
    -> Set.InjOn qOf
    -> 2^k <= rad(GN)
```

つまり、ABC 側の受け皿はもうかなり使いやすい。
今後は「実際に k 本の独立 primitive carrier をどう並べるか」が主戦場になる。

## 8. 総括

今回の更新を一言で言えば、

```text
RangeFamily が Set.InjOn ではなく pairwise 非衝突から使えるようになった。
```

これにより、実験側は

```text
i < k, j < k, i != j -> qOf i != qOf j
```

という自然な条件だけで、

```text
2^k <= supportMass(GN)
2^k <= rad(GN)
```

へ進める。

うむ。
これは **k 本の Beam を並べる展示台** に、さらに **Beam 同士が重ならないかを確認する検査口** が付いた段階じゃ。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Petal/RangeFamily.lean b/lean/dk_math/DkMath/Petal/RangeFamily.lean
index 6177cad8..f7d0e30a 100644
--- a/lean/dk_math/DkMath/Petal/RangeFamily.lean
+++ b/lean/dk_math/DkMath/Petal/RangeFamily.lean
@@ -46,6 +46,28 @@ theorem rangeSuccValue_injOn (k : ℕ) :
   intro i _hi j _hj h
   exact Nat.succ.inj h
 
+/--
+Pairwise label noncollision on natural range indices gives label injectivity on
+`Finset.range k`.
+
+This is a caller-facing helper for concrete experiments: it is often easier to
+prove
+
+```text
+i < k, j < k, i != j -> qOf i != qOf j
+```
+
+than to construct `Set.InjOn qOf ↑(Finset.range k)` directly.
+-/
+theorem rangeLabel_injOn_of_pairwise_ne
+    {k : ℕ} {qOf : ℕ → ℕ}
+    (hneq :
+      ∀ i, i < k → ∀ j, j < k → i ≠ j → qOf i ≠ qOf j) :
+    Set.InjOn qOf ↑(Finset.range k) := by
+  intro i hi j hj hq
+  by_contra hij
+  exact hneq i (by simpa using hi) j (by simpa using hj) hij hq
+
 /--
 Body-coordinate range-family constructor for `PetalCarrierLabelMapData`.
 
@@ -151,6 +173,50 @@ theorem petal_range_two_pow_le_rad_GN_of_bodyPrimitivePrimeFactor_family
       (petalCarrierLabelMapData_of_bodyPrimitivePrimeFactor_range_succIndex
         k d x u qOf hd hd1 hqinj hprim)
 
+/--
+Pairwise-noncollision version of
+`petal_range_two_pow_le_supportMass_GN_of_bodyPrimitivePrimeFactor_family`.
+
+The caller may provide label separation as
+`i < k -> j < k -> i != j -> qOf i != qOf j`; this theorem converts it to the
+`Set.InjOn` hypothesis required by the core range-family constructor.
+-/
+theorem petal_range_two_pow_le_supportMass_GN_of_bodyPrimitivePrimeFactor_pairwise
+    (k d x u : ℕ)
+    (qOf : ℕ → ℕ)
+    (hGN0 : GN d x u ≠ 0)
+    (hd : 0 < d) (hd1 : 1 < d)
+    (hneq :
+      ∀ i, i < k → ∀ j, j < k → i ≠ j → qOf i ≠ qOf j)
+    (hprim :
+      ∀ i, i ∈ Finset.range k →
+        DkMath.NumberTheory.PrimitiveBeam.PrimitivePrimeFactorOfDiffPow
+          (qOf i) (x + u) u d) :
+    2 ^ k ≤ DkMath.ABC.supportMass (GN d x u) :=
+  petal_range_two_pow_le_supportMass_GN_of_bodyPrimitivePrimeFactor_family
+    k d x u qOf hGN0 hd hd1
+    (rangeLabel_injOn_of_pairwise_ne hneq) hprim
+
+/--
+Pairwise-noncollision version of
+`petal_range_two_pow_le_rad_GN_of_bodyPrimitivePrimeFactor_family`.
+-/
+theorem petal_range_two_pow_le_rad_GN_of_bodyPrimitivePrimeFactor_pairwise
+    (k d x u : ℕ)
+    (qOf : ℕ → ℕ)
+    (hGN0 : GN d x u ≠ 0)
+    (hd : 0 < d) (hd1 : 1 < d)
+    (hneq :
+      ∀ i, i < k → ∀ j, j < k → i ≠ j → qOf i ≠ qOf j)
+    (hprim :
+      ∀ i, i ∈ Finset.range k →
+        DkMath.NumberTheory.PrimitiveBeam.PrimitivePrimeFactorOfDiffPow
+          (qOf i) (x + u) u d) :
+    2 ^ k ≤ DkMath.ABC.rad (GN d x u) :=
+  petal_range_two_pow_le_rad_GN_of_bodyPrimitivePrimeFactor_family
+    k d x u qOf hGN0 hd hd1
+    (rangeLabel_injOn_of_pairwise_ne hneq) hprim
+
 /--
 Range-indexed Zsigmondy family gives the concrete ABC support-mass lower bound
 `2^k <= supportMass(GN d (a - b) b)`.
@@ -191,5 +257,43 @@ theorem petal_range_two_pow_le_rad_GN_of_zsigmondyPrimitivePrimeDivisor_family
       (petalCarrierLabelMapData_of_zsigmondyPrimitivePrimeDivisor_range_succIndex
         k a b d qOf hd hd1 hab_lt hqinj hprim)
 
+/--
+Pairwise-noncollision version of
+`petal_range_two_pow_le_supportMass_GN_of_zsigmondyPrimitivePrimeDivisor_family`.
+-/
+theorem petal_range_two_pow_le_supportMass_GN_of_zsigmondyPrimitivePrimeDivisor_pairwise
+    (k a b d : ℕ)
+    (qOf : ℕ → ℕ)
+    (hGN0 : GN d (a - b) b ≠ 0)
+    (hd : 0 < d) (hd1 : 1 < d) (hab_lt : b < a)
+    (hneq :
+      ∀ i, i < k → ∀ j, j < k → i ≠ j → qOf i ≠ qOf j)
+    (hprim :
+      ∀ i, i ∈ Finset.range k →
+        DkMath.Zsigmondy.PrimitivePrimeDivisor a b d (qOf i)) :
+    2 ^ k ≤ DkMath.ABC.supportMass (GN d (a - b) b) :=
+  petal_range_two_pow_le_supportMass_GN_of_zsigmondyPrimitivePrimeDivisor_family
+    k a b d qOf hGN0 hd hd1 hab_lt
+    (rangeLabel_injOn_of_pairwise_ne hneq) hprim
+
+/--
+Pairwise-noncollision version of
+`petal_range_two_pow_le_rad_GN_of_zsigmondyPrimitivePrimeDivisor_family`.
+-/
+theorem petal_range_two_pow_le_rad_GN_of_zsigmondyPrimitivePrimeDivisor_pairwise
+    (k a b d : ℕ)
+    (qOf : ℕ → ℕ)
+    (hGN0 : GN d (a - b) b ≠ 0)
+    (hd : 0 < d) (hd1 : 1 < d) (hab_lt : b < a)
+    (hneq :
+      ∀ i, i < k → ∀ j, j < k → i ≠ j → qOf i ≠ qOf j)
+    (hprim :
+      ∀ i, i ∈ Finset.range k →
+        DkMath.Zsigmondy.PrimitivePrimeDivisor a b d (qOf i)) :
+    2 ^ k ≤ DkMath.ABC.rad (GN d (a - b) b) :=
+  petal_range_two_pow_le_rad_GN_of_zsigmondyPrimitivePrimeDivisor_family
+    k a b d qOf hGN0 hd hd1 hab_lt
+    (rangeLabel_injOn_of_pairwise_ne hneq) hprim
+
 end Petal
 end DkMath
diff --git a/lean/dk_math/DkMath/Petal/docs/Petal-Overview.md b/lean/dk_math/DkMath/Petal/docs/Petal-Overview.md
index 6c735cd6..9383d2aa 100644
--- a/lean/dk_math/DkMath/Petal/docs/Petal-Overview.md
+++ b/lean/dk_math/DkMath/Petal/docs/Petal-Overview.md
@@ -996,12 +996,17 @@ Important names:
 
 ```text
 rangeSuccValue_injOn
+rangeLabel_injOn_of_pairwise_ne
 petalCarrierLabelMapData_of_bodyPrimitivePrimeFactor_range_succIndex
 petalCarrierLabelMapData_of_zsigmondyPrimitivePrimeDivisor_range_succIndex
 petal_range_two_pow_le_supportMass_GN_of_bodyPrimitivePrimeFactor_family
 petal_range_two_pow_le_rad_GN_of_bodyPrimitivePrimeFactor_family
 petal_range_two_pow_le_supportMass_GN_of_zsigmondyPrimitivePrimeDivisor_family
 petal_range_two_pow_le_rad_GN_of_zsigmondyPrimitivePrimeDivisor_family
+petal_range_two_pow_le_supportMass_GN_of_bodyPrimitivePrimeFactor_pairwise
+petal_range_two_pow_le_rad_GN_of_bodyPrimitivePrimeFactor_pairwise
+petal_range_two_pow_le_supportMass_GN_of_zsigmondyPrimitivePrimeDivisor_pairwise
+petal_range_two_pow_le_rad_GN_of_zsigmondyPrimitivePrimeDivisor_pairwise
 ```
 
 This is the first endpoint that reads directly as:
@@ -1011,6 +1016,16 @@ k range-indexed primitive carriers
   -> 2^k <= supportMass/rad(GN)
 ```
 
+The `_pairwise` endpoints let experiments provide label separation in the
+natural indexed form:
+
+```text
+i < k, j < k, i != j -> qOf i != qOf j
+```
+
+The helper `rangeLabel_injOn_of_pairwise_ne` converts this to the `Set.InjOn`
+hypothesis required by the core constructors.
+
 ## What This Does Not Claim Yet
 
 The package does not yet prove a standard primorial theorem using a concrete
diff --git a/lean/dk_math/docs/dev/das-p2l-260607/review/summary-petal-064.md b/lean/dk_math/docs/dev/das-p2l-260607/review/summary-petal-064.md
index 0e752daa..513f262a 100644
--- a/lean/dk_math/docs/dev/das-p2l-260607/review/summary-petal-064.md
+++ b/lean/dk_math/docs/dev/das-p2l-260607/review/summary-petal-064.md
@@ -498,12 +498,17 @@ Implemented theorem set:
 
 ```lean
 rangeSuccValue_injOn
+rangeLabel_injOn_of_pairwise_ne
 petalCarrierLabelMapData_of_bodyPrimitivePrimeFactor_range_succIndex
 petalCarrierLabelMapData_of_zsigmondyPrimitivePrimeDivisor_range_succIndex
 petal_range_two_pow_le_supportMass_GN_of_bodyPrimitivePrimeFactor_family
 petal_range_two_pow_le_rad_GN_of_bodyPrimitivePrimeFactor_family
 petal_range_two_pow_le_supportMass_GN_of_zsigmondyPrimitivePrimeDivisor_family
 petal_range_two_pow_le_rad_GN_of_zsigmondyPrimitivePrimeDivisor_family
+petal_range_two_pow_le_supportMass_GN_of_bodyPrimitivePrimeFactor_pairwise
+petal_range_two_pow_le_rad_GN_of_bodyPrimitivePrimeFactor_pairwise
+petal_range_two_pow_le_supportMass_GN_of_zsigmondyPrimitivePrimeDivisor_pairwise
+petal_range_two_pow_le_rad_GN_of_zsigmondyPrimitivePrimeDivisor_pairwise
 ```
 
 The construction still leaves the serious arithmetic hypotheses explicit:
@@ -521,3 +526,14 @@ k range-indexed primitive carriers
   -> 2^k <= supportMass(GN)
   -> 2^k <= rad(GN)
 ```
+
+Follow-up checkpoint:
+
+The range layer now also accepts pairwise label noncollision:
+
+```text
+i < k, j < k, i != j -> qOf i != qOf j
+```
+
+This is converted into `Set.InjOn qOf ↑(Finset.range k)`, so concrete
+experiments can avoid constructing the subtype-level injectivity proof by hand.
````
`````
