# Git diff / Report / Review

## Upd: Petal.ABCBridge

gch: 99967b9e748f2d712989d49da3900f99b5ddaf59

## Report

進めました。`DkMath.Petal.ABCBridge` に `_of_card_le` 系を追加し、exact な `I.card = k` ではなく `k ≤ I.card` だけで ABC 下界へ入れるようにしました。

追加した主な theorem:

```lean
petalCarrierLabelMapData_two_pow_le_supportMass_GN_of_card_le
petalCarrierLabelMapData_two_pow_le_rad_GN_of_card_le
petalNoLiftCarrierLabelMapData_two_pow_le_supportMass_GN_of_card_le
petalNoLiftCarrierLabelMapData_two_pow_le_rad_GN_of_card_le
petal_two_pow_le_supportMass_GN_of_bodyPrimitivePrimeFactor_family_card_le
petal_two_pow_le_rad_GN_of_bodyPrimitivePrimeFactor_family_card_le
petal_two_pow_le_supportMass_GN_of_zsigmondyPrimitivePrimeDivisor_family_card_le
petal_two_pow_le_rad_GN_of_zsigmondyPrimitivePrimeDivisor_family_card_le
```

これで実験 construction がまず

```text
k <= I.card
```

だけを出せば、

```text
2^k <= supportMass(GN)
2^k <= rad(GN)
```

へ渡せます。exact count より先に lower count が出る場面を拾えるので、ABC 交渉用 API としてだいぶ使いやすくなりました。

文書も `Petal-Overview.md` と `summary-petal-064.md` に同期済みです。

検証:

```text
lake build DkMath.Petal.ABCBridge
lake build DkMath.Petal
git diff --check ...
```

すべて通っています。既存の `ZsigmondyCyclotomicResearch.lean` の `sorry` warning は別件として継続しています。

## Review

うむ。これは **Petal.ABCBridge が exact count API から lower count API へ進んだ** という状況じゃ。
前回の `_of_card_eq` は「`I.card = k` が出たら `2^k <= rad(GN)`」だった。今回の `_of_card_le` はさらに実験向きで、**`k ≤ I.card` だけで `2^k <= supportMass/rad` へ入れる** ようになった。

## 1. 何が変わったか

今回追加された中心はこの系統。

```lean
petalCarrierLabelMapData_two_pow_le_supportMass_GN_of_card_le
petalCarrierLabelMapData_two_pow_le_rad_GN_of_card_le
petalNoLiftCarrierLabelMapData_two_pow_le_supportMass_GN_of_card_le
petalNoLiftCarrierLabelMapData_two_pow_le_rad_GN_of_card_le
```

意味は、

```text
PetalCarrierLabelMapData on I
+ k ≤ I.card
-> 2^k <= supportMass(GN d x u)
-> 2^k <= rad(GN d x u)
```

じゃ。

前回は、

```text
I.card = k
```

が必要だった。

今回からは、

```text
少なくとも k 個ある
```

でよい。

これは大きい。具体 construction では、exact count より lower bound の方が先に出ることが多いからじゃ。

## 2. 数学的には何をしているか

中身は非常にきれい。

既存 theorem で、

```text
2^I.card <= rad(GN)
```

がある。

そこへ、

```text
k ≤ I.card
```

を入れる。

すると単調性から、

```text
2^k ≤ 2^I.card
```

が出る。

よって、

```text
2^k ≤ 2^I.card ≤ rad(GN)
```

となる。

Lean ではここを、

```lean
Nat.pow_le_pow_right (by norm_num : 0 < 2) hcard
```

で処理している。
素直でよい。

## 3. PrimitiveBeam / Zsigmondy 直通版も揃った

今回、data 版だけでなく、PrimitiveBeam / Zsigmondy family からの直通版も追加されている。

```lean
petal_two_pow_le_supportMass_GN_of_bodyPrimitivePrimeFactor_family_card_le
petal_two_pow_le_rad_GN_of_bodyPrimitivePrimeFactor_family_card_le
petal_two_pow_le_supportMass_GN_of_zsigmondyPrimitivePrimeDivisor_family_card_le
petal_two_pow_le_rad_GN_of_zsigmondyPrimitivePrimeDivisor_family_card_le
```

これで言えることはこう。

```text
PrimitiveBeam family
+ k ≤ I.card
-> 2^k <= rad(GN d x u)
```

および、

```text
Zsigmondy primitive-divisor family
+ k ≤ I.card
-> 2^k <= rad(GN d (a - b) b)
```

つまり、具体構成側が「少なくとも k 個の primitive carrier を選べた」と言えれば、ABC 側では即座に `rad` 下界が出る。

## 4. 今回の位置づけ

これは ABCBridge の **実験 construction 受け皿化** じゃ。

これまでの階段はこうだった。

```text
PetalCarrierLabelMapData
  -> label support is prime divisor support of GN
  -> product(labelSupport) <= supportMass/rad
  -> card(labelSupport) = I.card
  -> 2^I.card <= supportMass/rad
  -> I.card = k なら 2^k <= supportMass/rad
```

今回こうなった。

```text
k <= I.card なら 2^k <= supportMass/rad
```

つまり、exact な family cardinality が不要になった。

## 5. これがなぜ重要か

探索段階では、最初から

```text
I.card = k
```

を証明するのは重いことがある。

しかし、

```text
k ≤ I.card
```

なら、たとえば「この範囲に少なくとも k 個ある」「この injection で k 個埋め込める」という形で出しやすい。

これは Petal の実験と相性が良い。

```text
carrier family を完全分類する前に、
最低 k 個の独立 carrier を確保する
```

だけで ABC 側へ渡せるからじゃ。

## 6. NoLift の役割分離も維持されている

今回も NoLift は消費していない。

これは前回までと同じく正しい。

```text
ABCBridge:
  prime support / rad を見る

NoLift:
  p-adic valuation obstruction を見る
```

ABC の `rad` は、素数が一度でも出ればよい。
`q^2 ∣ GN` かどうかは見ない。

だから NoLift 版 theorem は「NoLift data を持つ caller 用の convenience」であって、証明中で NoLift 成分を使っているわけではない。

## 7. 現在の到達点

いま Petal.ABCBridge は、かなり使いやすい形になっている。

```text
PrimitiveBeam / Zsigmondy family
+ valid value
+ value injectivity
+ label recovery
+ k <= I.card
-> 2^k <= supportMass(GN)
-> 2^k <= rad(GN)
```

これは ABC 側に対して、

```text
少なくとも k 個の独立 Petal carrier がある。
したがって GN の radical は少なくとも 2^k である。
```

と言える定理群じゃ。

## 8. 次の本丸

次はもう、ABCBridge 内ではなく、**具体 family construction 側** じゃ。

狙うべきは、

```text
k <= I.card
```

を出す構成。

たとえば次のような方向になる。

```text
Finset.range k を carrier index にする
明示的な PrimitiveBeam witness を k 個並べる
Zsigmondy primitive divisor を k 個選ぶ
address / label recovery を満たすように qOf, mOf を設計する
```

ABCBridge はもう、それを受け取れる。

## 9. 総括

今回の進展を一言で言うと、

```text
Petal.ABCBridge が「ちょうど k 個」ではなく
「少なくとも k 個」の carrier family を消費できるようになった。
```

これは実験段階ではかなり強い。

exact count は完成後の定理。
lower count は探索中にも使える定理。

つまり、Petal は ABC に対して今やこう言える。

```text
完全な個数はまだ知らない。
だが少なくとも k 個の独立 carrier はある。
ゆえに rad(GN) は 2^k 以上でなければならない。
```

うむ。
これは **ABC 交渉用 API が、研究探索の粗い下界にも対応した** という進展じゃ。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Petal/ABCBridge.lean b/lean/dk_math/DkMath/Petal/ABCBridge.lean
index 2f8fd21a..4ab1726f 100644
--- a/lean/dk_math/DkMath/Petal/ABCBridge.lean
+++ b/lean/dk_math/DkMath/Petal/ABCBridge.lean
@@ -379,6 +379,76 @@ theorem petalNoLiftCarrierLabelMapData_two_pow_le_rad_GN_of_card_eq
   simpa [← hcard] using
     petalNoLiftCarrierLabelMapData_two_pow_card_le_rad_GN I hGN0 hdata
 
+/--
+Carrier-label map data gives an ABC support-mass lower bound from any lower
+bound `k ≤ I.card` on the selected family size.
+
+This is usually easier to use than the exact-cardinality form when a concrete
+construction only proves that it has at least `k` independent carriers.
+-/
+theorem petalCarrierLabelMapData_two_pow_le_supportMass_GN_of_card_le
+    {ι : Type _}
+    (I : Finset ι)
+    {d x u k : ℕ}
+    {mOf qOf : ι → ℕ}
+    (hcard : k ≤ I.card)
+    (hGN0 : GN d x u ≠ 0)
+    (hdata : PetalCarrierLabelMapData I d x u mOf qOf) :
+    2 ^ k ≤ DkMath.ABC.supportMass (GN d x u) :=
+  le_trans
+    (Nat.pow_le_pow_right (by norm_num : 0 < 2) hcard)
+    (petalCarrierLabelMapData_two_pow_card_le_supportMass_GN I hGN0 hdata)
+
+/--
+Carrier-label map data gives an ABC radical lower bound from any lower bound
+`k ≤ I.card` on the selected family size.
+-/
+theorem petalCarrierLabelMapData_two_pow_le_rad_GN_of_card_le
+    {ι : Type _}
+    (I : Finset ι)
+    {d x u k : ℕ}
+    {mOf qOf : ι → ℕ}
+    (hcard : k ≤ I.card)
+    (hGN0 : GN d x u ≠ 0)
+    (hdata : PetalCarrierLabelMapData I d x u mOf qOf) :
+    2 ^ k ≤ DkMath.ABC.rad (GN d x u) :=
+  le_trans
+    (Nat.pow_le_pow_right (by norm_num : 0 < 2) hcard)
+    (petalCarrierLabelMapData_two_pow_card_le_rad_GN I hGN0 hdata)
+
+/--
+No-lift carrier-label map data gives the same lower-cardinality support-mass
+bound.
+-/
+theorem petalNoLiftCarrierLabelMapData_two_pow_le_supportMass_GN_of_card_le
+    {ι : Type _}
+    (I : Finset ι)
+    {d x u k : ℕ}
+    {mOf qOf : ι → ℕ}
+    (hcard : k ≤ I.card)
+    (hGN0 : GN d x u ≠ 0)
+    (hdata : PetalNoLiftCarrierLabelMapData I d x u mOf qOf) :
+    2 ^ k ≤ DkMath.ABC.supportMass (GN d x u) :=
+  le_trans
+    (Nat.pow_le_pow_right (by norm_num : 0 < 2) hcard)
+    (petalNoLiftCarrierLabelMapData_two_pow_card_le_supportMass_GN I hGN0 hdata)
+
+/--
+No-lift carrier-label map data gives the same lower-cardinality radical bound.
+-/
+theorem petalNoLiftCarrierLabelMapData_two_pow_le_rad_GN_of_card_le
+    {ι : Type _}
+    (I : Finset ι)
+    {d x u k : ℕ}
+    {mOf qOf : ι → ℕ}
+    (hcard : k ≤ I.card)
+    (hGN0 : GN d x u ≠ 0)
+    (hdata : PetalNoLiftCarrierLabelMapData I d x u mOf qOf) :
+    2 ^ k ≤ DkMath.ABC.rad (GN d x u) :=
+  le_trans
+    (Nat.pow_le_pow_right (by norm_num : 0 < 2) hcard)
+    (petalNoLiftCarrierLabelMapData_two_pow_card_le_rad_GN I hGN0 hdata)
+
 /--
 Direct PrimitiveBeam-to-ABC support-mass count lower bound in body coordinates.
 
@@ -466,6 +536,60 @@ theorem petal_two_pow_le_rad_GN_of_bodyPrimitivePrimeFactor_family_card_eq
     petal_two_pow_card_le_rad_GN_of_bodyPrimitivePrimeFactor_family
       I d x u mOf qOf hGN0 hd hd1 hm hminj hlabel hprim
 
+/--
+Lower-cardinality PrimitiveBeam-to-ABC support-mass count bound in body
+coordinates.
+-/
+theorem petal_two_pow_le_supportMass_GN_of_bodyPrimitivePrimeFactor_family_card_le
+    {ι : Type _}
+    (I : Finset ι)
+    (d x u : ℕ)
+    (mOf qOf : ι → ℕ)
+    {k : ℕ}
+    (hcard : k ≤ I.card)
+    (hGN0 : GN d x u ≠ 0)
+    (hd : 0 < d) (hd1 : 1 < d)
+    (hm : ∀ i, i ∈ I → 1 ≤ mOf i)
+    (hminj : Set.InjOn mOf ↑I)
+    (hlabel :
+      ∀ i, i ∈ I → ∀ j, j ∈ I → qOf i = qOf j → mOf i = mOf j)
+    (hprim :
+      ∀ i, i ∈ I →
+        DkMath.NumberTheory.PrimitiveBeam.PrimitivePrimeFactorOfDiffPow
+          (qOf i) (x + u) u d) :
+    2 ^ k ≤ DkMath.ABC.supportMass (GN d x u) :=
+  le_trans
+    (Nat.pow_le_pow_right (by norm_num : 0 < 2) hcard)
+    (petal_two_pow_card_le_supportMass_GN_of_bodyPrimitivePrimeFactor_family
+      I d x u mOf qOf hGN0 hd hd1 hm hminj hlabel hprim)
+
+/--
+Lower-cardinality PrimitiveBeam-to-ABC radical count bound in body
+coordinates.
+-/
+theorem petal_two_pow_le_rad_GN_of_bodyPrimitivePrimeFactor_family_card_le
+    {ι : Type _}
+    (I : Finset ι)
+    (d x u : ℕ)
+    (mOf qOf : ι → ℕ)
+    {k : ℕ}
+    (hcard : k ≤ I.card)
+    (hGN0 : GN d x u ≠ 0)
+    (hd : 0 < d) (hd1 : 1 < d)
+    (hm : ∀ i, i ∈ I → 1 ≤ mOf i)
+    (hminj : Set.InjOn mOf ↑I)
+    (hlabel :
+      ∀ i, i ∈ I → ∀ j, j ∈ I → qOf i = qOf j → mOf i = mOf j)
+    (hprim :
+      ∀ i, i ∈ I →
+        DkMath.NumberTheory.PrimitiveBeam.PrimitivePrimeFactorOfDiffPow
+          (qOf i) (x + u) u d) :
+    2 ^ k ≤ DkMath.ABC.rad (GN d x u) :=
+  le_trans
+    (Nat.pow_le_pow_right (by norm_num : 0 < 2) hcard)
+    (petal_two_pow_card_le_rad_GN_of_bodyPrimitivePrimeFactor_family
+      I d x u mOf qOf hGN0 hd hd1 hm hminj hlabel hprim)
+
 /--
 Direct Zsigmondy-to-ABC support-mass count lower bound on the GN surface
 `GN d (a - b) b`.
@@ -547,5 +671,57 @@ theorem petal_two_pow_le_rad_GN_of_zsigmondyPrimitivePrimeDivisor_family_card_eq
     petal_two_pow_card_le_rad_GN_of_zsigmondyPrimitivePrimeDivisor_family
       I a b d mOf qOf hGN0 hd hd1 hab_lt hm hminj hlabel hprim
 
+/--
+Lower-cardinality Zsigmondy-to-ABC support-mass count bound on the GN surface
+`GN d (a - b) b`.
+-/
+theorem petal_two_pow_le_supportMass_GN_of_zsigmondyPrimitivePrimeDivisor_family_card_le
+    {ι : Type _}
+    (I : Finset ι)
+    (a b d : ℕ)
+    (mOf qOf : ι → ℕ)
+    {k : ℕ}
+    (hcard : k ≤ I.card)
+    (hGN0 : GN d (a - b) b ≠ 0)
+    (hd : 0 < d) (hd1 : 1 < d) (hab_lt : b < a)
+    (hm : ∀ i, i ∈ I → 1 ≤ mOf i)
+    (hminj : Set.InjOn mOf ↑I)
+    (hlabel :
+      ∀ i, i ∈ I → ∀ j, j ∈ I → qOf i = qOf j → mOf i = mOf j)
+    (hprim :
+      ∀ i, i ∈ I →
+        DkMath.Zsigmondy.PrimitivePrimeDivisor a b d (qOf i)) :
+    2 ^ k ≤ DkMath.ABC.supportMass (GN d (a - b) b) :=
+  le_trans
+    (Nat.pow_le_pow_right (by norm_num : 0 < 2) hcard)
+    (petal_two_pow_card_le_supportMass_GN_of_zsigmondyPrimitivePrimeDivisor_family
+      I a b d mOf qOf hGN0 hd hd1 hab_lt hm hminj hlabel hprim)
+
+/--
+Lower-cardinality Zsigmondy-to-ABC radical count bound on the GN surface
+`GN d (a - b) b`.
+-/
+theorem petal_two_pow_le_rad_GN_of_zsigmondyPrimitivePrimeDivisor_family_card_le
+    {ι : Type _}
+    (I : Finset ι)
+    (a b d : ℕ)
+    (mOf qOf : ι → ℕ)
+    {k : ℕ}
+    (hcard : k ≤ I.card)
+    (hGN0 : GN d (a - b) b ≠ 0)
+    (hd : 0 < d) (hd1 : 1 < d) (hab_lt : b < a)
+    (hm : ∀ i, i ∈ I → 1 ≤ mOf i)
+    (hminj : Set.InjOn mOf ↑I)
+    (hlabel :
+      ∀ i, i ∈ I → ∀ j, j ∈ I → qOf i = qOf j → mOf i = mOf j)
+    (hprim :
+      ∀ i, i ∈ I →
+        DkMath.Zsigmondy.PrimitivePrimeDivisor a b d (qOf i)) :
+    2 ^ k ≤ DkMath.ABC.rad (GN d (a - b) b) :=
+  le_trans
+    (Nat.pow_le_pow_right (by norm_num : 0 < 2) hcard)
+    (petal_two_pow_card_le_rad_GN_of_zsigmondyPrimitivePrimeDivisor_family
+      I a b d mOf qOf hGN0 hd hd1 hab_lt hm hminj hlabel hprim)
+
 end Petal
 end DkMath
diff --git a/lean/dk_math/DkMath/Petal/docs/Petal-Overview.md b/lean/dk_math/DkMath/Petal/docs/Petal-Overview.md
index 174df401..dec38165 100644
--- a/lean/dk_math/DkMath/Petal/docs/Petal-Overview.md
+++ b/lean/dk_math/DkMath/Petal/docs/Petal-Overview.md
@@ -949,18 +949,30 @@ petalCarrierLabelMapData_two_pow_le_supportMass_GN_of_card_eq
 petalCarrierLabelMapData_two_pow_le_rad_GN_of_card_eq
 petalNoLiftCarrierLabelMapData_two_pow_le_supportMass_GN_of_card_eq
 petalNoLiftCarrierLabelMapData_two_pow_le_rad_GN_of_card_eq
+petalCarrierLabelMapData_two_pow_le_supportMass_GN_of_card_le
+petalCarrierLabelMapData_two_pow_le_rad_GN_of_card_le
+petalNoLiftCarrierLabelMapData_two_pow_le_supportMass_GN_of_card_le
+petalNoLiftCarrierLabelMapData_two_pow_le_rad_GN_of_card_le
 petal_two_pow_card_le_supportMass_GN_of_bodyPrimitivePrimeFactor_family
 petal_two_pow_card_le_rad_GN_of_bodyPrimitivePrimeFactor_family
 petal_two_pow_card_le_supportMass_GN_of_zsigmondyPrimitivePrimeDivisor_family
 petal_two_pow_card_le_rad_GN_of_zsigmondyPrimitivePrimeDivisor_family
 petal_two_pow_le_rad_GN_of_bodyPrimitivePrimeFactor_family_card_eq
 petal_two_pow_le_rad_GN_of_zsigmondyPrimitivePrimeDivisor_family_card_eq
+petal_two_pow_le_supportMass_GN_of_bodyPrimitivePrimeFactor_family_card_le
+petal_two_pow_le_rad_GN_of_bodyPrimitivePrimeFactor_family_card_le
+petal_two_pow_le_supportMass_GN_of_zsigmondyPrimitivePrimeDivisor_family_card_le
+petal_two_pow_le_rad_GN_of_zsigmondyPrimitivePrimeDivisor_family_card_le
 ```
 
 The `_of_card_eq` forms are convenience endpoints for concrete finite family
 constructions.  Once a caller proves `I.card = k`, the lower bound can be read
 directly as `2^k <= supportMass/rad`.
 
+The `_of_card_le` forms are the lower-bound versions.  They only require
+`k <= I.card`, which is often the first usable output of an experimental
+family construction.
+
 NoLift is deliberately not consumed by this bridge.  The ABC support/rad side
 only needs finite prime support; NoLift remains available for valuation
 obstruction routes.
diff --git a/lean/dk_math/docs/dev/das-p2l-260607/review/summary-petal-064.md b/lean/dk_math/docs/dev/das-p2l-260607/review/summary-petal-064.md
index 65b51b23..126798b1 100644
--- a/lean/dk_math/docs/dev/das-p2l-260607/review/summary-petal-064.md
+++ b/lean/dk_math/docs/dev/das-p2l-260607/review/summary-petal-064.md
@@ -395,12 +395,20 @@ petalCarrierLabelMapData_two_pow_le_supportMass_GN_of_card_eq
 petalCarrierLabelMapData_two_pow_le_rad_GN_of_card_eq
 petalNoLiftCarrierLabelMapData_two_pow_le_supportMass_GN_of_card_eq
 petalNoLiftCarrierLabelMapData_two_pow_le_rad_GN_of_card_eq
+petalCarrierLabelMapData_two_pow_le_supportMass_GN_of_card_le
+petalCarrierLabelMapData_two_pow_le_rad_GN_of_card_le
+petalNoLiftCarrierLabelMapData_two_pow_le_supportMass_GN_of_card_le
+petalNoLiftCarrierLabelMapData_two_pow_le_rad_GN_of_card_le
 petal_two_pow_card_le_supportMass_GN_of_bodyPrimitivePrimeFactor_family
 petal_two_pow_card_le_rad_GN_of_bodyPrimitivePrimeFactor_family
 petal_two_pow_card_le_supportMass_GN_of_zsigmondyPrimitivePrimeDivisor_family
 petal_two_pow_card_le_rad_GN_of_zsigmondyPrimitivePrimeDivisor_family
 petal_two_pow_le_rad_GN_of_bodyPrimitivePrimeFactor_family_card_eq
 petal_two_pow_le_rad_GN_of_zsigmondyPrimitivePrimeDivisor_family_card_eq
+petal_two_pow_le_supportMass_GN_of_bodyPrimitivePrimeFactor_family_card_le
+petal_two_pow_le_rad_GN_of_bodyPrimitivePrimeFactor_family_card_le
+petal_two_pow_le_supportMass_GN_of_zsigmondyPrimitivePrimeDivisor_family_card_le
+petal_two_pow_le_rad_GN_of_zsigmondyPrimitivePrimeDivisor_family_card_le
 ```
 
 The bridge reads Petal carrier-label data as ABC finite support:
@@ -458,3 +466,15 @@ I.card = k
 This is the first small step toward concrete family constructions.  The
 construction-specific proof of `I.card = k` remains outside `ABCBridge`; this
 file now has the API needed to consume it immediately.
+
+The fifth checkpoint adds lower-cardinality endpoints:
+
+```text
+k <= I.card
+  -> 2^k <= supportMass(GN)
+  -> 2^k <= rad(GN)
+```
+
+This is more flexible than exact cardinality.  Experimental constructions often
+produce "at least k independent carriers" before they produce an exact count,
+so the `_of_card_le` API lets that weaker result already feed ABC.
````
`````
