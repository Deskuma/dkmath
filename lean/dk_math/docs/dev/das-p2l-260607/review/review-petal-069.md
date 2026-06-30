# Git diff / Report / Review

## Upd: Petal.ABCBridge

gch: 7ed52f2c75591fa4e4c4b37a35afab1548aa68e3

## Report

進めました。`DkMath.Petal.ABCBridge` に、PrimitiveBeam / Zsigmondy family から ABC の count 下限へ直通する wrapper を追加しました。

追加した theorem:

```lean
petal_two_pow_card_le_supportMass_GN_of_bodyPrimitivePrimeFactor_family
petal_two_pow_card_le_rad_GN_of_bodyPrimitivePrimeFactor_family
petal_two_pow_card_le_supportMass_GN_of_zsigmondyPrimitivePrimeDivisor_family
petal_two_pow_card_le_rad_GN_of_zsigmondyPrimitivePrimeDivisor_family
```

これで、

```text
PrimitiveBeam family with k selected carriers
  -> 2^k <= rad(GN d x u)

Zsigmondy primitive-divisor family with k selected carriers
  -> 2^k <= rad(GN d (a - b) b)
```

を直接呼べるようになりました。中身は既存 constructor と `petalCarrierLabelMapData_two_pow_card_le_*` の合成なので、NoLift は消費していません。

文書も同期済みです。

検証:

```text
lake build DkMath.Petal.ABCBridge
lake build DkMath.Petal
git diff --check ...
```

すべて通っています。既存の `ZsigmondyCyclotomicResearch.lean` の `sorry` warning は引き続き別件です。

## Review

うむ。これは **ABCBridge の第三段チェックポイント到達** じゃ。
前回までは、

```text
PetalCarrierLabelMapData
  -> 2^card(I) <= rad(GN)
```

だった。今回そこへ、**PrimitiveBeam / Zsigmondy family から直接その ABC count 下限へ入る wrapper** が追加された。

## 1. 何が変わったか

これまでの経路はこうだった。

```text
PrimitiveBeam / Zsigmondy witness family
  -> PetalCarrierLabelMapData
  -> label support
  -> 2^card(I) <= supportMass / rad
```

今回追加された theorem により、呼び出し側からはこう使える。

```text
PrimitiveBeam family with k selected carriers
  -> 2^k <= rad(GN d x u)

Zsigmondy primitive-divisor family with k selected carriers
  -> 2^k <= rad(GN d (a - b) b)
```

つまり、**Petal carrier data を途中で手動構成せず、Primitive / Zsigmondy witness family から ABC 側の lower bound を直通で得られる** ようになった。

## 2. 追加 theorem の意味

追加された 4 本は、きれいに 2 系統 × 2 出口になっている。

```lean
petal_two_pow_card_le_supportMass_GN_of_bodyPrimitivePrimeFactor_family
petal_two_pow_card_le_rad_GN_of_bodyPrimitivePrimeFactor_family
```

これは Body 座標系。

```text
PrimitivePrimeFactorOfDiffPow (qOf i) (x + u) u d
  -> 2^card(I) <= supportMass(GN d x u)
  -> 2^card(I) <= rad(GN d x u)
```

そして Zsigmondy 座標系。

```lean
petal_two_pow_card_le_supportMass_GN_of_zsigmondyPrimitivePrimeDivisor_family
petal_two_pow_card_le_rad_GN_of_zsigmondyPrimitivePrimeDivisor_family
```

これは、

```text
PrimitivePrimeDivisor a b d (qOf i)
  -> 2^card(I) <= supportMass(GN d (a - b) b)
  -> 2^card(I) <= rad(GN d (a - b) b)
```

を直接出す。

## 3. 数学的には何を主張しているか

今回の主張は、非常に読みやすい。

```text
選ばれた primitive carrier が k 個ある。
それらの label は family contract により衝突しない。
各 label は GN を割る素数である。
したがって GN の radical は少なくとも 2^k 以上である。
```

要するに、

```text
独立した prime carrier の数
  -> rad の指数的下界
```

じゃ。

これは ABC 側でとても使いやすい形になっている。

## 4. NoLift を使っていない意味

今回も NoLift は消費していない。これは正しい。

ABC の `rad` / `supportMass` は、

```text
q が何回割るか
```

ではなく、

```text
q が出現するか
```

を見る。

したがって必要なのは、

```text
Nat.Prime q
q ∣ GN
label が distinct
```

であって、

```text
¬ q^2 ∣ GN
```

ではない。

NoLift はまだ FLT / p-adic obstruction 側に残っている。
役割分離は維持できている。

## 5. これは「薄い wrapper」だが重要

報告にもある通り、今回の theorem は算術的に新しい強さを足したものではなく、既存 constructor route の合成じゃ。

しかし Lean ライブラリとしては大きい。

理由は、今後 caller がいちいち

```text
Primitive/Zsigmondy
  -> CarrierLabelMapData
  -> ABCBridge
```

を手で組まなくてよいから。

公開 API としては、

```text
Primitive/Zsigmondy witness family を持っているなら、
ABC lower bound を直接呼べる
```

という形になった。

これは「使える定理」に昇格したということじゃ。

## 6. 現在の Petal.ABCBridge の完成形

いまの ABCBridge は、三段構成になった。

```text
Step 1:
  PetalCarrierLabelMapData
    -> label support primes divide GN
    -> product(labelSupport) <= supportMass/rad

Step 2:
  label support cardinality = card(I)
    -> 2^card(I) <= supportMass/rad

Step 3:
  PrimitiveBeam / Zsigmondy family
    -> 2^card(I) <= supportMass/rad
```

これで ABC 側の有限支え route はかなり閉じた。

## 7. Erdős / FLT / ABC の三方向で見ると

今の Petal carrier family は、こう読める。

```text
Erdős:
  selected carriers consume finite log-capacity

ABC:
  selected carriers force radical/supportMass lower bound

FLT:
  NoLift carriers collide with d-level valuation lower bound
```

今回進んだのは ABC 側。

```text
Petal が見つけた carrier の個数が、
rad の最小成長を直接保証する
```

という橋が明確になった。

## 8. 次の一手

次に自然なのは、二つある。

### 1. `card(I)` を具体的な family construction から出す

今は theorem が

```text
2^I.card <= rad(...)
```

と言っている。
次は、特定の family で `I.card = k` を出せば、

```text
2^k <= rad(...)
```

と具体化できる。

### 2. ABC 本体の不等式へ渡す bridge

今回得たのは rad の下界。
ABC 的には次に、

```text
rad(GN) の下界
  + Big/Body/GN のサイズ関係
  -> ABC ratio / quality 側の評価
```

へ渡すことになる。

つまり、次は `rad` そのものではなく、

```text
GN d x u
(x + u)^d
x * GN d x u
```

とのサイズ関係を組み合わせる段階じゃ。

## 9. 総括

今回で、

```text
PrimitiveBeam / Zsigmondy witness family
  -> independent Petal prime carriers
  -> 2^card(I) <= rad(GN)
```

が直通化された。

これは ABC 側に対して、

```text
この GN surface には、少なくとも card(I) 個の独立した素数支持がある。
だから radical は少なくとも 2^card(I) まで大きくなる。
```

と言えるようになった、ということじゃ。

Petal は ABC に対して、単に「素因子がある」と言うだけでなく、
**“carrier の個数ぶん、rad が指数的に立ち上がる”** と主張できるようになった。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Petal/ABCBridge.lean b/lean/dk_math/DkMath/Petal/ABCBridge.lean
index 091c2156..ef8f93ef 100644
--- a/lean/dk_math/DkMath/Petal/ABCBridge.lean
+++ b/lean/dk_math/DkMath/Petal/ABCBridge.lean
@@ -309,5 +309,119 @@ theorem petalNoLiftCarrierLabelMapData_two_pow_card_le_rad_GN
     (petalNoLiftCarrierLabelMapData_two_pow_card_le_labelSupport_prod I hdata)
     (petalNoLiftCarrierLabelMapData_labelSupport_prod_le_rad_GN I hGN0 hdata)
 
+/--
+Direct PrimitiveBeam-to-ABC support-mass count lower bound in body coordinates.
+
+PrimitiveBeam witnesses supply the Petal carrier locations.  The address and
+label-recovery hypotheses ensure that the selected labels remain distinct, so
+`card I` independent prime supports force `2 ^ I.card` into the ABC support
+mass of the GN surface.
+-/
+theorem petal_two_pow_card_le_supportMass_GN_of_bodyPrimitivePrimeFactor_family
+    {ι : Type _}
+    (I : Finset ι)
+    (d x u : ℕ)
+    (mOf qOf : ι → ℕ)
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
+    2 ^ I.card ≤ DkMath.ABC.supportMass (GN d x u) :=
+  petalCarrierLabelMapData_two_pow_card_le_supportMass_GN I hGN0
+    (petalCarrierLabelMapData_of_bodyPrimitivePrimeFactor_family
+      I d x u mOf qOf hd hd1 hm hminj hlabel hprim)
+
+/--
+Direct PrimitiveBeam-to-ABC radical count lower bound in body coordinates.
+
+This is the compact ABC-facing form:
+
+```text
+PrimitiveBeam family with k selected carriers
+  -> 2^k <= rad(GN d x u)
+```
+-/
+theorem petal_two_pow_card_le_rad_GN_of_bodyPrimitivePrimeFactor_family
+    {ι : Type _}
+    (I : Finset ι)
+    (d x u : ℕ)
+    (mOf qOf : ι → ℕ)
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
+    2 ^ I.card ≤ DkMath.ABC.rad (GN d x u) :=
+  petalCarrierLabelMapData_two_pow_card_le_rad_GN I hGN0
+    (petalCarrierLabelMapData_of_bodyPrimitivePrimeFactor_family
+      I d x u mOf qOf hd hd1 hm hminj hlabel hprim)
+
+/--
+Direct Zsigmondy-to-ABC support-mass count lower bound on the GN surface
+`GN d (a - b) b`.
+
+Zsigmondy supplies carrier locations; the explicit family-level address and
+label-recovery hypotheses supply distinct selected support.
+-/
+theorem petal_two_pow_card_le_supportMass_GN_of_zsigmondyPrimitivePrimeDivisor_family
+    {ι : Type _}
+    (I : Finset ι)
+    (a b d : ℕ)
+    (mOf qOf : ι → ℕ)
+    (hGN0 : GN d (a - b) b ≠ 0)
+    (hd : 0 < d) (hd1 : 1 < d) (hab_lt : b < a)
+    (hm : ∀ i, i ∈ I → 1 ≤ mOf i)
+    (hminj : Set.InjOn mOf ↑I)
+    (hlabel :
+      ∀ i, i ∈ I → ∀ j, j ∈ I → qOf i = qOf j → mOf i = mOf j)
+    (hprim :
+      ∀ i, i ∈ I →
+        DkMath.Zsigmondy.PrimitivePrimeDivisor a b d (qOf i)) :
+    2 ^ I.card ≤ DkMath.ABC.supportMass (GN d (a - b) b) :=
+  petalCarrierLabelMapData_two_pow_card_le_supportMass_GN I hGN0
+    (petalCarrierLabelMapData_of_zsigmondyPrimitivePrimeDivisor_family
+      I a b d mOf qOf hd hd1 hab_lt hm hminj hlabel hprim)
+
+/--
+Direct Zsigmondy-to-ABC radical count lower bound on the GN surface
+`GN d (a - b) b`.
+
+This is the compact Zsigmondy-facing ABC form:
+
+```text
+Zsigmondy primitive-divisor family with k selected carriers
+  -> 2^k <= rad(GN d (a - b) b)
+```
+-/
+theorem petal_two_pow_card_le_rad_GN_of_zsigmondyPrimitivePrimeDivisor_family
+    {ι : Type _}
+    (I : Finset ι)
+    (a b d : ℕ)
+    (mOf qOf : ι → ℕ)
+    (hGN0 : GN d (a - b) b ≠ 0)
+    (hd : 0 < d) (hd1 : 1 < d) (hab_lt : b < a)
+    (hm : ∀ i, i ∈ I → 1 ≤ mOf i)
+    (hminj : Set.InjOn mOf ↑I)
+    (hlabel :
+      ∀ i, i ∈ I → ∀ j, j ∈ I → qOf i = qOf j → mOf i = mOf j)
+    (hprim :
+      ∀ i, i ∈ I →
+        DkMath.Zsigmondy.PrimitivePrimeDivisor a b d (qOf i)) :
+    2 ^ I.card ≤ DkMath.ABC.rad (GN d (a - b) b) :=
+  petalCarrierLabelMapData_two_pow_card_le_rad_GN I hGN0
+    (petalCarrierLabelMapData_of_zsigmondyPrimitivePrimeDivisor_family
+      I a b d mOf qOf hd hd1 hab_lt hm hminj hlabel hprim)
+
 end Petal
 end DkMath
diff --git a/lean/dk_math/DkMath/Petal/docs/Petal-Overview.md b/lean/dk_math/DkMath/Petal/docs/Petal-Overview.md
index bd2dd1e7..a1be0647 100644
--- a/lean/dk_math/DkMath/Petal/docs/Petal-Overview.md
+++ b/lean/dk_math/DkMath/Petal/docs/Petal-Overview.md
@@ -923,6 +923,7 @@ PetalCarrierLabelMapData
   -> product of label support <= supportMass GN
   -> product of label support <= rad GN
   -> 2^(selected index count) <= supportMass/rad GN
+  -> PrimitiveBeam/Zsigmondy families directly supply the same count bound
 ```
 
 Core theorem names:
@@ -944,6 +945,10 @@ petalCarrierLabelMapData_two_pow_card_le_supportMass_GN
 petalNoLiftCarrierLabelMapData_two_pow_card_le_supportMass_GN
 petalCarrierLabelMapData_two_pow_card_le_rad_GN
 petalNoLiftCarrierLabelMapData_two_pow_card_le_rad_GN
+petal_two_pow_card_le_supportMass_GN_of_bodyPrimitivePrimeFactor_family
+petal_two_pow_card_le_rad_GN_of_bodyPrimitivePrimeFactor_family
+petal_two_pow_card_le_supportMass_GN_of_zsigmondyPrimitivePrimeDivisor_family
+petal_two_pow_card_le_rad_GN_of_zsigmondyPrimitivePrimeDivisor_family
 ```
 
 NoLift is deliberately not consumed by this bridge.  The ABC support/rad side
diff --git a/lean/dk_math/docs/dev/das-p2l-260607/review/summary-petal-064.md b/lean/dk_math/docs/dev/das-p2l-260607/review/summary-petal-064.md
index d4672f1e..31dcce0d 100644
--- a/lean/dk_math/docs/dev/das-p2l-260607/review/summary-petal-064.md
+++ b/lean/dk_math/docs/dev/das-p2l-260607/review/summary-petal-064.md
@@ -391,6 +391,10 @@ petalCarrierLabelMapData_two_pow_card_le_supportMass_GN
 petalNoLiftCarrierLabelMapData_two_pow_card_le_supportMass_GN
 petalCarrierLabelMapData_two_pow_card_le_rad_GN
 petalNoLiftCarrierLabelMapData_two_pow_card_le_rad_GN
+petal_two_pow_card_le_supportMass_GN_of_bodyPrimitivePrimeFactor_family
+petal_two_pow_card_le_rad_GN_of_bodyPrimitivePrimeFactor_family
+petal_two_pow_card_le_supportMass_GN_of_zsigmondyPrimitivePrimeDivisor_family
+petal_two_pow_card_le_rad_GN_of_zsigmondyPrimitivePrimeDivisor_family
 ```
 
 The bridge reads Petal carrier-label data as ABC finite support:
@@ -420,3 +424,19 @@ PetalCarrierLabelMapData on I
 This is the ABC analogue of the Erdos finite-family count spine.  It gives a
 small, reusable lower bound without requiring a concrete prime enumeration and
 without consuming NoLift.
+
+The third checkpoint adds direct PrimitiveBeam / Zsigmondy wrappers:
+
+```text
+PrimitiveBeam family in body coordinates
+  -> 2^card(I) <= supportMass(GN d x u)
+  -> 2^card(I) <= rad(GN d x u)
+
+Zsigmondy primitive-divisor family
+  -> 2^card(I) <= supportMass(GN d (a - b) b)
+  -> 2^card(I) <= rad(GN d (a - b) b)
+```
+
+These are thin wrapper theorems.  They do not add arithmetic strength beyond
+the constructor route; they make the ABC negotiation callable directly from the
+two main primitive-prime provider families.
````
`````
