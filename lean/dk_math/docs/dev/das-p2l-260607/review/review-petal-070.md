# Git diff / Report / Review

## Upd: Petal.ABCBridge

gch: c17fce305ac391e79b35755f3f6b8caaffa2d7b5

## Report

進めました。`DkMath.Petal.ABCBridge` に `I.card = k` を受けて `2^k` 形へ落とす convenience theorem を追加しました。

追加した主な theorem:

```lean
petalCarrierLabelMapData_two_pow_le_supportMass_GN_of_card_eq
petalCarrierLabelMapData_two_pow_le_rad_GN_of_card_eq
petalNoLiftCarrierLabelMapData_two_pow_le_supportMass_GN_of_card_eq
petalNoLiftCarrierLabelMapData_two_pow_le_rad_GN_of_card_eq
petal_two_pow_le_rad_GN_of_bodyPrimitivePrimeFactor_family_card_eq
petal_two_pow_le_rad_GN_of_zsigmondyPrimitivePrimeDivisor_family_card_eq
```

これで具体的な family construction 側で `I.card = k` が出たら、

```text
2^k <= rad(GN ...)
```

を直接呼べます。`ABCBridge` 側は family の作り方には踏み込まず、cardinality 計算結果を消費する API として固定しています。

文書も `Petal-Overview.md` と `summary-petal-064.md` に同期済みです。

検証:

```text
lake build DkMath.Petal.ABCBridge
lake build DkMath.Petal
git diff --check ...
```

すべて通っています。既存の `ZsigmondyCyclotomicResearch.lean` の `sorry` warning は別件として継続しています。

## Review

うむ。これは **ABCBridge が具体 family construction を受け取る準備段階に入った** という進展じゃ。

前回までの到達点は、

```text id="6v846r"
PetalCarrierLabelMapData on I
  -> 2^I.card <= rad(GN ...)
```

だった。

今回の更新で、

```text id="50lued"
I.card = k
  -> 2^k <= rad(GN ...)
```

という **名前付き個数 `k` で読める endpoint** が追加された。

## 1. 何が良くなったか

これは算術的に新しい強さを足したというより、**使う側の定理になった** という進展じゃ。

具体的な family construction 側では、たいてい

```lean id="maubgv"
I.card = k
```

を別途証明する。

たとえば、

```text id="acp4co"
I = Finset.range k
```

なら `I.card = k` はすぐ出る。

今回の theorem により、そのまま

```text id="g994y6"
2^k <= rad(GN ...)
```

へ落とせる。

つまり、ABCBridge 側は family の作り方を知らなくてよい。
ただ `I.card = k` という結果だけを消費する。

この分離は正しい。

## 2. 追加 theorem の役割

汎用 data 版はこの 4 本。

```lean id="q5aw86"
petalCarrierLabelMapData_two_pow_le_supportMass_GN_of_card_eq
petalCarrierLabelMapData_two_pow_le_rad_GN_of_card_eq
petalNoLiftCarrierLabelMapData_two_pow_le_supportMass_GN_of_card_eq
petalNoLiftCarrierLabelMapData_two_pow_le_rad_GN_of_card_eq
```

意味は、

```text id="ss34xs"
PetalCarrierLabelMapData
+ I.card = k
-> 2^k <= supportMass/rad(GN)
```

NoLift 版もあるが、ここでも NoLift は消費していない。
NoLift data を持っている caller が、いちいち non-NoLift data へ戻さず使えるようにしているだけじゃ。

直通 Primitive / Zsigmondy 版はこの 2 本。

```lean id="cu00c9"
petal_two_pow_le_rad_GN_of_bodyPrimitivePrimeFactor_family_card_eq
petal_two_pow_le_rad_GN_of_zsigmondyPrimitivePrimeDivisor_family_card_eq
```

意味は、

```text id="jmst2d"
PrimitiveBeam family with I.card = k
  -> 2^k <= rad(GN d x u)

Zsigmondy family with I.card = k
  -> 2^k <= rad(GN d (a - b) b)
```

これで、具体 construction が `k` 個の primitive carrier を作れた瞬間に、ABC の `rad` 下界へ直結できる。

## 3. 今回の位置づけ

今の ABCBridge はこういう段階になった。

```text id="h0k8kl"
Step 1:
  carrier labels form finite prime support of GN

Step 2:
  support product <= supportMass/rad

Step 3:
  label noncollision gives card(labelSupport) = card(I)

Step 4:
  every prime label is >= 2, so 2^card(I) <= product(labelSupport)

Step 5:
  if I.card = k, then 2^k <= supportMass/rad
```

つまり、抽象 support から、具体的な指数下界 `2^k` まで降りてきた。

## 4. なぜこれは重要か

ABC で使いやすい形は、

```text id="uiht3u"
rad が大きい
```

だけではなく、

```text id="f1exl2"
rad は少なくとも 2^k 以上
```

のような、個数から読める明示下界じゃ。

今回の theorem により、Petal 側はこう言えるようになった。

```text id="uxw1az"
私は k 個の独立 carrier を作った。
したがって GN の rad は少なくとも 2^k だ。
```

これは強い。
family construction の個数計算が、そのまま ABC support/rad の下界になる。

## 5. 注意点

今回の theorem は、`I.card = k` を作ってくれるわけではない。

そこは別問題じゃ。

```text id="pfxpy5"
ABCBridge:
  I.card = k を消費する

Family construction:
  I.card = k を証明する
```

この分離は正しい。
ABCBridge が具体 family の作り方まで抱えると、すぐ巨大化する。

## 6. 次にあると便利なもの

次に自然なのは、このあたりじゃ。

```lean id="sdvqj4"
petalCarrierLabelMapData_two_pow_le_rad_GN_of_card_le
```

つまり、

```text id="nglqa2"
k <= I.card
  -> 2^k <= rad(GN)
```

exact に `I.card = k` が出ない場合でも、下界だけ使える。

実験 family では、最初から正確な個数より、

```text id="r4maq7"
少なくとも k 個ある
```

の方が出しやすいことが多い。

だから `_of_card_le` 版は、今後かなり便利になると思う。

もう一つは symmetry。

Primitive/Zsigmondy の named-cardinality direct wrapper は今の diff では `rad` 版のみなので、必要なら `supportMass` 版も揃えると API の対称性が増す。

## 7. 総括

今回でこうなった。

```text id="muouzl"
PrimitiveBeam / Zsigmondy family
  + I.card = k
  -> 2^k <= rad(GN)
```

これは ABC 側に向けて、かなり実用的な endpoint じゃ。

以前は、

```text id="qba6cm"
carrier support が rad を押し上げる
```

だった。

今は、

```text id="o0n7dv"
k 個の carrier があれば rad は 2^k 以上
```

と言える。

つまり、Petal.ABCBridge は **抽象 support bridge** から **個数評価 bridge** に進化した。
次は、実際に `I.card = k` または `k <= I.card` を出す concrete family construction が本丸になる。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Petal/ABCBridge.lean b/lean/dk_math/DkMath/Petal/ABCBridge.lean
index ef8f93ef..2f8fd21a 100644
--- a/lean/dk_math/DkMath/Petal/ABCBridge.lean
+++ b/lean/dk_math/DkMath/Petal/ABCBridge.lean
@@ -309,6 +309,76 @@ theorem petalNoLiftCarrierLabelMapData_two_pow_card_le_rad_GN
     (petalNoLiftCarrierLabelMapData_two_pow_card_le_labelSupport_prod I hdata)
     (petalNoLiftCarrierLabelMapData_labelSupport_prod_le_rad_GN I hGN0 hdata)
 
+/--
+Carrier-label map data gives an ABC support-mass lower bound for any named
+cardinality `k` of the selected family.
+
+This is a convenience form for callers that have already computed
+`I.card = k` from a concrete construction.
+-/
+theorem petalCarrierLabelMapData_two_pow_le_supportMass_GN_of_card_eq
+    {ι : Type _}
+    (I : Finset ι)
+    {d x u k : ℕ}
+    {mOf qOf : ι → ℕ}
+    (hcard : I.card = k)
+    (hGN0 : GN d x u ≠ 0)
+    (hdata : PetalCarrierLabelMapData I d x u mOf qOf) :
+    2 ^ k ≤ DkMath.ABC.supportMass (GN d x u) := by
+  simpa [← hcard] using
+    petalCarrierLabelMapData_two_pow_card_le_supportMass_GN I hGN0 hdata
+
+/--
+Carrier-label map data gives an ABC radical lower bound for any named
+cardinality `k` of the selected family.
+-/
+theorem petalCarrierLabelMapData_two_pow_le_rad_GN_of_card_eq
+    {ι : Type _}
+    (I : Finset ι)
+    {d x u k : ℕ}
+    {mOf qOf : ι → ℕ}
+    (hcard : I.card = k)
+    (hGN0 : GN d x u ≠ 0)
+    (hdata : PetalCarrierLabelMapData I d x u mOf qOf) :
+    2 ^ k ≤ DkMath.ABC.rad (GN d x u) := by
+  simpa [← hcard] using
+    petalCarrierLabelMapData_two_pow_card_le_rad_GN I hGN0 hdata
+
+/--
+No-lift carrier-label map data gives the same named-cardinality support-mass
+lower bound.
+
+NoLift is still not consumed by the ABC argument; this theorem exists so
+NoLift-family callers do not need to project back to the non-NoLift data layer.
+-/
+theorem petalNoLiftCarrierLabelMapData_two_pow_le_supportMass_GN_of_card_eq
+    {ι : Type _}
+    (I : Finset ι)
+    {d x u k : ℕ}
+    {mOf qOf : ι → ℕ}
+    (hcard : I.card = k)
+    (hGN0 : GN d x u ≠ 0)
+    (hdata : PetalNoLiftCarrierLabelMapData I d x u mOf qOf) :
+    2 ^ k ≤ DkMath.ABC.supportMass (GN d x u) := by
+  simpa [← hcard] using
+    petalNoLiftCarrierLabelMapData_two_pow_card_le_supportMass_GN I hGN0 hdata
+
+/--
+No-lift carrier-label map data gives the same named-cardinality radical lower
+bound.
+-/
+theorem petalNoLiftCarrierLabelMapData_two_pow_le_rad_GN_of_card_eq
+    {ι : Type _}
+    (I : Finset ι)
+    {d x u k : ℕ}
+    {mOf qOf : ι → ℕ}
+    (hcard : I.card = k)
+    (hGN0 : GN d x u ≠ 0)
+    (hdata : PetalNoLiftCarrierLabelMapData I d x u mOf qOf) :
+    2 ^ k ≤ DkMath.ABC.rad (GN d x u) := by
+  simpa [← hcard] using
+    petalNoLiftCarrierLabelMapData_two_pow_card_le_rad_GN I hGN0 hdata
+
 /--
 Direct PrimitiveBeam-to-ABC support-mass count lower bound in body coordinates.
 
@@ -367,6 +437,35 @@ theorem petal_two_pow_card_le_rad_GN_of_bodyPrimitivePrimeFactor_family
     (petalCarrierLabelMapData_of_bodyPrimitivePrimeFactor_family
       I d x u mOf qOf hd hd1 hm hminj hlabel hprim)
 
+/--
+Named-cardinality PrimitiveBeam-to-ABC radical count lower bound in body
+coordinates.
+
+Use this form when a concrete family construction has already proved
+`I.card = k`.
+-/
+theorem petal_two_pow_le_rad_GN_of_bodyPrimitivePrimeFactor_family_card_eq
+    {ι : Type _}
+    (I : Finset ι)
+    (d x u : ℕ)
+    (mOf qOf : ι → ℕ)
+    {k : ℕ}
+    (hcard : I.card = k)
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
+    2 ^ k ≤ DkMath.ABC.rad (GN d x u) := by
+  simpa [← hcard] using
+    petal_two_pow_card_le_rad_GN_of_bodyPrimitivePrimeFactor_family
+      I d x u mOf qOf hGN0 hd hd1 hm hminj hlabel hprim
+
 /--
 Direct Zsigmondy-to-ABC support-mass count lower bound on the GN surface
 `GN d (a - b) b`.
@@ -423,5 +522,30 @@ theorem petal_two_pow_card_le_rad_GN_of_zsigmondyPrimitivePrimeDivisor_family
     (petalCarrierLabelMapData_of_zsigmondyPrimitivePrimeDivisor_family
       I a b d mOf qOf hd hd1 hab_lt hm hminj hlabel hprim)
 
+/--
+Named-cardinality Zsigmondy-to-ABC radical count lower bound on the GN surface
+`GN d (a - b) b`.
+-/
+theorem petal_two_pow_le_rad_GN_of_zsigmondyPrimitivePrimeDivisor_family_card_eq
+    {ι : Type _}
+    (I : Finset ι)
+    (a b d : ℕ)
+    (mOf qOf : ι → ℕ)
+    {k : ℕ}
+    (hcard : I.card = k)
+    (hGN0 : GN d (a - b) b ≠ 0)
+    (hd : 0 < d) (hd1 : 1 < d) (hab_lt : b < a)
+    (hm : ∀ i, i ∈ I → 1 ≤ mOf i)
+    (hminj : Set.InjOn mOf ↑I)
+    (hlabel :
+      ∀ i, i ∈ I → ∀ j, j ∈ I → qOf i = qOf j → mOf i = mOf j)
+    (hprim :
+      ∀ i, i ∈ I →
+        DkMath.Zsigmondy.PrimitivePrimeDivisor a b d (qOf i)) :
+    2 ^ k ≤ DkMath.ABC.rad (GN d (a - b) b) := by
+  simpa [← hcard] using
+    petal_two_pow_card_le_rad_GN_of_zsigmondyPrimitivePrimeDivisor_family
+      I a b d mOf qOf hGN0 hd hd1 hab_lt hm hminj hlabel hprim
+
 end Petal
 end DkMath
diff --git a/lean/dk_math/DkMath/Petal/docs/Petal-Overview.md b/lean/dk_math/DkMath/Petal/docs/Petal-Overview.md
index a1be0647..174df401 100644
--- a/lean/dk_math/DkMath/Petal/docs/Petal-Overview.md
+++ b/lean/dk_math/DkMath/Petal/docs/Petal-Overview.md
@@ -945,12 +945,22 @@ petalCarrierLabelMapData_two_pow_card_le_supportMass_GN
 petalNoLiftCarrierLabelMapData_two_pow_card_le_supportMass_GN
 petalCarrierLabelMapData_two_pow_card_le_rad_GN
 petalNoLiftCarrierLabelMapData_two_pow_card_le_rad_GN
+petalCarrierLabelMapData_two_pow_le_supportMass_GN_of_card_eq
+petalCarrierLabelMapData_two_pow_le_rad_GN_of_card_eq
+petalNoLiftCarrierLabelMapData_two_pow_le_supportMass_GN_of_card_eq
+petalNoLiftCarrierLabelMapData_two_pow_le_rad_GN_of_card_eq
 petal_two_pow_card_le_supportMass_GN_of_bodyPrimitivePrimeFactor_family
 petal_two_pow_card_le_rad_GN_of_bodyPrimitivePrimeFactor_family
 petal_two_pow_card_le_supportMass_GN_of_zsigmondyPrimitivePrimeDivisor_family
 petal_two_pow_card_le_rad_GN_of_zsigmondyPrimitivePrimeDivisor_family
+petal_two_pow_le_rad_GN_of_bodyPrimitivePrimeFactor_family_card_eq
+petal_two_pow_le_rad_GN_of_zsigmondyPrimitivePrimeDivisor_family_card_eq
 ```
 
+The `_of_card_eq` forms are convenience endpoints for concrete finite family
+constructions.  Once a caller proves `I.card = k`, the lower bound can be read
+directly as `2^k <= supportMass/rad`.
+
 NoLift is deliberately not consumed by this bridge.  The ABC support/rad side
 only needs finite prime support; NoLift remains available for valuation
 obstruction routes.
diff --git a/lean/dk_math/docs/dev/das-p2l-260607/review/summary-petal-064.md b/lean/dk_math/docs/dev/das-p2l-260607/review/summary-petal-064.md
index 31dcce0d..65b51b23 100644
--- a/lean/dk_math/docs/dev/das-p2l-260607/review/summary-petal-064.md
+++ b/lean/dk_math/docs/dev/das-p2l-260607/review/summary-petal-064.md
@@ -391,10 +391,16 @@ petalCarrierLabelMapData_two_pow_card_le_supportMass_GN
 petalNoLiftCarrierLabelMapData_two_pow_card_le_supportMass_GN
 petalCarrierLabelMapData_two_pow_card_le_rad_GN
 petalNoLiftCarrierLabelMapData_two_pow_card_le_rad_GN
+petalCarrierLabelMapData_two_pow_le_supportMass_GN_of_card_eq
+petalCarrierLabelMapData_two_pow_le_rad_GN_of_card_eq
+petalNoLiftCarrierLabelMapData_two_pow_le_supportMass_GN_of_card_eq
+petalNoLiftCarrierLabelMapData_two_pow_le_rad_GN_of_card_eq
 petal_two_pow_card_le_supportMass_GN_of_bodyPrimitivePrimeFactor_family
 petal_two_pow_card_le_rad_GN_of_bodyPrimitivePrimeFactor_family
 petal_two_pow_card_le_supportMass_GN_of_zsigmondyPrimitivePrimeDivisor_family
 petal_two_pow_card_le_rad_GN_of_zsigmondyPrimitivePrimeDivisor_family
+petal_two_pow_le_rad_GN_of_bodyPrimitivePrimeFactor_family_card_eq
+petal_two_pow_le_rad_GN_of_zsigmondyPrimitivePrimeDivisor_family_card_eq
 ```
 
 The bridge reads Petal carrier-label data as ABC finite support:
@@ -440,3 +446,15 @@ Zsigmondy primitive-divisor family
 These are thin wrapper theorems.  They do not add arithmetic strength beyond
 the constructor route; they make the ABC negotiation callable directly from the
 two main primitive-prime provider families.
+
+The fourth checkpoint adds named-cardinality endpoints:
+
+```text
+I.card = k
+  -> 2^k <= supportMass(GN)
+  -> 2^k <= rad(GN)
+```
+
+This is the first small step toward concrete family constructions.  The
+construction-specific proof of `I.card = k` remains outside `ABCBridge`; this
+file now has the API needed to consume it immediately.
````
`````
