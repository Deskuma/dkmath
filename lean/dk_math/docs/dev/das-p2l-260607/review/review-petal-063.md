# Git diff / Report / Review

## Upd: Petal.ErdosBridge

gch: 7a04dfa53f4d87bb208b61a47d4ddab367435fdb

## Report

進めました。今回は `PetalCarrierLabelMapData` を実際に作る constructor theorem を追加しました。

[ErdosBridge.lean](/lean/dk_math/DkMath/Petal/ErdosBridge.lean) に追加したのは以下です。

- `petalCarrierLabelMapData_of_bodyPrimitivePrimeFactor_family`
- `petalNoLiftCarrierLabelMapData_of_bodyPrimitivePrimeFactor_family`
- `petalCarrierLabelMapData_of_zsigmondyPrimitivePrimeDivisor_family`
- `petalNoLiftCarrierLabelMapData_of_zsigmondyPrimitivePrimeDivisor_family`

これで、有限族について

```text
PrimitiveBeam / Zsigmondy witness family
+ valid value
+ mOf injective
+ label recovery
```

があれば、`PetalCarrierLabelMapData` を作れます。NoLift 版ではさらに明示的な

```text
¬ (qOf i)^2 ∣ GN ...
```

を受け取って `PetalNoLiftCarrierLabelMapData` を作ります。

重要な点として、今回も「Zsigmondy だけで NoLift」は主張していません。Primitive/Zsigmondy は carrier location を供給し、NoLift は別仮定として扱っています。

docs も同期しました。

- [Petal-Overview.md](/lean/dk_math/DkMath/Petal/docs/Petal-Overview.md)
- [Petal-ErdosBridge-ExperimentPlan.md](/lean/dk_math/DkMath/Petal/docs/Petal-ErdosBridge-ExperimentPlan.md)
- [FLGNB-PetalRoadmap.md](/lean/dk_math/DkMath/NumberTheory/docs/BinomialPrimeWeighted/FLGNB-PetalRoadmap.md)

検証は通っています。

```text
lake build DkMath.Petal
git diff --check ...
```

## Review

うむ。これは **かなり実戦段階に入った進展** じゃ。
前回までの `PetalCarrierLabelMapData` は「器」だった。今回、その器へ **PrimitiveBeam / Zsigmondy witness family から実際に流し込む constructor** が追加された。

つまり、状況はこう変わった。

```text id="1h9llg"
以前:
  carrier label data があれば log-capacity route に入れる

今回:
  PrimitiveBeam / Zsigmondy witness family から
  carrier label data を作れる
```

これは大きい。

## 1. 今回の核心

追加された constructor はこの 4 本。

```lean id="mj8tcg"
petalCarrierLabelMapData_of_bodyPrimitivePrimeFactor_family
petalNoLiftCarrierLabelMapData_of_bodyPrimitivePrimeFactor_family
petalCarrierLabelMapData_of_zsigmondyPrimitivePrimeDivisor_family
petalNoLiftCarrierLabelMapData_of_zsigmondyPrimitivePrimeDivisor_family
```

これらの意味は、

```text id="2qrlvi"
PrimitiveBeam / Zsigmondy witness family
  + valid value
  + value injectivity
  + label recovery
  -> PetalCarrierLabelMapData
```

NoLift 版ではさらに、

```text id="1cfz0d"
¬ (qOf i)^2 ∣ GN ...
```

を明示仮定として受け取り、

```text id="9qoql6"
PetalNoLiftCarrierLabelMapData
```

を作る。

ここで重要なのは、**Primitive / Zsigmondy は carrier location を供給する**、という役割に固定されたことじゃ。

## 2. 何が実戦的になったか

前回の `PetalCarrierLabelMapData` は、こういう契約だった。

```text id="j2gkfw"
validValue
valueInjective
labelRecovery
carrier
```

だが、`carrier` をどう作るかが未接続だった。

今回、そこに接続が入った。

### Body coordinates 側

```text id="a7i8pu"
PrimitivePrimeFactorOfDiffPow (qOf i) (x + u) u d
  -> PetalPrimeChannel d x u (qOf i)
```

つまり、

```text id="ac7p9c"
(x + u)^d - u^d
```

の primitive factor が、GN 上の Petal carrier になる。

### Zsigmondy 側

```text id="rkflir"
PrimitivePrimeDivisor a b d (qOf i)
  -> PetalPrimeChannel d (a - b) b (qOf i)
```

つまり、

```text id="95al1o"
a^d - b^d
```

の Zsigmondy primitive divisor が、`x = a - b`, `u = b` と読まれて GN carrier になる。

これは良い。
Zsigmondy が Petal/GN の世界に入ってきた。

## 3. まだ残している仮定

今回も、ちゃんと強すぎる主張は避けている。

まだ仮定として残っているものはこれ。

```text id="vrxjnh"
1 <= mOf i
Set.InjOn mOf ↑I
qOf i = qOf j -> mOf i = mOf j
NoLift 版では ¬ (qOf i)^2 ∣ GN ...
```

つまり、

```text id="ghpt3f"
Primitive/Zsigmondy witness
  -> carrier location
```

は出した。

しかし、

```text id="a21fdw"
Primitive/Zsigmondy witness
  -> label recovery
```

や、

```text id="s4wm19"
Zsigmondy alone -> NoLift
```

は主張していない。

この分離は正しい。

## 4. 今回の位置づけ

これまでの段階を並べると、こうじゃ。

```text id="htr5h5"
f = id:
  value-map API の制御実験

f = nthPrime:
  prime-valued injective label map の実験

PetalCarrierLabelMapData:
  実在 carrier assignment を受け取る器

今回:
  PrimitiveBeam / Zsigmondy family から
  その器を構成する constructor
```

つまり、ついに

```text id="thwk6q"
標準素数列の実験
```

から

```text id="76q8n0"
実際の primitive carrier witness
```

へ入った。

これは明確な進展じゃ。

## 5. Erdős finite route への意味

すでにある theorem と合成すれば、

```text id="8x2j5t"
PrimitiveBeam / Zsigmondy witness family
  + valid value
  + value injectivity
  + label recovery
  -> PetalCarrierLabelMapData
  -> finite GN log-capacity sub-probability
```

まで行ける。

つまり、Erdős 側では次が見えている。

```text id="x11gx7"
primitive divisor family
  -> GN carrier family
  -> label noncollision
  -> log-capacity sub-probability
```

これは、DkMath の有限 R/log route と Petal/Zsigmondy route の合流点じゃ。

## 6. FLT 方面での意味

FLT で重要なのは NoLift 版。

```text id="g9vdw5"
Zsigmondy primitive divisor
  + explicit NoLift
  -> PetalNoLiftCarrierLabelMapData
```

これがあると、各 selected q について

```text id="0xuj96"
padicValNat q GN = 1
```

側へ進める。

FLT 側で狙う衝突は、やはりこれ。

```text id="cme79k"
d-th power assumption
  -> valuation >= d

NoLift
  -> valuation = 1
```

したがって、次の FLT bridge はかなり自然に書ける。

```text id="yiadr2"
Zsigmondy primitive divisor family
  + NoLift
  + d-th power valuation transfer
  -> obstruction
```

今回の constructor は、その前段として十分に効く。

## 7. ABC 方面での意味

ABC 側では、NoLift family が重要素材になる。

```text id="tmkhvi"
NoLift carrier family
  -> distinct one-slot prime channels
  -> support/rad lower-bound material
```

今回の constructor は、

```text id="vmdbjf"
Zsigmondy / Primitive witness family
  + NoLift
  -> PetalNoLiftCarrierLabelMapData
```

を作るので、ABC 側の supportMass / rad bridge にも渡しやすくなる。

つまり、Primitive/Zsigmondy witness が、

```text id="kl5x6z"
新しい素因子
```

としてだけでなく、

```text id="5i95ho"
support/rad を押し上げる one-slot channel
```

として読める入口ができた。

## 8. 次に追加するとよい theorem

今回の constructor は良い。
次は、それを既存の log-capacity theorem と合成した **直通 wrapper** を作ると使いやすい。

候補名はこのあたり。

```lean id="m1f67l"
petalPrimeChannelFamily_logSubProbability_GN_of_bodyPrimitivePrimeFactor_family
petalNoLiftPrimeChannelFamily_logSubProbability_GN_of_bodyPrimitivePrimeFactor_family
petalPrimeChannelFamily_logSubProbability_GN_of_zsigmondyPrimitivePrimeDivisor_family
petalNoLiftPrimeChannelFamily_logSubProbability_GN_of_zsigmondyPrimitivePrimeDivisor_family
```

意味はこう。

```text id="4yry1s"
Primitive/Zsigmondy witness family
  + valid/injective/recovery
  + NoLift if needed
  -> finite GN log-capacity sub-probability
```

今でも既存 theorem を組み合わせれば到達できるが、公開 API としては直通名があるとよい。

## 9. さらに次の本命

その次は、残っている仮定を減らす段階じゃ。

特に本命はこれ。

```text id="j03plw"
labelRecovery:
  qOf i = qOf j -> mOf i = mOf j
```

これを、Primitive / Zsigmondy の性質からどこまで出せるか。

候補としては、

```text id="kqhjcm"
mOf i を qOf i そのものにする
```

なら recovery は自明に近い。

または、

```text id="nuj9l4"
mOf i を primitive witness の address / order / lap 情報として定義する
```

なら、same q から same address を復元できるかを調べることになる。

ここが次の研究本命じゃ。

## 10. 総括

今回の進展を一言で言うと、

```text id="p77j4t"
PetalCarrierLabelMapData が、
単なる器から Primitive/Zsigmondy witness family の受け皿になった。
```

現在の道はこう。

```text id="exqfmk"
PrimitiveBeam / Zsigmondy witness family
  -> PetalPrimeChannel family

valid value
  + value injectivity
  + label recovery
  -> carrier-label data

carrier-label data
  -> label noncollision
  -> GN multiplicity budget
  -> finite GN log-capacity

NoLift explicit
  -> one-slot carrier data
  -> FLT / ABC 方面へ
```

これは、Erdős / FLT / ABC の交差点としてかなり良い位置に来ている。

まだ本丸は、

```text id="fycydn"
NoLift をどう供給するか
labelRecovery をどこから出すか
d-th power obstruction にどう接続するか
support/rad bridge にどう渡すか
```

じゃが、今回で **Primitive/Zsigmondy witness が Petal/ErdosBridge の実用入力になった**。

これは確かな進展じゃ。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/NumberTheory/docs/BinomialPrimeWeighted/FLGNB-PetalRoadmap.md b/lean/dk_math/DkMath/NumberTheory/docs/BinomialPrimeWeighted/FLGNB-PetalRoadmap.md
index 432d14a0..c372e0b5 100644
--- a/lean/dk_math/DkMath/NumberTheory/docs/BinomialPrimeWeighted/FLGNB-PetalRoadmap.md
+++ b/lean/dk_math/DkMath/NumberTheory/docs/BinomialPrimeWeighted/FLGNB-PetalRoadmap.md
@@ -1898,6 +1898,18 @@ This is the structure/predicate precursor to `carrierAnchorOf(m)`: it records
 finite-family carrier assignments and their recovery conditions before
 requiring a canonical choice function.
 
+Primitive/Zsigmondy family constructors now feed this carrier-label data layer:
+
+```text
+petalCarrierLabelMapData_of_bodyPrimitivePrimeFactor_family
+petalNoLiftCarrierLabelMapData_of_bodyPrimitivePrimeFactor_family
+petalCarrierLabelMapData_of_zsigmondyPrimitivePrimeDivisor_family
+petalNoLiftCarrierLabelMapData_of_zsigmondyPrimitivePrimeDivisor_family
+```
+
+The no-lift constructors keep local no-lift as an explicit hypothesis.
+Primitive/Zsigmondy witnesses supply carrier location, not automatic no-lift.
+
 ### Step 7: Refactor imports gradually
 
 Status:
diff --git a/lean/dk_math/DkMath/Petal/ErdosBridge.lean b/lean/dk_math/DkMath/Petal/ErdosBridge.lean
index 3f4fe48d..c34ae7ab 100644
--- a/lean/dk_math/DkMath/Petal/ErdosBridge.lean
+++ b/lean/dk_math/DkMath/Petal/ErdosBridge.lean
@@ -672,6 +672,116 @@ theorem zsigmondyPrimitivePrimeDivisor_natPrimeValuedOn
   exact zsigmondyPrimitivePrimeDivisor_petalPrimeChannel
     (hprim i hi) (hd i hi) (hd1 i hi) (hab_lt i hi)
 
+/--
+PrimitiveBeam family constructor for `PetalCarrierLabelMapData` in body
+coordinates.
+
+This is the first practical constructor for the carrier-label data layer:
+primitive witnesses for `(x + u)^d - u^d` supply actual Petal prime channels
+on `GN d x u`; the caller supplies the finite-address validity and label
+recovery conditions.
+-/
+theorem petalCarrierLabelMapData_of_bodyPrimitivePrimeFactor_family
+    {ι : Type _}
+    (I : Finset ι)
+    (d x u : ℕ)
+    (mOf qOf : ι → ℕ)
+    (hd : 0 < d) (hd1 : 1 < d)
+    (hm : ∀ i, i ∈ I → 1 ≤ mOf i)
+    (hminj : Set.InjOn mOf ↑I)
+    (hlabel :
+      ∀ i, i ∈ I → ∀ j, j ∈ I → qOf i = qOf j → mOf i = mOf j)
+    (hprim :
+      ∀ i, i ∈ I →
+        DkMath.NumberTheory.PrimitiveBeam.PrimitivePrimeFactorOfDiffPow
+          (qOf i) (x + u) u d) :
+    PetalCarrierLabelMapData I d x u mOf qOf :=
+  ⟨hm, hminj, hlabel,
+    fun i hi =>
+      anchoredGNCarrier_of_bodyPrimitivePrimeFactor
+        (hprim i hi) hd hd1⟩
+
+/--
+PrimitiveBeam family constructor for no-lift carrier-label data in body
+coordinates.
+
+The primitive witnesses supply the GN carriers; the explicit local no-lift
+hypothesis supplies the one-slot strengthening.
+-/
+theorem petalNoLiftCarrierLabelMapData_of_bodyPrimitivePrimeFactor_family
+    {ι : Type _}
+    (I : Finset ι)
+    (d x u : ℕ)
+    (mOf qOf : ι → ℕ)
+    (hd : 0 < d) (hd1 : 1 < d)
+    (hm : ∀ i, i ∈ I → 1 ≤ mOf i)
+    (hminj : Set.InjOn mOf ↑I)
+    (hlabel :
+      ∀ i, i ∈ I → ∀ j, j ∈ I → qOf i = qOf j → mOf i = mOf j)
+    (hprim :
+      ∀ i, i ∈ I →
+        DkMath.NumberTheory.PrimitiveBeam.PrimitivePrimeFactorOfDiffPow
+          (qOf i) (x + u) u d)
+    (hNoLift : ∀ i, i ∈ I → ¬ (qOf i) ^ 2 ∣ GN d x u) :
+    PetalNoLiftCarrierLabelMapData I d x u mOf qOf :=
+  ⟨hm, hminj, hlabel,
+    fun i hi =>
+      ⟨anchoredGNCarrier_of_bodyPrimitivePrimeFactor
+          (hprim i hi) hd hd1,
+        hNoLift i hi⟩⟩
+
+/--
+Zsigmondy primitive-divisor family constructor for `PetalCarrierLabelMapData`.
+
+This is the non-body-coordinate constructor: primitive divisors of
+`a^d - b^d` supply Petal prime channels on `GN d (a - b) b`.
+-/
+theorem petalCarrierLabelMapData_of_zsigmondyPrimitivePrimeDivisor_family
+    {ι : Type _}
+    (I : Finset ι)
+    (a b d : ℕ)
+    (mOf qOf : ι → ℕ)
+    (hd : 0 < d) (hd1 : 1 < d) (hab_lt : b < a)
+    (hm : ∀ i, i ∈ I → 1 ≤ mOf i)
+    (hminj : Set.InjOn mOf ↑I)
+    (hlabel :
+      ∀ i, i ∈ I → ∀ j, j ∈ I → qOf i = qOf j → mOf i = mOf j)
+    (hprim :
+      ∀ i, i ∈ I →
+        DkMath.Zsigmondy.PrimitivePrimeDivisor a b d (qOf i)) :
+    PetalCarrierLabelMapData I d (a - b) b mOf qOf :=
+  ⟨hm, hminj, hlabel,
+    fun i hi =>
+      zsigmondyPrimitivePrimeDivisor_petalPrimeChannel
+        (hprim i hi) hd hd1 hab_lt⟩
+
+/--
+Zsigmondy primitive-divisor family constructor for no-lift carrier-label data.
+
+Zsigmondy supplies the carrier; local no-lift remains an explicit additional
+hypothesis.
+-/
+theorem petalNoLiftCarrierLabelMapData_of_zsigmondyPrimitivePrimeDivisor_family
+    {ι : Type _}
+    (I : Finset ι)
+    (a b d : ℕ)
+    (mOf qOf : ι → ℕ)
+    (hd : 0 < d) (hd1 : 1 < d) (hab_lt : b < a)
+    (hm : ∀ i, i ∈ I → 1 ≤ mOf i)
+    (hminj : Set.InjOn mOf ↑I)
+    (hlabel :
+      ∀ i, i ∈ I → ∀ j, j ∈ I → qOf i = qOf j → mOf i = mOf j)
+    (hprim :
+      ∀ i, i ∈ I →
+        DkMath.Zsigmondy.PrimitivePrimeDivisor a b d (qOf i))
+    (hNoLift : ∀ i, i ∈ I → ¬ (qOf i) ^ 2 ∣ GN d (a - b) b) :
+    PetalNoLiftCarrierLabelMapData I d (a - b) b mOf qOf :=
+  ⟨hm, hminj, hlabel,
+    fun i hi =>
+      ⟨zsigmondyPrimitivePrimeDivisor_petalPrimeChannel
+          (hprim i hi) hd hd1 hab_lt,
+        hNoLift i hi⟩⟩
+
 /--
 A finite family of Petal prime channels supplies the real/log nonnegativity
 input for the Erdos log-capacity route.
diff --git a/lean/dk_math/DkMath/Petal/docs/Petal-ErdosBridge-ExperimentPlan.md b/lean/dk_math/DkMath/Petal/docs/Petal-ErdosBridge-ExperimentPlan.md
index 63e3f90f..dbcb2f0c 100644
--- a/lean/dk_math/DkMath/Petal/docs/Petal-ErdosBridge-ExperimentPlan.md
+++ b/lean/dk_math/DkMath/Petal/docs/Petal-ErdosBridge-ExperimentPlan.md
@@ -689,5 +689,18 @@ This is the safe precursor to `carrierAnchorOf(m)`.  It lets experiments supply
 finite-family carrier labels, recovery, and GN divisibility/no-lift facts first;
 canonical choice can be added later if uniqueness becomes available.
 
+PrimitiveBeam and Zsigmondy family constructors are now available:
+
+```text
+petalCarrierLabelMapData_of_bodyPrimitivePrimeFactor_family
+petalNoLiftCarrierLabelMapData_of_bodyPrimitivePrimeFactor_family
+petalCarrierLabelMapData_of_zsigmondyPrimitivePrimeDivisor_family
+petalNoLiftCarrierLabelMapData_of_zsigmondyPrimitivePrimeDivisor_family
+```
+
+These constructors are the first practical supply route into
+`PetalCarrierLabelMapData`.  The no-lift versions still require explicit local
+no-lift hypotheses; they do not claim Zsigmondy alone implies no-lift.
+
 That is the point where Petal may start producing genuinely strong conditions
 useful for Zsigmondy, FLT, and ABC.
diff --git a/lean/dk_math/DkMath/Petal/docs/Petal-Overview.md b/lean/dk_math/DkMath/Petal/docs/Petal-Overview.md
index 52abf0be..2f45112b 100644
--- a/lean/dk_math/DkMath/Petal/docs/Petal-Overview.md
+++ b/lean/dk_math/DkMath/Petal/docs/Petal-Overview.md
@@ -843,6 +843,19 @@ This is the predicate/structure version of the future `carrierAnchorOf` route:
 it records valid values, value injectivity, label recovery, and actual GN
 carrier facts without forcing a uniqueness or choice theorem too early.
 
+Primitive/Zsigmondy family constructors now supply this data layer:
+
+```text
+petalCarrierLabelMapData_of_bodyPrimitivePrimeFactor_family
+petalNoLiftCarrierLabelMapData_of_bodyPrimitivePrimeFactor_family
+petalCarrierLabelMapData_of_zsigmondyPrimitivePrimeDivisor_family
+petalNoLiftCarrierLabelMapData_of_zsigmondyPrimitivePrimeDivisor_family
+```
+
+The no-lift constructors deliberately keep local no-lift as an explicit
+hypothesis.  Primitive/Zsigmondy witnesses supply GN carriers, not automatic
+no-lift.
+
 ## What This Does Not Claim Yet
 
 The package does not yet prove a standard primorial theorem using a concrete
````
`````
