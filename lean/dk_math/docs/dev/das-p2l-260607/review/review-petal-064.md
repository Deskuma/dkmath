# Git diff / Report / Review

## Upd: Petal.ErdosBridge

gch: 9e8e5134eec20d185da2a6400ea2f3226040c9d6

## Report

進めました。`ErdosBridge.lean` に direct wrapper を 4 本追加しました。

追加 theorem:

```lean
petalPrimeChannelFamily_logSubProbability_GN_of_bodyPrimitivePrimeFactor_family
petalNoLiftPrimeChannelFamily_logSubProbability_GN_of_bodyPrimitivePrimeFactor_family
petalPrimeChannelFamily_logSubProbability_GN_of_zsigmondyPrimitivePrimeDivisor_family
petalNoLiftPrimeChannelFamily_logSubProbability_GN_of_zsigmondyPrimitivePrimeDivisor_family
```

これで、

```text
PrimitiveBeam / Zsigmondy witness family
  -> PetalCarrierLabelMapData / PetalNoLiftCarrierLabelMapData
  -> finite GN log-capacity route
```

を一発で呼べるようになりました。NoLift 版は今回も明示的に `¬ (qOf i)^2 ∣ GN ...` を要求しています。Zsigmondy が carrier location を供給し、NoLift は別契約、という線は維持しています。

docs も同期しました。

- `lean/dk_math/DkMath/Petal/docs/Petal-Overview.md`
- `lean/dk_math/DkMath/Petal/docs/Petal-ErdosBridge-ExperimentPlan.md`
- `lean/dk_math/DkMath/NumberTheory/docs/BinomialPrimeWeighted/FLGNB-PetalRoadmap.md`

検証:

```text
lake build DkMath.Petal.ErdosBridge
lake build DkMath.Petal
git diff --check ...
```

すべて通っています。既存の `ZsigmondyCyclotomicResearch.lean` の `sorry` warning は引き続き表示されていますが、今回追加分とは別件です。

## Review

うむ。これは **一区切りのチェックポイント到達** じゃ。
前回は「PrimitiveBeam / Zsigmondy witness から `PetalCarrierLabelMapData` を作れる」段階だった。今回、その data layer を経由せずとも、**witness family から finite GN log-capacity provider まで一発で呼べる direct wrapper** が追加された。報告でも、PrimitiveBeam/Zsigmondy witness family から `PetalCarrierLabelMapData` / `PetalNoLiftCarrierLabelMapData` を作り、finite GN log-capacity route へ直通できるようになったと整理されている。

## 1. 今回の核心

追加された 4 本はこれ。

```lean
petalPrimeChannelFamily_logSubProbability_GN_of_bodyPrimitivePrimeFactor_family
petalNoLiftPrimeChannelFamily_logSubProbability_GN_of_bodyPrimitivePrimeFactor_family
petalPrimeChannelFamily_logSubProbability_GN_of_zsigmondyPrimitivePrimeDivisor_family
petalNoLiftPrimeChannelFamily_logSubProbability_GN_of_zsigmondyPrimitivePrimeDivisor_family
```

意味はこう。

```text
PrimitiveBeam / Zsigmondy witness family
  + valid value
  + value injectivity
  + label recovery
  + NoLift if needed
  -> finite GN log-capacity sub-probability
```

つまり、これまでの分解された道、

```text
Primitive/Zsigmondy witness
  -> PetalCarrierLabelMapData
  -> PetalCarrierLabelNoncollisionOn
  -> GN multiplicity budget
  -> log SubProbability
```

を、公開 API として一発で呼べるようにした。

これは実装利用上かなり大きい。
今後の caller は、中間 data theorem を手で組み合わせなくてもよくなる。

## 2. 何が進展したか

今回の進展は **理論の強化** というより、**ルートの閉包化** じゃ。

前回まで：

```text
constructor はある
log-capacity theorem もある
あとは caller が合成する
```

今回：

```text
constructor + log-capacity theorem を合成した direct wrapper がある
```

この差は大きい。
数学的には同じ内容でも、Lean ライブラリとしては「使える定理」になった。

とくに Zsigmondy 側は、

```text
PrimitivePrimeDivisor a b d q
  -> PetalPrimeChannel d (a - b) b q
  -> finite GN log-capacity
```

という読みが直接できるようになった。

## 3. NoLift の扱いが健全

今回も重要な線引きが保たれている。

```text
Zsigmondy supplies carrier location.
NoLift is a separate local contract.
```

つまり、

```text
Zsigmondy primitive divisor
  -> GN carrier
```

は使う。

しかし、

```text
Zsigmondy primitive divisor
  -> ¬ q^2 ∣ GN
```

は主張しない。

NoLift 版 theorem では、明示的に

```lean
∀ i, i ∈ I → ¬ (qOf i)^2 ∣ GN ...
```

を要求している。

これは非常に良い。
以前確認した通り、primitive divisor だけでは local multiplicity が 1 とは限らない。ここを混ぜないのは正しい。

## 4. 現在の到達点

現在の public route はこう整理できる。

### Body coordinate route

```text
PrimitivePrimeFactorOfDiffPow (qOf i) (x + u) u d
  + valid/injective/recovery
  -> finite log-capacity on GN d x u
```

NoLift 付きなら、

```text
PrimitivePrimeFactorOfDiffPow ...
  + explicit NoLift on GN d x u
  + valid/injective/recovery
  -> finite log-capacity on no-lift carrier family
```

### Zsigmondy route

```text
PrimitivePrimeDivisor a b d (qOf i)
  + b < a
  + valid/injective/recovery
  -> finite log-capacity on GN d (a - b) b
```

NoLift 付きなら、

```text
PrimitivePrimeDivisor a b d (qOf i)
  + explicit NoLift on GN d (a - b) b
  + valid/injective/recovery
  -> finite log-capacity on no-lift carrier family
```

これで、Petal/ErdosBridge はかなり「呼び出せる形」になった。

## 5. 交差点としての意味

### Erdős #1196 側

finite route は、かなり太くなった。

```text
Primitive/Zsigmondy witness family
  -> finite GN log-capacity sub-probability
```

ここまで direct theorem になったので、次は analytic tail へ行く前の有限 channel family 実験をしやすい。

### FLT 側

FLT で欲しいのは NoLift 版。

```text
Zsigmondy primitive q
  + NoLift
  -> padic one-slot
```

その先で、

```text
d-th power assumption
  -> valuation >= d
```

とぶつける。

今回の NoLift direct wrapper は、FLT obstruction theorem の入力にかなり近い。

### ABC 側

ABC 側では、

```text
distinct no-lift carrier family
  -> support/rad lower-bound material
```

が欲しい。

今回の direct wrapper は log-capacity 側だが、同じ data contract は support/rad bridge にも渡せる。
つまり、次に ABC 側で `PetalNoLiftCarrierLabelMapData` を食う theorem を作ると自然じゃ。

## 6. 次に残る本命

今回で「ルートの合成」は済んだ。
次に残る本命は、仮定を減らすことじゃ。

特にこの 3 つ。

```text
1. label recovery をどこから出すか
2. NoLift をどこから出すか
3. FLT / ABC 側の最終 bridge にどう渡すか
```

### label recovery

現在はまだ、

```lean
qOf i = qOf j -> mOf i = mOf j
```

を caller が渡す。

次はここを具体構造から出したい。

候補：

```text
mOf = qOf とする
mOf = petal address value とする
mOf = primitive witness の order/address とする
```

最初に安全なのは `mOf = qOf` 系の specialized wrapper じゃ。

### NoLift

NoLift はまだ明示仮定。

次の候補は、

```text
d = 3 特化
3-resonance 除外
gcd / localization / unitization 条件
```

を使って、

```text
Primitive/Zsigmondy + side conditions -> NoLift
```

を試すことじゃ。

ただし一般 d で急がない方がよい。
まず d=3 または既存 Petal bridge の 3 固定から攻めるのが安全。

### FLT obstruction

そろそろこの形の theorem が欲しい。

```text
PetalNoLiftPrimeChannel d x u q
  + valuation transfer to d-th power
  + 1 < d
  -> contradiction
```

これは log-capacity とは別方面だが、同じ NoLift carrier を食う。

## 7. 次の実装候補

わっちなら次はこの順にする。

```text
1. direct wrapper の docs に usage pattern を 1 つ追加
2. mOf = qOf specialized wrapper を作る
3. d=3 NoLift supply theorem の探索
4. PetalNoLiftCarrierLabelMapData -> ABC support/rad lower-bound bridge
5. PetalNoLiftPrimeChannel -> FLT valuation obstruction bridge
```

特に 2 はすぐ通る可能性がある。

たとえば、

```text
mOf := qOf
```

にすると、label recovery は自明になる。

ただし `validValue : 1 <= qOf i` は prime carrier から出せる可能性が高い。
`valueInjective` は結局 label noncollision と同等に近くなるので、そこをどう扱うかは注意じゃ。

## 8. 総括

今回の成果はこうじゃ。

```text
PrimitiveBeam / Zsigmondy witness family
  -> Petal carrier family
  -> direct finite GN log-capacity theorem
```

これで `Petal.ErdosBridge` は、かなり実用的な public API になった。

まだ残る本丸は、

```text
NoLift の供給
label recovery の供給
FLT obstruction への接続
ABC support/rad への接続
```

じゃが、今回で **Primitive/Zsigmondy から finite GN log-capacity へ至る道は直通化された**。

これは交差点の標識ではなく、もう **舗装された分岐路** になってきたのう。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/NumberTheory/docs/BinomialPrimeWeighted/FLGNB-PetalRoadmap.md b/lean/dk_math/DkMath/NumberTheory/docs/BinomialPrimeWeighted/FLGNB-PetalRoadmap.md
index c372e0b5..e6024ff6 100644
--- a/lean/dk_math/DkMath/NumberTheory/docs/BinomialPrimeWeighted/FLGNB-PetalRoadmap.md
+++ b/lean/dk_math/DkMath/NumberTheory/docs/BinomialPrimeWeighted/FLGNB-PetalRoadmap.md
@@ -1910,6 +1910,19 @@ petalNoLiftCarrierLabelMapData_of_zsigmondyPrimitivePrimeDivisor_family
 The no-lift constructors keep local no-lift as an explicit hypothesis.
 Primitive/Zsigmondy witnesses supply carrier location, not automatic no-lift.
 
+Direct log-capacity wrappers now close the constructor-to-provider route:
+
+```text
+petalPrimeChannelFamily_logSubProbability_GN_of_bodyPrimitivePrimeFactor_family
+petalNoLiftPrimeChannelFamily_logSubProbability_GN_of_bodyPrimitivePrimeFactor_family
+petalPrimeChannelFamily_logSubProbability_GN_of_zsigmondyPrimitivePrimeDivisor_family
+petalNoLiftPrimeChannelFamily_logSubProbability_GN_of_zsigmondyPrimitivePrimeDivisor_family
+```
+
+This is the current checkpoint before returning to the main Zsigmondy line:
+PrimitiveBeam/Zsigmondy witness families can be fed directly into the finite GN
+log-capacity route, while no-lift remains a separate local contract.
+
 ### Step 7: Refactor imports gradually
 
 Status:
diff --git a/lean/dk_math/DkMath/Petal/ErdosBridge.lean b/lean/dk_math/DkMath/Petal/ErdosBridge.lean
index c34ae7ab..25ef255a 100644
--- a/lean/dk_math/DkMath/Petal/ErdosBridge.lean
+++ b/lean/dk_math/DkMath/Petal/ErdosBridge.lean
@@ -1517,6 +1517,148 @@ theorem petalNoLiftPrimeChannelFamily_logSubProbability_GN_of_noLiftCarrierLabel
       I d x u n lap mOf qOf hdata)
     hdata.carrier
 
+/--
+Direct PrimitiveBeam-to-log-capacity wrapper in body coordinates.
+
+This composes the PrimitiveBeam family constructor for
+`PetalCarrierLabelMapData` with the packaged finite GN log-capacity route.
+The address/recovery hypotheses remain explicit.
+-/
+theorem petalPrimeChannelFamily_logSubProbability_GN_of_bodyPrimitivePrimeFactor_family
+    {ι : Type _}
+    (I : Finset ι)
+    (d x u : ℕ)
+    (n lap : Nat)
+    (mOf qOf : ι → Nat)
+    (hGN : 1 < GN d x u)
+    (hd : 0 < d) (hd1 : 1 < d)
+    (hm : ∀ i, i ∈ I → 1 ≤ mOf i)
+    (hminj : Set.InjOn mOf ↑I)
+    (hlabel :
+      ∀ i, i ∈ I → ∀ j, j ∈ I → qOf i = qOf j → mOf i = mOf j)
+    (hprim :
+      ∀ i, i ∈ I →
+        DkMath.NumberTheory.PrimitiveBeam.PrimitivePrimeFactorOfDiffPow
+          (qOf i) (x + u) u d) :
+    (DkMath.NumberTheory.PrimitiveSet.realLogRatioWeightProvider I qOf (GN d x u)
+      (petalPrimeChannel_realLogNonnegOn
+        I (fun _ => d) (fun _ => x) (fun _ => u) qOf
+        (petalCarrierLabelMapData_of_bodyPrimitivePrimeFactor_family
+          I d x u mOf qOf hd hd1 hm hminj hlabel hprim).carrier)
+      hGN).SubProbability :=
+  petalPrimeChannelFamily_logSubProbability_GN_of_carrierLabelMapData
+    I d x u n lap mOf qOf hGN
+    (petalCarrierLabelMapData_of_bodyPrimitivePrimeFactor_family
+      I d x u mOf qOf hd hd1 hm hminj hlabel hprim)
+
+/--
+Direct PrimitiveBeam-to-log-capacity wrapper with local no-lift.
+
+PrimitiveBeam witnesses supply the carrier location.  The no-lift condition is
+kept as an explicit hypothesis and then fed through
+`PetalNoLiftCarrierLabelMapData`.
+-/
+theorem petalNoLiftPrimeChannelFamily_logSubProbability_GN_of_bodyPrimitivePrimeFactor_family
+    {ι : Type _}
+    (I : Finset ι)
+    (d x u : ℕ)
+    (n lap : Nat)
+    (mOf qOf : ι → Nat)
+    (hGN : 1 < GN d x u)
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
+    (DkMath.NumberTheory.PrimitiveSet.realLogRatioWeightProvider I qOf (GN d x u)
+      (petalPrimeChannel_realLogNonnegOn
+        I (fun _ => d) (fun _ => x) (fun _ => u) qOf
+        (fun i hi =>
+          ((petalNoLiftCarrierLabelMapData_of_bodyPrimitivePrimeFactor_family
+              I d x u mOf qOf hd hd1 hm hminj hlabel hprim hNoLift).carrier
+            i hi).1))
+      hGN).SubProbability :=
+  petalNoLiftPrimeChannelFamily_logSubProbability_GN_of_noLiftCarrierLabelMapData
+    I d x u n lap mOf qOf hGN
+    (petalNoLiftCarrierLabelMapData_of_bodyPrimitivePrimeFactor_family
+      I d x u mOf qOf hd hd1 hm hminj hlabel hprim hNoLift)
+
+/--
+Direct Zsigmondy-to-log-capacity wrapper on the GN surface
+`GN d (a - b) b`.
+
+Zsigmondy primitive divisors supply Petal prime carriers after the coordinate
+reading `x = a - b`, `u = b`; address/recovery hypotheses are still supplied by
+the caller.
+-/
+theorem petalPrimeChannelFamily_logSubProbability_GN_of_zsigmondyPrimitivePrimeDivisor_family
+    {ι : Type _}
+    (I : Finset ι)
+    (a b d : ℕ)
+    (n lap : Nat)
+    (mOf qOf : ι → Nat)
+    (hGN : 1 < GN d (a - b) b)
+    (hd : 0 < d) (hd1 : 1 < d) (hab_lt : b < a)
+    (hm : ∀ i, i ∈ I → 1 ≤ mOf i)
+    (hminj : Set.InjOn mOf ↑I)
+    (hlabel :
+      ∀ i, i ∈ I → ∀ j, j ∈ I → qOf i = qOf j → mOf i = mOf j)
+    (hprim :
+      ∀ i, i ∈ I →
+        DkMath.Zsigmondy.PrimitivePrimeDivisor a b d (qOf i)) :
+    (DkMath.NumberTheory.PrimitiveSet.realLogRatioWeightProvider I qOf (GN d (a - b) b)
+      (petalPrimeChannel_realLogNonnegOn
+        I (fun _ => d) (fun _ => a - b) (fun _ => b) qOf
+        (petalCarrierLabelMapData_of_zsigmondyPrimitivePrimeDivisor_family
+          I a b d mOf qOf hd hd1 hab_lt hm hminj hlabel hprim).carrier)
+      hGN).SubProbability :=
+  petalPrimeChannelFamily_logSubProbability_GN_of_carrierLabelMapData
+    I d (a - b) b n lap mOf qOf hGN
+    (petalCarrierLabelMapData_of_zsigmondyPrimitivePrimeDivisor_family
+      I a b d mOf qOf hd hd1 hab_lt hm hminj hlabel hprim)
+
+/--
+Direct Zsigmondy-to-log-capacity wrapper with local no-lift.
+
+This is the no-lift Zsigmondy family route into the finite GN log-capacity
+provider.  It intentionally keeps
+`¬ (qOf i)^2 ∣ GN d (a - b) b` as an explicit hypothesis; Zsigmondy supplies the
+carrier location, not automatic one-slot multiplicity.
+-/
+theorem petalNoLiftPrimeChannelFamily_logSubProbability_GN_of_zsigmondyPrimitivePrimeDivisor_family
+    {ι : Type _}
+    (I : Finset ι)
+    (a b d : ℕ)
+    (n lap : Nat)
+    (mOf qOf : ι → Nat)
+    (hGN : 1 < GN d (a - b) b)
+    (hd : 0 < d) (hd1 : 1 < d) (hab_lt : b < a)
+    (hm : ∀ i, i ∈ I → 1 ≤ mOf i)
+    (hminj : Set.InjOn mOf ↑I)
+    (hlabel :
+      ∀ i, i ∈ I → ∀ j, j ∈ I → qOf i = qOf j → mOf i = mOf j)
+    (hprim :
+      ∀ i, i ∈ I →
+        DkMath.Zsigmondy.PrimitivePrimeDivisor a b d (qOf i))
+    (hNoLift : ∀ i, i ∈ I → ¬ (qOf i) ^ 2 ∣ GN d (a - b) b) :
+    (DkMath.NumberTheory.PrimitiveSet.realLogRatioWeightProvider I qOf (GN d (a - b) b)
+      (petalPrimeChannel_realLogNonnegOn
+        I (fun _ => d) (fun _ => a - b) (fun _ => b) qOf
+        (fun i hi =>
+          ((petalNoLiftCarrierLabelMapData_of_zsigmondyPrimitivePrimeDivisor_family
+              I a b d mOf qOf hd hd1 hab_lt hm hminj hlabel hprim hNoLift).carrier
+            i hi).1))
+      hGN).SubProbability :=
+  petalNoLiftPrimeChannelFamily_logSubProbability_GN_of_noLiftCarrierLabelMapData
+    I d (a - b) b n lap mOf qOf hGN
+    (petalNoLiftCarrierLabelMapData_of_zsigmondyPrimitivePrimeDivisor_family
+      I a b d mOf qOf hd hd1 hab_lt hm hminj hlabel hprim hNoLift)
+
 /--
 Value-map form of the outer-address no-lift GN log-capacity route.
 
diff --git a/lean/dk_math/DkMath/Petal/docs/Petal-ErdosBridge-ExperimentPlan.md b/lean/dk_math/DkMath/Petal/docs/Petal-ErdosBridge-ExperimentPlan.md
index dbcb2f0c..0813e896 100644
--- a/lean/dk_math/DkMath/Petal/docs/Petal-ErdosBridge-ExperimentPlan.md
+++ b/lean/dk_math/DkMath/Petal/docs/Petal-ErdosBridge-ExperimentPlan.md
@@ -702,5 +702,19 @@ These constructors are the first practical supply route into
 `PetalCarrierLabelMapData`.  The no-lift versions still require explicit local
 no-lift hypotheses; they do not claim Zsigmondy alone implies no-lift.
 
+The constructor layer now has direct log-capacity wrappers:
+
+```text
+petalPrimeChannelFamily_logSubProbability_GN_of_bodyPrimitivePrimeFactor_family
+petalNoLiftPrimeChannelFamily_logSubProbability_GN_of_bodyPrimitivePrimeFactor_family
+petalPrimeChannelFamily_logSubProbability_GN_of_zsigmondyPrimitivePrimeDivisor_family
+petalNoLiftPrimeChannelFamily_logSubProbability_GN_of_zsigmondyPrimitivePrimeDivisor_family
+```
+
+These are composition theorems: PrimitiveBeam/Zsigmondy family witnesses produce
+carrier-label data, and the existing finite GN route turns that data into a
+log-capacity sub-probability statement.  No-lift remains an explicit local
+condition.
+
 That is the point where Petal may start producing genuinely strong conditions
 useful for Zsigmondy, FLT, and ABC.
diff --git a/lean/dk_math/DkMath/Petal/docs/Petal-Overview.md b/lean/dk_math/DkMath/Petal/docs/Petal-Overview.md
index 2f45112b..cd42c106 100644
--- a/lean/dk_math/DkMath/Petal/docs/Petal-Overview.md
+++ b/lean/dk_math/DkMath/Petal/docs/Petal-Overview.md
@@ -856,6 +856,20 @@ The no-lift constructors deliberately keep local no-lift as an explicit
 hypothesis.  Primitive/Zsigmondy witnesses supply GN carriers, not automatic
 no-lift.
 
+Direct log-capacity wrappers now compose these constructors with the finite GN
+route:
+
+```text
+petalPrimeChannelFamily_logSubProbability_GN_of_bodyPrimitivePrimeFactor_family
+petalNoLiftPrimeChannelFamily_logSubProbability_GN_of_bodyPrimitivePrimeFactor_family
+petalPrimeChannelFamily_logSubProbability_GN_of_zsigmondyPrimitivePrimeDivisor_family
+petalNoLiftPrimeChannelFamily_logSubProbability_GN_of_zsigmondyPrimitivePrimeDivisor_family
+```
+
+These wrappers are the current public route from PrimitiveBeam/Zsigmondy witness
+families to the finite Erdos log-capacity provider.  The no-lift wrappers still
+require explicit local no-lift hypotheses.
+
 ## What This Does Not Claim Yet
 
 The package does not yet prove a standard primorial theorem using a concrete
````
`````
