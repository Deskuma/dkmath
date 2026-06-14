# Git diff / Report / Review

## Upd: Petal.ErdosBridge

gch: 15aafb627e9ae025f0cd59a4bfce89691b121d58

## Report

実装実験を進めました。`qOf = f (mOf i)` 型の具体 wrapper を [ErdosBridge.lean](/lean/dk_math/DkMath/Petal/ErdosBridge.lean) に追加しています。

追加した主な theorem は以下です。

- `petalCarrierLabelCompatibleOn_outer_of_value_map_injective`
- `petalCarrierLabelNoncollisionOn_outer_of_value_map_injective`
- `petalPrimeChannelFamily_multiplicityBudget_GN_of_outer_value_map_injective`
- `petalPrimeChannelFamily_logSubProbability_GN_of_outer_value_map_injective`
- `petalNoLiftPrimeChannelFamily_logSubProbability_GN_of_outer_value_map_injective`

意味としては、`qOf i = f (mOf i)` と書けて、選択された有限族上で `f (mOf i) = f (mOf j) -> mOf i = mOf j` が言えれば、前回の outer-address route にそのまま接続できる、という形です。これは prime channel の生成定理ではなく、label recovery / noncollision を供給するための実験 API として切っています。

ドキュメントも同期しました。

- [Petal-Overview.md](/lean/dk_math/DkMath/Petal/docs/Petal-Overview.md)
- [Petal-ErdosBridge-ExperimentPlan.md](/lean/dk_math/DkMath/Petal/docs/Petal-ErdosBridge-ExperimentPlan.md)
- [FLGNB-PetalRoadmap.md](/lean/dk_math/DkMath/NumberTheory/docs/BinomialPrimeWeighted/FLGNB-PetalRoadmap.md)

検証は通っています。

```text
lake build DkMath.Petal
git diff --check ...
```

既存の `ZsigmondyCyclotomicResearch.lean` の `sorry` warning は従来のものです。今回追加分は no-sorry で通っています。

## Review

うむ。今回の状況は、かなり整理されてきた。
一言で言えば、 **「住所値 (mOf) と prime label (qOf) の関係を、実験しやすい `qOf = f(mOf)` 形式に落とした」** という進展じゃ。

これは「素数を生成した」というより、 **prime label の衝突を防ぐための形式的な供給口を作った** というのが正確じゃな。

## 1. 今回の核心

前回までの道はこうだった。

```text
mOf injective
  -> outerPetalAddress noncollision

qOf i = qOf j -> mOf i = mOf j
  -> label compatibility

mOf injective
  + label compatibility
  -> PetalCarrierLabelNoncollisionOn

PetalCarrierLabelNoncollisionOn
  + PetalPrimeChannel family
  -> GN log-capacity route
```

今回追加したのは、この中の

```text
qOf i = qOf j -> mOf i = mOf j
```

を、より実用的な形で供給する wrapper じゃ。

つまり、

```text
qOf i = f (mOf i)
```

として label が value map `f` から来るなら、あとは selected family 上で

```text
f (mOf i) = f (mOf j) -> mOf i = mOf j
```

が言えればよい、という形になった。

これは `f` が全域で単射である必要はない。
選んだ有限集合 `I` 上でだけ、値を復元できればよい。ここが良い。

## 2. 何が通ったのか

今回の中心 theorem 群はこうじゃ。

```lean
petalCarrierLabelCompatibleOn_outer_of_value_map_injective
petalCarrierLabelNoncollisionOn_outer_of_value_map_injective
petalPrimeChannelFamily_multiplicityBudget_GN_of_outer_value_map_injective
petalPrimeChannelFamily_logSubProbability_GN_of_outer_value_map_injective
petalNoLiftPrimeChannelFamily_logSubProbability_GN_of_outer_value_map_injective
```

意味はこう。

```text
mOf が selected index 上で injective
qOf i = f (mOf i)
f が selected family 上で mOf を復元できる
PetalPrimeChannel / NoLift family がある

ならば
  label noncollision が出る
  GN multiplicity budget が出る
  finite GN log-capacity sub-probability が出る
```

NoLift 版まで通っているので、

```text
distinct selected no-lift carriers
  -> each has one GN exponent slot
  -> finite log-capacity route
```

が `qOf = f(mOf)` 型でも使えるようになった。

## 3. これは何を意味するか

これは、Petal address 側と prime label 側の接続が、かなり実装可能な形に落ちたということじゃ。

今までは、

```text
qOf i = qOf j -> mOf i = mOf j
```

を直接仮定していた。

今回からは、

```text
qOf i = f (mOf i)
```

という「ラベル生成っぽい形」を置ける。

ただし、ここで大事なのは docs にもある通り、これは **prime-channel construction ではない**。

つまり、

```text
f(m) が素数である
f(m) が GN を割る
f(m) が PetalPrimeChannel である
f(m) が NoLift である
```

までは今回の theorem は主張していない。

今回の theorem が供給するのは、あくまで

```text
label recovery / noncollision
```

じゃ。

## 4. なぜこれが重要か

Erdős finite route に必要なのは、selected labels が重複しないことじゃ。

```text
same q label を複数 index が使う
```

と、同じ exponent slot を二重に数えてしまう危険がある。

そこで必要なのが、

```text
qOf i = qOf j -> i = j
```

あるいはその途中形として、

```text
qOf i = qOf j -> mOf i = mOf j
```

じゃ。

今回の wrapper は、これを

```text
qOf i = f(mOf i)
f(mOf i) = f(mOf j) -> mOf i = mOf j
```

へ変換した。

これは実験で非常に使いやすい。
なぜなら、今後 concrete な `f` をいろいろ試せるからじゃ。

## 5. 次に試すべき `f`

候補はいくつかある。

```text
1. f(m) = m
```

これは素数 label ではないが、API の動作確認には最も安全。

```text
2. f(m) = nthPrime m
```

これが通れば、住所値から標準的な prime label を選ぶ route になる。
ただし `nthPrime` 周りの既存 API と import が重くなる可能性がある。

```text
3. f(m) = primitivePrimeChosenFrom m
```

Zsigmondy / primitive divisor 由来の選択関数。
数学的には本命だが、choice や witness packaging が絡む。

```text
4. f(m) = carrierAnchorOf m
```

Petal/GN carrier construction から anchor prime を読む。
これが一番 DkMath らしいが、carrier uniqueness が必要になる。

まずは 1 または 2 で形式を確認し、3 と 4 は研究 route として攻めるのがよい。

## 6. FLT / ABC / Erdős 交差点での位置

今回の value-map wrapper は三方向に効く。

### Erdős

```text
qOf = f(mOf)
  + selected injectivity / recovery
  + PetalPrimeChannel
  -> finite GN log-capacity sub-probability
```

Erdős finite route では、これで selected channel family を作りやすくなる。

### FLT

NoLift 版があるので、

```text
qOf = f(mOf)
  + NoLift family
  -> log-capacity route
```

に加えて、各 label は

```text
padicValNat q GN = 1
```

を持つ。

これを (d)-th power valuation obstruction に繋げたい。

### ABC

ABC 側では、

```text
distinct no-lift labels
```

が rad/supportMass の下界素材になる。

今回の wrapper は、その distinctness を value-map 形式で供給する道になる。

## 7. まだ残る本命

残っている本命は、やはりこれじゃ。

```text
f(mOf i) が実際に PetalPrimeChannel / NoLift channel を作る
```

今は、

```text
qOf i = f(mOf i)
```

と

```text
PetalPrimeChannel d x u (qOf i)
```

は別仮定。

次の研究段階では、この二つを一体化したい。

たとえば、

```lean
def PetalCarrierLabelMap ...
```

のような構造を作って、

```text
m -> q
q is prime
q divides GN
q is compatible with address
q is injective/recovering on selected family
```

を package する方向が考えられる。

ただし、急いで structure 化しすぎるより、あと 2、3 本 theorem を通してからでもよい。

## 8. 現状評価

わっちの判定はこう。

```text
抽象 bridge:
  ほぼ整備済み

address route:
  outerPetalAddress から noncollision 供給済み

label route:
  qOf = f(mOf) 型の recovery wrapper が通った

prime construction:
  まだ別仮定

次の本命:
  concrete f が PetalPrimeChannel / NoLift を供給するか
```

これはかなり良い進展じゃ。
「住所値から prime label を作る」という曖昧な言葉が、今回で次のように正確化された。

```text
住所値 mOf から label qOf を f(mOf) として表す。
その f が selected family 上で値を復元できるなら、label noncollision が出る。
ただし、その label が prime channel であることは別途証明する。
```

## 9. 次の一手

わっちなら次はこう進める。

```text
1. toy theorem:
   f = id で value-map wrapper の最小例を作る

2. prime enumeration theorem:
   f = nthPrime 形式を試す

3. carrier theorem:
   qOf = carrierAnchorOf(mOf) 型を設計する

4. FLT theorem:
   NoLift one-slot と d-th-power valuation obstruction を接続する

5. ABC theorem:
   distinct no-lift labels から rad/supportMass lower bound へ接続する
```

このうち、すぐ通りそうなのは 1。
研究として価値が高いのは 3。
目的地に近いのは 4 と 5。

総括すると、今回の進展で道はこうなった。

```text
outerPetalAddress
  -> mOf の復元 / noncollision

qOf = f(mOf)
  -> selected recovery
  -> label noncollision

label noncollision
  + PetalPrimeChannel / NoLift
  -> GN log-capacity route

NoLift
  -> FLT / ABC 方面の one-slot 素材
```

これは確かに、交差点から一歩進んだ。
次は `f` の正体を決める段階じゃ。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/NumberTheory/docs/BinomialPrimeWeighted/FLGNB-PetalRoadmap.md b/lean/dk_math/DkMath/NumberTheory/docs/BinomialPrimeWeighted/FLGNB-PetalRoadmap.md
index 7e691db9..1b3513ce 100644
--- a/lean/dk_math/DkMath/NumberTheory/docs/BinomialPrimeWeighted/FLGNB-PetalRoadmap.md
+++ b/lean/dk_math/DkMath/NumberTheory/docs/BinomialPrimeWeighted/FLGNB-PetalRoadmap.md
@@ -1824,6 +1824,32 @@ petalPrimeChannelFamily_logSubProbability_GN_of_outer_value_injOn
 petalNoLiftPrimeChannelFamily_logSubProbability_GN_of_outer_value_injOn
 ```
 
+A concrete value-map supply form is also implemented.  It applies when the
+selected label is presented as:
+
+```text
+qOf i = f (mOf i)
+```
+
+and equal selected `f (mOf)` labels recover equal selected values:
+
+```text
+f (mOf i) = f (mOf j) -> mOf i = mOf j
+```
+
+Implemented theorem names:
+
+```text
+petalCarrierLabelCompatibleOn_outer_of_value_map_injective
+petalCarrierLabelNoncollisionOn_outer_of_value_map_injective
+petalPrimeChannelFamily_multiplicityBudget_GN_of_outer_value_map_injective
+petalPrimeChannelFamily_logSubProbability_GN_of_outer_value_map_injective
+petalNoLiftPrimeChannelFamily_logSubProbability_GN_of_outer_value_map_injective
+```
+
+This is a label-recovery wrapper, not a theorem that a value map automatically
+constructs prime channels.
+
 ### Step 7: Refactor imports gradually
 
 Status:
diff --git a/lean/dk_math/DkMath/Petal/ErdosBridge.lean b/lean/dk_math/DkMath/Petal/ErdosBridge.lean
index beb8ee28..92919635 100644
--- a/lean/dk_math/DkMath/Petal/ErdosBridge.lean
+++ b/lean/dk_math/DkMath/Petal/ErdosBridge.lean
@@ -316,6 +316,66 @@ theorem petalCarrierLabelNoncollisionOn_outer_of_value_injOn
     (petalCarrierLabelCompatibleOn_outer_of_label_eq_imp_value_eq
       I n lap mOf qOf hlabel)
 
+/--
+Outer-address label compatibility from a value-indexed label map.
+
+This is the concrete `qOf = f(mOf)` supply form.  The map `f` does not have to
+be a global injection; it only has to recover the selected one-based values on
+the finite family under consideration.
+-/
+theorem petalCarrierLabelCompatibleOn_outer_of_value_map_injective
+    {ι : Type _}
+    (I : Finset ι)
+    (n lap : Nat)
+    (mOf qOf : ι → Nat)
+    (f : Nat → Nat)
+    (hq :
+      ∀ i, i ∈ I → qOf i = f (mOf i))
+    (hf :
+      ∀ i, i ∈ I → ∀ j, j ∈ I →
+        f (mOf i) = f (mOf j) → mOf i = mOf j) :
+    PetalCarrierLabelCompatibleOn I
+      (fun i => outerPetalAddress n lap (mOf i)) qOf := by
+  apply petalCarrierLabelCompatibleOn_outer_of_label_eq_imp_value_eq
+  intro i hi j hj hij
+  apply hf i hi j hj
+  rw [← hq i hi, ← hq j hj]
+  exact hij
+
+/--
+Outer-address value conditions supply carrier-label noncollision when labels
+come from a value-indexed map.
+
+This packages the common experimental situation:
+
+```text
+mOf i          selected one-based Petal value
+qOf i = f(mOf i)  selected prime/carrier label
+```
+
+The theorem only asks for the local recovery property of `f` on the selected
+family.  It does not claim that `f` constructs prime channels by itself.
+-/
+theorem petalCarrierLabelNoncollisionOn_outer_of_value_map_injective
+    {ι : Type _}
+    (I : Finset ι)
+    (n lap : Nat)
+    (mOf qOf : ι → Nat)
+    (f : Nat → Nat)
+    (hm : ∀ i, i ∈ I → 1 ≤ mOf i)
+    (hminj : Set.InjOn mOf ↑I)
+    (hq :
+      ∀ i, i ∈ I → qOf i = f (mOf i))
+    (hf :
+      ∀ i, i ∈ I → ∀ j, j ∈ I →
+        f (mOf i) = f (mOf j) → mOf i = mOf j) :
+    PetalCarrierLabelNoncollisionOn I qOf :=
+  petalAddressNoncollision_labelNoncollision I
+    (fun i => outerPetalAddress n lap (mOf i)) qOf
+    (petalAddressNoncollisionOn_outer_of_value_injOn I n lap mOf hm hminj)
+    (petalCarrierLabelCompatibleOn_outer_of_value_map_injective
+      I n lap mOf qOf f hq hf)
+
 /--
 PrimitiveBeam witnesses enter the Erdos bridge as Petal prime channels.
 -/
@@ -714,6 +774,74 @@ theorem petalPrimeChannelFamily_logSubProbability_GN_of_outer_value_injOn
       I n lap mOf qOf hm hminj hlabel)
     hcarrier
 
+/--
+Value-map form of the outer-address GN multiplicity-budget route.
+
+This is the practical wrapper for experiments where the selected label is
+presented as `qOf i = f (mOf i)`.
+-/
+theorem petalPrimeChannelFamily_multiplicityBudget_GN_of_outer_value_map_injective
+    {ι : Type _}
+    (I : Finset ι)
+    (d x u : ℕ)
+    (n lap : Nat)
+    (mOf qOf : ι → Nat)
+    (f : Nat → Nat)
+    (hGN0 : GN d x u ≠ 0)
+    (hm : ∀ i, i ∈ I → 1 ≤ mOf i)
+    (hminj : Set.InjOn mOf ↑I)
+    (hq :
+      ∀ i, i ∈ I → qOf i = f (mOf i))
+    (hf :
+      ∀ i, i ∈ I → ∀ j, j ∈ I →
+        f (mOf i) = f (mOf j) → mOf i = mOf j)
+    (hcarrier :
+      ∀ i, i ∈ I → PetalPrimeChannel d x u (qOf i)) :
+    DkMath.NumberTheory.PrimitiveSet.NatBaseMultiplicityBudgetOn
+      I qOf (GN d x u) :=
+  petalPrimeChannelFamily_multiplicityBudget_GN_of_labelNoncollision
+    I d x u qOf hGN0
+    (petalCarrierLabelNoncollisionOn_outer_of_value_map_injective
+      I n lap mOf qOf f hm hminj hq hf)
+    hcarrier
+
+/--
+Value-map form of the outer-address GN log-capacity route.
+
+The finite-family label noncollision is supplied from:
+
+* valid one-based values,
+* injectivity of `mOf` on the selected index set,
+* `qOf i = f (mOf i)`,
+* local recovery of `mOf` from equal `f (mOf)` labels.
+-/
+theorem petalPrimeChannelFamily_logSubProbability_GN_of_outer_value_map_injective
+    {ι : Type _}
+    (I : Finset ι)
+    (d x u : ℕ)
+    (n lap : Nat)
+    (mOf qOf : ι → Nat)
+    (f : Nat → Nat)
+    (hGN : 1 < GN d x u)
+    (hm : ∀ i, i ∈ I → 1 ≤ mOf i)
+    (hminj : Set.InjOn mOf ↑I)
+    (hq :
+      ∀ i, i ∈ I → qOf i = f (mOf i))
+    (hf :
+      ∀ i, i ∈ I → ∀ j, j ∈ I →
+        f (mOf i) = f (mOf j) → mOf i = mOf j)
+    (hcarrier :
+      ∀ i, i ∈ I → PetalPrimeChannel d x u (qOf i)) :
+    (DkMath.NumberTheory.PrimitiveSet.realLogRatioWeightProvider I qOf (GN d x u)
+      (petalPrimeChannel_realLogNonnegOn
+        I (fun _ => d) (fun _ => x) (fun _ => u) qOf hcarrier)
+      hGN).SubProbability :=
+  petalPrimeChannelFamily_logSubProbability_GN_of_labelNoncollision
+    I d x u qOf hGN
+    (petalCarrierLabelNoncollisionOn_outer_of_value_map_injective
+      I n lap mOf qOf f hm hminj hq hf)
+    hcarrier
+
 /--
 Local no-lift makes the observed GN surface nonzero.
 
@@ -890,6 +1018,40 @@ theorem petalNoLiftPrimeChannelFamily_logSubProbability_GN_of_outer_value_injOn
       I n lap mOf qOf hm hminj hlabel)
     hcarrier
 
+/--
+Value-map form of the outer-address no-lift GN log-capacity route.
+
+This is the no-lift counterpart of
+`petalPrimeChannelFamily_logSubProbability_GN_of_outer_value_map_injective`.
+-/
+theorem petalNoLiftPrimeChannelFamily_logSubProbability_GN_of_outer_value_map_injective
+    {ι : Type _}
+    (I : Finset ι)
+    (d x u : ℕ)
+    (n lap : Nat)
+    (mOf qOf : ι → Nat)
+    (f : Nat → Nat)
+    (hGN : 1 < GN d x u)
+    (hm : ∀ i, i ∈ I → 1 ≤ mOf i)
+    (hminj : Set.InjOn mOf ↑I)
+    (hq :
+      ∀ i, i ∈ I → qOf i = f (mOf i))
+    (hf :
+      ∀ i, i ∈ I → ∀ j, j ∈ I →
+        f (mOf i) = f (mOf j) → mOf i = mOf j)
+    (hcarrier :
+      ∀ i, i ∈ I → PetalNoLiftPrimeChannel d x u (qOf i)) :
+    (DkMath.NumberTheory.PrimitiveSet.realLogRatioWeightProvider I qOf (GN d x u)
+      (petalPrimeChannel_realLogNonnegOn
+        I (fun _ => d) (fun _ => x) (fun _ => u) qOf
+        (fun i hi => (hcarrier i hi).1))
+      hGN).SubProbability :=
+  petalNoLiftPrimeChannelFamily_logSubProbability_GN_of_labelNoncollision
+    I d x u qOf hGN
+    (petalCarrierLabelNoncollisionOn_outer_of_value_map_injective
+      I n lap mOf qOf f hm hminj hq hf)
+    hcarrier
+
 /--
 A single Petal prime channel fits into the Erdos multiplicity budget of its own
 nonzero GN surface.
diff --git a/lean/dk_math/DkMath/Petal/docs/Petal-ErdosBridge-ExperimentPlan.md b/lean/dk_math/DkMath/Petal/docs/Petal-ErdosBridge-ExperimentPlan.md
index af8e44dc..0254baec 100644
--- a/lean/dk_math/DkMath/Petal/docs/Petal-ErdosBridge-ExperimentPlan.md
+++ b/lean/dk_math/DkMath/Petal/docs/Petal-ErdosBridge-ExperimentPlan.md
@@ -612,5 +612,32 @@ petalPrimeChannelFamily_logSubProbability_GN_of_outer_value_injOn
 petalNoLiftPrimeChannelFamily_logSubProbability_GN_of_outer_value_injOn
 ```
 
+The next experimental wrapper is also implemented.  It covers the situation
+where labels are described by a value-indexed map:
+
+```text
+qOf i = f (mOf i)
+```
+
+The required condition is not that `f` is globally injective.  It is only that
+equal selected labels recover equal selected values on the finite family:
+
+```text
+f (mOf i) = f (mOf j) -> mOf i = mOf j
+```
+
+Implemented theorem names:
+
+```text
+petalCarrierLabelCompatibleOn_outer_of_value_map_injective
+petalCarrierLabelNoncollisionOn_outer_of_value_map_injective
+petalPrimeChannelFamily_multiplicityBudget_GN_of_outer_value_map_injective
+petalPrimeChannelFamily_logSubProbability_GN_of_outer_value_map_injective
+petalNoLiftPrimeChannelFamily_logSubProbability_GN_of_outer_value_map_injective
+```
+
+This wrapper deliberately keeps prime-channel construction separate.  The map
+form supplies only the noncollision/recovery layer.
+
 That is the point where Petal may start producing genuinely strong conditions
 useful for Zsigmondy, FLT, and ABC.
diff --git a/lean/dk_math/DkMath/Petal/docs/Petal-Overview.md b/lean/dk_math/DkMath/Petal/docs/Petal-Overview.md
index bcd621b2..c9192284 100644
--- a/lean/dk_math/DkMath/Petal/docs/Petal-Overview.md
+++ b/lean/dk_math/DkMath/Petal/docs/Petal-Overview.md
@@ -771,6 +771,28 @@ petalPrimeChannelFamily_logSubProbability_GN_of_outer_value_injOn
 petalNoLiftPrimeChannelFamily_logSubProbability_GN_of_outer_value_injOn
 ```
 
+There is also a concrete value-map supply form.  If the selected labels are
+presented as
+
+```text
+qOf i = f (mOf i)
+```
+
+and equality of `f (mOf i)` recovers equality of the selected values on the
+finite family, then the same outer-address route is available:
+
+```text
+petalCarrierLabelCompatibleOn_outer_of_value_map_injective
+petalCarrierLabelNoncollisionOn_outer_of_value_map_injective
+petalPrimeChannelFamily_multiplicityBudget_GN_of_outer_value_map_injective
+petalPrimeChannelFamily_logSubProbability_GN_of_outer_value_map_injective
+petalNoLiftPrimeChannelFamily_logSubProbability_GN_of_outer_value_map_injective
+```
+
+This does not claim that `f` constructs prime channels.  It only supplies the
+label-recovery/noncollision part once the prime-channel hypotheses are already
+available.
+
 ## What This Does Not Claim Yet
 
 The package does not yet prove a standard primorial theorem using a concrete
````
`````
