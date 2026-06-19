# Git diff / Report / Review

## Upd: Petal.ErdosBridge

gch: 1682f5dea9b62581587dfa151cc099392966428c

## Report

実装しました。交差点の標識として、`NoLift` 軸と `PetalCarrierLabelNoncollisionOn` 軸を合流させる公開 theorem を追加しています。

追加した中心 theorem は [ErdosBridge.lean](/lean/dk_math/DkMath/Petal/ErdosBridge.lean:526) のこれです。

```lean
petalNoLiftPrimeChannelFamily_logSubProbability_GN_of_labelNoncollision
```

意味は次の形です。

```text
PetalNoLiftPrimeChannel family
  + PetalCarrierLabelNoncollisionOn labels
  -> finite GN log-capacity sub-probability
```

あわせて、module doc と docs に交差点の行き先標識を追加しました。

- Erdős: address/carrier noncollision -> finite GN log-capacity family
- FLT: NoLift one-slot -> d-th-power valuation obstruction
- ABC: distinct one-slot channels -> support/rad lower-bound bridge

更新した docs は以下です。

- [Petal-Overview.md](/lean/dk_math/DkMath/Petal/docs/Petal-Overview.md:681)
- [Petal-ErdosBridge-ExperimentPlan.md](/lean/dk_math/DkMath/Petal/docs/Petal-ErdosBridge-ExperimentPlan.md:171)
- [FLGNB-PetalRoadmap.md](/lean/dk_math/DkMath/NumberTheory/docs/BinomialPrimeWeighted/FLGNB-PetalRoadmap.md:1757)

検証は通っています。

- `lake build DkMath.Petal.ErdosBridge` 成功
- `lake build DkMath.Petal` 成功
- `git diff --check` 成功

既存の `DkMath.NumberTheory.ZsigmondyCyclotomicResearch` の `sorry` warning は引き続き出ますが、今回追加分由来ではありません。次はいよいよ `Petal address / carrier noncollision -> PetalCarrierLabelNoncollisionOn` の実験に入れます。

## Review

うむ。これは **交差点の標識として非常に良い差分** じゃ。
今回の `petalNoLiftPrimeChannelFamily_logSubProbability_GN_of_labelNoncollision` によって、これまで別々だった **NoLift 軸** と **carrier-label noncollision 軸** が、公開 theorem として合流した。報告でも、Erdős / FLT / ABC の三方向へ向かう標識として整理されている。

## 1. レビュー結論

**Approve。公開 API として自然。**

今回の theorem は、ちょうど欲しかった交差点 theorem じゃ。

```lean
petalNoLiftPrimeChannelFamily_logSubProbability_GN_of_labelNoncollision
```

意味はこれ。

```text
PetalNoLiftPrimeChannel family
  + PetalCarrierLabelNoncollisionOn labels
  -> finite GN log-capacity sub-probability
```

これは強すぎない。
まだ、

```text
Petal address -> label noncollision
Zsigmondy -> NoLift
full Erdős #1196
FLT
ABC
```

を主張していない。
しかし、それらへ向かうための **共通通過点** は theorem として固定した。

## 2. 今回の本質

今までは二つの軸が別々だった。

```text
NoLift:
  q は GN 上で exact one-slot
```

```text
Label noncollision:
  selected indices が同じ prime label を再利用しない
```

今回、この二つが合わさった。

```text
NoLift family
  + carrier-label noncollision
  -> distinct selected channels, each with one local GN slot
  -> finite log-capacity control
```

これは非常に大きい。
Erdős 側だけでなく、FLT / ABC にもそのまま渡せる形になっている。

## 3. 目的地別の意味

### Erdős #1196 方面

有限 R/log route では、

```text
selected prime channels
  -> log cost sum <= parent log capacity
```

が必要じゃ。

今回の theorem は、Petal 側から

```text
distinct no-lift GN carriers
```

を与えると、それがそのまま

```text
finite GN log-capacity sub-probability
```

になることを示した。

つまり Erdős 側の現目的地はこうなる。

```text
Petal address / carrier noncollision
  -> PetalCarrierLabelNoncollisionOn
  -> finite GN log-capacity family
```

まだ analytic tail estimate ではない。
だが、DkMath 独自の有限 carrier route はかなり鮮明になった。

### FLT 方面

FLT では、最終的に

```text
d-th power 側の valuation lower bound
```

と

```text
NoLift による exact one-slot
```

を衝突させたい。

今回の theorem 自体は log-capacity theorem だが、その前提にある

```text
PetalNoLiftPrimeChannel family
```

はすでに

```text
padicValNat q GN = 1
```

を持つ。

つまり FLT 側の次の専用定理はこれじゃ。

```text
NoLift one-slot
  + body diff / GN valuation transfer
  + d-th power assumption
  -> contradiction
```

特に (d=3) では、`1` と `≥ 3` をぶつける形が見える。

### ABC 方面

ABC では、rad / supportMass / local load が主役になる。

今回の交差点 theorem は、ABC に対してこう読める。

```text
distinct one-slot prime channels
  -> support/rad lower-bound material
```

NoLift が local load を `1` にし、label noncollision が別 prime label を保証する。
ならば rad 側では、

```text
selected distinct q labels
  -> supportMass / rad が下から増える
```

という bridge が狙える。

## 4. 現在の未解決点

ここは目的地を忘れないために、明確に分けておくべきじゃ。

まだ通っていないもの:

```text
Petal address / carrier noncollision -> PetalCarrierLabelNoncollisionOn
Zsigmondy alone -> NoLift
GN carrier -> squarefree
NoLift family alone -> label noncollision
full Erdős #1196 analytic tail estimate
FLT descent / contradiction theorem
ABC rad/supportMass theorem
```

今回の theorem は、それらを解いたわけではない。
だが、それらが通るための **合流口** を作った。

## 5. 次のステップ推論

次は三段構えがよい。

### Step 1. Petal address から label noncollision

本命はこれ。

```lean
theorem petalAddressNoncollision_labelNoncollision
    ...
    (haddr : PetalAddressNoncollisionOn I addrOf)
    (hcompat : CarrierLabelCompatibleOn I addrOf qOf) :
    PetalCarrierLabelNoncollisionOn I qOf
```

いきなり address だけで label distinct を出すのは危ない。
おそらく中間に

```text
address と q label の対応性
```

が要る。

なので、最初はこの 2 層でよい。

```text
PetalAddressNoncollisionOn
LabelCompatibleOn
  -> PetalCarrierLabelNoncollisionOn
```

### Step 2. FLT 専用 obstruction theorem

次に、FLT 側へ切り出す。

候補名:

```lean
theorem petalNoLift_valuation_obstruction_of_dthPower
```

意味:

```text
q is on GN
padicValNat q GN = 1
body diff valuation transfers to GN
body diff is d-th power
1 < d
  -> contradiction
```

これは Erdős とは別方向じゃが、同じ NoLift one-slot を食う。

### Step 3. ABC support/rad bridge

ABC 側はこう。

```lean
theorem labelNoncollidingNoLiftChannels_supportMass_lowerBound
```

意味:

```text
PetalNoLiftPrimeChannel family
PetalCarrierLabelNoncollisionOn
  -> selected distinct labels contribute to rad/supportMass
```

これは ABC の `rad` / `supportMass` lower bound に接続する。

## 6. 実装順のおすすめ

わっちならこう進める。

```text
1. Petal address/noncollision の最小 predicate を作る
2. address noncollision + label compatibility -> PetalCarrierLabelNoncollisionOn
3. その theorem を今回の crossroads theorem に接続する
4. FLT 用 one-slot obstruction theorem を別 bridge に切る
5. ABC 用 support/rad lower-bound bridge を切る
6. docs に「三方向の目的地」を固定する
```

特に 1 と 2 は、Erdős / FLT / ABC の全部に効く。
だからここを焦点にすべきじゃ。

## 7. 総括

今回で交差点はこうなった。

```text
Petal / GN:
  carrier の居場所を与える

NoLift:
  carrier が GN 上で exact one-slot であることを与える

PetalCarrierLabelNoncollisionOn:
  selected carriers が同じ prime label を再利用しないことを与える

Erdős:
  finite GN log-capacity sub-probability へ進む

FLT:
  one-slot と d-th power valuation obstruction へ進む

ABC:
  distinct one-slot channels から rad/support lower bound へ進む
```

これは良い標識じゃ。
目的地は三つあるが、次の一歩は一つ。

```text
Petal address / carrier noncollision
  -> PetalCarrierLabelNoncollisionOn
```

ここを通せば、Erdős #1196、FLT、ABC の三方向すべてに橋が伸びる。
まさに DkMath の交差点じゃよ。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/NumberTheory/docs/BinomialPrimeWeighted/FLGNB-PetalRoadmap.md b/lean/dk_math/DkMath/NumberTheory/docs/BinomialPrimeWeighted/FLGNB-PetalRoadmap.md
index 964e34a4..92336b76 100644
--- a/lean/dk_math/DkMath/NumberTheory/docs/BinomialPrimeWeighted/FLGNB-PetalRoadmap.md
+++ b/lean/dk_math/DkMath/NumberTheory/docs/BinomialPrimeWeighted/FLGNB-PetalRoadmap.md
@@ -1757,6 +1757,10 @@ PetalPrimeChannel family on one GN surface

 PetalNoLiftPrimeChannel
   -> padicValNat q (GN d x u) = 1
+
+PetalNoLiftPrimeChannel family
+  + PetalCarrierLabelNoncollisionOn labels
+  -> finite GN log-capacity sub-probability
 ```

 The current research question after the first bridge is:
diff --git a/lean/dk_math/DkMath/Petal/ErdosBridge.lean b/lean/dk_math/DkMath/Petal/ErdosBridge.lean
index 84a81000..1007ff58 100644
--- a/lean/dk_math/DkMath/Petal/ErdosBridge.lean
+++ b/lean/dk_math/DkMath/Petal/ErdosBridge.lean
@@ -27,7 +27,7 @@ PetalPrimeChannel family
   -> multiplicity-budgeted log sub-probability

 PetalPrimeChannel family on one GN surface
-  + pairwise distinct prime labels
+  + PetalCarrierLabelNoncollisionOn prime labels
   -> GN multiplicity budget
   -> log sub-probability against that GN surface

@@ -37,17 +37,26 @@ PetalNoLiftPrimeChannel

 Two conditions remain separate by design:

-* `NatPairwiseDistinctOn I qOf` is the family noncollision condition that
-  prevents selected channels from reusing the same exponent slot.
+* `PetalCarrierLabelNoncollisionOn I qOf` is the family noncollision condition
+  that prevents selected channels from reusing the same exponent slot.
 * `PetalNoLiftPrimeChannel` is a local one-slot condition for one selected
   prime label.  A family of no-lift channels does not by itself imply that the
   labels are distinct.

+The current crossroad is:
+
+```text
+NoLift family
+  + carrier-label noncollision
+  -> distinct selected channels, each with one local GN slot
+  -> finite log-capacity control
+```
+
 Current research target:

 ```text
 Petal address / carrier noncollision
-  -> NatPairwiseDistinctOn I qOf
+  -> PetalCarrierLabelNoncollisionOn I qOf
 ```

 The file also keeps explicit guardrails: Zsigmondy alone is not claimed to imply
@@ -508,6 +517,38 @@ theorem petalNoLiftPrimeChannelFamily_padicValNat_GN_eq_one
   intro i hi
   exact petalNoLiftPrimeChannel_padicValNat_GN_eq_one (hcarrier i hi)

+/--
+No-lift Petal channel families with noncolliding labels feed the finite Erdos
+log-capacity bridge on the observed GN surface.
+
+This is the crossroads theorem for the current public API:
+
+* no-lift gives exact one-slot local valuation at each selected label;
+* carrier-label noncollision prevents two selected indices from reusing the
+  same prime label;
+* the existing GN budget bridge then gives log sub-probability.
+
+The theorem still does not claim that Petal address geometry supplies
+noncollision, nor that Zsigmondy alone supplies no-lift.
+-/
+theorem petalNoLiftPrimeChannelFamily_logSubProbability_GN_of_labelNoncollision
+    {ι : Type _}
+    (I : Finset ι)
+    (d x u : ℕ)
+    (qOf : ι → ℕ)
+    (hGN : 1 < GN d x u)
+    (hnoncollision : PetalCarrierLabelNoncollisionOn I qOf)
+    (hcarrier :
+      ∀ i, i ∈ I → PetalNoLiftPrimeChannel d x u (qOf i)) :
+    (DkMath.NumberTheory.PrimitiveSet.realLogRatioWeightProvider I qOf (GN d x u)
+      (petalPrimeChannel_realLogNonnegOn
+        I (fun _ => d) (fun _ => x) (fun _ => u) qOf
+        (fun i hi => (hcarrier i hi).1))
+      hGN).SubProbability :=
+  petalPrimeChannelFamily_logSubProbability_GN_of_labelNoncollision
+    I d x u qOf hGN hnoncollision
+    (fun i hi => (hcarrier i hi).1)
+
 /--
 A single Petal prime channel fits into the Erdos multiplicity budget of its own
 nonzero GN surface.
diff --git a/lean/dk_math/DkMath/Petal/docs/Petal-ErdosBridge-ExperimentPlan.md b/lean/dk_math/DkMath/Petal/docs/Petal-ErdosBridge-ExperimentPlan.md
index 88c657ed..ca6e0abe 100644
--- a/lean/dk_math/DkMath/Petal/docs/Petal-ErdosBridge-ExperimentPlan.md
+++ b/lean/dk_math/DkMath/Petal/docs/Petal-ErdosBridge-ExperimentPlan.md
@@ -171,6 +171,18 @@ PetalNoLiftPrimeChannel
 These are separate facts.  NoLift gives local one-slot valuation for a selected
 prime label; it does not prove family label distinctness.

+The first public crossroads theorem is now:
+
+```text
+PetalNoLiftPrimeChannel family
+  + PetalCarrierLabelNoncollisionOn labels
+  -> petalNoLiftPrimeChannelFamily_logSubProbability_GN_of_labelNoncollision
+```
+
+This theorem is intentionally finite and conditional.  It is a signpost for
+the common route, not a proof that address geometry gives noncollision or that
+Zsigmondy gives no-lift.
+
 ## Strong Claims We May Be Able to Extract

 ### Claim A: Zsigmondy Witness as an Erdos Channel
@@ -524,6 +536,19 @@ petalPrimeChannelFamily_logSubProbability_GN_of_labelNoncollision
 petalPrimeChannelFamily_logSubProbability_GN_of_pairwiseDistinct
 ```

+The downstream signposts from this checkpoint are:
+
+```text
+Erdos:
+  address/carrier noncollision -> finite GN log-capacity family
+
+FLT:
+  NoLift one-slot -> d-th-power valuation obstruction
+
+ABC:
+  distinct one-slot channels -> support/rad lower-bound bridge
+```
+
 ## Final Assessment

 The first public bridge is implemented:
diff --git a/lean/dk_math/DkMath/Petal/docs/Petal-Overview.md b/lean/dk_math/DkMath/Petal/docs/Petal-Overview.md
index 252abbcf..aac2c3d6 100644
--- a/lean/dk_math/DkMath/Petal/docs/Petal-Overview.md
+++ b/lean/dk_math/DkMath/Petal/docs/Petal-Overview.md
@@ -681,6 +681,38 @@ PetalNoLiftPrimeChannel
 This says that a selected channel has exactly one local exponent slot.  It does
 not say that different selected indices have different prime labels.

+The public crossroads theorem combines the two axes when both inputs are
+available:
+
+```text
+PetalNoLiftPrimeChannel family
+  + PetalCarrierLabelNoncollisionOn labels
+  -> petalNoLiftPrimeChannelFamily_logSubProbability_GN_of_labelNoncollision
+```
+
+This is the current finite log-capacity signpost.  It says that distinct
+selected no-lift carriers can be consumed by the Erdos bridge.  It still does
+not claim that address geometry supplies label noncollision, or that Zsigmondy
+alone supplies no-lift.
+
+## Crossroad Signposts
+
+The same selected prime label `q` now has three downstream readings:
+
+```text
+Erdos #1196:
+  finite target: selected Petal channels consume GN log capacity
+  next missing input: address/carrier noncollision -> label noncollision
+
+FLT:
+  target: clash one-slot GN valuation with d-th-power valuation transfer
+  next missing input: dedicated obstruction theorem
+
+ABC:
+  target: distinct one-slot channels become support/rad lower-bound material
+  next missing input: rad/supportMass bridge for label-noncolliding channels
+```
+
 Current research target:

 ```text
````
`````
