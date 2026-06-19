# Git diff / Report / Review

## Upd: Petal.ErdosBridge

gch: 74ba6e6fa276468c4db88bc911ba78318bb32512

## Report

進めました。今回の道順どおり、`address/carrier noncollision -> label noncollision` を直接主張しすぎず、互換条件を明示した形で Lean に固定しています。

追加した主な API は [ErdosBridge.lean](/lean/dk_math/DkMath/Petal/ErdosBridge.lean:112) です。

```lean
PetalAddressNoncollisionOn
PetalCarrierLabelCompatibleOn
petalAddressNoncollision_labelNoncollision
petalAddressNoncollision_label_injOn
```

さらに、そのまま finite GN log-capacity へ渡す wrapper も追加しました。

```lean
petalPrimeChannelFamily_multiplicityBudget_GN_of_addressNoncollision
petalPrimeChannelFamily_logSubProbability_GN_of_addressNoncollision
petalNoLiftPrimeChannelFamily_logSubProbability_GN_of_addressNoncollision
```

これで現在の道はこう固定されました。

```text
PetalAddressNoncollisionOn I addrOf
  + PetalCarrierLabelCompatibleOn I addrOf qOf
  -> PetalCarrierLabelNoncollisionOn I qOf
  -> finite GN log-capacity route
```

docs も同期済みです。

- [Petal-Overview.md](/lean/dk_math/DkMath/Petal/docs/Petal-Overview.md:716)
- [Petal-ErdosBridge-ExperimentPlan.md](/lean/dk_math/DkMath/Petal/docs/Petal-ErdosBridge-ExperimentPlan.md:576)
- [FLGNB-PetalRoadmap.md](/lean/dk_math/DkMath/NumberTheory/docs/BinomialPrimeWeighted/FLGNB-PetalRoadmap.md:1766)

検証:

- `lake build DkMath.Petal.ErdosBridge` 成功
- `lake build DkMath.Petal` 成功
- `git diff --check` 成功
- 古い「address だけで自動的に NatPairwiseDistinctOn」系の表現は検索で残りなし

既存の `ZsigmondyCyclotomicResearch` の `sorry` warning は継続していますが、今回追加分由来ではありません。次は「具体的な Petal geometry が `PetalAddressNoncollisionOn` と `PetalCarrierLabelCompatibleOn` をどう供給するか」を攻める段階です。

## Review

うむ。今回の状況は、かなり健全に進んでおる。
一言で言えば、 **「address 非衝突だけで label 非衝突が出る」と強く言いすぎず、`address-to-label compatibility` を明示したことで、Petal 幾何層へ渡す安全な橋ができた** という段階じゃ。

## 1. 今回の核心

今回追加された軸はこれじゃ。

```text id="l53wkm"
PetalAddressNoncollisionOn I addrOf
  + PetalCarrierLabelCompatibleOn I addrOf qOf
  -> PetalCarrierLabelNoncollisionOn I qOf
```

これはとても良い。

以前の目標は少し強かった。

```text id="88cs0p"
Petal address noncollision
  -> label noncollision
```

だが、よく考えると address が違うだけでは、必ずしも prime label `q` が違うとは限らない。
異なる住所に同じ素数ラベルが載る可能性を、理論上はまだ排除できていないからじゃ。

そこで今回、

```text id="dmx5zb"
address 非衝突
label compatibility
```

を分けた。

これは Lean 的にも研究的にも正しい。
強すぎる主張を避けつつ、次に証明すべき対象を分解できた。

## 2. 新しく固定された道

今回で、Erdős finite log-capacity への address-facing route はこうなった。

```text id="zp0u2b"
PetalAddressNoncollisionOn
  + PetalCarrierLabelCompatibleOn
  + PetalPrimeChannel family
  -> finite GN log-capacity sub-probability
```

さらに NoLift 付きなら、

```text id="4x7tov"
PetalAddressNoncollisionOn
  + PetalCarrierLabelCompatibleOn
  + PetalNoLiftPrimeChannel family
  -> finite GN log-capacity sub-probability
```

つまり、前回作った交差点 theorem に、address 側から入る正式な入口ができた。

これは大きい。
Petal 側の住所理論が完成すれば、そのまま Erdős route に流し込める。

## 3. 何がまだ仮定なのか

ここは重要じゃ。

まだ証明していないのは、

```text id="pq143d"
具体的な Petal geometry -> PetalAddressNoncollisionOn
具体的な Petal geometry -> PetalCarrierLabelCompatibleOn
Zsigmondy alone -> NoLift
address noncollision alone -> label noncollision
full Erdős #1196 analytic tail
FLT / ABC の最終定理
```

今回の theorem は、これらを勝手に主張していない。
むしろ「どこを証明すれば下流が動くか」を明確にした。

この整理は公開 API として非常に良い。

## 4. FLT / ABC / Erdős の交差点としての意味

### Erdős 方面

Erdős 側では、今や次がはっきりした。

```text id="gvdbgd"
具体的 Petal geometry
  -> address noncollision
  -> label compatibility
  -> label noncollision
  -> GN log-capacity sub-probability
```

finite route はかなり通った。
残るのは、Petal geometry がその前提を供給できるかじゃ。

### FLT 方面

FLT では NoLift が本命素材になる。

```text id="re9gyr"
PetalNoLiftPrimeChannel
  -> padicValNat q GN = 1
```

これを、差冪が (d)-乗であることから来る valuation lower bound とぶつけたい。

つまり次の FLT 向け bridge は、

```text id="7pldyd"
NoLift one-slot
  + valuation transfer
  + d-th-power assumption
  -> obstruction
```

じゃ。

### ABC 方面

ABC では、distinct one-slot channels が `rad` / supportMass の下界素材になる。

```text id="ur880i"
label noncollision
  + NoLift one-slot
  -> distinct prime support
  -> rad/supportMass lower-bound material
```

つまり、今回の address-facing route は ABC にも直結する。

## 5. 次の実装ステップ

次は「抽象 bridge」はもう十分なので、具体 Petal geometry 側に入るべきじゃ。

### Step 1. 具体的 `addrOf` を決める

まず、どの address を family に割り当てるかを決める。

候補は既存の Petal address 系。

```text id="q8f58m"
outerPetalAddress
nestedPetalAddress
carrier address
GN surface address
```

最初は最も薄く、

```lean id="cxg3ms"
addrOf : ι → PetalAddress
```

を外から与える theorem のままでよい。
だが、次の段では `addrOf` の具体生成 theorem が欲しい。

### Step 2. address noncollision の供給 theorem

目標はこれ。

```lean id="ylg8cw"
theorem concretePetalAddress_noncollisionOn
    ... :
    PetalAddressNoncollisionOn I addrOf
```

これは、Petal address が本当に「衝突しない住所」として働くかを見る試験になる。

### Step 3. label compatibility の供給 theorem

こちらが本命かもしれぬ。

```lean id="dk3fz3"
theorem concretePetalAddress_labelCompatibleOn
    ... :
    PetalCarrierLabelCompatibleOn I addrOf qOf
```

これは、「住所が違えば prime label も違う」という構造を証明する。
ここが通ると、Petal address はただの位置情報ではなく、prime label の識別子として機能する。

### Step 4. 合成 theorem

そのあと、今回の theorem に流す。

```lean id="so9w2r"
theorem concretePetalFamily_logSubProbability_GN
    ... :
    (...).SubProbability :=
  petalPrimeChannelFamily_logSubProbability_GN_of_addressNoncollision ...
```

ここまで通れば、Petal geometry 由来の finite log-capacity theorem になる。

## 6. 注意すべき設計リスク

`PetalCarrierLabelCompatibleOn` は便利だが、強くしすぎると単なる仮定置き場になる危険がある。

なので、次は docs でこう明記するとよい。

```text id="w5s5u0"
PetalCarrierLabelCompatibleOn is currently an explicit bridge assumption.
The next goal is not to assume it forever, but to derive it from concrete
Petal address construction or carrier construction.
```

つまり compatibility は最終目的ではない。
中間の足場じゃ。

## 7. 総括

現在の交差点はこうなった。

```text id="j03lbe"
Petal geometry
  -> address noncollision
  -> label compatibility
  -> label noncollision

label noncollision
  -> GN multiplicity budget
  -> Erdős finite log-capacity

NoLift
  -> exact one-slot valuation
  -> FLT obstruction / ABC support material
```

今回の進展で、抽象橋はかなり完成した。
次はついに、Petal geometry そのものが試される段階じゃ。

目的地を忘れずに言えば、

```text id="5gc73f"
Erdős:
  finite route から analytic tail へ向かう

FLT:
  one-slot valuation と d-th-power valuation を衝突させる

ABC:
  distinct one-slot channels を rad/support lower bound に変える
```

そして、その三つへ向かう次の一歩は共通している。

```text id="ndrtv2"
具体的 Petal address construction
  -> PetalAddressNoncollisionOn
  -> PetalCarrierLabelCompatibleOn
```

ここが次の登山口じゃ。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/NumberTheory/docs/BinomialPrimeWeighted/FLGNB-PetalRoadmap.md b/lean/dk_math/DkMath/NumberTheory/docs/BinomialPrimeWeighted/FLGNB-PetalRoadmap.md
index 92336b76..923335c2 100644
--- a/lean/dk_math/DkMath/NumberTheory/docs/BinomialPrimeWeighted/FLGNB-PetalRoadmap.md
+++ b/lean/dk_math/DkMath/NumberTheory/docs/BinomialPrimeWeighted/FLGNB-PetalRoadmap.md
@@ -1767,7 +1767,8 @@ The current research question after the first bridge is:
 
 ```text
 Can Petal address / carrier noncollision supply
-`PetalCarrierLabelNoncollisionOn I qOf`?
+`PetalCarrierLabelNoncollisionOn I qOf`
+through explicit address-to-label compatibility?
 ```
 
 `PetalCarrierLabelNoncollisionOn` is currently the public Petal-facing wrapper
@@ -1775,6 +1776,18 @@ around `NatPairwiseDistinctOn`.  It exists so the later address layer can target
 Petal vocabulary first, while the already-proved Erdos bridge consumes the
 underlying duplicate-free condition.
 
+The first address-facing checkpoint is now implemented by:
+
+```text
+PetalAddressNoncollisionOn I addrOf
+  + PetalCarrierLabelCompatibleOn I addrOf qOf
+  -> PetalCarrierLabelNoncollisionOn I qOf
+
+petalAddressNoncollision_labelNoncollision
+petalPrimeChannelFamily_logSubProbability_GN_of_addressNoncollision
+petalNoLiftPrimeChannelFamily_logSubProbability_GN_of_addressNoncollision
+```
+
 ### Step 7: Refactor imports gradually
 
 Status:
diff --git a/lean/dk_math/DkMath/Petal/ErdosBridge.lean b/lean/dk_math/DkMath/Petal/ErdosBridge.lean
index 1007ff58..e162f8fb 100644
--- a/lean/dk_math/DkMath/Petal/ErdosBridge.lean
+++ b/lean/dk_math/DkMath/Petal/ErdosBridge.lean
@@ -4,6 +4,7 @@ Released under MIT license as described in the file LICENSE.
 Authors: D. and Wise Wolf.
 -/
 
+import DkMath.Petal.Address
 import DkMath.Petal.BezoutBridge
 import DkMath.NumberTheory.PrimitiveSet.ValuationBudget
 
@@ -56,6 +57,7 @@ Current research target:
 
 ```text
 Petal address / carrier noncollision
+  + address-to-label compatibility
   -> PetalCarrierLabelNoncollisionOn I qOf
 ```
 
@@ -101,6 +103,33 @@ def PetalCarrierLabelNoncollisionOn
     (qOf : ι → ℕ) : Prop :=
   DkMath.NumberTheory.PrimitiveSet.NatPairwiseDistinctOn I qOf
 
+/--
+Address-level noncollision for a finite Petal carrier family.
+
+This says only that distinct selected indices have distinct Petal addresses.
+It does not by itself say anything about the selected prime labels.
+-/
+def PetalAddressNoncollisionOn
+    {ι : Type _}
+    (I : Finset ι)
+    (addrOf : ι → PetalAddress) : Prop :=
+  ∀ i, i ∈ I → ∀ j, j ∈ I → i ≠ j → addrOf i ≠ addrOf j
+
+/--
+Compatibility between Petal addresses and selected prime labels.
+
+This is the explicit bridge assumption saying that distinct observed addresses
+produce distinct selected labels.  Keeping this separate prevents the public
+API from pretending that address geometry alone already knows how labels are
+chosen.
+-/
+def PetalCarrierLabelCompatibleOn
+    {ι : Type _}
+    (I : Finset ι)
+    (addrOf : ι → PetalAddress)
+    (qOf : ι → ℕ) : Prop :=
+  ∀ i, i ∈ I → ∀ j, j ∈ I → addrOf i ≠ addrOf j → qOf i ≠ qOf j
+
 /-- A Petal prime channel carries a prime label. -/
 theorem petalPrimeChannel_prime
     {d x u q : ℕ}
@@ -156,6 +185,41 @@ theorem petalCarrierLabelNoncollisionOn_injOn
     Set.InjOn qOf ↑I :=
   DkMath.NumberTheory.PrimitiveSet.natPairwiseDistinctOn_injOn I qOf h
 
+/--
+Address noncollision plus address-to-label compatibility gives carrier-label
+noncollision.
+
+This is the first formal address-facing checkpoint.  The hard geometric work is
+still outside this theorem: callers must provide both the address noncollision
+fact and the compatibility explaining how addresses determine labels.
+-/
+theorem petalAddressNoncollision_labelNoncollision
+    {ι : Type _}
+    (I : Finset ι)
+    (addrOf : ι → PetalAddress)
+    (qOf : ι → ℕ)
+    (haddr : PetalAddressNoncollisionOn I addrOf)
+    (hcompat : PetalCarrierLabelCompatibleOn I addrOf qOf) :
+    PetalCarrierLabelNoncollisionOn I qOf := by
+  intro i hi j hj hij
+  exact hcompat i hi j hj (haddr i hi j hj hij)
+
+/--
+Address noncollision plus compatibility gives injectivity of selected labels.
+
+This is the `Set.InjOn` form for older bridge theorems.
+-/
+theorem petalAddressNoncollision_label_injOn
+    {ι : Type _}
+    (I : Finset ι)
+    (addrOf : ι → PetalAddress)
+    (qOf : ι → ℕ)
+    (haddr : PetalAddressNoncollisionOn I addrOf)
+    (hcompat : PetalCarrierLabelCompatibleOn I addrOf qOf) :
+    Set.InjOn qOf ↑I :=
+  petalCarrierLabelNoncollisionOn_injOn I qOf
+    (petalAddressNoncollision_labelNoncollision I addrOf qOf haddr hcompat)
+
 /--
 PrimitiveBeam witnesses enter the Erdos bridge as Petal prime channels.
 -/
@@ -440,6 +504,63 @@ theorem petalPrimeChannelFamily_logSubProbability_GN_of_labelNoncollision
     (petalCarrierLabelNoncollisionOn_pairwiseDistinct I qOf hnoncollision)
     hcarrier
 
+/--
+Address-facing GN multiplicity-budget bridge.
+
+If Petal addresses do not collide and the selected labels are compatible with
+those addresses, the existing carrier-label bridge supplies the GN multiplicity
+budget.
+-/
+theorem petalPrimeChannelFamily_multiplicityBudget_GN_of_addressNoncollision
+    {ι : Type _}
+    (I : Finset ι)
+    (d x u : ℕ)
+    (addrOf : ι → PetalAddress)
+    (qOf : ι → ℕ)
+    (hGN0 : GN d x u ≠ 0)
+    (haddr : PetalAddressNoncollisionOn I addrOf)
+    (hcompat : PetalCarrierLabelCompatibleOn I addrOf qOf)
+    (hcarrier :
+      ∀ i, i ∈ I → PetalPrimeChannel d x u (qOf i)) :
+    DkMath.NumberTheory.PrimitiveSet.NatBaseMultiplicityBudgetOn
+      I qOf (GN d x u) :=
+  petalPrimeChannelFamily_multiplicityBudget_GN_of_labelNoncollision
+    I d x u qOf hGN0
+    (petalAddressNoncollision_labelNoncollision I addrOf qOf haddr hcompat)
+    hcarrier
+
+/--
+Address-facing finite Erdos bridge for Petal prime channels on one GN surface.
+
+This is the public route:
+
+```text
+address noncollision
+  + address-to-label compatibility
+  + PetalPrimeChannel family
+  -> finite GN log-capacity sub-probability
+```
+-/
+theorem petalPrimeChannelFamily_logSubProbability_GN_of_addressNoncollision
+    {ι : Type _}
+    (I : Finset ι)
+    (d x u : ℕ)
+    (addrOf : ι → PetalAddress)
+    (qOf : ι → ℕ)
+    (hGN : 1 < GN d x u)
+    (haddr : PetalAddressNoncollisionOn I addrOf)
+    (hcompat : PetalCarrierLabelCompatibleOn I addrOf qOf)
+    (hcarrier :
+      ∀ i, i ∈ I → PetalPrimeChannel d x u (qOf i)) :
+    (DkMath.NumberTheory.PrimitiveSet.realLogRatioWeightProvider I qOf (GN d x u)
+      (petalPrimeChannel_realLogNonnegOn
+        I (fun _ => d) (fun _ => x) (fun _ => u) qOf hcarrier)
+      hGN).SubProbability :=
+  petalPrimeChannelFamily_logSubProbability_GN_of_labelNoncollision
+    I d x u qOf hGN
+    (petalAddressNoncollision_labelNoncollision I addrOf qOf haddr hcompat)
+    hcarrier
+
 /--
 Local no-lift makes the observed GN surface nonzero.
 
@@ -549,6 +670,42 @@ theorem petalNoLiftPrimeChannelFamily_logSubProbability_GN_of_labelNoncollision
     I d x u qOf hGN hnoncollision
     (fun i hi => (hcarrier i hi).1)
 
+/--
+Address-facing finite Erdos bridge for no-lift Petal channels.
+
+This composes the current address checkpoint with the crossroads theorem:
+
+```text
+address noncollision
+  + address-to-label compatibility
+  + NoLift Petal channel family
+  -> finite GN log-capacity sub-probability
+```
+
+It still keeps the two hard inputs explicit: address noncollision and
+compatibility between addresses and selected labels.
+-/
+theorem petalNoLiftPrimeChannelFamily_logSubProbability_GN_of_addressNoncollision
+    {ι : Type _}
+    (I : Finset ι)
+    (d x u : ℕ)
+    (addrOf : ι → PetalAddress)
+    (qOf : ι → ℕ)
+    (hGN : 1 < GN d x u)
+    (haddr : PetalAddressNoncollisionOn I addrOf)
+    (hcompat : PetalCarrierLabelCompatibleOn I addrOf qOf)
+    (hcarrier :
+      ∀ i, i ∈ I → PetalNoLiftPrimeChannel d x u (qOf i)) :
+    (DkMath.NumberTheory.PrimitiveSet.realLogRatioWeightProvider I qOf (GN d x u)
+      (petalPrimeChannel_realLogNonnegOn
+        I (fun _ => d) (fun _ => x) (fun _ => u) qOf
+        (fun i hi => (hcarrier i hi).1))
+      hGN).SubProbability :=
+  petalNoLiftPrimeChannelFamily_logSubProbability_GN_of_labelNoncollision
+    I d x u qOf hGN
+    (petalAddressNoncollision_labelNoncollision I addrOf qOf haddr hcompat)
+    hcarrier
+
 /--
 A single Petal prime channel fits into the Erdos multiplicity budget of its own
 nonzero GN surface.
diff --git a/lean/dk_math/DkMath/Petal/docs/Petal-ErdosBridge-ExperimentPlan.md b/lean/dk_math/DkMath/Petal/docs/Petal-ErdosBridge-ExperimentPlan.md
index ca6e0abe..4bafbf3b 100644
--- a/lean/dk_math/DkMath/Petal/docs/Petal-ErdosBridge-ExperimentPlan.md
+++ b/lean/dk_math/DkMath/Petal/docs/Petal-ErdosBridge-ExperimentPlan.md
@@ -159,7 +159,8 @@ PetalPrimeChannel family
 
 `PetalCarrierLabelNoncollisionOn I qOf` is currently the Petal-facing name for
 the lower-level `NatPairwiseDistinctOn I qOf` condition.  The intended next
-step is to derive it from Petal address/carrier geometry.
+step is to derive it from Petal address/carrier geometry plus an explicit
+address-to-label compatibility condition.
 
 The currently implemented local no-lift route is:
 
@@ -317,7 +318,7 @@ Petal carriers automatically satisfy the Erdos multiplicity budget.
 Zsigmondy automatically supplies local NoLift.
 Zsigmondy automatically supplies padicValNat <= 1.
 GN carriers are automatically squarefree.
-Petal address noncollision automatically supplies NatPairwiseDistinctOn.
+Petal address noncollision alone supplies NatPairwiseDistinctOn.
 Full analytic Erdős #1196 tail estimate.
 ```
 
@@ -468,6 +469,7 @@ Now that Step 5 is implemented, investigate:
 
 ```text
 Petal address noncollision
+  + PetalCarrierLabelCompatibleOn I addrOf qOf
   -> PetalCarrierLabelNoncollisionOn I qOf
   -> NatPairwiseDistinctOn I qOf
   -> base-prime multiplicity budget
@@ -525,6 +527,7 @@ Implement the address-facing noncollision layer:
 
 ```text
 Petal address / carrier noncollision
+  + address-to-label compatibility
   -> PetalCarrierLabelNoncollisionOn I qOf
   -> NatPairwiseDistinctOn I qOf
 ```
@@ -532,6 +535,9 @@ Petal address / carrier noncollision
 This is now the missing input needed by:
 
 ```lean
+petalAddressNoncollision_labelNoncollision
+petalPrimeChannelFamily_logSubProbability_GN_of_addressNoncollision
+petalNoLiftPrimeChannelFamily_logSubProbability_GN_of_addressNoncollision
 petalPrimeChannelFamily_logSubProbability_GN_of_labelNoncollision
 petalPrimeChannelFamily_logSubProbability_GN_of_pairwiseDistinct
 ```
@@ -540,7 +546,7 @@ The downstream signposts from this checkpoint are:
 
 ```text
 Erdos:
-  address/carrier noncollision -> finite GN log-capacity family
+  address noncollision + label compatibility -> finite GN log-capacity family
 
 FLT:
   NoLift one-slot -> d-th-power valuation obstruction
@@ -567,7 +573,8 @@ also proves the duplicate-free GN-family route through `NatPairwiseDistinctOn`.
 The next research target is:
 
 ```text
-Can Petal address / carrier noncollision supply `NatPairwiseDistinctOn`?
+Can Petal geometry supply concrete address noncollision and
+address-to-label compatibility?
 ```
 
 That is the point where Petal may start producing genuinely strong conditions
diff --git a/lean/dk_math/DkMath/Petal/docs/Petal-Overview.md b/lean/dk_math/DkMath/Petal/docs/Petal-Overview.md
index aac2c3d6..15890ff7 100644
--- a/lean/dk_math/DkMath/Petal/docs/Petal-Overview.md
+++ b/lean/dk_math/DkMath/Petal/docs/Petal-Overview.md
@@ -702,7 +702,7 @@ The same selected prime label `q` now has three downstream readings:
 ```text
 Erdos #1196:
   finite target: selected Petal channels consume GN log capacity
-  next missing input: address/carrier noncollision -> label noncollision
+  current bridge: address noncollision + label compatibility -> log capacity
 
 FLT:
   target: clash one-slot GN valuation with d-th-power valuation transfer
@@ -717,10 +717,24 @@ Current research target:
 
 ```text
 Petal address / carrier noncollision
+  + PetalCarrierLabelCompatibleOn I addrOf qOf
   -> PetalCarrierLabelNoncollisionOn I qOf
   -> NatPairwiseDistinctOn I qOf
 ```
 
+The address-facing theorem implemented for this checkpoint is:
+
+```text
+petalAddressNoncollision_labelNoncollision
+```
+
+and the direct finite log-capacity routes are:
+
+```text
+petalPrimeChannelFamily_logSubProbability_GN_of_addressNoncollision
+petalNoLiftPrimeChannelFamily_logSubProbability_GN_of_addressNoncollision
+```
+
 ## What This Does Not Claim Yet
 
 The package does not yet prove a standard primorial theorem using a concrete
@@ -733,7 +747,7 @@ general d boundary classification
 full Zsigmondy theorem
 FLT descent
 full Erdős #1196 analytic tail estimate
-Petal address noncollision -> NatPairwiseDistinctOn
+Petal address noncollision alone -> NatPairwiseDistinctOn
 complete Eisenstein refactor away from the FLT namespace
 complete split of BoundaryD3 and BoundaryD3Anchor
 concrete prime enumeration / standard primorial theorem
@@ -751,7 +765,7 @@ The next reasonable implementation directions are:
 
 ```text
 1. connect BoundaryD3 / EisensteinBridge to downstream FLT or Zsigmondy inputs
-2. connect Petal address / carrier noncollision to `NatPairwiseDistinctOn`
+2. derive concrete address noncollision and label compatibility from Petal geometry
 3. use Petal address decomposition in nested observations
 4. connect strict prime-base orbits to a concrete prime enumeration
 5. decide whether GNPrimitiveCandidate needs a separate vocabulary layer
````
`````
