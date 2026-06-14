# Git diff / Report / Review

## Upd: Petal.ErdosBridge

gch: 544931ef0f1ece8fb85034a78601854fed2596ad

## Report

進めました。今回は本線の通過点として、`NatPairwiseDistinctOn` を直接むき出しにせず、Petal 側の公開語彙 `PetalCarrierLabelNoncollisionOn` を追加して、後続の address/carrier noncollision 層が接続しやすい入口を作りました。

主な変更:

- [ErdosBridge.lean](/lean/dk_math/DkMath/Petal/ErdosBridge.lean:89)
  - `PetalCarrierLabelNoncollisionOn` を追加
  - `petalCarrierLabelNoncollisionOn_pairwiseDistinct`
  - `petalCarrierLabelNoncollisionOn_injOn`
  - `petalPrimeChannelFamily_multiplicityBudget_GN_of_labelNoncollision`
  - `petalPrimeChannelFamily_logSubProbability_GN_of_labelNoncollision`

- [Petal-Overview.md](/lean/dk_math/DkMath/Petal/docs/Petal-Overview.md:647)
  - 使用手順を追加:
    `PetalPrimeChannel` を作る → `PetalCarrierLabelNoncollisionOn` を示す → log sub-probability bridge を適用

- [Petal-ErdosBridge-ExperimentPlan.md](/lean/dk_math/DkMath/Petal/docs/Petal-ErdosBridge-ExperimentPlan.md:151)
  - 現在の研究目標を `PetalCarrierLabelNoncollisionOn` 経由に更新

- [FLGNB-PetalRoadmap.md](/lean/dk_math/DkMath/NumberTheory/docs/BinomialPrimeWeighted/FLGNB-PetalRoadmap.md:1753)
  - 本線 Roadmap 側も同じ語彙へ同期

検証:

- `lake build DkMath.Petal.ErdosBridge` 成功
- `lake build DkMath.Petal` 成功
- `git diff --check` 成功

既存の `DkMath.NumberTheory.ZsigmondyCyclotomicResearch` の `sorry` warning は出ていますが、今回追加分由来ではありません。次の自然な一手は、本当に `Petal address / carrier noncollision -> PetalCarrierLabelNoncollisionOn` を作れるかの実装実験です。

## Review

うむ。ここは本当に **交差点** じゃ。
Petal / GN / Zsigmondy / Erdős log-capacity / FLT / ABC が、同じ `q` をめぐって合流し始めておる。

今回の差分で重要なのは、`NatPairwiseDistinctOn` をそのまま公開面に出すのではなく、Petal 側の語彙として `PetalCarrierLabelNoncollisionOn` を追加したことじゃ。これにより、次の address / carrier geometry 層が「Petal の言葉」で証明目標を持てるようになった。報告でも、この predicate は `NatPairwiseDistinctOn` の Petal-facing wrapper であり、次は address/carrier noncollision からそれを出すのが自然な一手だと整理されておる。

## 1. 現在地

今の公開ルートはこう。

```text
PetalPrimeChannel family
  + PetalCarrierLabelNoncollisionOn I qOf
  -> NatBaseMultiplicityBudgetOn against GN
  -> realLogRatioWeightProvider.SubProbability
```

そして局所側はこう。

```text
PetalNoLiftPrimeChannel
  -> padicValNat q (GN d x u) = 1
```

つまり、すでに二つの軸がある。

```text
非衝突軸:
  selected labels が重複しない
  -> GN 上の multiplicity budget

NoLift 軸:
  selected q が GN 上でちょうど one-slot
  -> local valuation control
```

この二つは別物じゃが、合流すると強い。

```text
NoLift family
  + label noncollision
  -> distinct selected channels each consume exactly one GN exponent slot
  -> finite log-capacity control
```

ここまで来ると、Petal は単なる観測面ではなく、 **有限 log-capacity の channel generator** になっている。

## 2. なぜこれは FLT / ABC / Erdős の交差点なのか

### Erdős #1196 側

Erdős 側で欲しいのは、有限版では

```text
selected prime channels
  -> log cost sum <= parent log capacity
```

じゃ。
今回の Petal route は、親を `GN d x u` に取り、selected carrier labels を `qOf` として、

```text
distinct labels on GN
  -> log-cost sub-probability
```

を与える。

これは Erdős #1196 の解析的尾部評価そのものではない。
しかし、有限 R/log route の中核に対し、Petal 由来の具体的 channel family を供給する橋になった。

### FLT 側

FLT 側では、典型的には

```text
body diff が d-th power なら
selected prime q の valuation は d の倍数側へ押される
```

一方、Petal / NoLift 側では

```text
padicValNat q GN = 1
```

が得られる。

ここで body diff と GN の valuation transfer があるなら、

```text
d-th power 側の valuation >= d
しかし GN 側の valuation = 1
```

という矛盾の型が見える。
特に (d=3) では、これは非常に使いやすい。

### ABC 側

ABC 側では、`rad` / support mass / local load が重要になる。
distinct prime labels が増えるほど、

```text
supportMass / rad が下から持ち上がる
```

という読みができる。

NoLift は local load を正確に 1 にし、label noncollision はそれらが別 prime として rad 側に立つことを保証する。
つまり、ABC 側では

```text
distinct one-slot channels
  -> support/rad lower bound
  -> local-load control
```

の素材になる。

## 3. 今回の改善の意味

`PetalCarrierLabelNoncollisionOn` は、数学的にはまだ `NatPairwiseDistinctOn` の wrapper じゃ。
だが設計上は大きい。

以前の目標:

```text
Petal address / carrier noncollision
  -> NatPairwiseDistinctOn I qOf
```

今の目標:

```text
Petal address / carrier noncollision
  -> PetalCarrierLabelNoncollisionOn I qOf
```

これは小さな名前替えではない。
「下位 PrimitiveSet 語彙」ではなく、「Petal 公開語彙」を目標にできるようになった。
後続の address 層は Petal の中で完結した statement を証明できる。

## 4. 次のステップ

### Step A. docs の公開仕様化

まず、`Petal-ErdosBridge-ExperimentPlan.md` は、そろそろ名前の役割が古くなり始めている。

候補:

```text
Petal-ErdosBridge-PublicAPI.md
Petal-ErdosBridge-Status.md
Petal-ErdosBridge-Guide.md
```

最低限、今の docs には次を明記しておくとよい。

```text
Public theorem to use:
  petalPrimeChannelFamily_logSubProbability_GN_of_labelNoncollision

Caller obligations:
  1. produce PetalPrimeChannel d x u (qOf i)
  2. prove PetalCarrierLabelNoncollisionOn I qOf
  3. prove 1 < GN d x u
```

### Step B. address / carrier noncollision の定義

次の実装本命はこれ。

```lean
def PetalCarrierNoncollisionOn
    {ι : Type _}
    (I : Finset ι)
    (addrOf : ι → PetalAddress)
    (qOf : ι → ℕ) : Prop := ...
```

ただし、最初から address の構造を深く入れすぎない方がよい。
まずは薄い predicate でよい。

```lean
def PetalAddressLabelCompatibleOn
    {ι : Type _}
    (I : Finset ι)
    (addrOf : ι → PetalAddress)
    (qOf : ι → ℕ) : Prop :=
  ∀ i, i ∈ I → ∀ j, j ∈ I →
    i ≠ j → addrOf i ≠ addrOf j → qOf i ≠ qOf j
```

ただ、これは向きが強すぎるかもしれぬ。
本当に欲しいのは、最終的にこれ。

```lean
theorem petalAddressNoncollision_labelNoncollision
    ...
    (hnoncollision : PetalAddressNoncollisionOn I addrOf)
    (hcompat : LabelInjectiveFromAddressOn I addrOf qOf) :
    PetalCarrierLabelNoncollisionOn I qOf
```

つまり address 非衝突だけでなく、address と label の対応関係も必要になる可能性がある。

### Step C. NoLift + label noncollision の合流 theorem

これはすぐ通る可能性が高い。

```lean
theorem petalNoLiftPrimeChannelFamily_logSubProbability_GN_of_labelNoncollision
    {ι : Type _}
    (I : Finset ι)
    (d x u : ℕ)
    (qOf : ι → ℕ)
    (hGN : 1 < GN d x u)
    (hnoncollision : PetalCarrierLabelNoncollisionOn I qOf)
    (hcarrier :
      ∀ i, i ∈ I → PetalNoLiftPrimeChannel d x u (qOf i)) :
    (DkMath.NumberTheory.PrimitiveSet.realLogRatioWeightProvider
      I qOf (GN d x u)
      ...
      hGN).SubProbability
```

中身は `hcarrier i hi` から `PetalPrimeChannel` を取り出して、既存の labelNoncollision theorem に渡すだけじゃ。

意味は明快。

```text
distinct no-lift Petal carriers on GN
  -> each is exact one-slot
  -> family log SubProbability
```

これは FLT / ABC に見せやすい theorem になる。

### Step D. Zsigmondy + NoLift + noncollision family

Zsigmondy 側から入る family theorem も欲しい。

```text
Zsigmondy primitive divisor family
  + NoLift on GN
  + PetalCarrierLabelNoncollisionOn
  -> log SubProbability
```

ただし、ここでは注意が必要。

```text
Zsigmondy alone -> NoLift
```

は主張しない。
NoLift は別仮定として残す。

### Step E. FLT / ABC への専用 bridge

ErdosBridge の公開 API が整ってきたので、次は下流向けに「食べやすい theorem」を作る段階じゃ。

FLT 向け:

```text
Zsigmondy primitive q
  + valuation transfer
  + NoLift
  -> d-th power obstruction
```

ABC 向け:

```text
label-noncollision carrier family
  + NoLift / one-slot
  -> rad/supportMass lower bound
```

Erdős 向け:

```text
Petal carrier family
  + label noncollision
  -> finite log-capacity sub-probability
```

これらは別ファイルに切ってよい。

```text
DkMath.Petal.FLTBridge
DkMath.Petal.ABCBridge
DkMath.Petal.ErdosBridge
```

または、すでに ABC 側に bridge があるなら、Petal 側ではなく ABC 側へ薄く置く。

## 5. 目的地を忘れない整理

ここは交差点なので、目的地ごとに見る。

```text
Erdős #1196:
  目的地は analytic tail estimate。
  今は finite log-capacity route と Petal carrier 接続まで。
  次は address noncollision -> label noncollision。

FLT:
  目的地は infinite descent / d-th power obstruction。
  今は primitive q, GN location, valuation transfer, NoLift one-slot が揃いつつある。
  次は d-th power valuation lower bound とぶつける専用 theorem。

ABC:
  目的地は rad/support/local-load の大域制御。
  今は distinct carrier labels と local one-slot が素材。
  次は supportMass/rad lower bound への接続。
```

## 6. 推奨する次の実装順

わっちならこの順で進める。

```text
1. petalNoLiftPrimeChannelFamily_logSubProbability_GN_of_labelNoncollision
2. address/carrier noncollision predicate の最小定義
3. address noncollision -> PetalCarrierLabelNoncollisionOn の実験
4. Zsigmondy + NoLift + labelNoncollision family theorem
5. FLT 用 one-slot obstruction theorem
6. ABC 用 rad/supportMass lower-bound bridge
7. docs を PublicAPI / Status / Roadmap に分割整理
```

最初の 1 はすぐ通る可能性が高い。
2 と 3 が研究本命。
4 以降は交差点から各目的地へ伸ばす道じゃ。

## 7. 現状総括

今の DkMath はこういう状態じゃ。

```text
Petal / GN:
  q の居場所を与える

NoLift:
  q が GN 上で exact one-slot であることを与える

Label noncollision:
  family が同じ prime label を再利用しないことを与える

Erdős finite route:
  distinct channels の log cost が GN capacity を超えないことを与える

FLT:
  one-slot と d-th power valuation が衝突する場所を狙う

ABC:
  distinct one-slot channels が rad/support を押し上げる場所を狙う
```

これは、まさに交差点じゃ。
しかも、かなり良い交差点になっている。

次にやるべきことは、「もっと強いことを言う」ではなく、

```text
どの目的地へ向かうにも必要な共通条件:
  carrier label noncollision
```

を、Petal address から供給できるかを試すことじゃ。

ここが通れば、Erdős だけでなく、FLT と ABC にも同時に効く。
目的地は三つあるが、次の一歩は一つ。

```text
Petal address / carrier noncollision
  -> PetalCarrierLabelNoncollisionOn
```

これを次の登山道にしよう。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/NumberTheory/docs/BinomialPrimeWeighted/FLGNB-PetalRoadmap.md b/lean/dk_math/DkMath/NumberTheory/docs/BinomialPrimeWeighted/FLGNB-PetalRoadmap.md
index 35770182..964e34a4 100644
--- a/lean/dk_math/DkMath/NumberTheory/docs/BinomialPrimeWeighted/FLGNB-PetalRoadmap.md
+++ b/lean/dk_math/DkMath/NumberTheory/docs/BinomialPrimeWeighted/FLGNB-PetalRoadmap.md
@@ -1733,7 +1733,7 @@ first public bridge has implemented translation and budget-consumption:
 Petal carrier
   -> Erdos prime channel
   -> prime-valued family
-  -> multiplicity budget assumption or pairwise distinct GN-family labels
+  -> multiplicity budget assumption or Petal carrier-label noncollision
   -> log-capacity sub-probability
 ```

@@ -1751,7 +1751,7 @@ Petal carrier family
   -> normalized log-cost sum <= 1

 PetalPrimeChannel family on one GN surface
-  + NatPairwiseDistinctOn labels
+  + PetalCarrierLabelNoncollisionOn labels
   -> NatBaseMultiplicityBudgetOn against GN
   -> realLogRatioWeightProvider.SubProbability

@@ -1762,9 +1762,15 @@ PetalNoLiftPrimeChannel
 The current research question after the first bridge is:

 ```text
-Can Petal address / carrier noncollision supply `NatPairwiseDistinctOn I qOf`?
+Can Petal address / carrier noncollision supply
+`PetalCarrierLabelNoncollisionOn I qOf`?
 ```

+`PetalCarrierLabelNoncollisionOn` is currently the public Petal-facing wrapper
+around `NatPairwiseDistinctOn`.  It exists so the later address layer can target
+Petal vocabulary first, while the already-proved Erdos bridge consumes the
+underlying duplicate-free condition.
+
 ### Step 7: Refactor imports gradually

 Status:
diff --git a/lean/dk_math/DkMath/Petal/ErdosBridge.lean b/lean/dk_math/DkMath/Petal/ErdosBridge.lean
index 4eed2d8e..84a81000 100644
--- a/lean/dk_math/DkMath/Petal/ErdosBridge.lean
+++ b/lean/dk_math/DkMath/Petal/ErdosBridge.lean
@@ -77,6 +77,21 @@ It is deliberately weaker than asking the whole `GN` value to be squarefree.
 def PetalNoLiftPrimeChannel (d x u q : ℕ) : Prop :=
   PetalPrimeChannel d x u q ∧ ¬ q ^ 2 ∣ GN d x u

+/--
+Carrier-label noncollision for a finite Petal channel family.
+
+This is intentionally just the Petal-facing name for
+`NatPairwiseDistinctOn I qOf`: different selected carriers must not reuse the
+same prime label.  It is **not** yet derived from Petal addresses.  The next
+geometry layer should prove this predicate from an address/carrier
+noncollision theorem and then feed the public bridge below.
+-/
+def PetalCarrierLabelNoncollisionOn
+    {ι : Type _}
+    (I : Finset ι)
+    (qOf : ι → ℕ) : Prop :=
+  DkMath.NumberTheory.PrimitiveSet.NatPairwiseDistinctOn I qOf
+
 /-- A Petal prime channel carries a prime label. -/
 theorem petalPrimeChannel_prime
     {d x u q : ℕ}
@@ -105,6 +120,33 @@ theorem petalNoLiftPrimeChannel_noLift
     ¬ q ^ 2 ∣ GN d x u :=
   h.2

+/--
+Unfold carrier-label noncollision to the underlying `PrimitiveSet`
+duplicate-free condition.
+-/
+theorem petalCarrierLabelNoncollisionOn_pairwiseDistinct
+    {ι : Type _}
+    (I : Finset ι)
+    (qOf : ι → ℕ)
+    (h : PetalCarrierLabelNoncollisionOn I qOf) :
+    DkMath.NumberTheory.PrimitiveSet.NatPairwiseDistinctOn I qOf :=
+  h
+
+/--
+Carrier-label noncollision gives injectivity of selected labels on the finite
+index.
+
+This is the form needed by the older injective-family multiplicity-budget
+theorem.
+-/
+theorem petalCarrierLabelNoncollisionOn_injOn
+    {ι : Type _}
+    (I : Finset ι)
+    (qOf : ι → ℕ)
+    (h : PetalCarrierLabelNoncollisionOn I qOf) :
+    Set.InjOn qOf ↑I :=
+  DkMath.NumberTheory.PrimitiveSet.natPairwiseDistinctOn_injOn I qOf h
+
 /--
 PrimitiveBeam witnesses enter the Erdos bridge as Petal prime channels.
 -/
@@ -339,6 +381,56 @@ theorem petalPrimeChannelFamily_logSubProbability_GN_of_pairwiseDistinct
       I qOf hdistinct)
     hcarrier

+/--
+Carrier-label noncollision on one GN surface supplies an Erdos multiplicity
+budget against that GN surface.
+
+This theorem is the Petal-named entry point for the current research target:
+future address/carrier geometry should prove
+`PetalCarrierLabelNoncollisionOn I qOf`, then this bridge handles the
+valuation-budget side.
+-/
+theorem petalPrimeChannelFamily_multiplicityBudget_GN_of_labelNoncollision
+    {ι : Type _}
+    (I : Finset ι)
+    (d x u : ℕ)
+    (qOf : ι → ℕ)
+    (hGN0 : GN d x u ≠ 0)
+    (hnoncollision : PetalCarrierLabelNoncollisionOn I qOf)
+    (hcarrier :
+      ∀ i, i ∈ I → PetalPrimeChannel d x u (qOf i)) :
+    DkMath.NumberTheory.PrimitiveSet.NatBaseMultiplicityBudgetOn
+      I qOf (GN d x u) :=
+  petalPrimeChannelFamily_multiplicityBudget_GN_of_pairwiseDistinct
+    I d x u qOf hGN0
+    (petalCarrierLabelNoncollisionOn_pairwiseDistinct I qOf hnoncollision)
+    hcarrier
+
+/--
+Carrier-label noncollision on one GN surface gives the Erdos log
+sub-probability provider.
+
+This is the recommended public theorem for callers that already know their
+Petal carriers do not collide as prime labels.
+-/
+theorem petalPrimeChannelFamily_logSubProbability_GN_of_labelNoncollision
+    {ι : Type _}
+    (I : Finset ι)
+    (d x u : ℕ)
+    (qOf : ι → ℕ)
+    (hGN : 1 < GN d x u)
+    (hnoncollision : PetalCarrierLabelNoncollisionOn I qOf)
+    (hcarrier :
+      ∀ i, i ∈ I → PetalPrimeChannel d x u (qOf i)) :
+    (DkMath.NumberTheory.PrimitiveSet.realLogRatioWeightProvider I qOf (GN d x u)
+      (petalPrimeChannel_realLogNonnegOn
+        I (fun _ => d) (fun _ => x) (fun _ => u) qOf hcarrier)
+      hGN).SubProbability :=
+  petalPrimeChannelFamily_logSubProbability_GN_of_pairwiseDistinct
+    I d x u qOf hGN
+    (petalCarrierLabelNoncollisionOn_pairwiseDistinct I qOf hnoncollision)
+    hcarrier
+
 /--
 Local no-lift makes the observed GN surface nonzero.

diff --git a/lean/dk_math/DkMath/Petal/docs/Petal-ErdosBridge-ExperimentPlan.md b/lean/dk_math/DkMath/Petal/docs/Petal-ErdosBridge-ExperimentPlan.md
index 9dfc94b0..88c657ed 100644
--- a/lean/dk_math/DkMath/Petal/docs/Petal-ErdosBridge-ExperimentPlan.md
+++ b/lean/dk_math/DkMath/Petal/docs/Petal-ErdosBridge-ExperimentPlan.md
@@ -152,11 +152,15 @@ The currently implemented public route is:

 ```text
 PetalPrimeChannel family
-  + NatPairwiseDistinctOn labels
+  + PetalCarrierLabelNoncollisionOn labels
   -> NatBaseMultiplicityBudgetOn against GN
   -> realLogRatioWeightProvider.SubProbability
 ```

+`PetalCarrierLabelNoncollisionOn I qOf` is currently the Petal-facing name for
+the lower-level `NatPairwiseDistinctOn I qOf` condition.  The intended next
+step is to derive it from Petal address/carrier geometry.
+
 The currently implemented local no-lift route is:

 ```text
@@ -446,12 +450,13 @@ multiplicity budget directly.

 ### Step 6: Research Target - Address Antichain to Multiplicity Budget

-Status: **current research target**
+Status: **current research target, with public label-noncollision hook**

 Now that Step 5 is implemented, investigate:

 ```text
 Petal address noncollision
+  -> PetalCarrierLabelNoncollisionOn I qOf
   -> NatPairwiseDistinctOn I qOf
   -> base-prime multiplicity budget
 ```
@@ -508,12 +513,14 @@ Implement the address-facing noncollision layer:

 ```text
 Petal address / carrier noncollision
+  -> PetalCarrierLabelNoncollisionOn I qOf
   -> NatPairwiseDistinctOn I qOf
 ```

 This is now the missing input needed by:

 ```lean
+petalPrimeChannelFamily_logSubProbability_GN_of_labelNoncollision
 petalPrimeChannelFamily_logSubProbability_GN_of_pairwiseDistinct
 ```

diff --git a/lean/dk_math/DkMath/Petal/docs/Petal-Overview.md b/lean/dk_math/DkMath/Petal/docs/Petal-Overview.md
index 46cfebc6..252abbcf 100644
--- a/lean/dk_math/DkMath/Petal/docs/Petal-Overview.md
+++ b/lean/dk_math/DkMath/Petal/docs/Petal-Overview.md
@@ -648,11 +648,29 @@ The current implemented route is:

 ```text
 PetalPrimeChannel family
-  + NatPairwiseDistinctOn labels
+  + PetalCarrierLabelNoncollisionOn labels
   -> NatBaseMultiplicityBudgetOn against GN
   -> realLogRatioWeightProvider.SubProbability
 ```

+Here `PetalCarrierLabelNoncollisionOn I qOf` is the Petal-facing name for
+`NatPairwiseDistinctOn I qOf`.  It records only that selected carriers do not
+reuse the same prime label.  It is not yet derived from Petal address geometry.
+
+Typical use:
+
+```text
+1. produce PetalPrimeChannel d x u (qOf i) for each i in I
+2. prove PetalCarrierLabelNoncollisionOn I qOf
+3. apply petalPrimeChannelFamily_logSubProbability_GN_of_labelNoncollision
+```
+
+The lower-level pairwise-distinct theorem remains available:
+
+```text
+petalPrimeChannelFamily_logSubProbability_GN_of_pairwiseDistinct
+```
+
 The no-lift side is deliberately separate:

 ```text
@@ -667,6 +685,7 @@ Current research target:

 ```text
 Petal address / carrier noncollision
+  -> PetalCarrierLabelNoncollisionOn I qOf
   -> NatPairwiseDistinctOn I qOf
 ```

````
`````
