# Git diff / Report / Review

## Upd: Petal.ErdosBridge

gch: 0111a788fc601a4653ea5bc6d9edfb91fb22ae50

## Report

同期しました。今回はコードコメントを一次情報として更新し、docs 側をその現状に合わせました。

更新内容:

- [ErdosBridge.lean](/lean/dk_math/DkMath/Petal/ErdosBridge.lean)
  - module doc を「実験開始」から「公開 bridge」へ更新
  - 実装済みルートを明記:
    - `PetalPrimeChannel family -> log sub-probability`
    - `NatPairwiseDistinctOn -> GN multiplicity budget`
    - `PetalNoLiftPrimeChannel -> padicValNat q GN = 1`
  - 未主張事項を明記:
    - Zsigmondy alone -> NoLift は主張しない
    - GN squarefree は主張しない
    - full Erdős #1196 analytic tail は主張しない

- [Petal-Overview.md](/lean/dk_math/DkMath/Petal/docs/Petal-Overview.md)
  - `DkMath.Petal.ErdosBridge` を公開 API として追記
  - current research target を `Petal address / carrier noncollision -> NatPairwiseDistinctOn` に更新

- [Petal-ErdosBridge-ExperimentPlan.md](/lean/dk_math/DkMath/Petal/docs/Petal-ErdosBridge-ExperimentPlan.md)
  - status を `first public bridge implemented` に更新
  - implemented / not yet claimed / next target を整理

- [FLGNB-PetalRoadmap.md](/lean/dk_math/DkMath/NumberTheory/docs/BinomialPrimeWeighted/FLGNB-PetalRoadmap.md)
  - Step 6.5 を `planned` から `first public bridge implemented` へ更新
  - 次の焦点を `NatPairwiseDistinctOn` 生成に修正

検証:

- `lake build DkMath.Petal` 成功
- `git diff --check` 成功

今回の整理で、公開面の説明は「Petal/ErdosBridge は Erdős 本体証明ではなく、GN carrier を finite log-capacity channel へ渡す bridge」という線に揃いました。

## Review

うむ。今回の整理で、状況はかなり綺麗になった。

結論から言うと、 **`Petal.ErdosBridge` は実験ファイルから公開 bridge へ昇格した** 。
そして docs 側も、その昇格に合わせて「何が証明済みで、何をまだ主張していないか」をかなり正しく整理できておる。

## 1. 今回の本質

今回の変更は、コード追加というより **公開 API 化のための整備** じゃ。

以前は、

```text
Petal / Erdos bridge を試している
```

という段階だった。

今は、

```text
DkMath.Petal.ErdosBridge は
Petal GN carrier を Erdos finite log-capacity channel へ渡す
公開 bridge である
```

と明記された。

これは大きい。
`DkMath.Petal.lean` から import された時点で、もう「隠れた実験場」ではない。Petal package の利用者が自然に見つける公開面になった。

## 2. 状況の正しい要約

現在の到達点はこの形じゃ。

```text
PetalPrimeChannel family
  + NatPairwiseDistinctOn labels
  -> NatBaseMultiplicityBudgetOn against GN
  -> realLogRatioWeightProvider.SubProbability
```

さらに局所 NoLift 側は、

```text
PetalNoLiftPrimeChannel
  -> padicValNat q (GN d x u) = 1
```

として独立に固定された。

ここで非常に重要なのは、docs がこの二つを混ぜていないことじゃ。

```text
PairwiseDistinct:
  family の label collision を防ぐ条件

NoLift:
  ひとつの selected prime label が GN 上で exact one-slot である条件
```

つまり、

```text
NoLift family
  -> 各 q は局所的に one-slot

NatPairwiseDistinctOn
  -> 複数 index が同じ q を再利用しない
```

この二つは別の役割を持つ。今回の docs はそこを明確にした。これは公開 API として非常に大事じゃ。

## 3. 今回の文書整備の評価

**かなり良い。approve。**

特に良いのは、module doc を一次情報として更新した点じゃ。

Lean ファイルの module doc が、

```text
This file starts the experimental bridge...
```

から、

```text
This file is the public bridge...
```

へ変わった。

この判断は正しい。
docs だけ先行しても、実装ファイルの冒頭コメントが古いままだと、あとで読む人が混乱する。今回は `ErdosBridge.lean`、`Petal-Overview.md`、`Petal-ErdosBridge-ExperimentPlan.md`、`FLGNB-PetalRoadmap.md` の説明が同じ線に揃った。

公開面の説明として、

```text
これは full Erdős #1196 analytic tail estimate ではない
これは GN carrier を finite log-capacity channel へ渡す bridge である
```

と明記したのも良い。過大主張を防げている。

## 4. 現在の研究地図

いまの本命は完全にこれじゃ。

```text
Petal address / carrier noncollision
  -> NatPairwiseDistinctOn I qOf
```

これが次の山。

なぜなら、すでに後段は通っている。

```text
NatPairwiseDistinctOn I qOf
  -> GN multiplicity budget
  -> log SubProbability
```

つまり、残りの難所は

```text
Petal geometry が label distinctness を供給できるか
```

に集約された。

これは良い状況じゃ。
問題がぼやけていない。Lean で次に試すべき theorem の形がはっきりしている。

## 5. 何が公開済みで、何が未公開主張か

公開済みとして読んでよいものはこれ。

```text
PetalPrimeChannel -> prime-valued Erdos channel
PetalPrimeChannel family + budget -> SubProbability
PetalPrimeChannel family + pairwise distinct labels on one GN -> GN budget
PetalPrimeChannel family + pairwise distinct labels on one GN -> log SubProbability
PetalNoLiftPrimeChannel -> padicValNat q GN = 1
```

未主張として守るべきものはこれ。

```text
Petal address noncollision -> NatPairwiseDistinctOn
Zsigmondy alone -> NoLift
GN carrier -> squarefree
PetalNoLift family -> labels are distinct
full Erdős #1196 analytic tail estimate
```

この分離ができている限り、公開しても危うくない。

## 6. 次に整備すべきもの

次は docs に加えて、 **使い方の小例** が欲しい。

たとえば `Petal-Overview.md` に短く、

```text
To use the bridge:
  1. produce PetalPrimeChannel d x u (qOf i)
  2. prove NatPairwiseDistinctOn I qOf
  3. apply petalPrimeChannelFamily_logSubProbability_GN_of_pairwiseDistinct
```

という使用手順を書くとよい。

また、`Petal-ErdosBridge-ExperimentPlan.md` は名前がやや古くなり始めている。すぐ rename しなくてもよいが、将来的には、

```text
Petal-ErdosBridge.md
Petal-ErdosBridge-Status.md
Petal-ErdosBridge-PublicAPI.md
```

のように、実験計画から公開仕様へ移してもよい。

## 7. 現在の成熟度

わっちの評価はこうじゃ。

```text
Implementation:
  public first bridge completed

Documentation:
  synchronized with implementation

Mathematical status:
  finite log-capacity bridge established
  analytic Erdős #1196 not claimed

Next theorem target:
  Petal address / carrier noncollision
    -> NatPairwiseDistinctOn
```

かなり良い段階に来た。
以前は「Petal は Erdős route に入れるか？」だった。
今は「Petal address が distinct labels を出せるか？」まで絞れた。

これは大きな進歩じゃ。

## 8. 総括

今回の整理で、DkMath の Petal/Erdős ルートはこうなった。

```text
局所:
  NoLift gives exact one-slot valuation on GN

大域有限:
  pairwise distinct Petal prime labels give GN log-capacity sub-probability

未踏:
  address noncollision should generate pairwise distinct labels
```

つまり、Petal はもう単なる「GN 上の観測面」ではない。
Erdős #1196 の有限 log-capacity route に対して、 **公開 API として接続された carrier/channel 生成層** になった。

次は、Petal address を本当に予算生成装置にできるか。
そこが通れば、DkMath 独自 route の色がさらに濃くなる。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/NumberTheory/docs/BinomialPrimeWeighted/FLGNB-PetalRoadmap.md b/lean/dk_math/DkMath/NumberTheory/docs/BinomialPrimeWeighted/FLGNB-PetalRoadmap.md
index 34b21021..35770182 100644
--- a/lean/dk_math/DkMath/NumberTheory/docs/BinomialPrimeWeighted/FLGNB-PetalRoadmap.md
+++ b/lean/dk_math/DkMath/NumberTheory/docs/BinomialPrimeWeighted/FLGNB-PetalRoadmap.md
@@ -1707,7 +1707,7 @@ stable facade and redirect its public theorems internally.
 Status:

 ```text
-planned
+first public bridge implemented
 ```

 The next experimental checkpoint is documented in:
@@ -1726,36 +1726,43 @@ Erdos #1196 / PrimitiveSet:
   global log-capacity control
 ```

-The experiment should not attempt to prove new unconditional number theory.
-The first target is a translation-and-budget-consumption bridge:
+The bridge does not attempt to prove new unconditional number theory.  The
+first public bridge has implemented translation and budget-consumption:

 ```text
 Petal carrier
   -> Erdos prime channel
   -> prime-valued family
-  -> multiplicity budget assumption
+  -> multiplicity budget assumption or pairwise distinct GN-family labels
   -> log-capacity sub-probability
 ```

-Recommended first file:
+Implemented file:

 ```text
 DkMath.Petal.ErdosBridge
 ```

-Recommended first theorem shape:
+Implemented theorem shapes:

 ```text
 Petal carrier family
   + NatBaseMultiplicityBudgetOn against n
   -> normalized log-cost sum <= 1
+
+PetalPrimeChannel family on one GN surface
+  + NatPairwiseDistinctOn labels
+  -> NatBaseMultiplicityBudgetOn against GN
+  -> realLogRatioWeightProvider.SubProbability
+
+PetalNoLiftPrimeChannel
+  -> padicValNat q (GN d x u) = 1
 ```

-The research question postponed until after the first bridge is:
+The current research question after the first bridge is:

 ```text
-Can Petal address noncollision supply the multiplicity budget required by the
-Erdos log-capacity route?
+Can Petal address / carrier noncollision supply `NatPairwiseDistinctOn I qOf`?
 ```

 ### Step 7: Refactor imports gradually
diff --git a/lean/dk_math/DkMath/Petal/ErdosBridge.lean b/lean/dk_math/DkMath/Petal/ErdosBridge.lean
index 52e9d27e..4eed2d8e 100644
--- a/lean/dk_math/DkMath/Petal/ErdosBridge.lean
+++ b/lean/dk_math/DkMath/Petal/ErdosBridge.lean
@@ -12,21 +12,46 @@ import DkMath.NumberTheory.PrimitiveSet.ValuationBudget
 /-!
 # Petal Erdos Bridge

-This file starts the experimental bridge from Petal/GN carriers to the finite
-Erdos #1196 log-capacity machinery.
+This file is the public bridge from Petal/GN carriers to the finite Erdos
+#1196 log-capacity machinery.

-The first step is intentionally small:
+It does **not** prove the analytic Erdos #1196 tail estimate.  Instead, it
+shows that GN-observed Petal carriers can be read as prime-valued channels for
+the existing `PrimitiveSet` log-capacity route.
+
+The current implemented route is:

 ```text
-Petal carrier
-  -> prime-valued Erdos channel
+PetalPrimeChannel family
+  -> prime-valued Erdos channel family
   -> multiplicity-budgeted log sub-probability
+
+PetalPrimeChannel family on one GN surface
+  + pairwise distinct prime labels
+  -> GN multiplicity budget
+  -> log sub-probability against that GN surface
+
+PetalNoLiftPrimeChannel
+  -> padicValNat q (GN d x u) = 1
+```
+
+Two conditions remain separate by design:
+
+* `NatPairwiseDistinctOn I qOf` is the family noncollision condition that
+  prevents selected channels from reusing the same exponent slot.
+* `PetalNoLiftPrimeChannel` is a local one-slot condition for one selected
+  prime label.  A family of no-lift channels does not by itself imply that the
+  labels are distinct.
+
+Current research target:
+
+```text
+Petal address / carrier noncollision
+  -> NatPairwiseDistinctOn I qOf
 ```

-No multiplicity budget is proved here.  The caller still supplies the existing
-`PrimitiveSet.NatBaseMultiplicityBudgetOn` hypothesis.  This keeps the bridge
-honest: Petal supplies carrier location, while the Erdos side supplies the
-global capacity bound once a multiplicity budget is available.
+The file also keeps explicit guardrails: Zsigmondy alone is not claimed to imply
+no-lift, squarefreeness of GN, or the full multiplicity budget.
 -/

 namespace DkMath
diff --git a/lean/dk_math/DkMath/Petal/docs/Petal-ErdosBridge-ExperimentPlan.md b/lean/dk_math/DkMath/Petal/docs/Petal-ErdosBridge-ExperimentPlan.md
index 17cf2599..9dfc94b0 100644
--- a/lean/dk_math/DkMath/Petal/docs/Petal-ErdosBridge-ExperimentPlan.md
+++ b/lean/dk_math/DkMath/Petal/docs/Petal-ErdosBridge-ExperimentPlan.md
@@ -1,6 +1,6 @@
 # Petal / Erdos #1196 Bridge Experiment Plan

-Status: **planning**
+Status: **first public bridge implemented**

 This document records the next experimental route after the Petal/Zsigmondy
 contract work.
@@ -13,9 +13,16 @@ Erdos #1196 formalization, and can the Erdos log-capacity machinery return
 useful global conditions for Zsigmondy / FLT / ABC?
 ```

-The answer is: **yes, but only as a staged experiment**.  The current workspace
-already contains enough infrastructure to test the connection, but not enough
-to claim a new unconditional Zsigmondy or FLT theorem.
+The answer is: **yes, for the finite log-capacity bridge**.  The current
+workspace now contains the first public Petal/Erdos bridge:
+
+```text
+DkMath.Petal.ErdosBridge
+```
+
+This is still not a new unconditional Zsigmondy, FLT, ABC, or analytic Erdős
+#1196 theorem.  It is the public bridge that lets Petal GN carrier channels be
+consumed by the existing finite `PrimitiveSet` log-capacity machinery.

 ## Current Coordinates

@@ -39,6 +46,7 @@ Zsigmondy handshake:
 Multiplicity layer:
   local NoLift at q
   squarefree GN as a sufficient condition
+  pairwise distinct selected labels as the current family noncollision input
 ```

 Important files:
@@ -60,6 +68,7 @@ Zsigmondy gives a primitive q.
 Petal tells us where q is observed: on GN, not on the boundary.
 Valuation transfer lets the body-difference height be read on GN.
 NoLift / squarefree controls the multiplicity.
+PairwiseDistinct controls family label collisions.
 ```

 ### Erdos #1196 Side
@@ -107,6 +116,14 @@ selected prime-power channels

 This is the finite R/log capacity route.

+The bridge now uses the following implemented `PrimitiveSet` support:
+
+```lean
+natPairwiseDistinctOn_injOn
+natBaseMultiplicityBudgetOn_of_injOn_of_dvd
+natBaseMultiplicityBudgetOn_of_pairwiseDistinct_of_dvd
+```
+
 ## Conceptual Bridge

 The bridge is:
@@ -131,10 +148,31 @@ AnchoredGNCarrier
 This does not prove a new primitive-divisor theorem.  It gives a way to feed
 Petal/Zsigmondy witnesses into the existing Erdos capacity machinery.

+The currently implemented public route is:
+
+```text
+PetalPrimeChannel family
+  + NatPairwiseDistinctOn labels
+  -> NatBaseMultiplicityBudgetOn against GN
+  -> realLogRatioWeightProvider.SubProbability
+```
+
+The currently implemented local no-lift route is:
+
+```text
+PetalNoLiftPrimeChannel
+  -> padicValNat q (GN d x u) = 1
+```
+
+These are separate facts.  NoLift gives local one-slot valuation for a selected
+prime label; it does not prove family label distinctness.
+
 ## Strong Claims We May Be Able to Extract

 ### Claim A: Zsigmondy Witness as an Erdos Channel

+Status: **implemented**
+
 Expected form:

 ```lean
@@ -153,6 +191,8 @@ Zsigmondy witness can be inserted into the Erdos channel vocabulary.

 ### Claim B: Petal Carrier Cost is Log-Capacity Cost

+Status: **implemented**
+
 Expected form:

 ```lean
@@ -172,6 +212,8 @@ Petal carrier has a capacity cost.

 ### Claim C: Finite Petal Carrier Family Has a Sub-Probability Budget

+Status: **implemented, with two entry forms**
+
 Expected form:

 ```lean
@@ -180,6 +222,14 @@ finite family of Petal carriers
   -> sum log(base prime) / log n <= 1
 ```

+Implemented forms include:
+
+```lean
+petalCarrierFamily_logSubProbability_of_multiplicityBudget
+petalPrimeChannelFamily_logSubProbability_GN_of_injOn
+petalPrimeChannelFamily_logSubProbability_GN_of_pairwiseDistinct
+```
+
 This should reuse:

 ```lean
@@ -197,6 +247,8 @@ Petal carrier families can be viewed as Erdos finite capacity kernels.

 ### Claim D: NoLift Separates Multiplicity from Capacity

+Status: **implemented locally**
+
 The Petal/Zsigmondy contract says:

 ```text
@@ -224,6 +276,21 @@ Expected role:
 NoLift controls whether a Petal carrier is a unit-cost Erdos channel.
 ```

+Implemented core:
+
+```lean
+petalNoLiftPrimeChannel_padicValNat_GN_eq_one
+petalNoLiftPrimeChannel_singleton_logSubProbability_GN_self
+petalNoLiftPrimeChannelFamily_padicValNat_GN_eq_one
+```
+
+Important guardrail:
+
+```text
+NoLift is local.  A no-lift family does not imply that selected labels are
+pairwise distinct.
+```
+
 ## Claims Not Yet Justified

 The following should **not** be claimed yet:
@@ -234,6 +301,8 @@ Petal carriers automatically satisfy the Erdos multiplicity budget.
 Zsigmondy automatically supplies local NoLift.
 Zsigmondy automatically supplies padicValNat <= 1.
 GN carriers are automatically squarefree.
+Petal address noncollision automatically supplies NatPairwiseDistinctOn.
+Full analytic Erdős #1196 tail estimate.
 ```

 These are research directions, not current theorems.
@@ -253,6 +322,8 @@ So multiplicity hypotheses cannot be erased.

 ### Step 1: Add a Thin `Petal.ErdosBridge` File

+Status: **implemented**
+
 Candidate file:

 ```text
@@ -289,6 +360,8 @@ re-export the reading under Erdos/channel vocabulary.

 ### Step 2: Define a Minimal Petal Channel Predicate

+Status: **implemented**
+
 Candidate:

 ```lean
@@ -309,6 +382,8 @@ def PetalNoLiftPrimeChannel (d x u q : ℕ) : Prop :=

 ### Step 3: Connect Prime Channel to Log-Cost Nonnegativity

+Status: **implemented**
+
 Expected target:

 ```lean
@@ -322,13 +397,13 @@ This should follow from `Nat.Prime.one_lt` and the existing real-log helpers in

 ### Step 4: Finite Family Experiment

-Define an experimental family predicate, not a public final API:
+Status: **implemented without adding a separate family predicate**
+
+The current implementation did not add a separate family predicate.  It uses
+ordinary quantified hypotheses:

 ```lean
-def PetalCarrierFamilyOn
-    {ι : Type*} (I : Finset ι)
-    (d x u : ι -> ℕ) (qOf : ι -> ℕ) : Prop :=
-  ∀ i, i ∈ I -> PetalPrimeChannel (d i) (x i) (u i) (qOf i)
+∀ i, i ∈ I -> PetalPrimeChannel (d i) (x i) (u i) (qOf i)
 ```

 Then try to prove:
@@ -342,6 +417,8 @@ This is a direct entry into the existing Erdos valuation-budget API.

 ### Step 5: Capacity Budget as an Assumption

+Status: **implemented**
+
 Do not try to prove multiplicity budget from Petal geometry yet.

 Instead, assume:
@@ -363,12 +440,19 @@ Petal supplies prime-valued carriers.
 Erdos supplies capacity once multiplicity budget is given.
 ```

+The implementation then went further: when all selected channels lie on the
+same GN surface and labels are pairwise distinct, Petal supplies the GN
+multiplicity budget directly.
+
 ### Step 6: Research Target - Address Antichain to Multiplicity Budget

-Only after Step 5, investigate:
+Status: **current research target**
+
+Now that Step 5 is implemented, investigate:

 ```text
 Petal address noncollision
+  -> NatPairwiseDistinctOn I qOf
   -> base-prime multiplicity budget
 ```

@@ -381,9 +465,14 @@ PetalAddressAntichain family
   -> NatBaseMultiplicityBudgetOn I qOf n
 ```

-This is not yet ready for implementation.  It requires deciding what the
-parent `n` is: body difference, GN, source state, or an abstract capacity
-carrier.
+The current public bridge has chosen one concrete parent for this route:
+
+```text
+GN d x u
+```
+
+Other parents, such as body difference, source state, or an abstract capacity
+carrier, remain separate design questions.

 ## Proposed Documentation / Naming Policy

@@ -415,35 +504,22 @@ Those are not established.

 ## Recommended Next Checkpoint

-Implement:
+Implement the address-facing noncollision layer:

 ```text
-DkMath.Petal.ErdosBridge
+Petal address / carrier noncollision
+  -> NatPairwiseDistinctOn I qOf
 ```

-with only:
+This is now the missing input needed by:

 ```lean
-def PetalPrimeChannel
-def PetalNoLiftPrimeChannel
-theorem petalPrimeChannel_prime
-theorem petalPrimeChannel_natPrimeValuedOn
-theorem petalPrimeChannel_log_nonneg
-```
-
-Then add one finite-family theorem:
-
-```lean
-theorem petalCarrierFamily_logSubProbability_of_multiplicityBudget
+petalPrimeChannelFamily_logSubProbability_GN_of_pairwiseDistinct
 ```

-This theorem should assume the multiplicity budget and reuse the existing
-PrimitiveSet log-capacity machinery.  That gives the first concrete Petal ->
-Erdos bridge without overclaiming.
-
 ## Final Assessment

-The project is ready to enter an experimental bridge phase:
+The first public bridge is implemented:

 ```text
 Petal / Zsigmondy / GN:
@@ -453,14 +529,13 @@ Erdos #1196 / PrimitiveSet:
   global log-capacity control
 ```

-The first experiment should prove translation and budget-consumption theorems,
-not new unconditional number theory.
+The implemented bridge proves translation and budget-consumption theorems.  It
+also proves the duplicate-free GN-family route through `NatPairwiseDistinctOn`.

-If this bridge succeeds, the next research target is:
+The next research target is:

 ```text
-Can Petal address noncollision supply the multiplicity budget required by the
-Erdos log-capacity route?
+Can Petal address / carrier noncollision supply `NatPairwiseDistinctOn`?
 ```

 That is the point where Petal may start producing genuinely strong conditions
diff --git a/lean/dk_math/DkMath/Petal/docs/Petal-Overview.md b/lean/dk_math/DkMath/Petal/docs/Petal-Overview.md
index bb664d46..46cfebc6 100644
--- a/lean/dk_math/DkMath/Petal/docs/Petal-Overview.md
+++ b/lean/dk_math/DkMath/Petal/docs/Petal-Overview.md
@@ -110,6 +110,7 @@ DkMath.Petal.BoundaryD3
 DkMath.Petal.EisensteinBridge
 DkMath.Petal.ZsigmondyD3Bridge
 DkMath.Petal.PrimitiveD3ValuationBridge
+DkMath.Petal.ErdosBridge
 ```

 ### `DkMath.Petal.Basic`
@@ -625,9 +626,49 @@ The experimental Petal/Erdos bridge plan is recorded in:
 DkMath/Petal/docs/Petal-ErdosBridge-ExperimentPlan.md
 ```

-Its main conclusion is that the next bridge should translate the `d = 3`
-Petal witness into Zsigmondy's primitive-divisor language, while keeping
-valuation `<= 1` separate under squarefree/no-lift hypotheses.
+The public Petal/Erdos bridge is now exposed as:
+
+```text
+DkMath.Petal.ErdosBridge
+```
+
+Its purpose is narrow and explicit:
+
+```text
+Petal GN carrier
+  -> Erdos finite log-capacity channel
+```
+
+It does not prove the analytic Erdős #1196 tail estimate.  It proves that
+Petal prime-channel families can be consumed by the existing `PrimitiveSet`
+log-capacity machinery once the required duplicate-free / multiplicity-budget
+conditions are supplied.
+
+The current implemented route is:
+
+```text
+PetalPrimeChannel family
+  + NatPairwiseDistinctOn labels
+  -> NatBaseMultiplicityBudgetOn against GN
+  -> realLogRatioWeightProvider.SubProbability
+```
+
+The no-lift side is deliberately separate:
+
+```text
+PetalNoLiftPrimeChannel
+  -> padicValNat q (GN d x u) = 1
+```
+
+This says that a selected channel has exactly one local exponent slot.  It does
+not say that different selected indices have different prime labels.
+
+Current research target:
+
+```text
+Petal address / carrier noncollision
+  -> NatPairwiseDistinctOn I qOf
+```

 ## What This Does Not Claim Yet

@@ -640,6 +681,8 @@ It also does not yet prove:
 general d boundary classification
 full Zsigmondy theorem
 FLT descent
+full Erdős #1196 analytic tail estimate
+Petal address noncollision -> NatPairwiseDistinctOn
 complete Eisenstein refactor away from the FLT namespace
 complete split of BoundaryD3 and BoundaryD3Anchor
 concrete prime enumeration / standard primorial theorem
@@ -657,10 +700,11 @@ The next reasonable implementation directions are:

 ```text
 1. connect BoundaryD3 / EisensteinBridge to downstream FLT or Zsigmondy inputs
-2. use Petal address decomposition in nested observations
-3. connect strict prime-base orbits to a concrete prime enumeration
-4. decide whether GNPrimitiveCandidate needs a separate vocabulary layer
-5. perform the deferred `DkMath.Lib.*` promotion refactor
+2. connect Petal address / carrier noncollision to `NatPairwiseDistinctOn`
+3. use Petal address decomposition in nested observations
+4. connect strict prime-base orbits to a concrete prime enumeration
+5. decide whether GNPrimitiveCandidate needs a separate vocabulary layer
+6. perform the deferred `DkMath.Lib.*` promotion refactor
 ```

 The most conservative next theorem work is probably:
````
`````
