# Git diff / Report / Review

## Upd: Petal.ErdosBridge

gch: 0c9b652e04e6cffc09cde975a7bd36006b98f0b5

## Report

進めました。今回は `f = id` の toy route を [ErdosBridge.lean](/lean/dk_math/DkMath/Petal/ErdosBridge.lean) に追加しました。

追加 theorem は以下です。

- `petalCarrierLabelNoncollisionOn_outer_of_value_self`
- `petalPrimeChannelFamily_multiplicityBudget_GN_of_outer_value_self`
- `petalPrimeChannelFamily_logSubProbability_GN_of_outer_value_self`
- `petalNoLiftPrimeChannelFamily_logSubProbability_GN_of_outer_value_self`

これは `qOf = mOf`、つまり住所値そのものを label とみなす制御実験です。任意の Petal value が素数 channel になるとは言っていません。`PetalPrimeChannel d x u (mOf i)` や `PetalNoLiftPrimeChannel d x u (mOf i)` は明示仮定のままです。

docs も同期しました。

- [Petal-Overview.md](/lean/dk_math/DkMath/Petal/docs/Petal-Overview.md)
- [Petal-ErdosBridge-ExperimentPlan.md](/lean/dk_math/DkMath/Petal/docs/Petal-ErdosBridge-ExperimentPlan.md)
- [FLGNB-PetalRoadmap.md](/lean/dk_math/DkMath/NumberTheory/docs/BinomialPrimeWeighted/FLGNB-PetalRoadmap.md)

検証は通っています。

```text
lake build DkMath.Petal
git diff --check ...
```

次は `nthPrime` route を試すか、DkMath らしい `carrierAnchorOf(m)` 型へ設計を寄せる段階です。

## Review

うむ。今回の `f = id` toy route は、**数学的大前進というより、API 配線の健全性確認としてかなり良い一手** じゃ。

結論から言うと、これは **「value-map route がちゃんと最小例で閉じる」ことを確認した制御実験** じゃな。

## 1. 今回通った道

今回の道はこれ。

```text id="0nodvr"
qOf = mOf
```

つまり、selected value 自身を label とみなす。

その上で、

```text id="2t5ol8"
mOf が selected index 上で injective
```

なら、

```text id="adpn9n"
PetalCarrierLabelNoncollisionOn I mOf
```

が出る。

そこから既存 bridge により、

```text id="6d3g9m"
PetalPrimeChannel d x u (mOf i)
  + label noncollision
  -> GN multiplicity budget
  -> finite GN log-capacity sub-probability
```

まで流れる。

NoLift 版も同様に、

```text id="hyu680"
PetalNoLiftPrimeChannel d x u (mOf i)
  + label noncollision
  -> finite GN log-capacity sub-probability
```

へ進める。

## 2. 何が確認できたか

これは `qOf = f(mOf)` route の最小テストじゃ。

前回の一般形はこうだった。

```text id="eeebs3"
qOf i = f (mOf i)

f (mOf i) = f (mOf j)
  -> mOf i = mOf j
```

今回 `f = id` とすると、

```text id="m5rxnu"
mOf i = mOf j
  -> mOf i = mOf j
```

なので、recovery 条件は自明になる。

つまり今回の theorem 群は、

```text id="4g8jkw"
value-map route の抽象 API が、最小ケースでちゃんと合成できる
```

ことを確認したものじゃ。

これは地味だが重要。
抽象 wrapper を作ったとき、最小例が通るかどうかはかなり大事じゃからの。

## 3. 何を主張していないか

ここは docs の通り、かなり重要じゃ。

今回の `qOf = mOf` は、

```text id="xvzyll"
任意の Petal value が prime channel label になる
```

とは言っていない。

実際、theorem 側では依然として

```lean id="i84y65"
∀ i, i ∈ I → PetalPrimeChannel d x u (mOf i)
```

または

```lean id="z1p5e5"
∀ i, i ∈ I → PetalNoLiftPrimeChannel d x u (mOf i)
```

を明示仮定している。

つまり今回の theorem は、

```text id="b3mjn4"
prime channel を作る theorem ではない
```

あくまで、

```text id="dg12og"
すでに prime channel だと分かっている selected values が
互いに衝突しないなら、
Erdős log-capacity route に流せる
```

という theorem じゃ。

この切り分けは正しい。

## 4. 今回の意味を一言で言うと

今回の意味はこうじゃ。

```text id="n72tzw"
住所値そのものを label とした場合、
outer-address noncollision machinery は正しく動作する。
```

これは「本命 label construction」ではない。
だが、`qOf = f(mOf)` route の制御実験としては非常に良い。

ここで API の向きが確認できたので、次は安心して

```text id="yx6kch"
f = nthPrime
```

または

```text id="ibsk5g"
f = carrierAnchorOf
```

へ進める。

## 5. 次の候補 1: `nthPrime` route

`nthPrime` route の役割は、**住所値から確実に prime label を選ぶ toy/practical route** じゃ。

期待する形はこう。

```text id="8mnpco"
qOf i = nthPrime (mOf i)
```

もし `nthPrime` が injective に扱えるなら、

```text id="g292zu"
nthPrime (mOf i) = nthPrime (mOf j)
  -> mOf i = mOf j
```

が出る。

これにより label noncollision は供給できる。

ただし注意点がある。

`nthPrime` は prime label を作るかもしれぬが、

```text id="ld8w99"
PetalPrimeChannel d x u (nthPrime (mOf i))
```

は自動では出ない。

つまり `nthPrime` route は、

```text id="ty63ew"
prime label の非衝突・素数性の補助
```

にはなるが、

```text id="33y7g6"
その prime が GN を割る
```

までは別途必要じゃ。

だからこれは中間実験として有益。

## 6. 次の候補 2: `carrierAnchorOf(m)` route

こちらが DkMath 的には本命じゃ。

目指す構造はこう。

```text id="b3d77p"
m
  -> Petal / GN 観測点
  -> carrier anchor prime
  -> q
```

つまり、

```text id="ntc57z"
qOf i = carrierAnchorOf (mOf i)
```

のように、住所値から実際の GN carrier prime を読む。

これができれば、

```text id="p6zz1t"
qOf i は prime
qOf i は GN を割る
PetalPrimeChannel d x u (qOf i)
NoLift 条件を加えれば one-slot
```

まで一気に近づく。

ただしこれは強い。
たぶん必要になるのは、

```text id="86kggx"
carrier existence
carrier uniqueness
address reconstruction
label recovery
```

じゃ。

特に難所は、

```text id="gaoynv"
same carrier label -> same address/value
```

をどこまで出せるか。

## 7. 今後の推奨順

わっちなら次はこう進める。

```text id="hxf6q3"
1. f = id route は完了、これは control として維持
2. f = nthPrime route で label recovery API を検証
3. nthPrime route では PetalPrimeChannel は仮定のままにする
4. carrierAnchorOf(m) の設計を始める
5. carrierAnchorOf では PetalPrimeChannel まで供給する構造を目指す
```

焦らず、`nthPrime` で一度「素数 label map」としての配線を確認してから、DkMath 本命の `carrierAnchorOf` へ入るのがよい。

## 8. 現在地の総括

ここまでで道はこうなった。

```text id="pg7n50"
outerPetalAddress
  -> mOf の復元
  -> address noncollision

qOf = f(mOf)
  -> label recovery
  -> label noncollision

f = id
  -> 最小 control route 通過

label noncollision
  + PetalPrimeChannel / NoLift
  -> GN multiplicity budget
  -> finite GN log-capacity route
```

今回の成果は、**抽象 API の健全性確認** としてかなり良い。
次からは本当に `f` の中身を数学に寄せる段階じゃ。

目的地別にはこう。

```text id="0nzx0o"
Erdős:
  f が distinct carrier labels を供給できれば finite GN log-capacity family が増える

FLT:
  f が NoLift carrier labels を供給できれば one-slot obstruction に近づく

ABC:
  f が distinct one-slot carrier labels を供給できれば support/rad lower bound に近づく
```

うむ。
これは「制御実験」として成功じゃ。
次は `nthPrime` で素数列ラベルの配線を見るか、いよいよ `carrierAnchorOf(m)` で DkMath 本命の carrier label map を設計する段階じゃな。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/NumberTheory/docs/BinomialPrimeWeighted/FLGNB-PetalRoadmap.md b/lean/dk_math/DkMath/NumberTheory/docs/BinomialPrimeWeighted/FLGNB-PetalRoadmap.md
index 1b3513ce..74921cfa 100644
--- a/lean/dk_math/DkMath/NumberTheory/docs/BinomialPrimeWeighted/FLGNB-PetalRoadmap.md
+++ b/lean/dk_math/DkMath/NumberTheory/docs/BinomialPrimeWeighted/FLGNB-PetalRoadmap.md
@@ -1850,6 +1850,18 @@ petalNoLiftPrimeChannelFamily_logSubProbability_GN_of_outer_value_map_injective
 This is a label-recovery wrapper, not a theorem that a value map automatically
 constructs prime channels.
 
+The `f = id` toy case is also implemented:
+
+```text
+petalCarrierLabelNoncollisionOn_outer_of_value_self
+petalPrimeChannelFamily_multiplicityBudget_GN_of_outer_value_self
+petalPrimeChannelFamily_logSubProbability_GN_of_outer_value_self
+petalNoLiftPrimeChannelFamily_logSubProbability_GN_of_outer_value_self
+```
+
+This is a control theorem for the wrapper.  It does not turn arbitrary Petal
+values into prime-channel labels.
+
 ### Step 7: Refactor imports gradually
 
 Status:
diff --git a/lean/dk_math/DkMath/Petal/ErdosBridge.lean b/lean/dk_math/DkMath/Petal/ErdosBridge.lean
index 92919635..591a0f61 100644
--- a/lean/dk_math/DkMath/Petal/ErdosBridge.lean
+++ b/lean/dk_math/DkMath/Petal/ErdosBridge.lean
@@ -376,6 +376,26 @@ theorem petalCarrierLabelNoncollisionOn_outer_of_value_map_injective
     (petalCarrierLabelCompatibleOn_outer_of_value_map_injective
       I n lap mOf qOf f hq hf)
 
+/--
+Toy outer-address route where the selected label is the selected value itself.
+
+This is the `f = id` sanity check for the value-map API.  It proves only
+noncollision of labels; it does **not** say that the selected values are prime
+channels.
+-/
+theorem petalCarrierLabelNoncollisionOn_outer_of_value_self
+    {ι : Type _}
+    (I : Finset ι)
+    (n lap : Nat)
+    (mOf : ι → Nat)
+    (hm : ∀ i, i ∈ I → 1 ≤ mOf i)
+    (hminj : Set.InjOn mOf ↑I) :
+    PetalCarrierLabelNoncollisionOn I mOf :=
+  petalCarrierLabelNoncollisionOn_outer_of_value_map_injective
+    I n lap mOf mOf id hm hminj
+    (fun _ _ => rfl)
+    (fun _ _ _ _ h => h)
+
 /--
 PrimitiveBeam witnesses enter the Erdos bridge as Petal prime channels.
 -/
@@ -842,6 +862,60 @@ theorem petalPrimeChannelFamily_logSubProbability_GN_of_outer_value_map_injectiv
       I n lap mOf qOf f hm hminj hq hf)
     hcarrier
 
+/--
+Toy `qOf = mOf` form of the outer-address GN multiplicity-budget route.
+
+This is an API sanity check: if the selected values themselves are assumed to
+be Petal prime-channel labels, then value injectivity supplies the required
+label noncollision.
+-/
+theorem petalPrimeChannelFamily_multiplicityBudget_GN_of_outer_value_self
+    {ι : Type _}
+    (I : Finset ι)
+    (d x u : ℕ)
+    (n lap : Nat)
+    (mOf : ι → Nat)
+    (hGN0 : GN d x u ≠ 0)
+    (hm : ∀ i, i ∈ I → 1 ≤ mOf i)
+    (hminj : Set.InjOn mOf ↑I)
+    (hcarrier :
+      ∀ i, i ∈ I → PetalPrimeChannel d x u (mOf i)) :
+    DkMath.NumberTheory.PrimitiveSet.NatBaseMultiplicityBudgetOn
+      I mOf (GN d x u) :=
+  petalPrimeChannelFamily_multiplicityBudget_GN_of_labelNoncollision
+    I d x u mOf hGN0
+    (petalCarrierLabelNoncollisionOn_outer_of_value_self
+      I n lap mOf hm hminj)
+    hcarrier
+
+/--
+Toy `qOf = mOf` form of the outer-address GN log-capacity route.
+
+This theorem intentionally keeps the strong hypothesis
+`PetalPrimeChannel d x u (mOf i)` explicit.  It is a control theorem for the
+noncollision machinery, not a prime-construction theorem.
+-/
+theorem petalPrimeChannelFamily_logSubProbability_GN_of_outer_value_self
+    {ι : Type _}
+    (I : Finset ι)
+    (d x u : ℕ)
+    (n lap : Nat)
+    (mOf : ι → Nat)
+    (hGN : 1 < GN d x u)
+    (hm : ∀ i, i ∈ I → 1 ≤ mOf i)
+    (hminj : Set.InjOn mOf ↑I)
+    (hcarrier :
+      ∀ i, i ∈ I → PetalPrimeChannel d x u (mOf i)) :
+    (DkMath.NumberTheory.PrimitiveSet.realLogRatioWeightProvider I mOf (GN d x u)
+      (petalPrimeChannel_realLogNonnegOn
+        I (fun _ => d) (fun _ => x) (fun _ => u) mOf hcarrier)
+      hGN).SubProbability :=
+  petalPrimeChannelFamily_logSubProbability_GN_of_labelNoncollision
+    I d x u mOf hGN
+    (petalCarrierLabelNoncollisionOn_outer_of_value_self
+      I n lap mOf hm hminj)
+    hcarrier
+
 /--
 Local no-lift makes the observed GN surface nonzero.
 
@@ -1052,6 +1126,35 @@ theorem petalNoLiftPrimeChannelFamily_logSubProbability_GN_of_outer_value_map_in
       I n lap mOf qOf f hm hminj hq hf)
     hcarrier
 
+/--
+Toy `qOf = mOf` form of the outer-address no-lift GN log-capacity route.
+
+The theorem checks that the no-lift bridge composes with the identity value-map
+route.  It still assumes that each selected value is already a no-lift Petal
+prime-channel label.
+-/
+theorem petalNoLiftPrimeChannelFamily_logSubProbability_GN_of_outer_value_self
+    {ι : Type _}
+    (I : Finset ι)
+    (d x u : ℕ)
+    (n lap : Nat)
+    (mOf : ι → Nat)
+    (hGN : 1 < GN d x u)
+    (hm : ∀ i, i ∈ I → 1 ≤ mOf i)
+    (hminj : Set.InjOn mOf ↑I)
+    (hcarrier :
+      ∀ i, i ∈ I → PetalNoLiftPrimeChannel d x u (mOf i)) :
+    (DkMath.NumberTheory.PrimitiveSet.realLogRatioWeightProvider I mOf (GN d x u)
+      (petalPrimeChannel_realLogNonnegOn
+        I (fun _ => d) (fun _ => x) (fun _ => u) mOf
+        (fun i hi => (hcarrier i hi).1))
+      hGN).SubProbability :=
+  petalNoLiftPrimeChannelFamily_logSubProbability_GN_of_labelNoncollision
+    I d x u mOf hGN
+    (petalCarrierLabelNoncollisionOn_outer_of_value_self
+      I n lap mOf hm hminj)
+    hcarrier
+
 /--
 A single Petal prime channel fits into the Erdos multiplicity budget of its own
 nonzero GN surface.
diff --git a/lean/dk_math/DkMath/Petal/docs/Petal-ErdosBridge-ExperimentPlan.md b/lean/dk_math/DkMath/Petal/docs/Petal-ErdosBridge-ExperimentPlan.md
index 0254baec..4b4f1fce 100644
--- a/lean/dk_math/DkMath/Petal/docs/Petal-ErdosBridge-ExperimentPlan.md
+++ b/lean/dk_math/DkMath/Petal/docs/Petal-ErdosBridge-ExperimentPlan.md
@@ -639,5 +639,18 @@ petalNoLiftPrimeChannelFamily_logSubProbability_GN_of_outer_value_map_injective
 This wrapper deliberately keeps prime-channel construction separate.  The map
 form supplies only the noncollision/recovery layer.
 
+The first toy case `f = id` is now fixed:
+
+```text
+petalCarrierLabelNoncollisionOn_outer_of_value_self
+petalPrimeChannelFamily_multiplicityBudget_GN_of_outer_value_self
+petalPrimeChannelFamily_logSubProbability_GN_of_outer_value_self
+petalNoLiftPrimeChannelFamily_logSubProbability_GN_of_outer_value_self
+```
+
+This checks the value-map API without importing a prime enumeration or a choice
+function.  It still assumes the selected values are already valid
+PetalPrimeChannel / NoLift labels when the log-capacity theorem is applied.
+
 That is the point where Petal may start producing genuinely strong conditions
 useful for Zsigmondy, FLT, and ABC.
diff --git a/lean/dk_math/DkMath/Petal/docs/Petal-Overview.md b/lean/dk_math/DkMath/Petal/docs/Petal-Overview.md
index c9192284..343297cc 100644
--- a/lean/dk_math/DkMath/Petal/docs/Petal-Overview.md
+++ b/lean/dk_math/DkMath/Petal/docs/Petal-Overview.md
@@ -793,6 +793,19 @@ This does not claim that `f` constructs prime channels.  It only supplies the
 label-recovery/noncollision part once the prime-channel hypotheses are already
 available.
 
+The identity map sanity check is implemented separately:
+
+```text
+petalCarrierLabelNoncollisionOn_outer_of_value_self
+petalPrimeChannelFamily_multiplicityBudget_GN_of_outer_value_self
+petalPrimeChannelFamily_logSubProbability_GN_of_outer_value_self
+petalNoLiftPrimeChannelFamily_logSubProbability_GN_of_outer_value_self
+```
+
+This is a toy control route.  It says that if the selected values themselves
+are already assumed to be prime-channel labels, then the outer-address
+noncollision machinery composes correctly.
+
 ## What This Does Not Claim Yet
 
 The package does not yet prove a standard primorial theorem using a concrete
````
`````
