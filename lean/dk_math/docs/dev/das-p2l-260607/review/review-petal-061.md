# Git diff / Report / Review

## Upd: Petal.ErdosBridge

gch: a545ab0147bd4adc5c4959a95cab138133d8431b

## Report

進めました。今回は `nthPrime` route の実装実験として、Mathlib の `Nat.nth Nat.Prime` を Petal 側に接続しました。

[ErdosBridge.lean](/lean/dk_math/DkMath/Petal/ErdosBridge.lean) に追加した主なものです。

- `petalNthPrimeLabel`
- `petalNthPrimeLabel_prime`
- `petalNthPrimeLabel_injective`
- `petalNthPrimeLabel_eq_imp_eq`
- `petalCarrierLabelCompatibleOn_outer_of_nthPrime_value_map`
- `petalCarrierLabelNoncollisionOn_outer_of_nthPrime_value_map`
- `petalNthPrimeLabel_natPrimeValuedOn`
- `petalPrimeChannelFamily_multiplicityBudget_GN_of_outer_nthPrime_value_map`
- `petalPrimeChannelFamily_logSubProbability_GN_of_outer_nthPrime_value_map`
- `petalNoLiftPrimeChannelFamily_logSubProbability_GN_of_outer_nthPrime_value_map`

これで `qOf i = petalNthPrimeLabel (mOf i)` という標準素数列ラベルが、prime-valued かつ injective/recovering な label map として使えることを固定しました。

重要な切り分けとして、これはまだ「その素数が GN を割る」ことは主張しません。`PetalPrimeChannel` / `PetalNoLiftPrimeChannel` は明示仮定のままです。つまり今回の成果は、標準素数列による label noncollision route の通過確認です。

docs も同期しました。

- [Petal-Overview.md](/lean/dk_math/DkMath/Petal/docs/Petal-Overview.md)
- [Petal-ErdosBridge-ExperimentPlan.md](/lean/dk_math/DkMath/Petal/docs/Petal-ErdosBridge-ExperimentPlan.md)
- [FLGNB-PetalRoadmap.md](/lean/dk_math/DkMath/NumberTheory/docs/BinomialPrimeWeighted/FLGNB-PetalRoadmap.md)

検証は通っています。

```text
lake build DkMath.Petal
git diff --check ...
```

次はいよいよ `carrierAnchorOf(m)` 的な DkMath 本命 route の設計に入れます。

## Review

うむ。これは **toy route から、標準素数列 route へ進んだ** という意味で、かなりよい段階じゃ。
前回の `f = id` は「配線が正しく合成できるか」の制御実験。今回の `petalNthPrimeLabel` は、そこから一歩進んで **本当に prime-valued で injective な label map** を Petal 側に接続した実験じゃ。

## 1. 今回の核心

今回固定された route はこれ。

```text
mOf i
  -> petalNthPrimeLabel (mOf i)
  -> qOf i
```

つまり、

```text
qOf i = petalNthPrimeLabel (mOf i)
```

という形で、住所値 `mOf i` から標準素数列ラベルを読む。

ここで `petalNthPrimeLabel` は Mathlib の

```lean
Nat.nth Nat.Prime
```

を Petal 側の名前で包んだものじゃ。

今回の追加により、次が Lean 上で固定された。

```text
petalNthPrimeLabel m は prime
petalNthPrimeLabel は injective
同じ petalNthPrimeLabel なら元の m も同じ
```

これは前回の value-map API にとって、非常に良いテスト対象じゃ。
`f = id` は prime-valued ではなかった。
今回の `f = petalNthPrimeLabel` は prime-valued であり、しかも injective。
つまり、label map としてはかなり自然な実験体になった。

## 2. 何が通ったのか

現在の道はこう。

```text
mOf が injective
  + qOf i = petalNthPrimeLabel (mOf i)
  -> PetalCarrierLabelNoncollisionOn I qOf
```

さらに、

```text
PetalPrimeChannel family
  + PetalCarrierLabelNoncollisionOn
  -> GN multiplicity budget
  -> finite GN log-capacity sub-probability
```

まで合成されている。

NoLift 版も同様に、

```text
PetalNoLiftPrimeChannel family
  + nth-prime label noncollision
  -> finite GN log-capacity sub-probability
```

へ進める。

追加された theorem 名も、この流れをかなり素直に表しておる。

```lean
petalCarrierLabelCompatibleOn_outer_of_nthPrime_value_map
petalCarrierLabelNoncollisionOn_outer_of_nthPrime_value_map
petalNthPrimeLabel_natPrimeValuedOn
petalPrimeChannelFamily_logSubProbability_GN_of_outer_nthPrime_value_map
petalNoLiftPrimeChannelFamily_logSubProbability_GN_of_outer_nthPrime_value_map
```

ここまでで、`qOf = f(mOf)` route は、

```text
f = id
f = nthPrime
```

の 2 ケースで通ったことになる。

## 3. 何が進展なのか

今回の進展は、**prime label の生成っぽいもの** が初めて入ったことじゃ。

前回の `qOf = mOf` は、住所値そのものを label と見なす toy route だった。
しかし `mOf i` が素数である保証はない。

今回の `qOf i = petalNthPrimeLabel (mOf i)` は違う。
`qOf i` は確かに素数になる。

だから今回の route は、

```text
住所値
  -> 標準素数列上の prime label
```

という意味では、かなり「住所値から prime label を作る」に近づいた。

ただし、ここで大事な切り分けがある。

## 4. まだ主張していないこと

今回の theorem は、

```text
petalNthPrimeLabel (mOf i) が GN を割る
```

とは言っていない。

つまり、

```text
Nat.Prime (qOf i)
```

は得られるが、

```text
qOf i ∣ GN d x u
```

は別仮定のままじゃ。

だから、`PetalPrimeChannel d x u (qOf i)` や `PetalNoLiftPrimeChannel d x u (qOf i)` は、今回も明示仮定として残っている。報告でも、この route は「標準素数列による label noncollision route の通過確認」であり、nth prime が GN surface を割るとは主張しない、と整理されている。

これは正しい。
ここを混ぜると危ない。

`nthPrime` は prime label をくれる。
しかし carrier をくれるわけではない。

## 5. 現在地の正確な地図

いま通っているものはこう。

```text
outerPetalAddress
  -> mOf の復元
  -> address noncollision

petalNthPrimeLabel
  -> prime-valued label
  -> injective label
  -> label recovery

mOf injective
  + qOf = petalNthPrimeLabel ∘ mOf
  -> carrier label noncollision

carrier label noncollision
  + PetalPrimeChannel / NoLift family
  -> GN log-capacity route
```

つまり、今回で

```text
label map としての prime enumeration は使える
```

ことが確認された。

残りは、

```text
その label が本当に GN carrier になるか
```

じゃ。

## 6. 次の本命は何か

報告の通り、次はいよいよ `carrierAnchorOf(m)` 的な DkMath 本命 route じゃ。

`nthPrime` route は標準的で安全だが、DkMath 的には少し外部的じゃ。
本命は、住所値から「標準素数列の何番目」ではなく、**Petal/GN 上に実際に現れる carrier anchor** を読むこと。

目指す形はこう。

```text
m
  -> Petal address / GN observation
  -> carrier anchor q
  -> PetalPrimeChannel d x u q
```

つまり、

```lean
carrierAnchorOf d x u n lap m
```

のようなものを設計し、

```text
qOf i = carrierAnchorOf (mOf i)
```

としたい。

その上で欲しい性質は三つ。

```text
1. carrierAnchorOf m は prime
2. carrierAnchorOf m ∣ GN d x u
3. 同じ carrierAnchorOf なら同じ m に戻る
```

NoLift まで行くならさらに、

```text
4. ¬ q^2 ∣ GN d x u
```

が必要じゃ。

これが通ると、今回の `nthPrime` route とは違って、prime label と GN carrier が同時に出る。

## 7. 推奨する次の設計

いきなり `carrierAnchorOf` を関数として定義するのは重いかもしれない。
なぜなら carrier が一意に選べるとは限らないからじゃ。

まずは structure / predicate でよい。

```lean
structure PetalCarrierLabelMapData
    {ι : Type _}
    (I : Finset ι)
    (d x u : ℕ)
    (mOf qOf : ι → ℕ) : Prop where
  validValue :
    ∀ i, i ∈ I → 1 ≤ mOf i
  valueInjective :
    Set.InjOn mOf ↑I
  labelRecovery :
    ∀ i, i ∈ I → ∀ j, j ∈ I →
      qOf i = qOf j → mOf i = mOf j
  carrier :
    ∀ i, i ∈ I → PetalPrimeChannel d x u (qOf i)
```

NoLift 版なら、

```lean
structure PetalNoLiftCarrierLabelMapData ...
```

として、

```lean
carrier :
  ∀ i, i ∈ I → PetalNoLiftPrimeChannel d x u (qOf i)
```

にする。

この形なら、関数の一意選択問題を避けられる。
まず family data として package し、後で canonical choice が見えたら `carrierAnchorOf` を定義すればよい。

## 8. FLT / ABC / Erdős への意味

今回の `nthPrime` route は、三方向のうち **Erdős route の label noncollision 側** を確認するものじゃ。

```text
Erdős:
  prime-valued injective label map で finite GN log-capacity route が通る

FLT:
  まだ obstruction には直結しない
  NoLift carrier 仮定があるなら使える

ABC:
  distinct prime labels の support/rad 下界へ渡す準備になる
  ただし GN carrier / NoLift は別途必要
```

つまり、今回の成果は直接 FLT や ABC を押したというより、

```text
prime label map の標準実験が通った
```

ことにある。

これで、次の `carrierAnchorOf` では「標準列でなく、GN 実在 carrier から label を作る」方向へ進める。

## 9. 総括

今回の進展を短くまとめるとこうじゃ。

```text
f = id:
  value-map API の control route

f = petalNthPrimeLabel:
  genuine prime-valued injective label route

次:
  f = carrierAnchorOf:
    DkMath 本命の GN carrier label route
```

今回で確認できたことは、

```text
住所値 mOf
  -> injective prime label
  -> label noncollision
  -> GN log-capacity route
```

の配線じゃ。

ただし、まだ

```text
住所値 mOf
  -> GN を割る prime carrier
```

は別問題。

したがって次の本命は明確じゃ。

```text
Petal / GN geometry から
carrierAnchorOf(m)
または carrier label data
を作る
```

ここが通れば、`nthPrime` route は「標準実験」、`carrierAnchorOf` route は「DkMath 実戦 route」になる。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/NumberTheory/docs/BinomialPrimeWeighted/FLGNB-PetalRoadmap.md b/lean/dk_math/DkMath/NumberTheory/docs/BinomialPrimeWeighted/FLGNB-PetalRoadmap.md
index 74921cfa..2e86d35a 100644
--- a/lean/dk_math/DkMath/NumberTheory/docs/BinomialPrimeWeighted/FLGNB-PetalRoadmap.md
+++ b/lean/dk_math/DkMath/NumberTheory/docs/BinomialPrimeWeighted/FLGNB-PetalRoadmap.md
@@ -1862,6 +1862,25 @@ petalNoLiftPrimeChannelFamily_logSubProbability_GN_of_outer_value_self
 This is a control theorem for the wrapper.  It does not turn arbitrary Petal
 values into prime-channel labels.
 
+The standard prime-enumeration experiment is implemented through
+`petalNthPrimeLabel`, defined as a Petal-facing alias for `Nat.nth Nat.Prime`:
+
+```text
+petalNthPrimeLabel
+petalNthPrimeLabel_prime
+petalNthPrimeLabel_injective
+petalNthPrimeLabel_eq_imp_eq
+petalCarrierLabelCompatibleOn_outer_of_nthPrime_value_map
+petalCarrierLabelNoncollisionOn_outer_of_nthPrime_value_map
+petalNthPrimeLabel_natPrimeValuedOn
+petalPrimeChannelFamily_multiplicityBudget_GN_of_outer_nthPrime_value_map
+petalPrimeChannelFamily_logSubProbability_GN_of_outer_nthPrime_value_map
+petalNoLiftPrimeChannelFamily_logSubProbability_GN_of_outer_nthPrime_value_map
+```
+
+This confirms that the route works with a genuine prime-valued injective label
+map.  It does not prove that the nth prime divides a GN surface.
+
 ### Step 7: Refactor imports gradually
 
 Status:
diff --git a/lean/dk_math/DkMath/Petal/ErdosBridge.lean b/lean/dk_math/DkMath/Petal/ErdosBridge.lean
index 591a0f61..95f9c5c1 100644
--- a/lean/dk_math/DkMath/Petal/ErdosBridge.lean
+++ b/lean/dk_math/DkMath/Petal/ErdosBridge.lean
@@ -7,6 +7,7 @@ Authors: D. and Wise Wolf.
 import DkMath.Petal.Address
 import DkMath.Petal.BezoutBridge
 import DkMath.NumberTheory.PrimitiveSet.ValuationBudget
+import Mathlib.NumberTheory.PrimeCounting
 
 #print "file: DkMath.Petal.ErdosBridge"
 
@@ -88,6 +89,16 @@ It is deliberately weaker than asking the whole `GN` value to be squarefree.
 def PetalNoLiftPrimeChannel (d x u q : ℕ) : Prop :=
   PetalPrimeChannel d x u q ∧ ¬ q ^ 2 ∣ GN d x u
 
+/--
+The standard Mathlib prime enumeration, exposed under Petal naming.
+
+This is an experimental label map for the outer-address route.  It supplies
+prime labels and injectivity, but it does not say that the chosen prime divides
+any particular GN surface.
+-/
+noncomputable def petalNthPrimeLabel (m : Nat) : Nat :=
+  Nat.nth Nat.Prime m
+
 /--
 Carrier-label noncollision for a finite Petal channel family.
 
@@ -158,6 +169,26 @@ theorem petalNoLiftPrimeChannel_noLift
     ¬ q ^ 2 ∣ GN d x u :=
   h.2
 
+/-- The Petal nth-prime label is prime. -/
+theorem petalNthPrimeLabel_prime
+    (m : Nat) :
+    Nat.Prime (petalNthPrimeLabel m) := by
+  unfold petalNthPrimeLabel
+  exact Nat.prime_nth_prime m
+
+/-- The Petal nth-prime label map is injective. -/
+theorem petalNthPrimeLabel_injective :
+    Function.Injective petalNthPrimeLabel := by
+  unfold petalNthPrimeLabel
+  exact Nat.nth_injective Nat.infinite_setOf_prime
+
+/-- Equal Petal nth-prime labels recover equal source values. -/
+theorem petalNthPrimeLabel_eq_imp_eq
+    {m n : Nat}
+    (h : petalNthPrimeLabel m = petalNthPrimeLabel n) :
+    m = n :=
+  petalNthPrimeLabel_injective h
+
 /--
 Unfold carrier-label noncollision to the underlying `PrimitiveSet`
 duplicate-free condition.
@@ -396,6 +427,64 @@ theorem petalCarrierLabelNoncollisionOn_outer_of_value_self
     (fun _ _ => rfl)
     (fun _ _ _ _ h => h)
 
+/--
+Outer-address label compatibility for the nth-prime label map.
+
+This is the first standard prime-enumeration experiment:
+`qOf i = petalNthPrimeLabel (mOf i)`.  It supplies label recovery from the
+injectivity of Mathlib's prime enumeration.
+-/
+theorem petalCarrierLabelCompatibleOn_outer_of_nthPrime_value_map
+    {ι : Type _}
+    (I : Finset ι)
+    (n lap : Nat)
+    (mOf qOf : ι → Nat)
+    (hq :
+      ∀ i, i ∈ I → qOf i = petalNthPrimeLabel (mOf i)) :
+    PetalCarrierLabelCompatibleOn I
+      (fun i => outerPetalAddress n lap (mOf i)) qOf :=
+  petalCarrierLabelCompatibleOn_outer_of_value_map_injective
+    I n lap mOf qOf petalNthPrimeLabel hq
+    (fun _ _ _ _ h => petalNthPrimeLabel_eq_imp_eq h)
+
+/--
+Outer-address noncollision for nth-prime labels.
+
+The nth-prime map gives prime labels and label recovery.  This theorem only
+uses the recovery part; channel divisibility is still handled by separate
+PetalPrimeChannel hypotheses in the log-capacity route.
+-/
+theorem petalCarrierLabelNoncollisionOn_outer_of_nthPrime_value_map
+    {ι : Type _}
+    (I : Finset ι)
+    (n lap : Nat)
+    (mOf qOf : ι → Nat)
+    (hm : ∀ i, i ∈ I → 1 ≤ mOf i)
+    (hminj : Set.InjOn mOf ↑I)
+    (hq :
+      ∀ i, i ∈ I → qOf i = petalNthPrimeLabel (mOf i)) :
+    PetalCarrierLabelNoncollisionOn I qOf :=
+  petalCarrierLabelNoncollisionOn_outer_of_value_map_injective
+    I n lap mOf qOf petalNthPrimeLabel hm hminj hq
+    (fun _ _ _ _ h => petalNthPrimeLabel_eq_imp_eq h)
+
+/--
+The nth-prime label map gives a prime-valued family.
+
+This records the part of the experiment that really is supplied by
+`petalNthPrimeLabel`: primality of the selected labels.
+-/
+theorem petalNthPrimeLabel_natPrimeValuedOn
+    {ι : Type _}
+    (I : Finset ι)
+    (mOf qOf : ι → Nat)
+    (hq :
+      ∀ i, i ∈ I → qOf i = petalNthPrimeLabel (mOf i)) :
+    DkMath.NumberTheory.PrimitiveSet.NatPrimeValuedOn I qOf := by
+  intro i hi
+  rw [hq i hi]
+  exact petalNthPrimeLabel_prime (mOf i)
+
 /--
 PrimitiveBeam witnesses enter the Erdos bridge as Petal prime channels.
 -/
@@ -916,6 +1005,64 @@ theorem petalPrimeChannelFamily_logSubProbability_GN_of_outer_value_self
       I n lap mOf hm hminj)
     hcarrier
 
+/--
+Nth-prime label form of the outer-address GN multiplicity-budget route.
+
+The label map supplies prime labels and noncollision.  The theorem still
+requires explicit `PetalPrimeChannel` hypotheses, because being the nth prime
+does not imply divisibility of the observed GN surface.
+-/
+theorem petalPrimeChannelFamily_multiplicityBudget_GN_of_outer_nthPrime_value_map
+    {ι : Type _}
+    (I : Finset ι)
+    (d x u : ℕ)
+    (n lap : Nat)
+    (mOf qOf : ι → Nat)
+    (hGN0 : GN d x u ≠ 0)
+    (hm : ∀ i, i ∈ I → 1 ≤ mOf i)
+    (hminj : Set.InjOn mOf ↑I)
+    (hq :
+      ∀ i, i ∈ I → qOf i = petalNthPrimeLabel (mOf i))
+    (hcarrier :
+      ∀ i, i ∈ I → PetalPrimeChannel d x u (qOf i)) :
+    DkMath.NumberTheory.PrimitiveSet.NatBaseMultiplicityBudgetOn
+      I qOf (GN d x u) :=
+  petalPrimeChannelFamily_multiplicityBudget_GN_of_labelNoncollision
+    I d x u qOf hGN0
+    (petalCarrierLabelNoncollisionOn_outer_of_nthPrime_value_map
+      I n lap mOf qOf hm hminj hq)
+    hcarrier
+
+/--
+Nth-prime label form of the outer-address GN log-capacity route.
+
+This is the standard prime-enumeration experiment for the value-map API.
+It proves that the route works with a genuine prime-valued injective label map,
+while keeping the actual GN-carrier condition explicit.
+-/
+theorem petalPrimeChannelFamily_logSubProbability_GN_of_outer_nthPrime_value_map
+    {ι : Type _}
+    (I : Finset ι)
+    (d x u : ℕ)
+    (n lap : Nat)
+    (mOf qOf : ι → Nat)
+    (hGN : 1 < GN d x u)
+    (hm : ∀ i, i ∈ I → 1 ≤ mOf i)
+    (hminj : Set.InjOn mOf ↑I)
+    (hq :
+      ∀ i, i ∈ I → qOf i = petalNthPrimeLabel (mOf i))
+    (hcarrier :
+      ∀ i, i ∈ I → PetalPrimeChannel d x u (qOf i)) :
+    (DkMath.NumberTheory.PrimitiveSet.realLogRatioWeightProvider I qOf (GN d x u)
+      (petalPrimeChannel_realLogNonnegOn
+        I (fun _ => d) (fun _ => x) (fun _ => u) qOf hcarrier)
+      hGN).SubProbability :=
+  petalPrimeChannelFamily_logSubProbability_GN_of_labelNoncollision
+    I d x u qOf hGN
+    (petalCarrierLabelNoncollisionOn_outer_of_nthPrime_value_map
+      I n lap mOf qOf hm hminj hq)
+    hcarrier
+
 /--
 Local no-lift makes the observed GN surface nonzero.
 
@@ -1155,6 +1302,37 @@ theorem petalNoLiftPrimeChannelFamily_logSubProbability_GN_of_outer_value_self
       I n lap mOf hm hminj)
     hcarrier
 
+/--
+Nth-prime label form of the outer-address no-lift GN log-capacity route.
+
+The nth-prime map supplies a standard injective prime-valued label family.
+No-lift and GN divisibility remain explicit hypotheses through
+`PetalNoLiftPrimeChannel`.
+-/
+theorem petalNoLiftPrimeChannelFamily_logSubProbability_GN_of_outer_nthPrime_value_map
+    {ι : Type _}
+    (I : Finset ι)
+    (d x u : ℕ)
+    (n lap : Nat)
+    (mOf qOf : ι → Nat)
+    (hGN : 1 < GN d x u)
+    (hm : ∀ i, i ∈ I → 1 ≤ mOf i)
+    (hminj : Set.InjOn mOf ↑I)
+    (hq :
+      ∀ i, i ∈ I → qOf i = petalNthPrimeLabel (mOf i))
+    (hcarrier :
+      ∀ i, i ∈ I → PetalNoLiftPrimeChannel d x u (qOf i)) :
+    (DkMath.NumberTheory.PrimitiveSet.realLogRatioWeightProvider I qOf (GN d x u)
+      (petalPrimeChannel_realLogNonnegOn
+        I (fun _ => d) (fun _ => x) (fun _ => u) qOf
+        (fun i hi => (hcarrier i hi).1))
+      hGN).SubProbability :=
+  petalNoLiftPrimeChannelFamily_logSubProbability_GN_of_labelNoncollision
+    I d x u qOf hGN
+    (petalCarrierLabelNoncollisionOn_outer_of_nthPrime_value_map
+      I n lap mOf qOf hm hminj hq)
+    hcarrier
+
 /--
 A single Petal prime channel fits into the Erdos multiplicity budget of its own
 nonzero GN surface.
diff --git a/lean/dk_math/DkMath/Petal/docs/Petal-ErdosBridge-ExperimentPlan.md b/lean/dk_math/DkMath/Petal/docs/Petal-ErdosBridge-ExperimentPlan.md
index 4b4f1fce..f4a72cb5 100644
--- a/lean/dk_math/DkMath/Petal/docs/Petal-ErdosBridge-ExperimentPlan.md
+++ b/lean/dk_math/DkMath/Petal/docs/Petal-ErdosBridge-ExperimentPlan.md
@@ -652,5 +652,24 @@ This checks the value-map API without importing a prime enumeration or a choice
 function.  It still assumes the selected values are already valid
 PetalPrimeChannel / NoLift labels when the log-capacity theorem is applied.
 
+The next experiment uses Mathlib's standard prime enumeration through the
+Petal-facing alias `petalNthPrimeLabel`:
+
+```text
+petalNthPrimeLabel
+petalNthPrimeLabel_prime
+petalNthPrimeLabel_injective
+petalNthPrimeLabel_eq_imp_eq
+petalCarrierLabelCompatibleOn_outer_of_nthPrime_value_map
+petalCarrierLabelNoncollisionOn_outer_of_nthPrime_value_map
+petalNthPrimeLabel_natPrimeValuedOn
+petalPrimeChannelFamily_multiplicityBudget_GN_of_outer_nthPrime_value_map
+petalPrimeChannelFamily_logSubProbability_GN_of_outer_nthPrime_value_map
+petalNoLiftPrimeChannelFamily_logSubProbability_GN_of_outer_nthPrime_value_map
+```
+
+This verifies the route for a genuine injective prime-valued label map.  The
+GN carrier and no-lift facts remain separate hypotheses.
+
 That is the point where Petal may start producing genuinely strong conditions
 useful for Zsigmondy, FLT, and ABC.
diff --git a/lean/dk_math/DkMath/Petal/docs/Petal-Overview.md b/lean/dk_math/DkMath/Petal/docs/Petal-Overview.md
index 343297cc..5f6fa7da 100644
--- a/lean/dk_math/DkMath/Petal/docs/Petal-Overview.md
+++ b/lean/dk_math/DkMath/Petal/docs/Petal-Overview.md
@@ -806,6 +806,25 @@ This is a toy control route.  It says that if the selected values themselves
 are already assumed to be prime-channel labels, then the outer-address
 noncollision machinery composes correctly.
 
+The standard prime-enumeration experiment is also implemented through
+`petalNthPrimeLabel`, a Petal-facing alias for `Nat.nth Nat.Prime`:
+
+```text
+petalNthPrimeLabel
+petalNthPrimeLabel_prime
+petalNthPrimeLabel_injective
+petalNthPrimeLabel_eq_imp_eq
+petalCarrierLabelCompatibleOn_outer_of_nthPrime_value_map
+petalCarrierLabelNoncollisionOn_outer_of_nthPrime_value_map
+petalNthPrimeLabel_natPrimeValuedOn
+petalPrimeChannelFamily_multiplicityBudget_GN_of_outer_nthPrime_value_map
+petalPrimeChannelFamily_logSubProbability_GN_of_outer_nthPrime_value_map
+petalNoLiftPrimeChannelFamily_logSubProbability_GN_of_outer_nthPrime_value_map
+```
+
+This route supplies real prime labels and label recovery.  It still does not
+say that those primes divide the chosen GN surface.
+
 ## What This Does Not Claim Yet
 
 The package does not yet prove a standard primorial theorem using a concrete
````
`````
