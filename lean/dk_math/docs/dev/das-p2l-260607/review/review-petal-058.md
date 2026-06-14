# Git diff / Report / Review

## Upd: Petal.ErdosBridge

gch: 9c05a40abf81f9ed9ed0c459530dc315157413d2

## Report

進めました。今回は outer address 側で、`qOf i = qOf j -> mOf i = mOf j` という「ラベルが値を決める」条件から compatibility を供給するルートを固定しました。

追加した主な theorem は以下です。

- `petalCarrierLabelCompatibleOn_outer_of_label_eq_imp_value_eq`
- `petalCarrierLabelNoncollisionOn_outer_of_value_injOn`
- `petalPrimeChannelFamily_multiplicityBudget_GN_of_outer_value_injOn`
- `petalPrimeChannelFamily_logSubProbability_GN_of_outer_value_injOn`
- `petalNoLiftPrimeChannelFamily_logSubProbability_GN_of_outer_value_injOn`

これで outer address の `mOf` が injective で、prime label `qOf` が value を逆向きに決めるなら、GN 上の multiplicity budget / log-capacity route まで直接つながります。

ドキュメントも同期しました。

- `DkMath/Petal/docs/Petal-Overview.md`
- `DkMath/Petal/docs/Petal-ErdosBridge-ExperimentPlan.md`
- `DkMath/NumberTheory/docs/BinomialPrimeWeighted/FLGNB-PetalRoadmap.md`

検証は通っています。

```text
lake build DkMath.Petal
git diff --check ...
```

次の自然な地点は、レビューにもあった `qOf = f (mOf i)` 型の concrete carrier construction です。
ここまで来ると「住所値から prime label を作る」実用ルートに入れます。

## Review

うむ、ここは言葉が少し誤解を招きやすいところじゃな。

**「住所値から prime label を作る」** というのは、必ずしも

```text id="y5h9z7"
mOf i から計算式で素数 qOf i を生成する
```

という意味だけではない。
今回 Lean で固定した実際の条件は、むしろ逆向きじゃ。

```text id="ljcipc"
qOf i = qOf j なら mOf i = mOf j
```

つまり、**prime label が同じなら、その元になった住所値も同じだと分かる**、という条件じゃ。今回追加された `petalCarrierLabelCompatibleOn_outer_of_label_eq_imp_value_eq` は、まさにこの「ラベルが値を決める」条件から outer address との compatibility を供給する theorem じゃ。

## 1. 登場人物を分ける

いまの構造には 3 つの値がある。

```text id="z8s36c"
i       : family の index
mOf i   : Petal outer address を作る元の one-based value
addrOf i: outerPetalAddress n lap (mOf i)
qOf i   : PetalPrimeChannel / NoLift channel の prime label
```

関係はこう。

```text id="qgn7vw"
mOf i
  -> outerPetalAddress n lap (mOf i)
  -> addrOf i
```

これは住所側。

一方、

```text id="krcbfc"
qOf i
```

は、その index に対応する selected prime channel のラベルじゃ。
たとえば Zsigmondy primitive divisor 由来の (q)、PetalPrimeChannel の anchor (q)、NoLift channel の prime (q) など。

## 2. 今回分かったこと

まず、`outerPetalAddress` は復元性を持つ。

```text id="97k8k1"
outerPetalAddress n lap m₁ = outerPetalAddress n lap m₂
  -> m₁ = m₂
```

ただし (1 \le m₁), (1 \le m₂) の valid one-based value 条件つき。
これが `outerPetalAddress_eq_value_eq` じゃ。

だから、

```text id="s6gtqp"
mOf が injective
  -> outerPetalAddress n lap (mOf i) も noncolliding
```

が出る。これが `petalAddressNoncollisionOn_outer_of_value_injOn`。

ここまでは「値から住所を作る」話。

## 3. では prime label はどこから来るのか

prime label (qOf i) は、住所だけから自動的に湧くわけではない。

本当はこういう carrier construction が必要じゃ。

```text id="x6msmf"
mOf i に対応する Petal / GN 観測点がある
その観測点に prime channel qOf i が載っている
つまり PetalPrimeChannel d x u (qOf i)
```

この (qOf i) は、たとえば primitive divisor や GN carrier の定理から得る。
つまり「住所値から prime label を作る」とは、より正確には、

```text id="rt2ilr"
住所値 mOf i に対応する GN/Petal 観測から
prime carrier label qOf i を選ぶ
```

という意味じゃ。

ただし、今回の theorem はそこまで具体的な生成方法を仮定していない。
必要としているのは、次の性質だけ。

```text id="sfqvke"
qOf i = qOf j
  -> mOf i = mOf j
```

つまり、同じ prime label が出たなら、それは同じ住所値から来たものだ、と言えること。

## 4. なぜこの向きで十分なのか

欲しいのは最終的に

```text id="sp6uv8"
qOf i ≠ qOf j
```

つまり prime label の非衝突じゃ。

そのために、今はこういう論理を使っている。

```text id="7r4gx9"
i ≠ j
mOf が injective
  -> mOf i ≠ mOf j

もし qOf i = qOf j なら
  -> mOf i = mOf j

矛盾
  -> qOf i ≠ qOf j
```

だから必要なのは、

```text id="6bma51"
mOf injective
```

と

```text id="r1cbzj"
qOf equality implies mOf equality
```

の 2 つ。

これで `PetalCarrierLabelNoncollisionOn I qOf` が出る。
今回の diff では、この流れを `petalCarrierLabelNoncollisionOn_outer_of_value_injOn` として固定しておる。

## 5. 「qOf = f(mOf i)」ならどうなるか

もし本当に

```text id="0if2y7"
qOf i = f (mOf i)
```

という形で prime label を作るなら、必要なのは (f) が injective であることじゃ。

```text id="a9a984"
f (mOf i) = f (mOf j)
  -> mOf i = mOf j
```

これがあれば、

```text id="h8ssx0"
qOf i = qOf j
  -> mOf i = mOf j
```

が出る。

ただし、ここで注意。

`f` は何でもよいわけではない。
`qOf i` は最終的に `PetalPrimeChannel d x u (qOf i)` を満たす必要がある。つまり prime label でなければならない。

だから実用的には、

```text id="d272xv"
mOf i
  -> その位置で観測される primitive prime / carrier prime を選ぶ
  -> qOf i
```

という construction が欲しい。

## 6. 直感的な例

たとえば、住所値が

```text id="qswg8x"
mOf i = 5, 8, 13
```

で、それぞれに対応する prime label が

```text id="ug19vn"
qOf i = 7, 11, 19
```

だったとする。

このとき、もし同じ prime label が出たら同じ住所値だった、と言えるならよい。

だが、

```text id="bsyyra"
m = 5 -> q = 7
m = 8 -> q = 7
```

のように、異なる住所値が同じ prime label を共有するなら、label noncollision は壊れる。

なので `PetalCarrierLabelCompatibleOn` は、

```text id="aezo86"
住所が違えば label も違う
```

あるいは同値に近い形で、

```text id="ya7so4"
label が同じなら住所値も同じ
```

を要求している。

## 7. 現在の状況

今の到達点はこう。

```text id="lc96z9"
outerPetalAddress
  -> value reconstruction は通った

mOf injective
  -> address noncollision は通った

qOf equality -> mOf equality
  -> label compatibility は通った

mOf injective
  + qOf equality -> mOf equality
  -> label noncollision は通った

label noncollision
  + PetalPrimeChannel family
  -> finite GN log-capacity route も通った
```

今回の report では、`petalPrimeChannelFamily_logSubProbability_GN_of_outer_value_injOn` と NoLift 版まで実装済みになっておる。

## 8. まだ残る本命

残るのはこれじゃ。

```text id="atx1jg"
実際の Petal / GN carrier construction から
qOf i = qOf j -> mOf i = mOf j
をどう出すか
```

つまり、「prime label が住所値を決める」ことを、どの具体構造から出すか。

候補は複数ある。

```text id="fd8u0o"
1. qOf i を injective な prime enumeration から作る
2. qOf i を primitive divisor として選び、その primitive 性から値を復元する
3. qOf i を GN carrier の anchor として選び、carrier uniqueness を証明する
4. qOf i を Petal address に紐づく canonical prime label として定義する
```

このうち最も安全なのは 1 か 4。
数論的に強いのは 2 と 3。

## 9. まとめ

「住所値から prime label を作る」とは、厳密にはこうじゃ。

```text id="qfcwp3"
住所値 mOf i に Petal/GN 上の prime carrier qOf i を割り当てる。
その割り当ては、少なくとも同じ qOf が出たら同じ mOf だったと分かる程度に、衝突しない必要がある。
```

Lean 上で必要な条件はこれ。

```text id="o4z5kd"
qOf i = qOf j -> mOf i = mOf j
```

これは「prime label が住所値を決める」という意味であって、必ずしも「住所値だけから素数を計算して生成する」という意味ではない。

現在の道は、かなり綺麗に分解されている。

```text id="m7my0y"
mOf injective
  -> outer address noncollision

qOf equality -> mOf equality
  -> address-to-label compatibility

この二つから
  -> carrier-label noncollision

そして
  -> GN multiplicity budget
  -> finite log-capacity route
```

だから次の本命は、

```text id="q4mudk"
具体的な carrier construction で
qOf i = qOf j -> mOf i = mOf j
を出せるか
```

じゃな。
ここが通れば、「住所値から prime label を作る」という言葉が、比喩ではなく DkMath の実装ルートになる。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/NumberTheory/docs/BinomialPrimeWeighted/FLGNB-PetalRoadmap.md b/lean/dk_math/DkMath/NumberTheory/docs/BinomialPrimeWeighted/FLGNB-PetalRoadmap.md
index 1768ef43..7e691db9 100644
--- a/lean/dk_math/DkMath/NumberTheory/docs/BinomialPrimeWeighted/FLGNB-PetalRoadmap.md
+++ b/lean/dk_math/DkMath/NumberTheory/docs/BinomialPrimeWeighted/FLGNB-PetalRoadmap.md
@@ -1807,6 +1807,23 @@ contrapositive helper:
 petalCarrierLabelCompatibleOn_of_label_eq_imp_address_eq
 ```
 
+For outer addresses, the compatibility side can now be supplied by a value
+determination condition:
+
+```text
+qOf i = qOf j -> mOf i = mOf j
+```
+
+Implemented theorem names:
+
+```text
+petalCarrierLabelCompatibleOn_outer_of_label_eq_imp_value_eq
+petalCarrierLabelNoncollisionOn_outer_of_value_injOn
+petalPrimeChannelFamily_multiplicityBudget_GN_of_outer_value_injOn
+petalPrimeChannelFamily_logSubProbability_GN_of_outer_value_injOn
+petalNoLiftPrimeChannelFamily_logSubProbability_GN_of_outer_value_injOn
+```
+
 ### Step 7: Refactor imports gradually
 
 Status:
diff --git a/lean/dk_math/DkMath/Petal/ErdosBridge.lean b/lean/dk_math/DkMath/Petal/ErdosBridge.lean
index 7925a94a..beb8ee28 100644
--- a/lean/dk_math/DkMath/Petal/ErdosBridge.lean
+++ b/lean/dk_math/DkMath/Petal/ErdosBridge.lean
@@ -273,6 +273,49 @@ theorem petalAddressNoncollisionOn_outer_of_value_injOn
   exact hinj hi hj
     (outerPetalAddress_eq_value_eq (hm i hi) (hm j hj) haddr)
 
+/--
+Outer-address label compatibility from value determination by labels.
+
+If equality of selected labels forces equality of the underlying one-based
+values, then those labels are compatible with the corresponding outer Petal
+addresses.
+-/
+theorem petalCarrierLabelCompatibleOn_outer_of_label_eq_imp_value_eq
+    {ι : Type _}
+    (I : Finset ι)
+    (n lap : Nat)
+    (mOf qOf : ι → Nat)
+    (hlabel :
+      ∀ i, i ∈ I → ∀ j, j ∈ I → qOf i = qOf j → mOf i = mOf j) :
+    PetalCarrierLabelCompatibleOn I
+      (fun i => outerPetalAddress n lap (mOf i)) qOf := by
+  apply petalCarrierLabelCompatibleOn_of_label_eq_imp_address_eq
+  intro i hi j hj hij
+  rw [hlabel i hi j hj hij]
+
+/--
+Outer-address value conditions supply carrier-label noncollision.
+
+This is the first fully outer-address-facing noncollision theorem: injective
+values give address noncollision, and labels that determine values give
+address-to-label compatibility.
+-/
+theorem petalCarrierLabelNoncollisionOn_outer_of_value_injOn
+    {ι : Type _}
+    (I : Finset ι)
+    (n lap : Nat)
+    (mOf qOf : ι → Nat)
+    (hm : ∀ i, i ∈ I → 1 ≤ mOf i)
+    (hminj : Set.InjOn mOf ↑I)
+    (hlabel :
+      ∀ i, i ∈ I → ∀ j, j ∈ I → qOf i = qOf j → mOf i = mOf j) :
+    PetalCarrierLabelNoncollisionOn I qOf :=
+  petalAddressNoncollision_labelNoncollision I
+    (fun i => outerPetalAddress n lap (mOf i)) qOf
+    (petalAddressNoncollisionOn_outer_of_value_injOn I n lap mOf hm hminj)
+    (petalCarrierLabelCompatibleOn_outer_of_label_eq_imp_value_eq
+      I n lap mOf qOf hlabel)
+
 /--
 PrimitiveBeam witnesses enter the Erdos bridge as Petal prime channels.
 -/
@@ -614,6 +657,63 @@ theorem petalPrimeChannelFamily_logSubProbability_GN_of_addressNoncollision
     (petalAddressNoncollision_labelNoncollision I addrOf qOf haddr hcompat)
     hcarrier
 
+/--
+Outer-address value conditions supply an Erdos multiplicity budget on one GN
+surface.
+
+This is the multiplicity-budget form of the outer-address route.
+-/
+theorem petalPrimeChannelFamily_multiplicityBudget_GN_of_outer_value_injOn
+    {ι : Type _}
+    (I : Finset ι)
+    (d x u : ℕ)
+    (n lap : Nat)
+    (mOf qOf : ι → Nat)
+    (hGN0 : GN d x u ≠ 0)
+    (hm : ∀ i, i ∈ I → 1 ≤ mOf i)
+    (hminj : Set.InjOn mOf ↑I)
+    (hlabel :
+      ∀ i, i ∈ I → ∀ j, j ∈ I → qOf i = qOf j → mOf i = mOf j)
+    (hcarrier :
+      ∀ i, i ∈ I → PetalPrimeChannel d x u (qOf i)) :
+    DkMath.NumberTheory.PrimitiveSet.NatBaseMultiplicityBudgetOn
+      I qOf (GN d x u) :=
+  petalPrimeChannelFamily_multiplicityBudget_GN_of_labelNoncollision
+    I d x u qOf hGN0
+    (petalCarrierLabelNoncollisionOn_outer_of_value_injOn
+      I n lap mOf qOf hm hminj hlabel)
+    hcarrier
+
+/--
+Outer-address value conditions feed Petal prime channels into the finite GN
+log-capacity route.
+
+The hypotheses say that the selected one-based values are noncolliding and that
+the selected prime labels determine those values.
+-/
+theorem petalPrimeChannelFamily_logSubProbability_GN_of_outer_value_injOn
+    {ι : Type _}
+    (I : Finset ι)
+    (d x u : ℕ)
+    (n lap : Nat)
+    (mOf qOf : ι → Nat)
+    (hGN : 1 < GN d x u)
+    (hm : ∀ i, i ∈ I → 1 ≤ mOf i)
+    (hminj : Set.InjOn mOf ↑I)
+    (hlabel :
+      ∀ i, i ∈ I → ∀ j, j ∈ I → qOf i = qOf j → mOf i = mOf j)
+    (hcarrier :
+      ∀ i, i ∈ I → PetalPrimeChannel d x u (qOf i)) :
+    (DkMath.NumberTheory.PrimitiveSet.realLogRatioWeightProvider I qOf (GN d x u)
+      (petalPrimeChannel_realLogNonnegOn
+        I (fun _ => d) (fun _ => x) (fun _ => u) qOf hcarrier)
+      hGN).SubProbability :=
+  petalPrimeChannelFamily_logSubProbability_GN_of_labelNoncollision
+    I d x u qOf hGN
+    (petalCarrierLabelNoncollisionOn_outer_of_value_injOn
+      I n lap mOf qOf hm hminj hlabel)
+    hcarrier
+
 /--
 Local no-lift makes the observed GN surface nonzero.
 
@@ -759,6 +859,37 @@ theorem petalNoLiftPrimeChannelFamily_logSubProbability_GN_of_addressNoncollisio
     (petalAddressNoncollision_labelNoncollision I addrOf qOf haddr hcompat)
     hcarrier
 
+/--
+Outer-address value conditions feed no-lift Petal channels into the finite GN
+log-capacity route.
+
+This is the no-lift version of
+`petalPrimeChannelFamily_logSubProbability_GN_of_outer_value_injOn`.
+-/
+theorem petalNoLiftPrimeChannelFamily_logSubProbability_GN_of_outer_value_injOn
+    {ι : Type _}
+    (I : Finset ι)
+    (d x u : ℕ)
+    (n lap : Nat)
+    (mOf qOf : ι → Nat)
+    (hGN : 1 < GN d x u)
+    (hm : ∀ i, i ∈ I → 1 ≤ mOf i)
+    (hminj : Set.InjOn mOf ↑I)
+    (hlabel :
+      ∀ i, i ∈ I → ∀ j, j ∈ I → qOf i = qOf j → mOf i = mOf j)
+    (hcarrier :
+      ∀ i, i ∈ I → PetalNoLiftPrimeChannel d x u (qOf i)) :
+    (DkMath.NumberTheory.PrimitiveSet.realLogRatioWeightProvider I qOf (GN d x u)
+      (petalPrimeChannel_realLogNonnegOn
+        I (fun _ => d) (fun _ => x) (fun _ => u) qOf
+        (fun i hi => (hcarrier i hi).1))
+      hGN).SubProbability :=
+  petalNoLiftPrimeChannelFamily_logSubProbability_GN_of_labelNoncollision
+    I d x u qOf hGN
+    (petalCarrierLabelNoncollisionOn_outer_of_value_injOn
+      I n lap mOf qOf hm hminj hlabel)
+    hcarrier
+
 /--
 A single Petal prime channel fits into the Erdos multiplicity budget of its own
 nonzero GN surface.
diff --git a/lean/dk_math/DkMath/Petal/docs/Petal-ErdosBridge-ExperimentPlan.md b/lean/dk_math/DkMath/Petal/docs/Petal-ErdosBridge-ExperimentPlan.md
index 1ca83e55..af8e44dc 100644
--- a/lean/dk_math/DkMath/Petal/docs/Petal-ErdosBridge-ExperimentPlan.md
+++ b/lean/dk_math/DkMath/Petal/docs/Petal-ErdosBridge-ExperimentPlan.md
@@ -591,5 +591,26 @@ meaningful `PetalCarrierLabelCompatibleOn` assumptions from the actual carrier
 or label construction, rather than keeping compatibility as a permanent raw
 hypothesis.
 
+The first outer-address compatibility supply theorem is now implemented:
+
+```text
+petalCarrierLabelCompatibleOn_outer_of_label_eq_imp_value_eq
+```
+
+It uses the condition:
+
+```text
+qOf i = qOf j -> mOf i = mOf j
+```
+
+Together with value injectivity, this gives the outer-address log-capacity
+route:
+
+```text
+petalCarrierLabelNoncollisionOn_outer_of_value_injOn
+petalPrimeChannelFamily_logSubProbability_GN_of_outer_value_injOn
+petalNoLiftPrimeChannelFamily_logSubProbability_GN_of_outer_value_injOn
+```
+
 That is the point where Petal may start producing genuinely strong conditions
 useful for Zsigmondy, FLT, and ABC.
diff --git a/lean/dk_math/DkMath/Petal/docs/Petal-Overview.md b/lean/dk_math/DkMath/Petal/docs/Petal-Overview.md
index 26f8e9b8..bcd621b2 100644
--- a/lean/dk_math/DkMath/Petal/docs/Petal-Overview.md
+++ b/lean/dk_math/DkMath/Petal/docs/Petal-Overview.md
@@ -755,6 +755,22 @@ contrapositive criterion:
 petalCarrierLabelCompatibleOn_of_label_eq_imp_address_eq
 ```
 
+For outer addresses, compatibility can now be supplied from value determination:
+
+```text
+petalCarrierLabelCompatibleOn_outer_of_label_eq_imp_value_eq
+```
+
+Combining value injectivity with value determination by labels gives the
+outer-address noncollision route directly:
+
+```text
+petalCarrierLabelNoncollisionOn_outer_of_value_injOn
+petalPrimeChannelFamily_multiplicityBudget_GN_of_outer_value_injOn
+petalPrimeChannelFamily_logSubProbability_GN_of_outer_value_injOn
+petalNoLiftPrimeChannelFamily_logSubProbability_GN_of_outer_value_injOn
+```
+
 ## What This Does Not Claim Yet
 
 The package does not yet prove a standard primorial theorem using a concrete
````
`````
