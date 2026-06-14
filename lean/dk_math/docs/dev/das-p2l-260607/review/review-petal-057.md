# Git diff / Report / Review

## Upd: Petal.ErdosBridge, Address

gch: 48b84c75fd096f036deb7c6423fe282c0ffb4aff

## Report

進めました。今回は「具体 Petal geometry 側」の最初の供給口として、`outerPetalAddress` から `PetalAddressNoncollisionOn` を作る道を固定しました。

追加した Lean 側の中心は以下です。

- [Address.lean](/lean/dk_math/DkMath/Petal/Address.lean:376)
  - `outerPetalAddress_eq_value_eq`
  - 同じ `outerPetalAddress` を持つ valid one-based value は元の値も等しい、という復元補題

- [ErdosBridge.lean](/lean/dk_math/DkMath/Petal/ErdosBridge.lean:227)
  - `petalAddressNoncollisionOn_of_injOn`
  - `petalCarrierLabelCompatibleOn_of_label_eq_imp_address_eq`
  - `petalAddressNoncollisionOn_outer_of_value_injOn`

これで次の道が通りました。

```text
mOf が selected index 上で injective
  + 1 <= mOf i
  -> outerPetalAddress n lap (mOf i) が noncolliding
  -> PetalAddressNoncollisionOn
```

docs も同期しています。

- [Petal-Overview.md](/lean/dk_math/DkMath/Petal/docs/Petal-Overview.md:725)
- [Petal-ErdosBridge-ExperimentPlan.md](/lean/dk_math/DkMath/Petal/docs/Petal-ErdosBridge-ExperimentPlan.md:580)
- [FLGNB-PetalRoadmap.md](/lean/dk_math/DkMath/NumberTheory/docs/BinomialPrimeWeighted/FLGNB-PetalRoadmap.md:1779)

検証:

- `lake build DkMath.Petal.ErdosBridge` 成功
- `lake build DkMath.Petal` 成功
- `git diff --check` 成功

次の本命は `PetalCarrierLabelCompatibleOn` を、実際の carrier/label construction からどう供給するかです。

## Review

うむ。これは **進展あり** じゃ。
しかも、前回までの「抽象 bridge」から、ついに **具体 Petal geometry 側の供給口** に一歩入った。

今回の核心はこれじゃ。

```text id="vf9hkk"
mOf が selected index 上で injective
  + 1 <= mOf i
  -> outerPetalAddress n lap (mOf i) が noncolliding
  -> PetalAddressNoncollisionOn
```

つまり、`outerPetalAddress` が単なる住所計算ではなく、**valid one-based value を復元できる injective な観測座標** として使えることが Lean で固定された。報告でも、`outerPetalAddress_eq_value_eq` により同じ outer address を持つ valid value は元の値も等しい、と整理されている。

## 1. 今回の意味

前回の道はこうだった。

```text id="4f9gf7"
PetalAddressNoncollisionOn
  + PetalCarrierLabelCompatibleOn
  -> PetalCarrierLabelNoncollisionOn
  -> finite GN log-capacity route
```

今回、このうち左側の一つ、

```text id="q05e87"
PetalAddressNoncollisionOn
```

を、具体的な `outerPetalAddress` から供給できるようになった。

```lean id="43m3qw"
petalAddressNoncollisionOn_outer_of_value_injOn
```

これはかなり良い。
今までは `addrOf : ι → PetalAddress` を外から仮定していた。
今回から、少なくとも outer address については、

```text id="7smh4v"
value family mOf が injective
  -> address family も noncolliding
```

が言える。

## 2. なぜ重要か

これは Petal address が「ただのラベル」ではなく、**復元可能な座標** であることを示している。

```lean id="7ejv83"
outerPetalAddress_eq_value_eq
```

の意味は、

```text id="811fwu"
outer address が等しい
  -> 元の one-based value も等しい
```

じゃ。

だから contrapositive 的には、

```text id="cxqxu8"
元の value が違う
  -> outer address も違う
```

として使える。

つまり Petal address は、少なくとも outer layer では selected value の衝突を検出できる。
これは address / carrier noncollision 研究にとって重要な基礎補題じゃ。

## 3. まだ残っているもの

残りは、compatibility 側じゃ。

今の道はこう。

```text id="gpcqmp"
value injective
  -> outer address noncollision

address noncollision
  + label compatibility
  -> label noncollision

label noncollision
  -> GN multiplicity budget
  -> log SubProbability
```

今回通ったのは上段。

まだ残る本命は、

```text id="3klrd7"
PetalCarrierLabelCompatibleOn
```

を実際の carrier / label construction から供給すること。

つまり、

```text id="iio1ee"
qOf i = qOf j
  -> outerPetalAddress n lap (mOf i) = outerPetalAddress n lap (mOf j)
```

またはさらに強く、

```text id="4pcjc0"
qOf i = qOf j
  -> mOf i = mOf j
```

のような補題が欲しい。

## 4. 次に通せそうな補題

次はこれが自然じゃ。

```lean id="apancw"
theorem petalCarrierLabelCompatibleOn_outer_of_label_eq_imp_value_eq
    {ι : Type _}
    (I : Finset ι)
    (n lap : Nat)
    (mOf qOf : ι → Nat)
    (hlabel :
      ∀ i, i ∈ I → ∀ j, j ∈ I → qOf i = qOf j → mOf i = mOf j) :
    PetalCarrierLabelCompatibleOn I
      (fun i => outerPetalAddress n lap (mOf i)) qOf
```

これはかなり通りそう。
証明は、`hlabel` で `mOf i = mOf j` を得て、`rw` すれば address equality が出るはずじゃ。

意味はこう。

```text id="da4snl"
label が value を決める
  -> label は outer address と compatible
```

これで compatibility も concrete outer address に近づく。

## 5. さらに合成すると見える道

上の補題が通れば、次はこうなる。

```text id="3szyil"
mOf injective
  + label equality implies value equality
  -> address noncollision
  + label compatibility
  -> label noncollision
  -> finite GN log-capacity
```

最終的な theorem 候補はこれ。

```lean id="b8tar7"
theorem petalPrimeChannelFamily_logSubProbability_GN_of_outer_value_injOn
```

意味は、

```text id="r6yc8g"
outerPetalAddress 由来の family で、
mOf が injective かつ qOf が mOf を決めるなら、
Petal carrier family は GN log-capacity route に入る
```

これはかなり DkMath らしい。
住所、値、ラベル、GN capacity が全部つながる。

## 6. FLT / ABC / Erdős への位置づけ

今回の進展は三方向すべてに効く。

```text id="55wu0o"
Erdős:
  outer address noncollision から finite GN log-capacity route へ近づいた

FLT:
  NoLift one-slot family を、非衝突 carrier family として扱う足場が強くなった

ABC:
  distinct one-slot channels を rad/support 下界へ渡す前提が整い始めた
```

ただし、まだ目的地に着いたわけではない。
今回の成果は、

```text id="6zks5s"
address noncollision の具体供給
```

であって、

```text id="kn24ly"
label compatibility の具体供給
```

は次じゃ。

## 7. 判定

**Approve。これは明確な進展じゃ。**

特に良い点は、強い主張を避けていること。

```text id="gouyei"
address noncollision alone -> label noncollision
```

とは言っていない。

代わりに、

```text id="da3nu9"
outer address は value injectivity から noncollision を供給できる
label compatibility は別に必要
```

と分けた。

これは正しい。
Lean が通っただけでなく、理論の分解も健全じゃ。

## 8. 次の一手

次はこの順がよい。

```text id="cv47o3"
1. petalCarrierLabelCompatibleOn_outer_of_label_eq_imp_value_eq
2. petalAddressNoncollision_labelNoncollision の outer 専用合成 theorem
3. petalPrimeChannelFamily_logSubProbability_GN_of_outer_value_injOn
4. NoLift 版の outer address logSubProbability theorem
5. 具体 carrier construction で qOf = f(mOf) 型を作る
```

今回で「住所が衝突しない」は outerPetalAddress 側から供給できた。
次は「ラベルが住所と整合する」を供給する番じゃ。

総括すると、現在の道はこう。

```text id="usvr4b"
outerPetalAddress
  -> value reconstruction
  -> address noncollision

address noncollision
  + label compatibility
  -> label noncollision

label noncollision
  + Petal carrier
  -> finite GN log-capacity route
```

うむ。これは確かに進展ありじゃ。
Petal geometry が、Erdős / FLT / ABC 交差点へ具体的に入り始めた。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/NumberTheory/docs/BinomialPrimeWeighted/FLGNB-PetalRoadmap.md b/lean/dk_math/DkMath/NumberTheory/docs/BinomialPrimeWeighted/FLGNB-PetalRoadmap.md
index 923335c2..1768ef43 100644
--- a/lean/dk_math/DkMath/NumberTheory/docs/BinomialPrimeWeighted/FLGNB-PetalRoadmap.md
+++ b/lean/dk_math/DkMath/NumberTheory/docs/BinomialPrimeWeighted/FLGNB-PetalRoadmap.md
@@ -1788,6 +1788,25 @@ petalPrimeChannelFamily_logSubProbability_GN_of_addressNoncollision
 petalNoLiftPrimeChannelFamily_logSubProbability_GN_of_addressNoncollision
 ```
 
+The first concrete Petal-address supply theorem is also available:
+
+```text
+outerPetalAddress_eq_value_eq
+
+petalAddressNoncollisionOn_outer_of_value_injOn
+```
+
+This says that valid one-based values can be recovered from their
+`outerPetalAddress`, so any injective selected value family yields
+`PetalAddressNoncollisionOn` for the corresponding outer addresses.
+
+The compatibility side remains a separate input, but it has a useful
+contrapositive helper:
+
+```text
+petalCarrierLabelCompatibleOn_of_label_eq_imp_address_eq
+```
+
 ### Step 7: Refactor imports gradually
 
 Status:
diff --git a/lean/dk_math/DkMath/Petal/Address.lean b/lean/dk_math/DkMath/Petal/Address.lean
index be91d118..1ed953b7 100644
--- a/lean/dk_math/DkMath/Petal/Address.lean
+++ b/lean/dk_math/DkMath/Petal/Address.lean
@@ -367,6 +367,31 @@ theorem outerPetalAddress_decompose_sub_one
   rw [Nat.mul_comm B ((m - 1) / B)]
   rw [Nat.add_comm ((m - 1) % B) (((m - 1) / B) * B)]
 
+/--
+An outer Petal address determines its one-based value, provided the values are
+valid one-based inputs.
+
+This is the injectivity form needed by later carrier-family noncollision
+bridges: if two valid values have the same one-step address, then the values
+were already the same.
+-/
+theorem outerPetalAddress_eq_value_eq
+    {n lap m₁ m₂ : Nat}
+    (hm₁ : 1 ≤ m₁)
+    (hm₂ : 1 ≤ m₂)
+    (haddr : outerPetalAddress n lap m₁ = outerPetalAddress n lap m₂) :
+    m₁ = m₂ := by
+  calc
+    m₁ =
+        (outerPetalAddress n lap m₁).channel * relPetalBlockSize n lap
+          + outerPetalRemainder n lap m₁ := outerPetalAddress_decompose hm₁
+    _ =
+        (outerPetalAddress n lap m₂).channel * relPetalBlockSize n lap
+          + outerPetalRemainder n lap m₂ := by
+          rw [outerPetalRemainder_eq_offset, outerPetalRemainder_eq_offset]
+          rw [haddr]
+    _ = m₂ := (outerPetalAddress_decompose hm₂).symm
+
 /-- In the pentagonal two-lap example, the outer remainder stays `25`. -/
 theorem outerPetalRemainder_five_two_twentyfive :
     outerPetalRemainder 5 2 25 = 25 := by
diff --git a/lean/dk_math/DkMath/Petal/ErdosBridge.lean b/lean/dk_math/DkMath/Petal/ErdosBridge.lean
index e162f8fb..7925a94a 100644
--- a/lean/dk_math/DkMath/Petal/ErdosBridge.lean
+++ b/lean/dk_math/DkMath/Petal/ErdosBridge.lean
@@ -220,6 +220,59 @@ theorem petalAddressNoncollision_label_injOn
   petalCarrierLabelNoncollisionOn_injOn I qOf
     (petalAddressNoncollision_labelNoncollision I addrOf qOf haddr hcompat)
 
+/--
+Injective selected addresses supply Petal address noncollision.
+
+This is a generic bridge for concrete address constructions: once a construction
+is known to be injective on the selected finite index, it satisfies the Petal
+noncollision predicate used by the log-capacity route.
+-/
+theorem petalAddressNoncollisionOn_of_injOn
+    {ι : Type _}
+    (I : Finset ι)
+    (addrOf : ι → PetalAddress)
+    (hinj : Set.InjOn addrOf ↑I) :
+    PetalAddressNoncollisionOn I addrOf := by
+  intro i hi j hj hij haddr
+  exact hij (hinj hi hj haddr)
+
+/--
+Contrapositive label compatibility criterion.
+
+If equal selected labels force equal Petal addresses, then distinct Petal
+addresses force distinct selected labels.
+-/
+theorem petalCarrierLabelCompatibleOn_of_label_eq_imp_address_eq
+    {ι : Type _}
+    (I : Finset ι)
+    (addrOf : ι → PetalAddress)
+    (qOf : ι → ℕ)
+    (hlabel :
+      ∀ i, i ∈ I → ∀ j, j ∈ I → qOf i = qOf j → addrOf i = addrOf j) :
+    PetalCarrierLabelCompatibleOn I addrOf qOf := by
+  intro i hi j hj haddr hij
+  exact haddr (hlabel i hi j hj hij)
+
+/--
+Outer Petal addresses are noncolliding when their source one-based values are
+injective on the selected finite index.
+
+This is the first concrete address-construction supply theorem for the current
+Erdos bridge.
+-/
+theorem petalAddressNoncollisionOn_outer_of_value_injOn
+    {ι : Type _}
+    (I : Finset ι)
+    (n lap : Nat)
+    (mOf : ι → Nat)
+    (hm : ∀ i, i ∈ I → 1 ≤ mOf i)
+    (hinj : Set.InjOn mOf ↑I) :
+    PetalAddressNoncollisionOn I (fun i => outerPetalAddress n lap (mOf i)) := by
+  apply petalAddressNoncollisionOn_of_injOn
+  intro i hi j hj haddr
+  exact hinj hi hj
+    (outerPetalAddress_eq_value_eq (hm i hi) (hm j hj) haddr)
+
 /--
 PrimitiveBeam witnesses enter the Erdos bridge as Petal prime channels.
 -/
diff --git a/lean/dk_math/DkMath/Petal/docs/Petal-ErdosBridge-ExperimentPlan.md b/lean/dk_math/DkMath/Petal/docs/Petal-ErdosBridge-ExperimentPlan.md
index 4bafbf3b..1ca83e55 100644
--- a/lean/dk_math/DkMath/Petal/docs/Petal-ErdosBridge-ExperimentPlan.md
+++ b/lean/dk_math/DkMath/Petal/docs/Petal-ErdosBridge-ExperimentPlan.md
@@ -577,5 +577,19 @@ Can Petal geometry supply concrete address noncollision and
 address-to-label compatibility?
 ```
 
+The first part now has a concrete outer-address supply theorem:
+
+```text
+outerPetalAddress_eq_value_eq
+
+petalAddressNoncollisionOn_outer_of_value_injOn
+```
+
+Thus an injective selected value family gives noncolliding
+`outerPetalAddress` values.  The remaining geometric task is to derive
+meaningful `PetalCarrierLabelCompatibleOn` assumptions from the actual carrier
+or label construction, rather than keeping compatibility as a permanent raw
+hypothesis.
+
 That is the point where Petal may start producing genuinely strong conditions
 useful for Zsigmondy, FLT, and ABC.
diff --git a/lean/dk_math/DkMath/Petal/docs/Petal-Overview.md b/lean/dk_math/DkMath/Petal/docs/Petal-Overview.md
index 15890ff7..26f8e9b8 100644
--- a/lean/dk_math/DkMath/Petal/docs/Petal-Overview.md
+++ b/lean/dk_math/DkMath/Petal/docs/Petal-Overview.md
@@ -735,6 +735,26 @@ petalPrimeChannelFamily_logSubProbability_GN_of_addressNoncollision
 petalNoLiftPrimeChannelFamily_logSubProbability_GN_of_addressNoncollision
 ```
 
+The first concrete address-construction supply theorem is:
+
+```text
+petalAddressNoncollisionOn_outer_of_value_injOn
+```
+
+It says that an injective family of valid one-based values gives noncolliding
+`outerPetalAddress` values.  The underlying address reconstruction lemma is:
+
+```text
+outerPetalAddress_eq_value_eq
+```
+
+The compatibility side is still explicit, but it now has a convenient
+contrapositive criterion:
+
+```text
+petalCarrierLabelCompatibleOn_of_label_eq_imp_address_eq
+```
+
 ## What This Does Not Claim Yet
 
 The package does not yet prove a standard primorial theorem using a concrete
````
`````
