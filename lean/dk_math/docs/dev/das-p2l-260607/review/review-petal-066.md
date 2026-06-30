# Git diff / Report / Review

## Upd: Petal.Obstruction

gch: 53a094b2bf821f20b2266c13f779ff8d43ee01c5

## Report

進めました。今回は `Petal.Obstruction` に、レビューで見えていた安全鎖を追加しました。

追加した中心はこれです。

```lean
same label -> same value -> same selected index
```

具体 theorem:

```lean
labelRecovery_valueInjective_eq_of_same_label
petalCarrierLabelMapData_eq_of_same_label
petalNoLiftCarrierLabelMapData_eq_of_same_label
petalCarrierLabelMapData_contradiction_of_same_label_ne_index
petalNoLiftCarrierLabelMapData_contradiction_of_same_label_ne_index
```

意味としては、`PetalCarrierLabelMapData` があるなら、同じ prime label を別 index で再利用する道は閉じる、ということです。False 補題だけでなく、正方向の「衝突時に index が一致する」補題も置いたので、後続の finite channel / ABC support / log-capacity 側で使いやすくなりました。

docs も同期しました。

- `DkMath/Petal/docs/Petal-Overview.md`
- `docs/dev/das-p2l-260607/review/summary-petal-064.md`

検証:

```text
lake build DkMath.Petal.Obstruction
lake build DkMath.Petal
git diff --check ...
```

通っています。既存の `ZsigmondyCyclotomicResearch.lean` の `sorry` warning は今回も別件です。

## Review

うむ。これは **`Obstruction` が単なる False 補題集から、有限族の安全鎖を持つ診断モジュールへ進化した** という進展じゃ。

今回の核心はこれ。

```text
same label
  -> same value
  -> same selected index
```

つまり、

```text
qOf i = qOf j
```

が起きたときに、それが本当に同じ選択点なのか、それとも prime label の重複事故なのかを Lean 上で判定できるようになった。

## 1. 今回追加された「正方向」の意味

前回の `Obstruction` は主に、

```text
この条件があるのに、この破綻証拠が来たら False
```

という形だった。

今回の追加は、それに加えて、

```lean
labelRecovery_valueInjective_eq_of_same_label
```

を入れたのが大きい。

これは、

```text
labelRecovery:
  qOf i = qOf j -> mOf i = mOf j

valueInjective:
  mOf i = mOf j -> i = j
```

を合成して、

```text
qOf i = qOf j -> i = j
```

を得る補題じゃ。

つまり、同じ label が出ても、それが同じ index なら問題ない。
違う index で同じ label を使ったときだけ破綻する。

これはかなり重要な整理じゃ。

## 2. `PetalCarrierLabelMapData` の意味が強くなった

今回、

```lean
petalCarrierLabelMapData_eq_of_same_label
petalNoLiftCarrierLabelMapData_eq_of_same_label
```

が入ったことで、`PetalCarrierLabelMapData` は単なる条件パッケージではなく、

```text
この data を持つ有限族では、同じ prime label は同じ selected index を意味する
```

と言えるようになった。

これは、後続の finite channel / log-capacity / ABC support 側で非常に使いやすい。

今までは、

```text
PetalCarrierLabelMapData には recovery と injectivity が入っている
```

だった。

今回からは、

```text
PetalCarrierLabelMapData があれば、label-level injectivity が得られる
```

と言える。

かなり API として締まった。

## 3. False 補題も自然に強化された

追加された obstruction はこれ。

```lean
petalCarrierLabelMapData_contradiction_of_same_label_ne_index
petalNoLiftCarrierLabelMapData_contradiction_of_same_label_ne_index
```

意味は、

```text
PetalCarrierLabelMapData がある
同じ label を持つ
しかし index は違う
なら False
```

じゃ。

これはまさに有限族 route の安全境界。

```text
same label -> same selected index
```

が正方向。

```text
same label + different selected index -> False
```

が破綻方向。

この両方が揃ったのが今回の良いところじゃ。

## 4. Review で見えていた逆向き問題への回答

前回 Review で、

```text
labelRecovery_contradiction_of_same_label_ne_value
valueInjective_contradiction_of_same_value_ne_index
```

は視点が逆ではないか、という指摘があった。

今回の実装は、その答えになっている。

実際には逆ではなく、二段の安全鎖だった。

```text
labelRecovery:
  same label -> same value

valueInjective:
  same value -> same index
```

これを合成すると、

```text
same label -> same index
```

になる。

つまり、前回は部品が並んでいた。
今回はその部品をつないで、一本の診断ルートにした。

## 5. Erdos / ABC 側での使い道

### Erdos finite log-capacity

finite log-capacity では、同じ prime label を別々の selected channel として数えると危ない。

今回の補題により、

```text
PetalCarrierLabelMapData があるなら、
同じ qOf は同じ index でしか起きない
```

と分かる。

したがって、duplicate-free channel family として扱いやすい。

### ABC support / rad

ABC 側では、`rad` や supportMass に渡すとき、

```text
異なる index が異なる prime support を持つ
```

ことが重要になる。

今回の補題はその入口じゃ。

```text
different selected index
  -> not same label
```

の contrapositive 的な使い方で、distinct prime support の材料になる。

### NoLift route

NoLift 版にも同じ補題があるが、ここで大事なのはコメント通り、

```text
NoLift がこの衝突を防いでいるわけではない。
finite-family recovery contract が防いでいる。
```

という点じゃ。

NoLift は local valuation の条件。
label reuse を防ぐのは recovery + injectivity。
この分離は非常に良い。

## 6. 現在の `Petal.Obstruction` の役割

これで `Petal.Obstruction` は二層になった。

```text
正方向:
  条件が揃えば衝突は同一 index に潰れる

破綻方向:
  条件が揃っているのに別 index で衝突したら False
```

つまり、単なる「失敗集」ではなくなった。

```text
route safety verifier
```

に近くなった。

## 7. 次にやるなら

次は、この安全鎖を `ErdosBridge` や ABC bridge 側へ渡す薄い wrapper が自然じゃ。

候補はこう。

```lean
petalCarrierLabelMapData_label_injOn
petalNoLiftCarrierLabelMapData_label_injOn
```

意味は、

```lean
Set.InjOn qOf ↑I
```

を直接出す補題。

今の

```lean
petalCarrierLabelMapData_eq_of_same_label
```

からほぼそのまま作れるはずじゃ。

これがあると、後続の `NatPairwiseDistinctOn` や rad/support 系に渡しやすい。

## 8. 総括

今回の進展はこう。

```text
前回:
  route-breaking witness -> False

今回:
  same label -> same value -> same index
  という安全鎖を定理化

結果:
  PetalCarrierLabelMapData が
  finite prime channel family の重複防止証明として使いやすくなった
```

これはとても良い。

`False` を受け入れたことで、逆に「破綻しない条件」も明確になった。
行き止まりを見たから、通れる道の幅がはっきりした、という進展じゃ。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Petal/Obstruction.lean b/lean/dk_math/DkMath/Petal/Obstruction.lean
index 7504cef0..fb2ec2e9 100644
--- a/lean/dk_math/DkMath/Petal/Obstruction.lean
+++ b/lean/dk_math/DkMath/Petal/Obstruction.lean
@@ -90,6 +90,108 @@ theorem valueInjective_contradiction_of_same_value_ne_index
     False :=
   hne (hinj hi hj hvalue)
 
+/--
+Label recovery followed by value injectivity turns equal labels into equal
+selected indices.
+
+This is the positive form of the finite-family safety chain:
+
+```text
+same label -> same value -> same index
+```
+-/
+theorem labelRecovery_valueInjective_eq_of_same_label
+    {ι : Type _}
+    {I : Finset ι}
+    {mOf qOf : ι → ℕ}
+    {i j : ι}
+    (hrec :
+      ∀ i, i ∈ I → ∀ j, j ∈ I → qOf i = qOf j → mOf i = mOf j)
+    (hinj : Set.InjOn mOf ↑I)
+    (hi : i ∈ I) (hj : j ∈ I)
+    (hlabel : qOf i = qOf j) :
+    i = j :=
+  hinj hi hj (hrec i hi j hj hlabel)
+
+/--
+Carrier-label map data turns equal labels into equal selected indices.
+
+This packages the safety chain stored in `PetalCarrierLabelMapData`.
+-/
+theorem petalCarrierLabelMapData_eq_of_same_label
+    {ι : Type _}
+    {I : Finset ι}
+    {d x u : ℕ}
+    {mOf qOf : ι → ℕ}
+    {i j : ι}
+    (hdata : PetalCarrierLabelMapData I d x u mOf qOf)
+    (hi : i ∈ I) (hj : j ∈ I)
+    (hlabel : qOf i = qOf j) :
+    i = j :=
+  labelRecovery_valueInjective_eq_of_same_label
+    hdata.labelRecovery hdata.valueInjective hi hj hlabel
+
+/--
+No-lift carrier-label map data also turns equal labels into equal selected
+indices.
+
+The no-lift data carries the same finite-family recovery and injectivity
+contract as the prime-channel data.
+-/
+theorem petalNoLiftCarrierLabelMapData_eq_of_same_label
+    {ι : Type _}
+    {I : Finset ι}
+    {d x u : ℕ}
+    {mOf qOf : ι → ℕ}
+    {i j : ι}
+    (hdata : PetalNoLiftCarrierLabelMapData I d x u mOf qOf)
+    (hi : i ∈ I) (hj : j ∈ I)
+    (hlabel : qOf i = qOf j) :
+    i = j :=
+  labelRecovery_valueInjective_eq_of_same_label
+    hdata.labelRecovery hdata.valueInjective hi hj hlabel
+
+/--
+Carrier-label map data breaks if two distinct selected indices reuse the same
+label.
+
+This is the packaged obstruction form of
+`same label -> same value -> same index`.
+-/
+theorem petalCarrierLabelMapData_contradiction_of_same_label_ne_index
+    {ι : Type _}
+    {I : Finset ι}
+    {d x u : ℕ}
+    {mOf qOf : ι → ℕ}
+    {i j : ι}
+    (hdata : PetalCarrierLabelMapData I d x u mOf qOf)
+    (hi : i ∈ I) (hj : j ∈ I)
+    (hlabel : qOf i = qOf j)
+    (hne : i ≠ j) :
+    False :=
+  hne (petalCarrierLabelMapData_eq_of_same_label hdata hi hj hlabel)
+
+/--
+No-lift carrier-label map data breaks if two distinct selected indices reuse
+the same label.
+
+NoLift does not cause this obstruction; the finite-family recovery contract
+does.  Keeping the theorem named for no-lift data makes the packaged route easy
+to diagnose.
+-/
+theorem petalNoLiftCarrierLabelMapData_contradiction_of_same_label_ne_index
+    {ι : Type _}
+    {I : Finset ι}
+    {d x u : ℕ}
+    {mOf qOf : ι → ℕ}
+    {i j : ι}
+    (hdata : PetalNoLiftCarrierLabelMapData I d x u mOf qOf)
+    (hi : i ∈ I) (hj : j ∈ I)
+    (hlabel : qOf i = qOf j)
+    (hne : i ≠ j) :
+    False :=
+  hne (petalNoLiftCarrierLabelMapData_eq_of_same_label hdata hi hj hlabel)
+
 /--
 Carrier-label noncollision breaks when two distinct selected indices reuse the
 same prime label.
diff --git a/lean/dk_math/DkMath/Petal/docs/Petal-Overview.md b/lean/dk_math/DkMath/Petal/docs/Petal-Overview.md
index 60985221..f2340052 100644
--- a/lean/dk_math/DkMath/Petal/docs/Petal-Overview.md
+++ b/lean/dk_math/DkMath/Petal/docs/Petal-Overview.md
@@ -879,6 +879,11 @@ boundaries:
 petalAddressNoncollision_contradiction_of_same_address_ne_index
 labelRecovery_contradiction_of_same_label_ne_value
 valueInjective_contradiction_of_same_value_ne_index
+labelRecovery_valueInjective_eq_of_same_label
+petalCarrierLabelMapData_eq_of_same_label
+petalNoLiftCarrierLabelMapData_eq_of_same_label
+petalCarrierLabelMapData_contradiction_of_same_label_ne_index
+petalNoLiftCarrierLabelMapData_contradiction_of_same_label_ne_index
 petalCarrierLabelNoncollision_contradiction_of_same_label_ne_index
 noLift_contradiction_of_square_dvd_GN
 padicValNat_eq_one_contradiction_of_two_le
@@ -890,6 +895,15 @@ These theorems do not add bad assumptions as axioms.  They name the points where
 a candidate route stops being compatible with address noncollision, finite
 prime-channel independence, or local no-lift valuation control.
 
+The packaged carrier-label map lemmas also record the positive safety chain:
+
+```text
+same label -> same value -> same selected index
+```
+
+The corresponding obstruction theorem fires when a candidate route tries to
+reuse the same selected prime label at two distinct indices.
+
 ## What This Does Not Claim Yet
 
 The package does not yet prove a standard primorial theorem using a concrete
diff --git a/lean/dk_math/docs/dev/das-p2l-260607/review/summary-petal-064.md b/lean/dk_math/docs/dev/das-p2l-260607/review/summary-petal-064.md
index de4aaba8..6732620c 100644
--- a/lean/dk_math/docs/dev/das-p2l-260607/review/summary-petal-064.md
+++ b/lean/dk_math/docs/dev/das-p2l-260607/review/summary-petal-064.md
@@ -211,6 +211,11 @@ Implemented theorem set:
 petalAddressNoncollision_contradiction_of_same_address_ne_index
 labelRecovery_contradiction_of_same_label_ne_value
 valueInjective_contradiction_of_same_value_ne_index
+labelRecovery_valueInjective_eq_of_same_label
+petalCarrierLabelMapData_eq_of_same_label
+petalNoLiftCarrierLabelMapData_eq_of_same_label
+petalCarrierLabelMapData_contradiction_of_same_label_ne_index
+petalNoLiftCarrierLabelMapData_contradiction_of_same_label_ne_index
 petalCarrierLabelNoncollision_contradiction_of_same_label_ne_index
 noLift_contradiction_of_square_dvd_GN
 padicValNat_eq_one_contradiction_of_two_le
@@ -218,12 +223,14 @@ petalNoLift_contradiction_of_padicValNat_two_le
 petalNoLift_obstruction_of_padicValNat_ge
 ```
 
-This first set focuses on the smallest route-breaking witnesses:
+This first set focuses on the smallest route-breaking witnesses and the
+positive safety chain behind them:
 
 ```text
 same address under address noncollision
 same label but different value under label recovery
 same value but different index under value injectivity
+same label -> same value -> same selected index
 duplicate selected prime label under carrier-label noncollision
 q^2 | GN under NoLift
 two-slot valuation under one-slot p-adic reading
````
`````
