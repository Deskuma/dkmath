# Git diff / Report / Review

## Upd: Petal.ErdosBridge

gch: 97c431d70088fa065743280d01da09799d4b3462

## Report

進めました。今回は `carrierAnchorOf(m)` を関数として急いで定義せず、その前段の契約層を [ErdosBridge.lean](/lean/dk_math/DkMath/Petal/ErdosBridge.lean) に追加しました。

追加した中心はこの 2 つです。

- `PetalCarrierLabelMapData`
- `PetalNoLiftCarrierLabelMapData`

これは有限族 `I` 上で、

```text
mOf : index -> Petal one-based value
qOf : index -> carrier label
```

を持ち、以下をまとめる structure/predicate です。

```text
validValue
valueInjective
labelRecovery
carrier
```

NoLift 版では `carrier` が `PetalNoLiftPrimeChannel` になります。

そこから既存 route へ流す theorem も追加しました。

- `petalCarrierLabelNoncollisionOn_outer_of_carrierLabelMapData`
- `petalCarrierLabelNoncollisionOn_outer_of_noLiftCarrierLabelMapData`
- `petalCarrierLabelMapData_of_noLiftCarrierLabelMapData`
- `petalPrimeChannelFamily_multiplicityBudget_GN_of_carrierLabelMapData`
- `petalPrimeChannelFamily_logSubProbability_GN_of_carrierLabelMapData`
- `petalNoLiftPrimeChannelFamily_logSubProbability_GN_of_noLiftCarrierLabelMapData`

これで「住所値から実在 GN carrier label を読む」本命 route の前に、選択関数なしで実験できる土台ができました。canonical な `carrierAnchorOf` は、carrier uniqueness や choice が見えてから定義できます。

docs も同期済みです。

- [Petal-Overview.md](/lean/dk_math/DkMath/Petal/docs/Petal-Overview.md)
- [Petal-ErdosBridge-ExperimentPlan.md](/lean/dk_math/DkMath/Petal/docs/Petal-ErdosBridge-ExperimentPlan.md)
- [FLGNB-PetalRoadmap.md](/lean/dk_math/DkMath/NumberTheory/docs/BinomialPrimeWeighted/FLGNB-PetalRoadmap.md)

検証は通っています。

```text
lake build DkMath.Petal
git diff --check ...
```

## Review

うむ。これはかなり良い進展じゃ。
今回の差分は、**`carrierAnchorOf(m)` を急いで関数化せず、その前に必要な契約を structure として固定した** ところが重要じゃ。

## 1. 今回の核心

今回追加された中心はこの 2 つ。

```lean
PetalCarrierLabelMapData
PetalNoLiftCarrierLabelMapData
```

これは、有限族 `I` 上で

```text
mOf : index -> Petal one-based value
qOf : index -> carrier label
```

を持ち、以下をまとめる契約じゃ。

```text
validValue:
  1 <= mOf i

valueInjective:
  mOf が I 上で injective

labelRecovery:
  qOf i = qOf j -> mOf i = mOf j

carrier:
  PetalPrimeChannel d x u (qOf i)
```

NoLift 版では `carrier` が

```lean
PetalNoLiftPrimeChannel d x u (qOf i)
```

になる。

つまり、これまでバラバラに theorem の引数として渡していた条件を、**DkMath 本命 route 用のデータパッケージ** にまとめたわけじゃ。

## 2. なぜ `carrierAnchorOf(m)` を急がないのが正しいか

`carrierAnchorOf(m)` を関数として定義するには、本当は次が要る。

```text
m に対応する carrier が存在する
その carrier を一意に選べる
または choice で選ぶ方針を決める
選んだ q が prime / GN divisor / NoLift である
同じ q なら同じ m に戻れる
```

これは重い。

今の段階でいきなり

```lean
def carrierAnchorOf ...
```

を作ると、後で uniqueness や choice の設計が変わったときに、API 全体が揺れる。

今回の `PetalCarrierLabelMapData` は、その前段として正しい。

```text
canonical choice はまだ作らない。
ただし、有限族として carrier label の割当が与えられたなら、
Erdős finite log-capacity route へ流せる。
```

この形なら、Zsigmondy 由来でも、Petal geometry 由来でも、実験的 choice 由来でも受け取れる。

## 3. 今回通った道

今回で固定された道はこう。

```text
PetalCarrierLabelMapData
  -> PetalCarrierLabelNoncollisionOn
  -> GN multiplicity budget
  -> finite GN log-capacity sub-probability
```

NoLift 版はこう。

```text
PetalNoLiftCarrierLabelMapData
  -> PetalCarrierLabelNoncollisionOn
  -> NoLift crossroads theorem
  -> finite GN log-capacity sub-probability
```

しかも、

```lean
petalCarrierLabelMapData_of_noLiftCarrierLabelMapData
```

があるので、NoLift data は prime-channel data に弱められる。

これは構造として綺麗じゃ。

```text
NoLift data
  -> PrimeChannel data
```

という包含関係が Lean 上でも明示された。

## 4. 何が進展なのか

前回までの route は、だいたいこうだった。

```text
f = id
f = nthPrime
qOf = f(mOf)
```

つまり、label map の形を外側から与えていた。

今回の route は違う。

```text
mOf / qOf / carrier / recovery をまとめた有限族データ
```

を主語にした。

これは `f` の形に依存しない。
つまり、`qOf = f(mOf)` 型だけでなく、Zsigmondy witness や Petal carrier witness のような **非関数的・存在証明的な割当** も受け取れる。

ここが大きい。

`nthPrime` は標準素数列実験。
`PetalCarrierLabelMapData` は DkMath 実戦 route の器じゃ。

## 5. まだ主張していないこと

今回も、まだ次は主張していない。

```text
carrierAnchorOf(m) が存在する
carrierAnchorOf(m) が一意である
任意の m から PetalPrimeChannel が出る
任意の m から NoLift が出る
Zsigmondy alone -> NoLift
```

今回の theorem は、

```text
もし有限族として carrier label assignment が与えられ、
validValue / injectivity / recovery / carrier が揃っているなら、
既存の log-capacity route に流せる
```

というもの。

これは過大主張ではなく、正しい橋じゃ。

## 6. FLT / ABC / Erdős 交差点での意味

### Erdős 方面

Erdős finite route では、もう十分に使いやすい形になった。

```text
PetalCarrierLabelMapData
  -> finite GN log-capacity sub-probability
```

つまり、carrier family のデータさえ作れれば、log-capacity 側は閉じる。

### FLT 方面

FLT では NoLift 版が重要。

```text
PetalNoLiftCarrierLabelMapData
  -> each selected carrier has one-slot behavior
  -> log-capacity route
```

ここから次に欲しいのは、

```text
NoLift one-slot
  + d-th-power valuation lower bound
  -> contradiction
```

という obstruction theorem じゃ。

### ABC 方面

ABC では、NoLift data はかなり良い素材になる。

```text
NoLift carrier family
  + labelRecovery
  + valueInjective
  -> distinct one-slot prime support
```

これは `rad` / supportMass 下界へ渡せる。

## 7. 次にやるべきこと

次の本命は、`PetalCarrierLabelMapData` を作る **constructor theorem** じゃ。

たとえば候補はこう。

```lean
theorem petalCarrierLabelMapData_of_family
```

ただしこれは今の structure をそのまま包むだけなので、あまり意味はない。

もっと実用的には、次のような供給元別 constructor が欲しい。

```text
1. Zsigmondy witness family -> PetalCarrierLabelMapData
2. PrimitiveBeam witness family -> PetalCarrierLabelMapData
3. NoLift witness family -> PetalNoLiftCarrierLabelMapData
4. concrete Petal address family -> PetalCarrierLabelMapData
```

特に本命はこれ。

```text
Primitive / Zsigmondy witness family
  + GN carrier bridge
  + label recovery
  + value injectivity
  -> PetalCarrierLabelMapData
```

ここが通ると、`carrierAnchorOf` 関数がなくても、実戦用の finite carrier family theorem が使える。

## 8. 設計上の良い点

今回の design は、将来に強い。

なぜなら、

```text
choice に依存しない
uniqueness に依存しない
finite family 実験を先に進められる
NoLift 版と prime-channel 版の階層が明確
```

だからじゃ。

`carrierAnchorOf` を作るなら後でよい。
今は、

```text
carrier assignment data
```

として有限族を受け取る方が柔軟。

これは Lean 形式化では非常に大事じゃ。
選択関数を早く作りすぎると、あとで証明義務が重くなる。

## 9. 現在地の総括

ここまでの流れはこう。

```text
outerPetalAddress
  -> value reconstruction
  -> address noncollision

qOf = f(mOf)
  -> label recovery
  -> label noncollision

f = id
  -> toy control route

f = nthPrime
  -> prime-valued injective label route

PetalCarrierLabelMapData
  -> DkMath-facing real carrier assignment route
```

今回で、`f` の実験から一段進み、

```text
実在 GN carrier label を有限族データとして受け取る
```

ための器ができた。

これは確かに DkMath 本命 route の前段じゃ。

次の山はこれ。

```text
具体的な Petal / Zsigmondy / PrimitiveBeam 構造から
PetalCarrierLabelMapData
または
PetalNoLiftCarrierLabelMapData
を生成する
```

ここが通れば、Erdős finite log-capacity、FLT obstruction、ABC support/rad bridge の三方向へ同時に伸びる。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/NumberTheory/docs/BinomialPrimeWeighted/FLGNB-PetalRoadmap.md b/lean/dk_math/DkMath/NumberTheory/docs/BinomialPrimeWeighted/FLGNB-PetalRoadmap.md
index 2e86d35a..432d14a0 100644
--- a/lean/dk_math/DkMath/NumberTheory/docs/BinomialPrimeWeighted/FLGNB-PetalRoadmap.md
+++ b/lean/dk_math/DkMath/NumberTheory/docs/BinomialPrimeWeighted/FLGNB-PetalRoadmap.md
@@ -1881,6 +1881,23 @@ petalNoLiftPrimeChannelFamily_logSubProbability_GN_of_outer_nthPrime_value_map
 This confirms that the route works with a genuine prime-valued injective label
 map.  It does not prove that the nth prime divides a GN surface.
 
+The DkMath carrier-label route now has a packaged data layer:
+
+```text
+PetalCarrierLabelMapData
+PetalNoLiftCarrierLabelMapData
+petalCarrierLabelNoncollisionOn_outer_of_carrierLabelMapData
+petalCarrierLabelNoncollisionOn_outer_of_noLiftCarrierLabelMapData
+petalCarrierLabelMapData_of_noLiftCarrierLabelMapData
+petalPrimeChannelFamily_multiplicityBudget_GN_of_carrierLabelMapData
+petalPrimeChannelFamily_logSubProbability_GN_of_carrierLabelMapData
+petalNoLiftPrimeChannelFamily_logSubProbability_GN_of_noLiftCarrierLabelMapData
+```
+
+This is the structure/predicate precursor to `carrierAnchorOf(m)`: it records
+finite-family carrier assignments and their recovery conditions before
+requiring a canonical choice function.
+
 ### Step 7: Refactor imports gradually
 
 Status:
diff --git a/lean/dk_math/DkMath/Petal/ErdosBridge.lean b/lean/dk_math/DkMath/Petal/ErdosBridge.lean
index 95f9c5c1..3f4fe48d 100644
--- a/lean/dk_math/DkMath/Petal/ErdosBridge.lean
+++ b/lean/dk_math/DkMath/Petal/ErdosBridge.lean
@@ -89,6 +89,49 @@ It is deliberately weaker than asking the whole `GN` value to be squarefree.
 def PetalNoLiftPrimeChannel (d x u q : ℕ) : Prop :=
   PetalPrimeChannel d x u q ∧ ¬ q ^ 2 ∣ GN d x u
 
+/--
+Family data for a Petal carrier label map on one GN surface.
+
+This is the predicate form of the planned `carrierAnchorOf` route.  It avoids
+choosing a canonical carrier function too early: callers may supply any
+finite-family assignment `mOf/qOf` as long as values are valid and injective,
+labels recover values, and every label is an actual Petal prime channel.
+-/
+structure PetalCarrierLabelMapData
+    {ι : Type _}
+    (I : Finset ι)
+    (d x u : ℕ)
+    (mOf qOf : ι → ℕ) : Prop where
+  validValue :
+    ∀ i, i ∈ I → 1 ≤ mOf i
+  valueInjective :
+    Set.InjOn mOf ↑I
+  labelRecovery :
+    ∀ i, i ∈ I → ∀ j, j ∈ I → qOf i = qOf j → mOf i = mOf j
+  carrier :
+    ∀ i, i ∈ I → PetalPrimeChannel d x u (qOf i)
+
+/--
+No-lift version of `PetalCarrierLabelMapData`.
+
+This strengthens the local channel condition from `PetalPrimeChannel` to
+`PetalNoLiftPrimeChannel`, while keeping the same value/address and label
+recovery contract.
+-/
+structure PetalNoLiftCarrierLabelMapData
+    {ι : Type _}
+    (I : Finset ι)
+    (d x u : ℕ)
+    (mOf qOf : ι → ℕ) : Prop where
+  validValue :
+    ∀ i, i ∈ I → 1 ≤ mOf i
+  valueInjective :
+    Set.InjOn mOf ↑I
+  labelRecovery :
+    ∀ i, i ∈ I → ∀ j, j ∈ I → qOf i = qOf j → mOf i = mOf j
+  carrier :
+    ∀ i, i ∈ I → PetalNoLiftPrimeChannel d x u (qOf i)
+
 /--
 The standard Mathlib prime enumeration, exposed under Petal naming.
 
@@ -427,6 +470,59 @@ theorem petalCarrierLabelNoncollisionOn_outer_of_value_self
     (fun _ _ => rfl)
     (fun _ _ _ _ h => h)
 
+/--
+Carrier-label map data supplies outer-address label noncollision.
+
+This is the packaged form of the current DkMath route: a family data object
+stores valid values, value injectivity, label recovery, and carrier facts.
+This theorem extracts only the noncollision part.
+-/
+theorem petalCarrierLabelNoncollisionOn_outer_of_carrierLabelMapData
+    {ι : Type _}
+    (I : Finset ι)
+    (d x u : ℕ)
+    (n lap : Nat)
+    (mOf qOf : ι → Nat)
+    (hdata : PetalCarrierLabelMapData I d x u mOf qOf) :
+    PetalCarrierLabelNoncollisionOn I qOf :=
+  petalCarrierLabelNoncollisionOn_outer_of_value_injOn
+    I n lap mOf qOf hdata.validValue hdata.valueInjective
+    hdata.labelRecovery
+
+/--
+No-lift carrier-label map data supplies outer-address label noncollision.
+
+The no-lift data has the same recovery contract as the prime-channel data, so
+the noncollision extraction is identical.
+-/
+theorem petalCarrierLabelNoncollisionOn_outer_of_noLiftCarrierLabelMapData
+    {ι : Type _}
+    (I : Finset ι)
+    (d x u : ℕ)
+    (n lap : Nat)
+    (mOf qOf : ι → Nat)
+    (hdata : PetalNoLiftCarrierLabelMapData I d x u mOf qOf) :
+    PetalCarrierLabelNoncollisionOn I qOf :=
+  petalCarrierLabelNoncollisionOn_outer_of_value_injOn
+    I n lap mOf qOf hdata.validValue hdata.valueInjective
+    hdata.labelRecovery
+
+/--
+No-lift carrier-label map data can be weakened to prime-channel data.
+
+This keeps the structure layer composable: no-lift data is a stronger version
+of the same carrier-label contract.
+-/
+theorem petalCarrierLabelMapData_of_noLiftCarrierLabelMapData
+    {ι : Type _}
+    (I : Finset ι)
+    (d x u : ℕ)
+    (mOf qOf : ι → Nat)
+    (hdata : PetalNoLiftCarrierLabelMapData I d x u mOf qOf) :
+    PetalCarrierLabelMapData I d x u mOf qOf :=
+  ⟨hdata.validValue, hdata.valueInjective, hdata.labelRecovery,
+    fun i hi => (hdata.carrier i hi).1⟩
+
 /--
 Outer-address label compatibility for the nth-prime label map.
 
@@ -883,6 +979,53 @@ theorem petalPrimeChannelFamily_logSubProbability_GN_of_outer_value_injOn
       I n lap mOf qOf hm hminj hlabel)
     hcarrier
 
+/--
+Carrier-label map data supplies an Erdos multiplicity budget on one GN surface.
+
+This is the packaged `carrierAnchorOf`-preparation theorem: once a family data
+object supplies valid values, label recovery, and prime-channel carriers, the
+GN multiplicity budget follows.
+-/
+theorem petalPrimeChannelFamily_multiplicityBudget_GN_of_carrierLabelMapData
+    {ι : Type _}
+    (I : Finset ι)
+    (d x u : ℕ)
+    (n lap : Nat)
+    (mOf qOf : ι → Nat)
+    (hGN0 : GN d x u ≠ 0)
+    (hdata : PetalCarrierLabelMapData I d x u mOf qOf) :
+    DkMath.NumberTheory.PrimitiveSet.NatBaseMultiplicityBudgetOn
+      I qOf (GN d x u) :=
+  petalPrimeChannelFamily_multiplicityBudget_GN_of_labelNoncollision
+    I d x u qOf hGN0
+    (petalCarrierLabelNoncollisionOn_outer_of_carrierLabelMapData
+      I d x u n lap mOf qOf hdata)
+    hdata.carrier
+
+/--
+Carrier-label map data feeds the finite GN log-capacity route.
+
+This is the structure-packaged version of
+`petalPrimeChannelFamily_logSubProbability_GN_of_outer_value_injOn`.
+-/
+theorem petalPrimeChannelFamily_logSubProbability_GN_of_carrierLabelMapData
+    {ι : Type _}
+    (I : Finset ι)
+    (d x u : ℕ)
+    (n lap : Nat)
+    (mOf qOf : ι → Nat)
+    (hGN : 1 < GN d x u)
+    (hdata : PetalCarrierLabelMapData I d x u mOf qOf) :
+    (DkMath.NumberTheory.PrimitiveSet.realLogRatioWeightProvider I qOf (GN d x u)
+      (petalPrimeChannel_realLogNonnegOn
+        I (fun _ => d) (fun _ => x) (fun _ => u) qOf hdata.carrier)
+      hGN).SubProbability :=
+  petalPrimeChannelFamily_logSubProbability_GN_of_labelNoncollision
+    I d x u qOf hGN
+    (petalCarrierLabelNoncollisionOn_outer_of_carrierLabelMapData
+      I d x u n lap mOf qOf hdata)
+    hdata.carrier
+
 /--
 Value-map form of the outer-address GN multiplicity-budget route.
 
@@ -1239,6 +1382,31 @@ theorem petalNoLiftPrimeChannelFamily_logSubProbability_GN_of_outer_value_injOn
       I n lap mOf qOf hm hminj hlabel)
     hcarrier
 
+/--
+No-lift carrier-label map data feeds the finite GN log-capacity route.
+
+This is the packaged form for the future `carrierAnchorOf` route when the
+selected carriers also have local one-slot/no-lift information.
+-/
+theorem petalNoLiftPrimeChannelFamily_logSubProbability_GN_of_noLiftCarrierLabelMapData
+    {ι : Type _}
+    (I : Finset ι)
+    (d x u : ℕ)
+    (n lap : Nat)
+    (mOf qOf : ι → Nat)
+    (hGN : 1 < GN d x u)
+    (hdata : PetalNoLiftCarrierLabelMapData I d x u mOf qOf) :
+    (DkMath.NumberTheory.PrimitiveSet.realLogRatioWeightProvider I qOf (GN d x u)
+      (petalPrimeChannel_realLogNonnegOn
+        I (fun _ => d) (fun _ => x) (fun _ => u) qOf
+        (fun i hi => (hdata.carrier i hi).1))
+      hGN).SubProbability :=
+  petalNoLiftPrimeChannelFamily_logSubProbability_GN_of_labelNoncollision
+    I d x u qOf hGN
+    (petalCarrierLabelNoncollisionOn_outer_of_noLiftCarrierLabelMapData
+      I d x u n lap mOf qOf hdata)
+    hdata.carrier
+
 /--
 Value-map form of the outer-address no-lift GN log-capacity route.
 
diff --git a/lean/dk_math/DkMath/Petal/docs/Petal-ErdosBridge-ExperimentPlan.md b/lean/dk_math/DkMath/Petal/docs/Petal-ErdosBridge-ExperimentPlan.md
index f4a72cb5..63e3f90f 100644
--- a/lean/dk_math/DkMath/Petal/docs/Petal-ErdosBridge-ExperimentPlan.md
+++ b/lean/dk_math/DkMath/Petal/docs/Petal-ErdosBridge-ExperimentPlan.md
@@ -671,5 +671,23 @@ petalNoLiftPrimeChannelFamily_logSubProbability_GN_of_outer_nthPrime_value_map
 This verifies the route for a genuine injective prime-valued label map.  The
 GN carrier and no-lift facts remain separate hypotheses.
 
+The first DkMath-facing carrier-label contract is now implemented as data,
+without forcing a canonical carrier-selection function:
+
+```text
+PetalCarrierLabelMapData
+PetalNoLiftCarrierLabelMapData
+petalCarrierLabelNoncollisionOn_outer_of_carrierLabelMapData
+petalCarrierLabelNoncollisionOn_outer_of_noLiftCarrierLabelMapData
+petalCarrierLabelMapData_of_noLiftCarrierLabelMapData
+petalPrimeChannelFamily_multiplicityBudget_GN_of_carrierLabelMapData
+petalPrimeChannelFamily_logSubProbability_GN_of_carrierLabelMapData
+petalNoLiftPrimeChannelFamily_logSubProbability_GN_of_noLiftCarrierLabelMapData
+```
+
+This is the safe precursor to `carrierAnchorOf(m)`.  It lets experiments supply
+finite-family carrier labels, recovery, and GN divisibility/no-lift facts first;
+canonical choice can be added later if uniqueness becomes available.
+
 That is the point where Petal may start producing genuinely strong conditions
 useful for Zsigmondy, FLT, and ABC.
diff --git a/lean/dk_math/DkMath/Petal/docs/Petal-Overview.md b/lean/dk_math/DkMath/Petal/docs/Petal-Overview.md
index 5f6fa7da..52abf0be 100644
--- a/lean/dk_math/DkMath/Petal/docs/Petal-Overview.md
+++ b/lean/dk_math/DkMath/Petal/docs/Petal-Overview.md
@@ -825,6 +825,24 @@ petalNoLiftPrimeChannelFamily_logSubProbability_GN_of_outer_nthPrime_value_map
 This route supplies real prime labels and label recovery.  It still does not
 say that those primes divide the chosen GN surface.
 
+The DkMath-facing carrier-label contract is now packaged before choosing a
+canonical `carrierAnchorOf` function:
+
+```text
+PetalCarrierLabelMapData
+PetalNoLiftCarrierLabelMapData
+petalCarrierLabelNoncollisionOn_outer_of_carrierLabelMapData
+petalCarrierLabelNoncollisionOn_outer_of_noLiftCarrierLabelMapData
+petalCarrierLabelMapData_of_noLiftCarrierLabelMapData
+petalPrimeChannelFamily_multiplicityBudget_GN_of_carrierLabelMapData
+petalPrimeChannelFamily_logSubProbability_GN_of_carrierLabelMapData
+petalNoLiftPrimeChannelFamily_logSubProbability_GN_of_noLiftCarrierLabelMapData
+```
+
+This is the predicate/structure version of the future `carrierAnchorOf` route:
+it records valid values, value injectivity, label recovery, and actual GN
+carrier facts without forcing a uniqueness or choice theorem too early.
+
 ## What This Does Not Claim Yet
 
 The package does not yet prove a standard primorial theorem using a concrete
````
`````
