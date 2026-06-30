# Git diff / Report / Review

## Upd: Petal.ABCBridge

gch: 0432a196348b2d7cd194928bdaefeb796a6bb069

## Report

進めました。`DkMath.Petal.ABCBridge` に、label support の cardinality と ABC 下限をつなぐ補題群を追加しています。

主な追加:

- `petalCarrierLabelMapData_labelSupport_card_eq`
- `petalNoLiftCarrierLabelMapData_labelSupport_card_eq`
- `petal_two_pow_card_le_prod_of_two_le`
- `petalCarrierLabelMapData_two_pow_card_le_supportMass_GN`
- `petalCarrierLabelMapData_two_pow_card_le_rad_GN`
- NoLift 版の対応 theorem

これで、

```text
PetalCarrierLabelMapData on I
  -> card(labelSupport) = card(I)
  -> 2^card(I) <= product(labelSupport)
  -> 2^card(I) <= supportMass(GN)
  -> 2^card(I) <= rad(GN)
```

まで Lean で固定できました。NoLift は今回も消費せず、ABC 側は prime support / distinct support として扱う設計を維持しています。

文書も同期しました。

- [ABCBridge.lean](/lean/dk_math/DkMath/Petal/ABCBridge.lean)
- [Petal-Overview.md](/lean/dk_math/DkMath/Petal/docs/Petal-Overview.md)
- [summary-petal-064.md](/lean/dk_math/docs/dev/das-p2l-260607/review/summary-petal-064.md)

検証:

```text
lake build DkMath.Petal.ABCBridge
lake build DkMath.Petal
git diff --check ...
```

すべて通っています。既存の `ZsigmondyCyclotomicResearch.lean` の `sorry` warning は継続して出ていますが、今回差分とは別件です。

## Review

うむ。これは **Petal.ABCBridge が「support/rad に渡すだけ」から、「選択した carrier の個数が rad を指数的に押し上げる」段階へ進んだ** ということじゃ。かなり良い進展じゃぞ。

## 1. 何が起きたか

前回の ABCBridge は、こうだった。

```text
PetalCarrierLabelMapData
  -> label support primes divide GN
  -> product(labelSupport) <= supportMass(GN)
  -> product(labelSupport) <= rad(GN)
```

今回そこに、**個数評価** が入った。

```text
PetalCarrierLabelMapData on I
  -> card(labelSupport) = card(I)
  -> 2^card(I) <= product(labelSupport)
  -> 2^card(I) <= supportMass(GN)
  -> 2^card(I) <= rad(GN)
```

つまり、選んだ Petal carrier が (k) 個あるなら、

```text
2^k <= rad(GN d x u)
```

まで Lean で固定できた。

これはかなり分かりやすい下界じゃ。

## 2. なぜ `2^card(I)` が出るのか

理由は単純で、label support の各要素は prime だからじゃ。

素数 (q) は必ず

```text
2 <= q
```

を満たす。

したがって、support に (k) 個の異なる素数があるなら、その積は最低でも

```text
2 * 2 * ... * 2 = 2^k
```

になる。

今回の補題

```lean
petal_two_pow_card_le_prod_of_two_le
```

は、その一般形じゃな。

```text
有限集合 S の全要素が 2 以上なら、
2^card(S) <= product(S)
```

これを Petal label support に適用している。

## 3. `card(labelSupport) = card(I)` が大事

ここが今回の要。

`labelSupport` は

```lean
I.image qOf
```

だから、普通は重複が潰れて cardinality が減る可能性がある。

しかし `PetalCarrierLabelMapData` には、

```text
same label -> same value -> same selected index
```

の安全鎖が入っている。

そのため、`qOf` は selected family 上で injective に振る舞い、

```text
card(labelSupport) = card(I)
```

が出る。

つまり、Petal が選んだ (I) 個の carrier は、ABC support 側でもちゃんと (I) 個の異なる prime support として残る。

これは前回の `Obstruction` / 安全鎖が、今回 ABC 側で実際に効いた形じゃ。

## 4. NoLift を使っていないのが良い

今回も NoLift は消費していない。

これは正しい。

ABC の `rad` / `supportMass` は、素数が **何回割るか** ではなく、素数が **出現するか** を見る。

だから必要なのは、

```text
q is prime
q divides GN
q labels are distinct
```

であって、

```text
q^2 does not divide GN
```

までは不要。

NoLift は引き続き FLT / p-adic obstruction 側に温存される。

この役割分離はとても良い。

```text
ABCBridge:
  prime support を食べる

Obstruction / FLT:
  NoLift valuation を食べる
```

## 5. 今回の意味を一言で言うと

前回まで：

```text
Petal carrier があると rad の下界になる
```

今回から：

```text
Petal carrier が k 個あると rad は少なくとも 2^k 以上
```

になった。

これは ABC 側の見通しとしてかなり強い。
なぜなら、carrier の個数を増やすことが、そのまま `rad` の指数的下界になるからじゃ。

## 6. 現在の三方向の地図

今、Petal carrier family は三方向に使える。

```text
ErdosBridge:
  carrier labels
    -> finite log-capacity / SubProbability

ABCBridge:
  carrier labels
    -> supportMass / rad lower bound
    -> 2^card(I) <= rad(GN)

Obstruction:
  NoLift + valuation lower bound
    -> False
```

つまり、

```text
Erdős は容量を見る。
ABC は支持を見る。
FLT は破綻を見る。
```

同じ Petal carrier を、三つの見方で読めるようになってきた。

## 7. 次に見るべき点

次の自然な一手は、PrimitiveBeam / Zsigmondy から ABC の count 下界へ直通する wrapper じゃ。

いまは、

```text
Primitive/Zsigmondy
  -> PetalCarrierLabelMapData
  -> 2^card(I) <= rad(GN)
```

と合成すれば行ける。

これを一発 theorem にするなら、候補はこう。

```lean
petalCarrierLabelMapData_two_pow_card_le_rad_GN
```

は今回すでに入ったので、その上に、

```lean
petal_two_pow_card_le_rad_GN_of_bodyPrimitivePrimeFactor_family
petal_two_pow_card_le_rad_GN_of_zsigmondyPrimitivePrimeDivisor_family
```

のような直通 theorem が欲しい。

意味は、

```text
PrimitiveBeam / Zsigmondy witness family が k 個ある
  -> rad(GN) >= 2^k
```

じゃ。

## 8. 総括

今回で、ABCBridge はかなり実用的になった。

```text
PetalCarrierLabelMapData on I
  -> distinct prime support of GN
  -> support size = card(I)
  -> product support >= 2^card(I)
  -> rad(GN) >= 2^card(I)
```

これは小さいが強い橋じゃ。

Petal の探索で carrier を増やせば、ABC 側では `rad` が指数的に増える。
つまり、Petal は ABC に対して、

```text
私は GN の中にこれだけ多くの独立した素数支持を見つけた。
だから rad はここまで大きくならざるを得ない。
```

と言えるようになった。

うむ。
これは **Petal が ABC へ渡す名刺に「支えの個数」まで書けるようになった** という段階じゃ。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Petal/ABCBridge.lean b/lean/dk_math/DkMath/Petal/ABCBridge.lean
index e88708b7..091c2156 100644
--- a/lean/dk_math/DkMath/Petal/ABCBridge.lean
+++ b/lean/dk_math/DkMath/Petal/ABCBridge.lean
@@ -80,6 +80,104 @@ theorem petalNoLiftCarrierLabelMapData_labelSupport_prime_dvd_GN
   exact ⟨petalNoLiftPrimeChannel_prime (hdata.carrier i hi),
     anchoredGNCarrier_dvd_GN (hdata.carrier i hi).1⟩
 
+/--
+Carrier-label map data identifies the ABC label support cardinality with the
+selected finite index cardinality.
+
+The support is defined by `Finset.image`; the point of this theorem is that
+the Petal noncollision contract prevents that image from losing entries.
+-/
+theorem petalCarrierLabelMapData_labelSupport_card_eq
+    {ι : Type _}
+    (I : Finset ι)
+    {d x u : ℕ}
+    {mOf qOf : ι → ℕ}
+    (hdata : PetalCarrierLabelMapData I d x u mOf qOf) :
+    (petalCarrierLabelSupport I qOf).card = I.card := by
+  unfold petalCarrierLabelSupport
+  exact Finset.card_image_of_injOn (petalCarrierLabelMapData_label_injOn hdata)
+
+/--
+No-lift carrier-label map data has the same support-cardinality identification.
+
+The no-lift condition is not needed for cardinality; the inherited
+label-noncollision contract is enough.
+-/
+theorem petalNoLiftCarrierLabelMapData_labelSupport_card_eq
+    {ι : Type _}
+    (I : Finset ι)
+    {d x u : ℕ}
+    {mOf qOf : ι → ℕ}
+    (hdata : PetalNoLiftCarrierLabelMapData I d x u mOf qOf) :
+    (petalCarrierLabelSupport I qOf).card = I.card := by
+  unfold petalCarrierLabelSupport
+  exact Finset.card_image_of_injOn (petalNoLiftCarrierLabelMapData_label_injOn hdata)
+
+/--
+A finite natural support whose members are all at least `2` has product at
+least `2 ^ card`.
+
+This small counting spine is intentionally local to the Petal/ABC bridge:
+it converts a support cardinality statement into a product lower bound without
+committing to any stronger ABC or Zsigmondy vocabulary.
+-/
+theorem petal_two_pow_card_le_prod_of_two_le
+    {S : Finset ℕ}
+    (hS : ∀ q, q ∈ S → 2 ≤ q) :
+    2 ^ S.card ≤ S.prod id := by
+  classical
+  revert hS
+  refine Finset.induction_on S ?_ ?_
+  · intro _hS
+    simp
+  · intro p s hp ih hS
+    have hp_two : 2 ≤ p := hS p (Finset.mem_insert_self p s)
+    have hs_two : ∀ q, q ∈ s → 2 ≤ q := by
+      intro q hq
+      exact hS q (Finset.mem_insert_of_mem hq)
+    have ih' : 2 ^ s.card ≤ s.prod id := ih hs_two
+    calc
+      2 ^ (insert p s).card = 2 ^ s.card * 2 := by
+        simp [hp, Nat.pow_succ]
+      _ = 2 * 2 ^ s.card := by
+        rw [Nat.mul_comm]
+      _ ≤ p * s.prod id := by
+        simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using
+          Nat.mul_le_mul ih' hp_two
+      _ = (insert p s).prod id := by
+        simp [hp]
+
+/--
+Carrier-label map data turns selected index count into a lower bound on the
+label-support product.
+-/
+theorem petalCarrierLabelMapData_two_pow_card_le_labelSupport_prod
+    {ι : Type _}
+    (I : Finset ι)
+    {d x u : ℕ}
+    {mOf qOf : ι → ℕ}
+    (hdata : PetalCarrierLabelMapData I d x u mOf qOf) :
+    2 ^ I.card ≤ (petalCarrierLabelSupport I qOf).prod id := by
+  rw [← petalCarrierLabelMapData_labelSupport_card_eq I hdata]
+  exact petal_two_pow_card_le_prod_of_two_le
+    (fun q hq =>
+      (petalCarrierLabelMapData_labelSupport_prime_dvd_GN I hdata q hq).1.two_le)
+
+/--
+No-lift carrier-label map data gives the same count-to-product lower bound.
+-/
+theorem petalNoLiftCarrierLabelMapData_two_pow_card_le_labelSupport_prod
+    {ι : Type _}
+    (I : Finset ι)
+    {d x u : ℕ}
+    {mOf qOf : ι → ℕ}
+    (hdata : PetalNoLiftCarrierLabelMapData I d x u mOf qOf) :
+    2 ^ I.card ≤ (petalCarrierLabelSupport I qOf).prod id := by
+  rw [← petalNoLiftCarrierLabelMapData_labelSupport_card_eq I hdata]
+  exact petal_two_pow_card_le_prod_of_two_le
+    (fun q hq =>
+      (petalNoLiftCarrierLabelMapData_labelSupport_prime_dvd_GN I hdata q hq).1.two_le)
+
 /--
 Petal carrier-label data gives an ABC support-mass lower bound for the observed
 GN surface.
@@ -147,5 +245,69 @@ theorem petalNoLiftCarrierLabelMapData_labelSupport_prod_le_rad_GN
   simpa [DkMath.ABC.supportMass_eq_abc_rad] using
     petalNoLiftCarrierLabelMapData_labelSupport_prod_le_supportMass_GN I hGN0 hdata
 
+/--
+Carrier-label map data gives an ABC support-mass lower bound measured only by
+the number of selected Petal channels.
+-/
+theorem petalCarrierLabelMapData_two_pow_card_le_supportMass_GN
+    {ι : Type _}
+    (I : Finset ι)
+    {d x u : ℕ}
+    {mOf qOf : ι → ℕ}
+    (hGN0 : GN d x u ≠ 0)
+    (hdata : PetalCarrierLabelMapData I d x u mOf qOf) :
+    2 ^ I.card ≤ DkMath.ABC.supportMass (GN d x u) :=
+  le_trans
+    (petalCarrierLabelMapData_two_pow_card_le_labelSupport_prod I hdata)
+    (petalCarrierLabelMapData_labelSupport_prod_le_supportMass_GN I hGN0 hdata)
+
+/--
+No-lift carrier-label map data gives the same channel-count lower bound on
+ABC support mass.
+-/
+theorem petalNoLiftCarrierLabelMapData_two_pow_card_le_supportMass_GN
+    {ι : Type _}
+    (I : Finset ι)
+    {d x u : ℕ}
+    {mOf qOf : ι → ℕ}
+    (hGN0 : GN d x u ≠ 0)
+    (hdata : PetalNoLiftCarrierLabelMapData I d x u mOf qOf) :
+    2 ^ I.card ≤ DkMath.ABC.supportMass (GN d x u) :=
+  le_trans
+    (petalNoLiftCarrierLabelMapData_two_pow_card_le_labelSupport_prod I hdata)
+    (petalNoLiftCarrierLabelMapData_labelSupport_prod_le_supportMass_GN I hGN0 hdata)
+
+/--
+Carrier-label map data gives an ABC radical lower bound measured by selected
+Petal channel count.
+-/
+theorem petalCarrierLabelMapData_two_pow_card_le_rad_GN
+    {ι : Type _}
+    (I : Finset ι)
+    {d x u : ℕ}
+    {mOf qOf : ι → ℕ}
+    (hGN0 : GN d x u ≠ 0)
+    (hdata : PetalCarrierLabelMapData I d x u mOf qOf) :
+    2 ^ I.card ≤ DkMath.ABC.rad (GN d x u) :=
+  le_trans
+    (petalCarrierLabelMapData_two_pow_card_le_labelSupport_prod I hdata)
+    (petalCarrierLabelMapData_labelSupport_prod_le_rad_GN I hGN0 hdata)
+
+/--
+No-lift carrier-label map data gives the same channel-count lower bound on the
+ABC radical.
+-/
+theorem petalNoLiftCarrierLabelMapData_two_pow_card_le_rad_GN
+    {ι : Type _}
+    (I : Finset ι)
+    {d x u : ℕ}
+    {mOf qOf : ι → ℕ}
+    (hGN0 : GN d x u ≠ 0)
+    (hdata : PetalNoLiftCarrierLabelMapData I d x u mOf qOf) :
+    2 ^ I.card ≤ DkMath.ABC.rad (GN d x u) :=
+  le_trans
+    (petalNoLiftCarrierLabelMapData_two_pow_card_le_labelSupport_prod I hdata)
+    (petalNoLiftCarrierLabelMapData_labelSupport_prod_le_rad_GN I hGN0 hdata)
+
 end Petal
 end DkMath
diff --git a/lean/dk_math/DkMath/Petal/docs/Petal-Overview.md b/lean/dk_math/DkMath/Petal/docs/Petal-Overview.md
index 19ff50ce..bd2dd1e7 100644
--- a/lean/dk_math/DkMath/Petal/docs/Petal-Overview.md
+++ b/lean/dk_math/DkMath/Petal/docs/Petal-Overview.md
@@ -111,6 +111,8 @@ DkMath.Petal.EisensteinBridge
 DkMath.Petal.ZsigmondyD3Bridge
 DkMath.Petal.PrimitiveD3ValuationBridge
 DkMath.Petal.ErdosBridge
+DkMath.Petal.Obstruction
+DkMath.Petal.ABCBridge
 ```
 
 ### `DkMath.Petal.Basic`
@@ -709,8 +711,8 @@ FLT:
   next missing input: dedicated obstruction theorem
 
 ABC:
-  target: distinct one-slot channels become support/rad lower-bound material
-  next missing input: rad/supportMass bridge for label-noncolliding channels
+  current bridge: distinct carrier labels become supportMass/rad lower bounds
+  count form: selected channel count gives 2^card <= supportMass/rad
 ```
 
 Current research target:
@@ -917,8 +919,10 @@ reuse the same selected prime label at two distinct indices.
 ```text
 PetalCarrierLabelMapData
   -> label support primes divide GN
+  -> label support cardinality = selected index cardinality
   -> product of label support <= supportMass GN
   -> product of label support <= rad GN
+  -> 2^(selected index count) <= supportMass/rad GN
 ```
 
 Core theorem names:
@@ -927,10 +931,19 @@ Core theorem names:
 petalCarrierLabelSupport
 petalCarrierLabelMapData_labelSupport_prime_dvd_GN
 petalNoLiftCarrierLabelMapData_labelSupport_prime_dvd_GN
+petalCarrierLabelMapData_labelSupport_card_eq
+petalNoLiftCarrierLabelMapData_labelSupport_card_eq
+petal_two_pow_card_le_prod_of_two_le
+petalCarrierLabelMapData_two_pow_card_le_labelSupport_prod
+petalNoLiftCarrierLabelMapData_two_pow_card_le_labelSupport_prod
 petalCarrierLabelMapData_labelSupport_prod_le_supportMass_GN
 petalNoLiftCarrierLabelMapData_labelSupport_prod_le_supportMass_GN
 petalCarrierLabelMapData_labelSupport_prod_le_rad_GN
 petalNoLiftCarrierLabelMapData_labelSupport_prod_le_rad_GN
+petalCarrierLabelMapData_two_pow_card_le_supportMass_GN
+petalNoLiftCarrierLabelMapData_two_pow_card_le_supportMass_GN
+petalCarrierLabelMapData_two_pow_card_le_rad_GN
+petalNoLiftCarrierLabelMapData_two_pow_card_le_rad_GN
 ```
 
 NoLift is deliberately not consumed by this bridge.  The ABC support/rad side
diff --git a/lean/dk_math/docs/dev/das-p2l-260607/review/summary-petal-064.md b/lean/dk_math/docs/dev/das-p2l-260607/review/summary-petal-064.md
index c015cdac..d4672f1e 100644
--- a/lean/dk_math/docs/dev/das-p2l-260607/review/summary-petal-064.md
+++ b/lean/dk_math/docs/dev/das-p2l-260607/review/summary-petal-064.md
@@ -378,10 +378,19 @@ Implemented theorem set:
 petalCarrierLabelSupport
 petalCarrierLabelMapData_labelSupport_prime_dvd_GN
 petalNoLiftCarrierLabelMapData_labelSupport_prime_dvd_GN
+petalCarrierLabelMapData_labelSupport_card_eq
+petalNoLiftCarrierLabelMapData_labelSupport_card_eq
+petal_two_pow_card_le_prod_of_two_le
+petalCarrierLabelMapData_two_pow_card_le_labelSupport_prod
+petalNoLiftCarrierLabelMapData_two_pow_card_le_labelSupport_prod
 petalCarrierLabelMapData_labelSupport_prod_le_supportMass_GN
 petalNoLiftCarrierLabelMapData_labelSupport_prod_le_supportMass_GN
 petalCarrierLabelMapData_labelSupport_prod_le_rad_GN
 petalNoLiftCarrierLabelMapData_labelSupport_prod_le_rad_GN
+petalCarrierLabelMapData_two_pow_card_le_supportMass_GN
+petalNoLiftCarrierLabelMapData_two_pow_card_le_supportMass_GN
+petalCarrierLabelMapData_two_pow_card_le_rad_GN
+petalNoLiftCarrierLabelMapData_two_pow_card_le_rad_GN
 ```
 
 The bridge reads Petal carrier-label data as ABC finite support:
@@ -389,8 +398,25 @@ The bridge reads Petal carrier-label data as ABC finite support:
 ```text
 Petal carrier labels on GN
   -> finite support of prime divisors of GN
+  -> label noncollision preserves selected cardinality
+  -> 2^(selected channel count) <= product of label support
   -> supportMass/rad lower bound
 ```
 
 This is intentionally separate from NoLift.  ABC support/rad consumes prime
 support; NoLift is kept for p-adic valuation obstruction.
+
+The second checkpoint makes the bridge count-facing:
+
+```text
+PetalCarrierLabelMapData on I
+  -> card(labelSupport) = card(I)
+  -> every label prime has 2 <= q
+  -> 2^card(I) <= product(labelSupport)
+  -> 2^card(I) <= supportMass(GN d x u)
+  -> 2^card(I) <= rad(GN d x u)
+```
+
+This is the ABC analogue of the Erdos finite-family count spine.  It gives a
+small, reusable lower bound without requiring a concrete prime enumeration and
+without consuming NoLift.
````
`````
