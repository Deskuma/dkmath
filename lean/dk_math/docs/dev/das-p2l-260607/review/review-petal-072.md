# Git diff / Report / Review

## Add: Petal.RangeFamily

gch: 5147d68ffedcad49c28a47feae37446e27fc7860

## Report

進めました。

`DkMath.Petal.RangeFamily` を新設し、`I = Finset.range k`, `mOf i = i + 1` の具体ファミリーから `PetalCarrierLabelMapData` を作れる入口を固定しました。これで PrimitiveBeam / Zsigmondy primitive divisor の族を、そのまま `2^k <= supportMass(GN)` / `2^k <= rad(GN)` へ渡せます。

追加した主な内容は以下です。

- `rangeSuccValue_injOn`
- `petalCarrierLabelMapData_of_bodyPrimitivePrimeFactor_range_succIndex`
- `petalCarrierLabelMapData_of_zsigmondyPrimitivePrimeDivisor_range_succIndex`
- `petal_range_two_pow_le_supportMass_GN_of_bodyPrimitivePrimeFactor_family`
- `petal_range_two_pow_le_rad_GN_of_bodyPrimitivePrimeFactor_family`
- `petal_range_two_pow_le_supportMass_GN_of_zsigmondyPrimitivePrimeDivisor_family`
- `petal_range_two_pow_le_rad_GN_of_zsigmondyPrimitivePrimeDivisor_family`

あわせて `DkMath.Petal` の import と、`Petal-Overview.md` / `summary-petal-064.md` に現在地を追記しました。

検証済みです。

```bash
lake build DkMath.Petal.RangeFamily
lake build DkMath.Petal
git diff --check -- ...
```

既存の `ZsigmondyCyclotomicResearch.lean` の `sorry` warning は今回範囲外の既知警告として残っています。

## Review

うむ。これは **抽象 API から、初めて concrete finite family construction に降りた** 進展じゃ。
`Petal.ABCBridge` までは「有限族 `I` があるなら ABC 側へ渡せる」だった。今回の `DkMath.Petal.RangeFamily` は、その `I` を具体的に

```text
I = Finset.range k
mOf i = i + 1
```

と固定して、`k` 個の Petal carrier family を ABC の `2^k <= supportMass/rad` へ直接送れる入口を作った、ということじゃ。

## 1. 今回の核心

追加された流れはこう。

```text
I = Finset.range k
mOf i = i + 1
PrimitiveBeam / Zsigmondy witness for each i
label injectivity on qOf
  -> PetalCarrierLabelMapData
  -> 2^k <= supportMass(GN)
  -> 2^k <= rad(GN)
```

これまで必要だった

```text
I.card = k
```

の証明が、`Finset.range k` にしたことで自動的に `Finset.card_range` で処理できるようになった。つまり、ABCBridge が受け取れる「個数 `k`」が、具体 family construction 側で自然に供給されるようになったわけじゃ。

## 2. `mOf i = i + 1` の意味

`mOf i = i + 1` は、Petal value/address 側の最小 concrete model じゃ。

この選び方には二つの利点がある。

```text
1. 1 <= mOf i が自動で出る
2. mOf は range 上で injective
```

今回 `rangeSuccValue_injOn` が追加されていて、

```lean
Set.InjOn (fun i : ℕ => i + 1) ↑(Finset.range k)
```

を保証している。これで `PetalCarrierLabelMapData` が要求する `validValue` と `valueInjective` のうち、value 側の機械的条件が片付く。

## 3. まだ caller が供給するもの

今回の RangeFamily は、全部を自動化したわけではない。重要な算術条件はまだ明示仮定として残っている。

```text
label injectivity on Finset.range k
PrimitiveBeam witness or Zsigmondy primitive divisor witness for each i
GN != 0
d > 0, 1 < d
Zsigmondy 側では b < a
```

特に本命は、

```lean
Set.InjOn qOf ↑(Finset.range k)
```

と、

```lean
∀ i, i ∈ Finset.range k -> PrimitivePrimeFactorOfDiffPow ...
```

または

```lean
∀ i, i ∈ Finset.range k -> PrimitivePrimeDivisor a b d (qOf i)
```

じゃ。

つまり、RangeFamily は **index と value の構造を固定する層**。
まだ **実際に異なる primitive carrier を k 個作る算術部分** は caller 側に残している。

この分離は正しい。

## 4. PrimitiveBeam route と Zsigmondy route

今回の endpoint は 2 系統ある。

### PrimitiveBeam / body coordinate route

```lean
petal_range_two_pow_le_supportMass_GN_of_bodyPrimitivePrimeFactor_family
petal_range_two_pow_le_rad_GN_of_bodyPrimitivePrimeFactor_family
```

これは、

```text
k 個の PrimitiveBeam witness
  -> 2^k <= supportMass(GN d x u)
  -> 2^k <= rad(GN d x u)
```

という意味。

### Zsigmondy route

```lean
petal_range_two_pow_le_supportMass_GN_of_zsigmondyPrimitivePrimeDivisor_family
petal_range_two_pow_le_rad_GN_of_zsigmondyPrimitivePrimeDivisor_family
```

これは、

```text
k 個の Zsigmondy primitive divisor witness
  -> 2^k <= supportMass(GN d (a - b) b)
  -> 2^k <= rad(GN d (a - b) b)
```

という意味。

Zsigmondy 側は `x = a - b`, `u = b` に落として GN surface へ接続している。

## 5. 何が前進したか

これまでの ABCBridge は、抽象的には強かった。

```text
PetalCarrierLabelMapData on I
  -> 2^I.card <= rad(GN)
```

しかし caller から見ると、

```text
I をどう作るか
mOf をどう作るか
I.card をどう処理するか
```

が残っていた。

今回の RangeFamily によって、最小の具体形が固定された。

```text
I = range k
mOf i = i + 1
```

なので、今後の実験では caller は、

```text
qOf i をどう選ぶか
qOf が injective か
qOf i が primitive witness か
```

に集中できる。

これは大きい。
構造部分と算術部分が分離された。

## 6. トロミノ論法として見ると

今回の RangeFamily は、トロミノ論法で言うと **Beam を並べる台座** じゃ。

```text
Core:
  GN surface

Beam:
  range k に並ぶ k 本の candidate carrier

Gap:
  label injectivity / primitive witness という未供給条件

Big:
  2^k <= rad(GN)
```

`range k` は「k 本の Beam を置く枠」。
`qOf` は各 Beam に乗る prime label。
`hqinj` と `hprim` が、Beam が本当に独立 carrier であることを保証する。

つまり今回は、**真偽を試す候補 Beam を k 本並べる共通器** ができた。

## 7. 現在の到達点

ここまでの Petal → ABC route は、かなり実用段階に入った。

```text
Abstract layer:
  PetalCarrierLabelMapData
    -> 2^card(I) <= rad(GN)

Cardinality layer:
  k <= I.card
    -> 2^k <= rad(GN)

Concrete range layer:
  I = range k, mOf i = i + 1
    -> k 個の witness から直接 2^k <= rad(GN)
```

今回で一番下の concrete range layer が入った。

## 8. 次の本丸

次に残る本丸は明確じゃ。

```text
qOf i をどう構成するか
qOf が range k 上 injective であることをどう出すか
各 qOf i が primitive witness であることをどう出すか
```

つまり次は `RangeFamily` の上に、

```text
ConcreteProvider
PrimitiveProvider
ZsigmondyProvider
```

のような「qOf を作る層」が欲しくなる。

特に Zsigmondy route では、各 `i < k` に対して異なる primitive divisor を選べるか、という問題になる。ここは choice / uniqueness / noncollision が絡むので、いきなり自動化せず、まずは明示 family として受け取るのが安全じゃ。

## 9. 総括

今回の進展を一言で言うと、

```text
Petal.ABCBridge の抽象 lower-bound theorem に、
range k という concrete finite family constructor が接続された。
```

これで、

```text
k 個の range-indexed primitive carriers
  -> 2^k <= supportMass(GN)
  -> 2^k <= rad(GN)
```

が直接読めるようになった。

うむ。
これは ABC 交渉のための「名刺」から一歩進んで、**k 本の carrier を並べる展示台** ができた段階じゃ。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Petal.lean b/lean/dk_math/DkMath/Petal.lean
index 9638d33d..9d576822 100644
--- a/lean/dk_math/DkMath/Petal.lean
+++ b/lean/dk_math/DkMath/Petal.lean
@@ -24,6 +24,7 @@ import DkMath.Petal.PrimitiveD3ValuationBridge
 import DkMath.Petal.ErdosBridge
 import DkMath.Petal.Obstruction
 import DkMath.Petal.ABCBridge
+import DkMath.Petal.RangeFamily
 
 #print "file: DkMath.Petal"
 
@@ -50,6 +51,7 @@ basic forms / relative polygon vocabulary
   -> Erdos log-capacity bridge from GN carrier channels
   -> obstruction lemmas marking route-breaking assumptions
   -> ABC supportMass/rad bridge from Petal carrier-label support
+  -> concrete range-family constructors feeding ABC count lower bounds
 ```
 
 This is not a claim that every import is logically minimal.  Some files still
diff --git a/lean/dk_math/DkMath/Petal/RangeFamily.lean b/lean/dk_math/DkMath/Petal/RangeFamily.lean
new file mode 100644
index 00000000..6177cad8
--- /dev/null
+++ b/lean/dk_math/DkMath/Petal/RangeFamily.lean
@@ -0,0 +1,195 @@
+/-
+Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
+Released under MIT license as described in the file LICENSE.
+Authors: D. and Wise Wolf.
+-/
+
+import DkMath.Petal.ABCBridge
+
+#print "file: DkMath.Petal.RangeFamily"
+
+/-!
+# Petal Range Family Constructors
+
+This file is the first concrete finite-family construction layer for the
+Petal-to-ABC route.
+
+`DkMath.Petal.ABCBridge` intentionally consumes abstract finite carrier data:
+
+```text
+PetalCarrierLabelMapData on I
+  -> 2^card(I) <= supportMass/rad(GN)
+```
+
+Here we provide the smallest concrete index choice:
+
+```text
+I = Finset.range k
+mOf i = i + 1
+```
+
+The range supplies exactly `k` addresses, while `mOf i = i + 1` supplies
+positive, injective selected values.  The caller still supplies the meaningful
+arithmetic input: primitive/Zsigmondy witnesses and label injectivity.
+-/
+
+namespace DkMath
+namespace Petal
+
+open DkMath.CosmicFormulaBinom
+
+/--
+The standard range value map `i ↦ i + 1` is injective on `Finset.range k`.
+-/
+theorem rangeSuccValue_injOn (k : ℕ) :
+    Set.InjOn (fun i : ℕ => i + 1) ↑(Finset.range k) := by
+  intro i _hi j _hj h
+  exact Nat.succ.inj h
+
+/--
+Body-coordinate range-family constructor for `PetalCarrierLabelMapData`.
+
+The concrete address/value choice is:
+
+```text
+I = Finset.range k
+mOf i = i + 1
+```
+
+The caller supplies label injectivity and the PrimitiveBeam witnesses.  This is
+the first practical construction that can feed `ABCBridge` without manually
+assembling every field of `PetalCarrierLabelMapData`.
+-/
+theorem petalCarrierLabelMapData_of_bodyPrimitivePrimeFactor_range_succIndex
+    (k d x u : ℕ)
+    (qOf : ℕ → ℕ)
+    (hd : 0 < d) (hd1 : 1 < d)
+    (hqinj : Set.InjOn qOf ↑(Finset.range k))
+    (hprim :
+      ∀ i, i ∈ Finset.range k →
+        DkMath.NumberTheory.PrimitiveBeam.PrimitivePrimeFactorOfDiffPow
+          (qOf i) (x + u) u d) :
+    PetalCarrierLabelMapData (Finset.range k) d x u (fun i => i + 1) qOf :=
+  petalCarrierLabelMapData_of_bodyPrimitivePrimeFactor_family
+    (Finset.range k) d x u (fun i => i + 1) qOf hd hd1
+    (by
+      intro i _hi
+      exact Nat.succ_le_succ (Nat.zero_le i))
+    (rangeSuccValue_injOn k)
+    (by
+      intro i hi j hj hq
+      have hij : i = j := hqinj hi hj hq
+      simp [hij])
+    hprim
+
+/--
+Zsigmondy range-family constructor for `PetalCarrierLabelMapData`.
+
+This is the range-indexed counterpart of
+`petalCarrierLabelMapData_of_zsigmondyPrimitivePrimeDivisor_family`.
+-/
+theorem petalCarrierLabelMapData_of_zsigmondyPrimitivePrimeDivisor_range_succIndex
+    (k a b d : ℕ)
+    (qOf : ℕ → ℕ)
+    (hd : 0 < d) (hd1 : 1 < d) (hab_lt : b < a)
+    (hqinj : Set.InjOn qOf ↑(Finset.range k))
+    (hprim :
+      ∀ i, i ∈ Finset.range k →
+        DkMath.Zsigmondy.PrimitivePrimeDivisor a b d (qOf i)) :
+    PetalCarrierLabelMapData (Finset.range k) d (a - b) b (fun i => i + 1) qOf :=
+  petalCarrierLabelMapData_of_zsigmondyPrimitivePrimeDivisor_family
+    (Finset.range k) a b d (fun i => i + 1) qOf hd hd1 hab_lt
+    (by
+      intro i _hi
+      exact Nat.succ_le_succ (Nat.zero_le i))
+    (rangeSuccValue_injOn k)
+    (by
+      intro i hi j hj hq
+      have hij : i = j := hqinj hi hj hq
+      simp [hij])
+    hprim
+
+/--
+Range-indexed PrimitiveBeam family gives the concrete ABC support-mass lower
+bound `2^k <= supportMass(GN d x u)`.
+-/
+theorem petal_range_two_pow_le_supportMass_GN_of_bodyPrimitivePrimeFactor_family
+    (k d x u : ℕ)
+    (qOf : ℕ → ℕ)
+    (hGN0 : GN d x u ≠ 0)
+    (hd : 0 < d) (hd1 : 1 < d)
+    (hqinj : Set.InjOn qOf ↑(Finset.range k))
+    (hprim :
+      ∀ i, i ∈ Finset.range k →
+        DkMath.NumberTheory.PrimitiveBeam.PrimitivePrimeFactorOfDiffPow
+          (qOf i) (x + u) u d) :
+    2 ^ k ≤ DkMath.ABC.supportMass (GN d x u) := by
+  simpa [Finset.card_range] using
+    petalCarrierLabelMapData_two_pow_card_le_supportMass_GN
+      (Finset.range k) hGN0
+      (petalCarrierLabelMapData_of_bodyPrimitivePrimeFactor_range_succIndex
+        k d x u qOf hd hd1 hqinj hprim)
+
+/--
+Range-indexed PrimitiveBeam family gives the concrete ABC radical lower bound
+`2^k <= rad(GN d x u)`.
+-/
+theorem petal_range_two_pow_le_rad_GN_of_bodyPrimitivePrimeFactor_family
+    (k d x u : ℕ)
+    (qOf : ℕ → ℕ)
+    (hGN0 : GN d x u ≠ 0)
+    (hd : 0 < d) (hd1 : 1 < d)
+    (hqinj : Set.InjOn qOf ↑(Finset.range k))
+    (hprim :
+      ∀ i, i ∈ Finset.range k →
+        DkMath.NumberTheory.PrimitiveBeam.PrimitivePrimeFactorOfDiffPow
+          (qOf i) (x + u) u d) :
+    2 ^ k ≤ DkMath.ABC.rad (GN d x u) := by
+  simpa [Finset.card_range] using
+    petalCarrierLabelMapData_two_pow_card_le_rad_GN
+      (Finset.range k) hGN0
+      (petalCarrierLabelMapData_of_bodyPrimitivePrimeFactor_range_succIndex
+        k d x u qOf hd hd1 hqinj hprim)
+
+/--
+Range-indexed Zsigmondy family gives the concrete ABC support-mass lower bound
+`2^k <= supportMass(GN d (a - b) b)`.
+-/
+theorem petal_range_two_pow_le_supportMass_GN_of_zsigmondyPrimitivePrimeDivisor_family
+    (k a b d : ℕ)
+    (qOf : ℕ → ℕ)
+    (hGN0 : GN d (a - b) b ≠ 0)
+    (hd : 0 < d) (hd1 : 1 < d) (hab_lt : b < a)
+    (hqinj : Set.InjOn qOf ↑(Finset.range k))
+    (hprim :
+      ∀ i, i ∈ Finset.range k →
+        DkMath.Zsigmondy.PrimitivePrimeDivisor a b d (qOf i)) :
+    2 ^ k ≤ DkMath.ABC.supportMass (GN d (a - b) b) := by
+  simpa [Finset.card_range] using
+    petalCarrierLabelMapData_two_pow_card_le_supportMass_GN
+      (Finset.range k) hGN0
+      (petalCarrierLabelMapData_of_zsigmondyPrimitivePrimeDivisor_range_succIndex
+        k a b d qOf hd hd1 hab_lt hqinj hprim)
+
+/--
+Range-indexed Zsigmondy family gives the concrete ABC radical lower bound
+`2^k <= rad(GN d (a - b) b)`.
+-/
+theorem petal_range_two_pow_le_rad_GN_of_zsigmondyPrimitivePrimeDivisor_family
+    (k a b d : ℕ)
+    (qOf : ℕ → ℕ)
+    (hGN0 : GN d (a - b) b ≠ 0)
+    (hd : 0 < d) (hd1 : 1 < d) (hab_lt : b < a)
+    (hqinj : Set.InjOn qOf ↑(Finset.range k))
+    (hprim :
+      ∀ i, i ∈ Finset.range k →
+        DkMath.Zsigmondy.PrimitivePrimeDivisor a b d (qOf i)) :
+    2 ^ k ≤ DkMath.ABC.rad (GN d (a - b) b) := by
+  simpa [Finset.card_range] using
+    petalCarrierLabelMapData_two_pow_card_le_rad_GN
+      (Finset.range k) hGN0
+      (petalCarrierLabelMapData_of_zsigmondyPrimitivePrimeDivisor_range_succIndex
+        k a b d qOf hd hd1 hab_lt hqinj hprim)
+
+end Petal
+end DkMath
diff --git a/lean/dk_math/DkMath/Petal/docs/Petal-Overview.md b/lean/dk_math/DkMath/Petal/docs/Petal-Overview.md
index dec38165..6c735cd6 100644
--- a/lean/dk_math/DkMath/Petal/docs/Petal-Overview.md
+++ b/lean/dk_math/DkMath/Petal/docs/Petal-Overview.md
@@ -113,6 +113,7 @@ DkMath.Petal.PrimitiveD3ValuationBridge
 DkMath.Petal.ErdosBridge
 DkMath.Petal.Obstruction
 DkMath.Petal.ABCBridge
+DkMath.Petal.RangeFamily
 ```
 
 ### `DkMath.Petal.Basic`
@@ -977,6 +978,39 @@ NoLift is deliberately not consumed by this bridge.  The ABC support/rad side
 only needs finite prime support; NoLift remains available for valuation
 obstruction routes.
 
+### Range Family
+
+`DkMath.Petal.RangeFamily` is the first concrete finite-family construction
+layer for the Petal-to-ABC route.  It fixes the index set and selected value
+map as:
+
+```text
+I = Finset.range k
+mOf i = i + 1
+```
+
+The caller still supplies the arithmetic content: label injectivity and
+PrimitiveBeam / Zsigmondy witnesses.
+
+Important names:
+
+```text
+rangeSuccValue_injOn
+petalCarrierLabelMapData_of_bodyPrimitivePrimeFactor_range_succIndex
+petalCarrierLabelMapData_of_zsigmondyPrimitivePrimeDivisor_range_succIndex
+petal_range_two_pow_le_supportMass_GN_of_bodyPrimitivePrimeFactor_family
+petal_range_two_pow_le_rad_GN_of_bodyPrimitivePrimeFactor_family
+petal_range_two_pow_le_supportMass_GN_of_zsigmondyPrimitivePrimeDivisor_family
+petal_range_two_pow_le_rad_GN_of_zsigmondyPrimitivePrimeDivisor_family
+```
+
+This is the first endpoint that reads directly as:
+
+```text
+k range-indexed primitive carriers
+  -> 2^k <= supportMass/rad(GN)
+```
+
 ## What This Does Not Claim Yet
 
 The package does not yet prove a standard primorial theorem using a concrete
diff --git a/lean/dk_math/docs/dev/das-p2l-260607/review/summary-petal-064.md b/lean/dk_math/docs/dev/das-p2l-260607/review/summary-petal-064.md
index 126798b1..0e752daa 100644
--- a/lean/dk_math/docs/dev/das-p2l-260607/review/summary-petal-064.md
+++ b/lean/dk_math/docs/dev/das-p2l-260607/review/summary-petal-064.md
@@ -478,3 +478,46 @@ k <= I.card
 This is more flexible than exact cardinality.  Experimental constructions often
 produce "at least k independent carriers" before they produce an exact count,
 so the `_of_card_le` API lets that weaker result already feed ABC.
+
+## 9. Range Family Construction Checkpoint
+
+Implemented first concrete range-indexed construction layer:
+
+```text
+DkMath.Petal.RangeFamily
+```
+
+This fixes the finite family shape as:
+
+```text
+I = Finset.range k
+mOf i = i + 1
+```
+
+Implemented theorem set:
+
+```lean
+rangeSuccValue_injOn
+petalCarrierLabelMapData_of_bodyPrimitivePrimeFactor_range_succIndex
+petalCarrierLabelMapData_of_zsigmondyPrimitivePrimeDivisor_range_succIndex
+petal_range_two_pow_le_supportMass_GN_of_bodyPrimitivePrimeFactor_family
+petal_range_two_pow_le_rad_GN_of_bodyPrimitivePrimeFactor_family
+petal_range_two_pow_le_supportMass_GN_of_zsigmondyPrimitivePrimeDivisor_family
+petal_range_two_pow_le_rad_GN_of_zsigmondyPrimitivePrimeDivisor_family
+```
+
+The construction still leaves the serious arithmetic hypotheses explicit:
+
+```text
+label injectivity on Finset.range k
+PrimitiveBeam or Zsigmondy witnesses for each index
+```
+
+But once those are supplied, the range cardinality is automatic, so the ABC
+endpoint is concrete:
+
+```text
+k range-indexed primitive carriers
+  -> 2^k <= supportMass(GN)
+  -> 2^k <= rad(GN)
+```
````
`````
