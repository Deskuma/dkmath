# Git diff / Report / Review

## Add: new: Petal.Anchor

gch: 215f311d0f9004a91e1505801bbf154c9833fcac

## Report

`DkMath.Petal.Anchor` を新設して、Anchor と S0/GN の接続を始めました。

追加:

- [Anchor.lean](/lean/dk_math/DkMath/Petal/Anchor.lean)
  - `AnchoredS0Carrier`
  - `AnchoredGNCarrier`
  - `anchoredS0Carrier_anchor`
  - `anchoredS0Carrier_dvd_S0`
  - `anchoredS0Carrier_pos`
  - `anchoredS0Carrier_ne_zero`
  - `anchoredS0Carrier_anchor_le_of_prime_dvd`
  - `anchoredGNCarrier_anchor`
  - `anchoredGNCarrier_dvd_GN`
  - `anchoredGNCarrier_pos`
  - `anchoredGNCarrier_ne_zero`
  - `anchoredGNCarrier_anchor_le_of_prime_dvd`
  - `anchoredGNCarrier_of_anchoredS0Carrier`
  - `anchoredS0Carrier_of_anchoredGNCarrier`

ポイントは、`ReducedSupport` は S0/GN 非依存のまま維持し、`Anchor.lean` で初めて `S0_nat` / `GN` へ接続したことです。

集約:

- [Petal.lean](/lean/dk_math/DkMath/Petal.lean) に `DkMath.Petal.Anchor` を追加。

Docs:

- [Petal-Overview.md](/lean/dk_math/DkMath/Petal/docs/Petal-Overview.md)
- [FLGNB-PetalRoadmap.md](/lean/dk_math/DkMath/NumberTheory/docs/BinomialPrimeWeighted/FLGNB-PetalRoadmap.md)

確認:

- `lake build DkMath.Petal.Anchor` 成功
- `lake build DkMath.Petal` 成功
- `git diff --check` 成功

既存の `ZsigmondyCyclotomicResearch.lean` の `sorry` warning は出ていますが、今回追加分に `sorry` はありません。

## Review

うむ、これは方針どおりで **良い追加** じゃ。
`ReducedSupport` を S0/GN 非依存に保ち、`Anchor.lean` で初めて接続した。ここが一番大事で、設計の層分離が守られておる。

## レビュー結論

```text
DkMath.Petal.ReducedSupport
  = anchor / positive support の純粋語彙

DkMath.Petal.Anchor
  = ReducedSupport と S0/GN divisibility surface の接続層
```

この分離はかなり綺麗じゃ。
`*Research.lean` を import せず、`GNBridge` と `ReducedSupport` だけで薄い橋を作っている点も良い。

## 良い点

`AnchoredS0Carrier` と `AnchoredGNCarrier` の定義は、必要最小限でよい。

```lean
def AnchoredS0Carrier (r c b n : ℕ) : Prop :=
  HasPositiveAnchorPrime r n ∧ n ∣ S0_nat c b

def AnchoredGNCarrier (r d x u n : ℕ) : Prop :=
  HasPositiveAnchorPrime r n ∧ n ∣ GN d x u
```

これは「carrier が anchor support を持つ」ことと「観測面を割る」ことを分離している。後から primitive witness や padic valuation を重ねやすい。

また、抽出補題群も良い。Lean API としては、

```lean
anchoredS0Carrier_anchor
anchoredS0Carrier_dvd_S0
anchoredS0Carrier_pos
anchoredS0Carrier_ne_zero
anchoredS0Carrier_anchor_le_of_prime_dvd
```

のような projection があるだけで、下流証明の摩擦がかなり減る。

そして今回の一番大きな補題はこれじゃな。

```lean
anchoredGNCarrier_of_anchoredS0Carrier
anchoredS0Carrier_of_anchoredGNCarrier
```

これで、

$$
S0_nat(c,b)
\quad\leftrightarrow\quad
GN\ 3\ (c-b)\ b
$$

の上で、anchored carrier が往復できる。
つまり S0 は Petal 表面、GN は一般核、という二つの見方を Lean 上で行き来できるようになった。

## 気になる点

一点だけ、import 順は少し気になる。

```lean
import DkMath.Petal.ReducedSupport
import DkMath.Petal.GNBridge
```

`GNBridge` 側が `S0_nat` と `GN` の両方を持ってきているなら現状でよい。ただし将来 `GNBridge` が重くなるなら、`Forms` と `GNBridge` を分けて、

```lean
import DkMath.Petal.Forms
import DkMath.Petal.GNBridge
```

のように明示する選択肢もある。今すぐ変更は不要じゃが、`Anchor` は今後よく import される可能性があるので、依存は軽く保ちたい。

もう一つ、`open DkMath.FLT.PetalDetect` が出ている点は、長期的には少し気になる。

```lean
open DkMath.FLT.PetalDetect
```

今は `S0_nat` の所在がそこなので仕方ない。だが Petal 本線としては、将来的には `DkMath.Petal.Forms` 側の alias を使って、`Anchor.lean` から FLT namespace を意識しない形にしたい。これは今すぐのブロッカーではないが、 **FLT には今は着手しないが布石を作る** という方針から見ると、次の整理候補じゃ。

## 次に足すなら

この実装は初期 API として区切れる。
次に足すなら、`PrimitiveBridge` との接続じゃな。

たとえば、

```lean
theorem exists_anchoredS0Carrier_of_not_three_dvd_sub
    {c b : ℕ} (hbc : b < c) (hb : 0 < b)
    (hcop : Nat.Coprime c b) (h3 : ¬ 3 ∣ c - b) :
    ∃ q : ℕ, AnchoredS0Carrier q c b q ∧ ¬ q ∣ c - b
```

のような方向が考えられる。

ただしここで注意。`AnchoredS0Carrier q c b q` は carrier と anchor が同じ素数 (q) なので、これはかなり特殊な形じゃ。
`q` が素数で `q ∣ S0_nat c b` なら、

```lean
HasPositiveAnchorPrime q q
```

は通るはずじゃが、別途小補題があると便利になる。

```lean
theorem hasPositiveAnchorPrime_self_of_prime
    {q : ℕ} (hq : Nat.Prime q) :
    HasPositiveAnchorPrime q q
```

これを `ReducedSupport.lean` に置くか、`Anchor.lean` に置くかは迷うところじゃ。
S0/GN に依存しないので、置くなら `ReducedSupport.lean` が自然。

証明のイメージは、

```lean
⟨hq.pos, hq, dvd_rfl, ?_⟩
```

で、`p < q` かつ `p ∣ q` と `p.Prime` から矛盾を出す形になる。Lean では `Nat.Prime.dvd_of_dvd_pow` ではなく、`hq.eq_of_dvd_of_prime hp hpdiv` 系が使えるか確認が必要じゃ。

これがあると、`exists_prime_dvd_S0_nat_of_not_three_dvd_sub` から `AnchoredS0Carrier` へ持ち上げやすくなる。

## 判定

```text
Petal.Anchor
  -> 初期 API として採用可

Research import 排除
  -> 成功

ReducedSupport と S0/GN の層分離
  -> 成功

次の課題
  -> PrimitiveBridge から AnchoredS0Carrier への existence bridge
  -> FLT namespace 依存を Petal alias 経由に寄せる検討
```

うむ。これは良い。
ここで `Anchor` は「S0/GN carrier 接続層」として成立した。次は primitive witness を anchor carrier に昇格する道、つまり

```text
PrimitiveBridge
  -> Anchor
  -> BoundaryD3 / future Zsigmondy input
```

へ進めるのが自然じゃ。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/NumberTheory/docs/BinomialPrimeWeighted/FLGNB-PetalRoadmap.md b/lean/dk_math/DkMath/NumberTheory/docs/BinomialPrimeWeighted/FLGNB-PetalRoadmap.md
index ca1853c2..6f89737f 100644
--- a/lean/dk_math/DkMath/NumberTheory/docs/BinomialPrimeWeighted/FLGNB-PetalRoadmap.md
+++ b/lean/dk_math/DkMath/NumberTheory/docs/BinomialPrimeWeighted/FLGNB-PetalRoadmap.md
@@ -820,6 +820,42 @@ HasPositiveAnchorPrime is the strict support predicate for nonzero carriers.
 This keeps the entrance broad while preventing `0` from being treated as an
 actual support carrier in downstream theorems.
 
+### `DkMath.Petal.Anchor`
+
+Purpose:
+
+```text
+connect positive anchored carriers to concrete S0/GN divisibility surfaces
+```
+
+Status:
+
+```text
+initial API implemented
+```
+
+Implemented names:
+
+```lean
+AnchoredS0Carrier
+AnchoredGNCarrier
+anchoredS0Carrier_anchor
+anchoredS0Carrier_dvd_S0
+anchoredS0Carrier_pos
+anchoredS0Carrier_ne_zero
+anchoredS0Carrier_anchor_le_of_prime_dvd
+anchoredGNCarrier_anchor
+anchoredGNCarrier_dvd_GN
+anchoredGNCarrier_pos
+anchoredGNCarrier_ne_zero
+anchoredGNCarrier_anchor_le_of_prime_dvd
+anchoredGNCarrier_of_anchoredS0Carrier
+anchoredS0Carrier_of_anchoredGNCarrier
+```
+
+This layer is the first place where `ReducedSupport` imports meet the S0/GN
+surface.  `ReducedSupport` itself remains independent.
+
 ### `DkMath.Petal.EisensteinBridge`
 
 Purpose:
@@ -1024,6 +1060,30 @@ lake build DkMath.Petal.ReducedSupport
 lake build DkMath.Petal
 ```
 
+### Step 5.6: Add `DkMath.Petal.Anchor`
+
+Status:
+
+```text
+initial API implemented
+```
+
+Implemented:
+
+```lean
+AnchoredS0Carrier
+AnchoredGNCarrier
+anchoredGNCarrier_of_anchoredS0Carrier
+anchoredS0Carrier_of_anchoredGNCarrier
+```
+
+Expected validation:
+
+```sh
+lake build DkMath.Petal.Anchor
+lake build DkMath.Petal
+```
+
 ### Step 6: Add `DkMath.Petal.EisensteinBridge`
 
 Status:
diff --git a/lean/dk_math/DkMath/Petal.lean b/lean/dk_math/DkMath/Petal.lean
index 4f69d814..7a3d6a0f 100644
--- a/lean/dk_math/DkMath/Petal.lean
+++ b/lean/dk_math/DkMath/Petal.lean
@@ -6,6 +6,7 @@ Authors: D. and Wise Wolf.
 
 import DkMath.Petal.Basic
 import DkMath.Petal.ReducedSupport
+import DkMath.Petal.Anchor
 import DkMath.Petal.Counting
 import DkMath.Petal.Address
 import DkMath.Petal.Forms
diff --git a/lean/dk_math/DkMath/Petal/Anchor.lean b/lean/dk_math/DkMath/Petal/Anchor.lean
new file mode 100644
index 00000000..eb84927b
--- /dev/null
+++ b/lean/dk_math/DkMath/Petal/Anchor.lean
@@ -0,0 +1,128 @@
+/-
+Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
+Released under MIT license as described in the file LICENSE.
+Authors: D. and Wise Wolf.
+-/
+
+import DkMath.Petal.ReducedSupport
+import DkMath.Petal.GNBridge
+
+#print "file: DkMath.Petal.Anchor"
+
+/-!
+# Petal Anchor
+
+This file connects the reduced-support vocabulary to the `S0` / `GN` carrier
+surfaces.
+
+`ReducedSupport` stays independent of `S0` and `GN`.  This file is the first
+bridge layer where a positive anchored carrier is required to divide a concrete
+Petal or GN observation target.
+-/
+
+namespace DkMath
+namespace Petal
+
+open DkMath.CosmicFormulaBinom
+open DkMath.FLT.PetalDetect
+
+/--
+An anchored positive carrier dividing the cubic Petal detector `S0_nat c b`.
+-/
+def AnchoredS0Carrier (r c b n : ℕ) : Prop :=
+  HasPositiveAnchorPrime r n ∧ n ∣ S0_nat c b
+
+/--
+An anchored positive carrier dividing the general GN kernel `GN d x u`.
+-/
+def AnchoredGNCarrier (r d x u n : ℕ) : Prop :=
+  HasPositiveAnchorPrime r n ∧ n ∣ GN d x u
+
+/-- Extract the positive anchor witness from an anchored `S0_nat` carrier. -/
+theorem anchoredS0Carrier_anchor
+    {r c b n : ℕ} (h : AnchoredS0Carrier r c b n) :
+    HasPositiveAnchorPrime r n :=
+  h.1
+
+/-- Extract the divisibility statement from an anchored `S0_nat` carrier. -/
+theorem anchoredS0Carrier_dvd_S0
+    {r c b n : ℕ} (h : AnchoredS0Carrier r c b n) :
+    n ∣ S0_nat c b :=
+  h.2
+
+/-- The carrier in an anchored `S0_nat` carrier is positive. -/
+theorem anchoredS0Carrier_pos
+    {r c b n : ℕ} (h : AnchoredS0Carrier r c b n) :
+    0 < n :=
+  hasPositiveAnchorPrime_pos h.1
+
+/-- The carrier in an anchored `S0_nat` carrier is nonzero. -/
+theorem anchoredS0Carrier_ne_zero
+    {r c b n : ℕ} (h : AnchoredS0Carrier r c b n) :
+    n ≠ 0 :=
+  hasPositiveAnchorPrime_ne_zero h.1
+
+/-- Any prime divisor of an anchored `S0_nat` carrier is at least the anchor. -/
+theorem anchoredS0Carrier_anchor_le_of_prime_dvd
+    {r c b n p : ℕ} (h : AnchoredS0Carrier r c b n)
+    (hp : Nat.Prime p) (hpdiv : p ∣ n) :
+    r ≤ p :=
+  hasPositiveAnchorPrime_anchor_le_of_prime_dvd h.1 hp hpdiv
+
+/-- Extract the positive anchor witness from an anchored GN carrier. -/
+theorem anchoredGNCarrier_anchor
+    {r d x u n : ℕ} (h : AnchoredGNCarrier r d x u n) :
+    HasPositiveAnchorPrime r n :=
+  h.1
+
+/-- Extract the divisibility statement from an anchored GN carrier. -/
+theorem anchoredGNCarrier_dvd_GN
+    {r d x u n : ℕ} (h : AnchoredGNCarrier r d x u n) :
+    n ∣ GN d x u :=
+  h.2
+
+/-- The carrier in an anchored GN carrier is positive. -/
+theorem anchoredGNCarrier_pos
+    {r d x u n : ℕ} (h : AnchoredGNCarrier r d x u n) :
+    0 < n :=
+  hasPositiveAnchorPrime_pos h.1
+
+/-- The carrier in an anchored GN carrier is nonzero. -/
+theorem anchoredGNCarrier_ne_zero
+    {r d x u n : ℕ} (h : AnchoredGNCarrier r d x u n) :
+    n ≠ 0 :=
+  hasPositiveAnchorPrime_ne_zero h.1
+
+/-- Any prime divisor of an anchored GN carrier is at least the anchor. -/
+theorem anchoredGNCarrier_anchor_le_of_prime_dvd
+    {r d x u n p : ℕ} (h : AnchoredGNCarrier r d x u n)
+    (hp : Nat.Prime p) (hpdiv : p ∣ n) :
+    r ≤ p :=
+  hasPositiveAnchorPrime_anchor_le_of_prime_dvd h.1 hp hpdiv
+
+/--
+The degree-three Petal face turns an anchored `S0_nat` carrier into an anchored
+GN carrier.
+-/
+theorem anchoredGNCarrier_of_anchoredS0Carrier
+    {r c b n : ℕ} (hbc : b < c)
+    (h : AnchoredS0Carrier r c b n) :
+    AnchoredGNCarrier r 3 (c - b) b n := by
+  refine ⟨h.1, ?_⟩
+  rw [← S0_nat_eq_GN_three_sub hbc]
+  exact h.2
+
+/--
+The degree-three GN face turns an anchored GN carrier into an anchored
+`S0_nat` carrier.
+-/
+theorem anchoredS0Carrier_of_anchoredGNCarrier
+    {r c b n : ℕ} (hbc : b < c)
+    (h : AnchoredGNCarrier r 3 (c - b) b n) :
+    AnchoredS0Carrier r c b n := by
+  refine ⟨h.1, ?_⟩
+  rw [S0_nat_eq_GN_three_sub hbc]
+  exact h.2
+
+end Petal
+end DkMath
diff --git a/lean/dk_math/DkMath/Petal/docs/Petal-Overview.md b/lean/dk_math/DkMath/Petal/docs/Petal-Overview.md
index b768dee3..829e7925 100644
--- a/lean/dk_math/DkMath/Petal/docs/Petal-Overview.md
+++ b/lean/dk_math/DkMath/Petal/docs/Petal-Overview.md
@@ -240,6 +240,22 @@ hasPositiveAnchorPrime_anchor_le_of_prime_dvd
 `HasPositiveAnchorPrime` when the carrier must be a genuine nonzero support
 object.
 
+### `DkMath.Petal.Anchor`
+
+Connects positive anchored carriers to concrete `S0_nat` and `GN` divisibility
+surfaces.
+
+Important names:
+
+```lean
+AnchoredS0Carrier
+AnchoredGNCarrier
+anchoredS0Carrier_dvd_S0
+anchoredGNCarrier_dvd_GN
+anchoredGNCarrier_of_anchoredS0Carrier
+anchoredS0Carrier_of_anchoredGNCarrier
+```
+
 ### `DkMath.Petal.Counting`
 
 Defines the fixed and dynamic counting layer.
@@ -387,7 +403,7 @@ how GN degree 3 becomes the Petal S0 face
 The next reasonable implementation directions are:
 
 ```text
-1. connect ReducedSupport to GN/S0 carriers
+1. connect AnchoredS0Carrier to the primitive S0 witnesses
 2. use Petal address decomposition in nested observations
 3. connect strict prime-base orbits to a concrete prime enumeration
 4. decide whether GNPrimitiveCandidate needs a separate vocabulary layer
@@ -396,7 +412,7 @@ The next reasonable implementation directions are:
 The most conservative next theorem work is probably:
 
 ```text
-DkMath.Petal.Anchor
+DkMath.Petal.Anchor plus PrimitiveBridge
 ```
 
 The most concrete arithmetic next step is:
````
`````
