# Git diff / Report / Review

## Upd: Petal: Anchor, ReducedSupport

gch: 602e54f403ddd2d8303f8d3a82a0b3983bc9ce30

## Report

レビューの次目的地に合わせて進めました。

追加実装:

- [ReducedSupport.lean](/lean/dk_math/DkMath/Petal/ReducedSupport.lean)
  - `hasPositiveAnchorPrime_self_of_prime`
  - prime witness 自身を positive anchored carrier として扱うための基礎補題です。

- [Anchor.lean](/lean/dk_math/DkMath/Petal/Anchor.lean)
  - `exists_anchoredS0Carrier_of_not_three_dvd_sub`
  - `PrimitiveBridge` の `exists_prime_dvd_S0_nat_of_not_three_dvd_sub` を使い、`S0_nat` 上の primitive prime witness を `AnchoredS0Carrier q c b q` へ昇格します。

依存方向も整理しました:

```text
ReducedSupport
  -> PrimitiveBridge
  -> Anchor
```

Docs も同期:

- [Petal-Overview.md](/lean/dk_math/DkMath/Petal/docs/Petal-Overview.md)
- [FLGNB-PetalRoadmap.md](/lean/dk_math/DkMath/NumberTheory/docs/BinomialPrimeWeighted/FLGNB-PetalRoadmap.md)
- [S0_GN_Anchor_Phase_実験設計書.md](/lean/dk_math/DkMath/NumberTheory/docs/BinomialPrimeWeighted/S0_GN_Anchor_Phase_実験設計書.md)

確認:

- `lake build DkMath.Petal.ReducedSupport` 成功
- `lake build DkMath.Petal.Anchor` 成功
- `lake build DkMath.Petal` 成功
- `git diff --check` 成功

既存の `ZsigmondyCyclotomicResearch.lean` の `sorry` warning は出ていますが、今回追加分に `sorry` はありません。

## Review

うむ、これはかなり良い。
`Anchor` がただの carrier wrapper から、 **primitive witness を受け取れる入口** になった。レビューとしては **採用でよい** 。

## 良い点

依存方向がかなり綺麗じゃ。

```text
ReducedSupport
  -> PrimitiveBridge
  -> Anchor
```

正確には `Anchor.lean` が `ReducedSupport`、`GNBridge`、`PrimitiveBridge` を import しておるので、

```text
ReducedSupport  = support 語彙
GNBridge        = S0/GN 同一視
PrimitiveBridge = S0 primitive witness
Anchor          = support + S0/GN + primitive witness の接続
```

という形になった。
`ReducedSupport` が S0/GN 非依存のまま維持されているのも良い。

## `hasPositiveAnchorPrime_self_of_prime`

これはかなり大事な補題じゃ。

```lean
theorem hasPositiveAnchorPrime_self_of_prime
    {q : ℕ} (hq : Nat.Prime q) :
    HasPositiveAnchorPrime q q
```

意味は、

```text
素数 q は、それ自身を carrier とする positive anchor である
```

じゃな。これにより、primitive prime witness (q) をそのまま anchored carrier へ昇格できる。

証明も妥当じゃ。

```lean
have hp_eq_q : p = q := (Nat.prime_dvd_prime_iff_eq hp hq).1 hp_dvd
omega
```

(p<q) かつ (p=q) の矛盾を `omega` で閉じる。良い。

## `exists_anchoredS0Carrier_of_not_three_dvd_sub`

これが今回の実質的な進展じゃ。

```lean
theorem exists_anchoredS0Carrier_of_not_three_dvd_sub
    {c b : ℕ} (hbc : b < c) (hb : 0 < b)
    (hcop : Nat.Coprime c b) (h3 : ¬ 3 ∣ c - b) :
    ∃ q : ℕ, AnchoredS0Carrier q c b q ∧ ¬ q ∣ c - b
```

これは非常に良い API じゃ。
以前は、

```text
∃ q, q.Prime ∧ q ∣ S0_nat c b ∧ ¬ q ∣ c - b
```

だったものが、

```text
∃ q, AnchoredS0Carrier q c b q ∧ ¬ q ∣ c - b
```

へ昇格した。

つまり、primitive witness (q) は単に (S0) を割るだけではなく、

```text
q 自身を anchor とする positive carrier
```

として扱えるようになった。
これは「素数の種」を carrier として扱う方向に、かなり合っておる。

## 気になる点

大きな問題はない。
ただし、後で欲しくなりそうな projection が一つある。

今の結論は、

```lean
∃ q, AnchoredS0Carrier q c b q ∧ ¬ q ∣ c - b
```

なので、下流で `q.Prime` が欲しいときに、

```lean
hasPositiveAnchorPrime_prime (anchoredS0Carrier_anchor h)
```

と辿ることになる。

これは通るが、よく使うなら補題があると便利じゃ。

```lean
theorem anchoredS0Carrier_anchor_prime
    {r c b n : ℕ} (h : AnchoredS0Carrier r c b n) :
    Nat.Prime r :=
  hasPositiveAnchorPrime_prime h.1
```

同様に GN 側も。

```lean
theorem anchoredGNCarrier_anchor_prime
    {r d x u n : ℕ} (h : AnchoredGNCarrier r d x u n) :
    Nat.Prime r :=
  hasPositiveAnchorPrime_prime h.1
```

さらに今回の existence 専用には、

```lean
theorem exists_anchoredS0Carrier_prime_of_not_three_dvd_sub ...
```

までは不要。既存の `exists_anchoredS0Carrier...` から取り出せる。

## `Petal.lean` の import 順

今回、`Anchor` を `PrimitiveBridge` の後へ移したのは良い。

```lean
import DkMath.Petal.PrimitiveBridge
import DkMath.Petal.Anchor
```

これは依存順を反映している。小さいことじゃが、こういう順番は後で効く。

## 判定

```text
ReducedSupport
  -> prime witness self-anchor 補題が追加され、完成度上昇

Anchor
  -> primitive S0 witness を anchored carrier へ昇格可能

Research import 排除
  -> 維持

sorry
  -> 追加なし

次段
  -> Anchor projection API を少し増やすか、BoundaryD3 へ進む
```

わっちのおすすめは、次に `Anchor` へ projection 補題を少し足してから、`BoundaryD3` に進むことじゃ。

最小追加候補はこれ。

```lean
anchoredS0Carrier_anchor_prime
anchoredGNCarrier_anchor_prime
```

この二つだけで十分。
その後に、

```text
DkMath.Petal.BoundaryD3
```

へ進めば、S0 (d=3) の (3)-primary 例外分類を本線 API として固定しやすくなる。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/NumberTheory/docs/BinomialPrimeWeighted/FLGNB-PetalRoadmap.md b/lean/dk_math/DkMath/NumberTheory/docs/BinomialPrimeWeighted/FLGNB-PetalRoadmap.md
index 6f89737f..067ce600 100644
--- a/lean/dk_math/DkMath/NumberTheory/docs/BinomialPrimeWeighted/FLGNB-PetalRoadmap.md
+++ b/lean/dk_math/DkMath/NumberTheory/docs/BinomialPrimeWeighted/FLGNB-PetalRoadmap.md
@@ -804,6 +804,7 @@ hasPositiveAnchorPrime_prime
 hasPositiveAnchorPrime_anchor_dvd
 hasPositiveAnchorPrime_no_smaller_prime
 hasPositiveAnchorPrime_anchor_le_of_prime_dvd
+hasPositiveAnchorPrime_self_of_prime
 ```
 
 This layer intentionally does not import S0/GN bridge files yet.  It should
@@ -851,6 +852,7 @@ anchoredGNCarrier_ne_zero
 anchoredGNCarrier_anchor_le_of_prime_dvd
 anchoredGNCarrier_of_anchoredS0Carrier
 anchoredS0Carrier_of_anchoredGNCarrier
+exists_anchoredS0Carrier_of_not_three_dvd_sub
 ```
 
 This layer is the first place where `ReducedSupport` imports meet the S0/GN
@@ -1051,6 +1053,7 @@ hasPositiveAnchorPrime_prime
 hasPositiveAnchorPrime_anchor_dvd
 hasPositiveAnchorPrime_no_smaller_prime
 hasPositiveAnchorPrime_anchor_le_of_prime_dvd
+hasPositiveAnchorPrime_self_of_prime
 ```
 
 Expected validation:
@@ -1075,6 +1078,7 @@ AnchoredS0Carrier
 AnchoredGNCarrier
 anchoredGNCarrier_of_anchoredS0Carrier
 anchoredS0Carrier_of_anchoredGNCarrier
+exists_anchoredS0Carrier_of_not_three_dvd_sub
 ```
 
 Expected validation:
diff --git "a/lean/dk_math/DkMath/NumberTheory/docs/BinomialPrimeWeighted/S0_GN_Anchor_Phase_\345\256\237\351\250\223\350\250\255\350\250\210\346\233\270.md" "b/lean/dk_math/DkMath/NumberTheory/docs/BinomialPrimeWeighted/S0_GN_Anchor_Phase_\345\256\237\351\250\223\350\250\255\350\250\210\346\233\270.md"
index e612fcfc..f7fb0300 100644
--- "a/lean/dk_math/DkMath/NumberTheory/docs/BinomialPrimeWeighted/S0_GN_Anchor_Phase_\345\256\237\351\250\223\350\250\255\350\250\210\346\233\270.md"
+++ "b/lean/dk_math/DkMath/NumberTheory/docs/BinomialPrimeWeighted/S0_GN_Anchor_Phase_\345\256\237\351\250\223\350\250\255\350\250\210\346\233\270.md"
@@ -404,6 +404,7 @@ theorem hasPositiveAnchorPrime_prime
 theorem hasPositiveAnchorPrime_anchor_dvd
 theorem hasPositiveAnchorPrime_no_smaller_prime
 theorem hasPositiveAnchorPrime_anchor_le_of_prime_dvd
+theorem hasPositiveAnchorPrime_self_of_prime
 ```
 
 Keep this layer independent of S0 at first.
diff --git a/lean/dk_math/DkMath/Petal.lean b/lean/dk_math/DkMath/Petal.lean
index 7a3d6a0f..93f041dc 100644
--- a/lean/dk_math/DkMath/Petal.lean
+++ b/lean/dk_math/DkMath/Petal.lean
@@ -6,7 +6,6 @@ Authors: D. and Wise Wolf.
 
 import DkMath.Petal.Basic
 import DkMath.Petal.ReducedSupport
-import DkMath.Petal.Anchor
 import DkMath.Petal.Counting
 import DkMath.Petal.Address
 import DkMath.Petal.Forms
@@ -16,6 +15,7 @@ import DkMath.Petal.GNBridge
 import DkMath.Petal.GcdBridge
 import DkMath.Petal.PadicBridge
 import DkMath.Petal.PrimitiveBridge
+import DkMath.Petal.Anchor
 
 #print "file: DkMath.Petal"
 
diff --git a/lean/dk_math/DkMath/Petal/Anchor.lean b/lean/dk_math/DkMath/Petal/Anchor.lean
index eb84927b..e6126f62 100644
--- a/lean/dk_math/DkMath/Petal/Anchor.lean
+++ b/lean/dk_math/DkMath/Petal/Anchor.lean
@@ -6,6 +6,7 @@ Authors: D. and Wise Wolf.
 
 import DkMath.Petal.ReducedSupport
 import DkMath.Petal.GNBridge
+import DkMath.Petal.PrimitiveBridge
 
 #print "file: DkMath.Petal.Anchor"
 
@@ -124,5 +125,20 @@ theorem anchoredS0Carrier_of_anchoredGNCarrier
   rw [S0_nat_eq_GN_three_sub hbc]
   exact h.2
 
+/--
+Primitive S0 existence, upgraded to an anchored S0 carrier.
+
+If `3` does not divide the boundary gap, then there is a prime `q` such that
+`q` is its own positive anchor carrier, `q` divides `S0_nat c b`, and `q` does
+not divide the boundary gap.
+-/
+theorem exists_anchoredS0Carrier_of_not_three_dvd_sub
+    {c b : ℕ} (hbc : b < c) (hb : 0 < b)
+    (hcop : Nat.Coprime c b) (h3 : ¬ 3 ∣ c - b) :
+    ∃ q : ℕ, AnchoredS0Carrier q c b q ∧ ¬ q ∣ c - b := by
+  rcases exists_prime_dvd_S0_nat_of_not_three_dvd_sub hbc hb hcop h3 with
+    ⟨q, hq, hq_dvd_S0, hq_not_dvd_sub⟩
+  exact ⟨q, ⟨⟨hasPositiveAnchorPrime_self_of_prime hq, hq_dvd_S0⟩, hq_not_dvd_sub⟩⟩
+
 end Petal
 end DkMath
diff --git a/lean/dk_math/DkMath/Petal/ReducedSupport.lean b/lean/dk_math/DkMath/Petal/ReducedSupport.lean
index 18348535..d4f7b649 100644
--- a/lean/dk_math/DkMath/Petal/ReducedSupport.lean
+++ b/lean/dk_math/DkMath/Petal/ReducedSupport.lean
@@ -125,5 +125,19 @@ theorem hasPositiveAnchorPrime_anchor_le_of_prime_dvd
     r ≤ p :=
   hasAnchorPrime_anchor_le_of_prime_dvd h.2 hp hpdiv
 
+/--
+A prime is its own positive anchor carrier.
+
+This is useful when a primitive-prime witness itself is used as the anchored
+carrier.
+-/
+theorem hasPositiveAnchorPrime_self_of_prime
+    {q : ℕ} (hq : Nat.Prime q) :
+    HasPositiveAnchorPrime q q := by
+  refine ⟨hq.pos, hq, dvd_rfl, ?_⟩
+  intro p hp hp_lt hp_dvd
+  have hp_eq_q : p = q := (Nat.prime_dvd_prime_iff_eq hp hq).1 hp_dvd
+  omega
+
 end Petal
 end DkMath
diff --git a/lean/dk_math/DkMath/Petal/docs/Petal-Overview.md b/lean/dk_math/DkMath/Petal/docs/Petal-Overview.md
index 829e7925..d05df3d4 100644
--- a/lean/dk_math/DkMath/Petal/docs/Petal-Overview.md
+++ b/lean/dk_math/DkMath/Petal/docs/Petal-Overview.md
@@ -234,6 +234,7 @@ hasPositiveAnchorPrime_prime
 hasPositiveAnchorPrime_anchor_dvd
 hasPositiveAnchorPrime_no_smaller_prime
 hasPositiveAnchorPrime_anchor_le_of_prime_dvd
+hasPositiveAnchorPrime_self_of_prime
 ```
 
 `HasAnchorPrime` is the wide raw carrier predicate.  Use
@@ -254,6 +255,7 @@ anchoredS0Carrier_dvd_S0
 anchoredGNCarrier_dvd_GN
 anchoredGNCarrier_of_anchoredS0Carrier
 anchoredS0Carrier_of_anchoredGNCarrier
+exists_anchoredS0Carrier_of_not_three_dvd_sub
 ```
 
 ### `DkMath.Petal.Counting`
````
`````
