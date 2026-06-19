# Git diff / Report / Review

## Update: Petal.ReducedSupport

gch: 2da203fd81b7010f500addf6d2a8380ae8eee355

## Report

B 案で実装しました。`HasAnchorPrime` は広い raw predicate のまま残し、厳密な非ゼロ support 用に `HasPositiveAnchorPrime` を追加しています。

変更:

- [ReducedSupport.lean](/lean/dk_math/DkMath/Petal/ReducedSupport.lean)
  - `HasPositiveAnchorPrime`
  - `hasAnchorPrime_anchor_le_of_prime_dvd`
  - `hasPositiveAnchorPrime_pos`
  - `hasPositiveAnchorPrime_prime`
  - `hasPositiveAnchorPrime_anchor_dvd`
  - `hasPositiveAnchorPrime_no_smaller_prime`
  - `hasPositiveAnchorPrime_anchor_le_of_prime_dvd`

意味づけ:

```text
HasAnchorPrime           = 間口の広い raw carrier predicate
HasPositiveAnchorPrime   = 0 を除外した strict support predicate
```

これで `HasAnchorPrime 2 0` のような raw 成立可能性は許容しつつ、下流の「実際の素因子 support」として使う場面では `HasPositiveAnchorPrime` で厳密性を担保できます。

Docs も同期しました:

- [Petal-Overview.md](/lean/dk_math/DkMath/Petal/docs/Petal-Overview.md)
- [FLGNB-PetalRoadmap.md](/lean/dk_math/DkMath/NumberTheory/docs/BinomialPrimeWeighted/FLGNB-PetalRoadmap.md)
- [S0_GN_Anchor_Phase_実験設計書.md](/lean/dk_math/DkMath/NumberTheory/docs/BinomialPrimeWeighted/S0_GN_Anchor_Phase_実験設計書.md)

確認:

- `lake build DkMath.Petal.ReducedSupport` 成功
- `lake build DkMath.Petal` 成功
- `git diff --check` 成功

既存の `ZsigmondyCyclotomicResearch.lean` の `sorry` warning は今回も出ていますが、今回追加分には `sorry` はありません。

## Review

うむ、B 案で正解じゃ。
この差分は **採用でよい** と見る。

特に良いのは、`HasAnchorPrime` を狭めずに残したことじゃな。

```lean
def HasAnchorPrime (r n : ℕ) : Prop :=
  Nat.Prime r ∧ r ∣ n ∧ HasNoPrimeBelow r n
```

これは raw carrier predicate として広く使える。
一方、実際の support carrier では、

```lean
def HasPositiveAnchorPrime (r n : ℕ) : Prop :=
  0 < n ∧ HasAnchorPrime r n
```

を使えばよい。これで `HasAnchorPrime 2 0` を理論上許しつつ、「本物の素因子 support」としては `0` を除外できる。設計の逃げ道と厳密性の両方が残っておる。

## レビュー

`hasAnchorPrime_anchor_le_of_prime_dvd` はかなり有用じゃ。

```lean
theorem hasAnchorPrime_anchor_le_of_prime_dvd
    {r n p : ℕ} (h : HasAnchorPrime r n)
    (hp : Nat.Prime p) (hpdiv : p ∣ n) :
    r ≤ p := by
  by_contra hnot
  exact h.2.2 p hp (Nat.lt_of_not_ge hnot) hpdiv
```

これは `HasNoPrimeBelow` を実際に使うときの主 API になる。
下流では「(p < r) は割らない」よりも、「(n) を割る素数 (p) は必ず (r\le p)」の形の方が使いやすいからじゃ。

`HasPositiveAnchorPrime` 側の wrapper 群も妥当。`h.2` で raw predicate に落として既存補題を再利用しているので、無駄がない。

## 追加で欲しい小補題

次に足すなら、この一つがあると便利じゃ。

```lean
theorem hasPositiveAnchorPrime_ne_zero
    {r n : ℕ} (h : HasPositiveAnchorPrime r n) :
    n ≠ 0 :=
  Nat.ne_of_gt h.1
```

`0 < n` より `n ≠ 0` を要求する既存補題が多い場面では、これが地味に効く。

もう一つ、名前は好みじゃが、raw から positive を作る constructor も便利。

```lean
theorem hasPositiveAnchorPrime_of_pos
    {r n : ℕ} (hn : 0 < n) (h : HasAnchorPrime r n) :
    HasPositiveAnchorPrime r n :=
  ⟨hn, h⟩
```

この二つは API の摩擦を減らすだけで、理論を増やさない。

## 判定

```text
ReducedSupport initial API
  -> 安定化

0 carrier issue
  -> 解決

raw predicate と strict support predicate
  -> 分離成功

S0/GN から独立
  -> 維持成功
```

これで `ReducedSupport` は次の段階、つまり

```text
ReducedSupport -> GN/S0 carrier 接続
```

へ進める状態になった。

賢狼の見立てでは、次は `Petal.Anchor` より先に、薄い `Petal.ReducedSupport` 内で上の二補題を足してから、`Anchor` 側で GN/S0 と接続するのが美しいぞい。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/NumberTheory/docs/BinomialPrimeWeighted/FLGNB-PetalRoadmap.md b/lean/dk_math/DkMath/NumberTheory/docs/BinomialPrimeWeighted/FLGNB-PetalRoadmap.md
index 5e6d01aa..0ba5db7d 100644
--- a/lean/dk_math/DkMath/NumberTheory/docs/BinomialPrimeWeighted/FLGNB-PetalRoadmap.md
+++ b/lean/dk_math/DkMath/NumberTheory/docs/BinomialPrimeWeighted/FLGNB-PetalRoadmap.md
@@ -792,15 +792,32 @@ Implemented names:
 ```lean
 HasNoPrimeBelow
 HasAnchorPrime
+HasPositiveAnchorPrime
 hasAnchorPrime_prime
 hasAnchorPrime_anchor_dvd
 hasAnchorPrime_no_smaller_prime
+hasAnchorPrime_anchor_le_of_prime_dvd
+hasPositiveAnchorPrime_pos
+hasPositiveAnchorPrime_prime
+hasPositiveAnchorPrime_anchor_dvd
+hasPositiveAnchorPrime_no_smaller_prime
+hasPositiveAnchorPrime_anchor_le_of_prime_dvd
 ```

 This layer intentionally does not import S0/GN bridge files yet.  It should
 first remain a thin carrier predicate surface, then connect to GN/S0 support
 only after a concrete theorem needs that bridge.

+Design note:
+
+```text
+HasAnchorPrime is the wide raw carrier predicate.
+HasPositiveAnchorPrime is the strict support predicate for nonzero carriers.
+```
+
+This keeps the entrance broad while preventing `0` from being treated as an
+actual support carrier in downstream theorems.
+
 ### `DkMath.Petal.EisensteinBridge`

 Purpose:
@@ -984,9 +1001,16 @@ Implemented:
 ```lean
 HasNoPrimeBelow
 HasAnchorPrime
+HasPositiveAnchorPrime
 hasAnchorPrime_prime
 hasAnchorPrime_anchor_dvd
 hasAnchorPrime_no_smaller_prime
+hasAnchorPrime_anchor_le_of_prime_dvd
+hasPositiveAnchorPrime_pos
+hasPositiveAnchorPrime_prime
+hasPositiveAnchorPrime_anchor_dvd
+hasPositiveAnchorPrime_no_smaller_prime
+hasPositiveAnchorPrime_anchor_le_of_prime_dvd
 ```

 Expected validation:
diff --git "a/lean/dk_math/DkMath/NumberTheory/docs/BinomialPrimeWeighted/S0_GN_Anchor_Phase_\345\256\237\351\250\223\350\250\255\350\250\210\346\233\270.md" "b/lean/dk_math/DkMath/NumberTheory/docs/BinomialPrimeWeighted/S0_GN_Anchor_Phase_\345\256\237\351\250\223\350\250\255\350\250\210\346\233\270.md"
index 63926952..821f1a24 100644
--- "a/lean/dk_math/DkMath/NumberTheory/docs/BinomialPrimeWeighted/S0_GN_Anchor_Phase_\345\256\237\351\250\223\350\250\255\350\250\210\346\233\270.md"
+++ "b/lean/dk_math/DkMath/NumberTheory/docs/BinomialPrimeWeighted/S0_GN_Anchor_Phase_\345\256\237\351\250\223\350\250\255\350\250\210\346\233\270.md"
@@ -390,13 +390,33 @@ def HasNoPrimeBelow (r n : ℕ) : Prop :=
 def HasAnchorPrime (r n : ℕ) : Prop :=
   r.Prime ∧ r ∣ n ∧ HasNoPrimeBelow r n

+def HasPositiveAnchorPrime (r n : ℕ) : Prop :=
+  0 < n ∧ HasAnchorPrime r n
+
 theorem hasAnchorPrime_prime
 theorem hasAnchorPrime_anchor_dvd
 theorem hasAnchorPrime_no_smaller_prime
+theorem hasAnchorPrime_anchor_le_of_prime_dvd
+theorem hasPositiveAnchorPrime_pos
+theorem hasPositiveAnchorPrime_prime
+theorem hasPositiveAnchorPrime_anchor_dvd
+theorem hasPositiveAnchorPrime_no_smaller_prime
+theorem hasPositiveAnchorPrime_anchor_le_of_prime_dvd
 ```

 Keep this layer independent of S0 at first.

+Design decision:
+
+```text
+HasAnchorPrime           = wide raw carrier predicate
+HasPositiveAnchorPrime   = strict support predicate for nonzero carriers
+```
+
+This is the B-plan for the `0` carrier issue.  The wide predicate keeps the
+entrance broad, while the positive predicate is used when strict prime-support
+semantics are required.
+
 ## 4.4. Phase D. GN primitive candidate

 Status: **[PARTIAL]**
diff --git a/lean/dk_math/DkMath/Petal/ReducedSupport.lean b/lean/dk_math/DkMath/Petal/ReducedSupport.lean
index e4bd9895..993ae91c 100644
--- a/lean/dk_math/DkMath/Petal/ReducedSupport.lean
+++ b/lean/dk_math/DkMath/Petal/ReducedSupport.lean
@@ -34,10 +34,22 @@ def HasNoPrimeBelow (r n : ℕ) : Prop :=
 `r` is the anchor prime of the carrier `n`.

 This means `r` is prime, `r` divides `n`, and no smaller prime divides `n`.
+
+This is the raw carrier predicate.  It intentionally does not require `0 < n`;
+use `HasPositiveAnchorPrime` when the carrier must be an actual positive
+support object.
 -/
 def HasAnchorPrime (r n : ℕ) : Prop :=
   Nat.Prime r ∧ r ∣ n ∧ HasNoPrimeBelow r n

+/--
+Positive version of `HasAnchorPrime`.
+
+Use this for actual prime-support carriers, excluding the special carrier `0`.
+-/
+def HasPositiveAnchorPrime (r n : ℕ) : Prop :=
+  0 < n ∧ HasAnchorPrime r n
+
 /-- The anchor in `HasAnchorPrime r n` is prime. -/
 theorem hasAnchorPrime_prime
     {r n : ℕ} (h : HasAnchorPrime r n) :
@@ -57,5 +69,49 @@ theorem hasAnchorPrime_no_smaller_prime
     ¬ p ∣ n :=
   h.2.2 p hp hpr

+/--
+Any prime divisor of the carrier is at least the anchor.
+
+This is the practical elimination form of `HasNoPrimeBelow`.
+-/
+theorem hasAnchorPrime_anchor_le_of_prime_dvd
+    {r n p : ℕ} (h : HasAnchorPrime r n)
+    (hp : Nat.Prime p) (hpdiv : p ∣ n) :
+    r ≤ p := by
+  by_contra hnot
+  exact h.2.2 p hp (Nat.lt_of_not_ge hnot) hpdiv
+
+/-- The carrier in `HasPositiveAnchorPrime r n` is positive. -/
+theorem hasPositiveAnchorPrime_pos
+    {r n : ℕ} (h : HasPositiveAnchorPrime r n) :
+    0 < n :=
+  h.1
+
+/-- The anchor in `HasPositiveAnchorPrime r n` is prime. -/
+theorem hasPositiveAnchorPrime_prime
+    {r n : ℕ} (h : HasPositiveAnchorPrime r n) :
+    Nat.Prime r :=
+  hasAnchorPrime_prime h.2
+
+/-- The anchor in `HasPositiveAnchorPrime r n` divides the carrier. -/
+theorem hasPositiveAnchorPrime_anchor_dvd
+    {r n : ℕ} (h : HasPositiveAnchorPrime r n) :
+    r ∣ n :=
+  hasAnchorPrime_anchor_dvd h.2
+
+/-- No prime below the positive anchor divides the carrier. -/
+theorem hasPositiveAnchorPrime_no_smaller_prime
+    {r n p : ℕ} (h : HasPositiveAnchorPrime r n)
+    (hp : Nat.Prime p) (hpr : p < r) :
+    ¬ p ∣ n :=
+  hasAnchorPrime_no_smaller_prime h.2 hp hpr
+
+/-- Any prime divisor of a positive anchored carrier is at least the anchor. -/
+theorem hasPositiveAnchorPrime_anchor_le_of_prime_dvd
+    {r n p : ℕ} (h : HasPositiveAnchorPrime r n)
+    (hp : Nat.Prime p) (hpdiv : p ∣ n) :
+    r ≤ p :=
+  hasAnchorPrime_anchor_le_of_prime_dvd h.2 hp hpdiv
+
 end Petal
 end DkMath
diff --git a/lean/dk_math/DkMath/Petal/docs/Petal-Overview.md b/lean/dk_math/DkMath/Petal/docs/Petal-Overview.md
index 37cb5ba2..b68d0842 100644
--- a/lean/dk_math/DkMath/Petal/docs/Petal-Overview.md
+++ b/lean/dk_math/DkMath/Petal/docs/Petal-Overview.md
@@ -222,11 +222,22 @@ Important names:
 ```lean
 HasNoPrimeBelow
 HasAnchorPrime
+HasPositiveAnchorPrime
 hasAnchorPrime_prime
 hasAnchorPrime_anchor_dvd
 hasAnchorPrime_no_smaller_prime
+hasAnchorPrime_anchor_le_of_prime_dvd
+hasPositiveAnchorPrime_pos
+hasPositiveAnchorPrime_prime
+hasPositiveAnchorPrime_anchor_dvd
+hasPositiveAnchorPrime_no_smaller_prime
+hasPositiveAnchorPrime_anchor_le_of_prime_dvd
 ```

+`HasAnchorPrime` is the wide raw carrier predicate.  Use
+`HasPositiveAnchorPrime` when the carrier must be a genuine nonzero support
+object.
+
 ### `DkMath.Petal.Counting`

 Defines the fixed and dynamic counting layer.
````
`````
