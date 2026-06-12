# Git diff / Report / Review

## Add: Petal.ReducedSupport

gch: 35e57e167ff5dae4885f8133f274e818bc8b0bb8

## Report

進めました。

実装:

- [PrimitiveBridge.lean](/lean/dk_math/DkMath/Petal/PrimitiveBridge.lean:94)
  - `exists_prime_dvd_S0_nat_of_not_three_dvd_sub`
  - `PrimitiveOnS0` を知らない caller 向けに、`∃ q, Nat.Prime q ∧ q ∣ S0_nat c b ∧ ¬ q ∣ c - b` を直接返す projection です。

- [ReducedSupport.lean](/lean/dk_math/DkMath/Petal/ReducedSupport.lean:30)
  - `HasNoPrimeBelow`
  - `HasAnchorPrime`
  - `hasAnchorPrime_prime`
  - `hasAnchorPrime_anchor_dvd`
  - `hasAnchorPrime_no_smaller_prime`

- [Petal.lean](/lean/dk_math/DkMath/Petal.lean:8)
  - `DkMath.Petal.ReducedSupport` を集約 import に追加。

Docs:

- [Petal-Overview.md](/lean/dk_math/DkMath/Petal/docs/Petal-Overview.md:216)
  - `GcdBridge / PadicBridge / PrimitiveBridge / ReducedSupport` の小総括を追加。
- [FLGNB-PetalRoadmap.md](/lean/dk_math/DkMath/NumberTheory/docs/BinomialPrimeWeighted/FLGNB-PetalRoadmap.md:776)
  - Bridge 完了、`ReducedSupport` initial API 実装済みとして更新。

確認:

- `lake build DkMath.Petal.ReducedSupport` 成功
- `lake build DkMath.Petal.PrimitiveBridge` 成功
- `lake build DkMath.Petal` 成功
- `git diff --check` 成功

既存の `ZsigmondyCyclotomicResearch.lean` の `sorry` warning は引き続き出ていますが、今回追加分には `sorry` はありません。

## Review

うむ、これはかなり良い進捗じゃ。
わっちのレビュー結論はこう。

```text
実装方針: 良い
命名: 良い
本線との接続: 良い
ただし ReducedSupport に 0-carrier 問題の芽がある
```

## 1. 良い点

`PrimitiveBridge` の

```lean
exists_prime_dvd_S0_nat_of_not_three_dvd_sub
```

は、とても良い追加じゃ。`PrimitiveOnS0` を知らない caller が、

```lean
∃ q, Nat.Prime q ∧ q ∣ S0_nat c b ∧ ¬ q ∣ c - b
```

を直接得られる。これは downstream でかなり使いやすい。
「構造体を返す theorem」と「素朴な存在命題を返す theorem」の両方があるのは、Lean API として強い。

`ReducedSupport.lean` も、今の段階では正しく薄い。

```lean
HasNoPrimeBelow
HasAnchorPrime
```

を S0/GN から独立させたのは正解じゃ。ここで GN を import してしまうと、`ReducedSupport` が理論依存を持ちすぎる。まず carrier predicate として自立させた判断は賢い。

## 2. 注意点: `HasAnchorPrime r 0` 問題

ただし、ここは少し危ない。

現在の定義は、

```lean
def HasAnchorPrime (r n : ℕ) : Prop :=
  Nat.Prime r ∧ r ∣ n ∧ HasNoPrimeBelow r n
```

じゃな。

このとき、

```lean
HasAnchorPrime 2 0
```

が成立し得る。

理由は、

```lean
Nat.Prime 2
2 ∣ 0
HasNoPrimeBelow 2 0
```

で、`2` より小さい素数は存在しないため、`HasNoPrimeBelow 2 0` が空虚真になるからじゃ。

だが「carrier の anchor prime」という意味では、(0) はすべての素数で割れる特異 carrier なので、たぶん含めたくないはずじゃ。

対策は二択。

### A. 定義に positivity を入れる

```lean
def HasAnchorPrime (r n : ℕ) : Prop :=
  0 < n ∧ Nat.Prime r ∧ r ∣ n ∧ HasNoPrimeBelow r n
```

これは意味として一番安全。

### B. 現定義は残し、正の版を追加する

```lean
def HasPositiveAnchorPrime (r n : ℕ) : Prop :=
  0 < n ∧ HasAnchorPrime r n
```

既存 API を壊したくないなら、こちらが保守的じゃ。

わっちの推奨は **B** 。
今の `HasAnchorPrime` は薄い predicate として残し、実際の素因子 support で使うときは `HasPositiveAnchorPrime` を使う。

## 3. 次に足すと良い補題

次はこのあたりが欲しい。

```lean
theorem hasAnchorPrime_not_dvd_smaller
    {r n p : ℕ} (h : HasAnchorPrime r n)
    (hp : Nat.Prime p) (hpdiv : p ∣ n) :
    r ≤ p
```

これは `HasNoPrimeBelow` の実用形じゃ。
「(n) を割る素数は anchor 未満ではあり得ない」を直接使える。

もし positive 版を入れるなら、

```lean
theorem hasPositiveAnchorPrime_pos
theorem hasPositiveAnchorPrime_prime
theorem hasPositiveAnchorPrime_anchor_dvd
theorem hasPositiveAnchorPrime_no_smaller_prime
theorem hasPositiveAnchorPrime_anchor_le_of_prime_dvd
```

この辺りが良い。

## 4. ドキュメント更新について

`FLGNB-PetalRoadmap.md` の更新は妥当じゃ。

特に、

```text
This completed the Petal-side Zsigmondy preparation bridge for the cubic S0 surface.
The remaining experiment is the reduced-support / anchor vocabulary,
not the S0/GN bridge itself.
```

この整理は非常に良い。
S0/GN bridge はもう「計画」ではなく **完了済み橋** 。残るのは anchor/reduced support 側、という切り分けが明確になった。

## 5. 判定

今回の差分は採用でよいと思う。

ただし次 commit で、

```text
HasAnchorPrime 2 0
```

が意図せず真になる点だけは、早めに設計判断しておくのがよい。

わっちなら次の小パッチを勧める。

```text
Add: HasPositiveAnchorPrime
Add: hasAnchorPrime_anchor_le_of_prime_dvd
Docs: HasAnchorPrime is a raw carrier predicate; positive support should use HasPositiveAnchorPrime
```

これで `ReducedSupport` はかなり安定する。
うむ、Petal 側は想定よりずっと速く、Zsigmondy の麓まで道が敷かれてきたのう。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/NumberTheory/docs/BinomialPrimeWeighted/FLGNB-PetalRoadmap.md b/lean/dk_math/DkMath/NumberTheory/docs/BinomialPrimeWeighted/FLGNB-PetalRoadmap.md
index d73b619c..5e6d01aa 100644
--- a/lean/dk_math/DkMath/NumberTheory/docs/BinomialPrimeWeighted/FLGNB-PetalRoadmap.md
+++ b/lean/dk_math/DkMath/NumberTheory/docs/BinomialPrimeWeighted/FLGNB-PetalRoadmap.md
@@ -744,6 +744,63 @@ theorem GN_three_sub_eq_S0_nat
 This file should also collect p-adic bridge statements where the S0 theorem is
 only a rewritten GN theorem.
 
+Status:
+
+```text
+completed
+```
+
+Implemented bridge files:
+
+```text
+DkMath.Petal.GcdBridge
+DkMath.Petal.PadicBridge
+DkMath.Petal.PrimitiveBridge
+```
+
+Important names:
+
+```lean
+gcd_sub_S0_nat_eq_gcd_sub_three
+padicValNat_cube_sub_eq_padicValNat_S0_nat_of_not_dvd_sub
+primitive_prime_dvd_S0_nat
+primitive_prime_padicValNat_cube_sub_eq_S0_nat
+primitiveOnS0_of_prime_dvd_cube_sub_not_dvd_sub
+exists_prime_dvd_S0_nat_of_not_three_dvd_sub
+```
+
+This completed the Petal-side Zsigmondy preparation bridge for the cubic S0
+surface.  The remaining experiment is the reduced-support / anchor vocabulary,
+not the S0/GN bridge itself.
+
+### `DkMath.Petal.ReducedSupport`
+
+Purpose:
+
+```text
+introduce a small carrier-level vocabulary for r-started prime support
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
+HasNoPrimeBelow
+HasAnchorPrime
+hasAnchorPrime_prime
+hasAnchorPrime_anchor_dvd
+hasAnchorPrime_no_smaller_prime
+```
+
+This layer intentionally does not import S0/GN bridge files yet.  It should
+first remain a thin carrier predicate surface, then connect to GN/S0 support
+only after a concrete theorem needs that bridge.
+
 ### `DkMath.Petal.EisensteinBridge`
 
 Purpose:
@@ -886,7 +943,7 @@ lake build DkMath.Petal
 Status:
 
 ```text
-planned
+completed
 ```
 
 Transfer the existing GN gcd statements to S0-facing names.
@@ -900,6 +957,45 @@ GN_three_sub_eq_S0_nat
 This step should not invent new gcd theory.  It should provide link theorem
 names that downstream FLT and primitive-factor files can import.
 
+Implemented as the three bridge files:
+
+```text
+DkMath/Petal/GcdBridge.lean
+DkMath/Petal/PadicBridge.lean
+DkMath/Petal/PrimitiveBridge.lean
+```
+
+Additional caller-friendly projection:
+
+```lean
+exists_prime_dvd_S0_nat_of_not_three_dvd_sub
+```
+
+### Step 5.5: Add `DkMath.Petal.ReducedSupport`
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
+HasNoPrimeBelow
+HasAnchorPrime
+hasAnchorPrime_prime
+hasAnchorPrime_anchor_dvd
+hasAnchorPrime_no_smaller_prime
+```
+
+Expected validation:
+
+```sh
+lake build DkMath.Petal.ReducedSupport
+lake build DkMath.Petal
+```
+
 ### Step 6: Add `DkMath.Petal.EisensteinBridge`
 
 Status:
diff --git a/lean/dk_math/DkMath/Petal.lean b/lean/dk_math/DkMath/Petal.lean
index 44e8ea02..4f69d814 100644
--- a/lean/dk_math/DkMath/Petal.lean
+++ b/lean/dk_math/DkMath/Petal.lean
@@ -5,6 +5,7 @@ Authors: D. and Wise Wolf.
 -/
 
 import DkMath.Petal.Basic
+import DkMath.Petal.ReducedSupport
 import DkMath.Petal.Counting
 import DkMath.Petal.Address
 import DkMath.Petal.Forms
diff --git a/lean/dk_math/DkMath/Petal/PrimitiveBridge.lean b/lean/dk_math/DkMath/Petal/PrimitiveBridge.lean
index f79bb9e5..453c20c7 100644
--- a/lean/dk_math/DkMath/Petal/PrimitiveBridge.lean
+++ b/lean/dk_math/DkMath/Petal/PrimitiveBridge.lean
@@ -85,5 +85,18 @@ theorem exists_primitiveOnS0_of_not_three_dvd_sub
       hbc hb hcop h3 with ⟨q, hq, hq_dvd, hq_not_dvd_sub⟩
   exact ⟨q, primitiveOnS0_of_prime_dvd_cube_sub_not_dvd_sub hbc hq hq_dvd hq_not_dvd_sub⟩
 
+/--
+Petal-facing projection of the primitive witness.
+
+If the boundary gap is not divisible by `3`, then `S0_nat` has a prime divisor
+that does not divide the boundary gap.
+-/
+theorem exists_prime_dvd_S0_nat_of_not_three_dvd_sub
+    {c b : ℕ} (hbc : b < c) (hb : 0 < b)
+    (hcop : Nat.Coprime c b) (h3 : ¬ 3 ∣ c - b) :
+    ∃ q : ℕ, Nat.Prime q ∧ q ∣ S0_nat c b ∧ ¬ q ∣ c - b := by
+  rcases exists_primitiveOnS0_of_not_three_dvd_sub hbc hb hcop h3 with ⟨q, hprim⟩
+  exact ⟨q, hprim.1, hprim.2.1, hprim.2.2⟩
+
 end Petal
 end DkMath
diff --git a/lean/dk_math/DkMath/Petal/ReducedSupport.lean b/lean/dk_math/DkMath/Petal/ReducedSupport.lean
new file mode 100644
index 00000000..e4bd9895
--- /dev/null
+++ b/lean/dk_math/DkMath/Petal/ReducedSupport.lean
@@ -0,0 +1,61 @@
+/-
+Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
+Released under MIT license as described in the file LICENSE.
+Authors: D. and Wise Wolf.
+-/
+
+import DkMath.Petal.Basic
+
+#print "file: DkMath.Petal.ReducedSupport"
+
+/-!
+# Petal Reduced Support
+
+This file introduces a small support vocabulary for later anchor-prime
+observations.
+
+It deliberately does not import the `S0` / `GN` bridge files.  The first layer
+only says that a carrier has no prime support below a chosen anchor, and that
+the anchor prime itself divides the carrier.
+-/
+
+namespace DkMath
+namespace Petal
+
+/--
+`n` has no prime divisor below `r`.
+
+This is the reduced-support predicate for an `r`-started observation world.
+-/
+def HasNoPrimeBelow (r n : ℕ) : Prop :=
+  ∀ p, Nat.Prime p → p < r → ¬ p ∣ n
+
+/--
+`r` is the anchor prime of the carrier `n`.
+
+This means `r` is prime, `r` divides `n`, and no smaller prime divides `n`.
+-/
+def HasAnchorPrime (r n : ℕ) : Prop :=
+  Nat.Prime r ∧ r ∣ n ∧ HasNoPrimeBelow r n
+
+/-- The anchor in `HasAnchorPrime r n` is prime. -/
+theorem hasAnchorPrime_prime
+    {r n : ℕ} (h : HasAnchorPrime r n) :
+    Nat.Prime r :=
+  h.1
+
+/-- The anchor in `HasAnchorPrime r n` divides the carrier. -/
+theorem hasAnchorPrime_anchor_dvd
+    {r n : ℕ} (h : HasAnchorPrime r n) :
+    r ∣ n :=
+  h.2.1
+
+/-- No prime below the anchor divides the carrier. -/
+theorem hasAnchorPrime_no_smaller_prime
+    {r n p : ℕ} (h : HasAnchorPrime r n)
+    (hp : Nat.Prime p) (hpr : p < r) :
+    ¬ p ∣ n :=
+  h.2.2 p hp hpr
+
+end Petal
+end DkMath
diff --git a/lean/dk_math/DkMath/Petal/docs/Petal-Overview.md b/lean/dk_math/DkMath/Petal/docs/Petal-Overview.md
index 82d9378f..37cb5ba2 100644
--- a/lean/dk_math/DkMath/Petal/docs/Petal-Overview.md
+++ b/lean/dk_math/DkMath/Petal/docs/Petal-Overview.md
@@ -176,6 +176,57 @@ GN 3
   -> divisibility observation
 ```
 
+### `DkMath.Petal.GcdBridge`
+
+Transfers existing degree-three GN gcd control to the `S0_nat` surface.
+
+Important names:
+
+```lean
+gcd_sub_S0_nat_eq_gcd_sub_three
+gcd_sub_S0_nat_dvd_three
+coprime_sub_S0_nat_of_coprime_of_not_dvd_three
+```
+
+### `DkMath.Petal.PadicBridge`
+
+Reads boundary-free cubic valuations on the `S0_nat` surface.
+
+Important names:
+
+```lean
+padicValNat_cube_sub_eq_padicValNat_S0_nat_of_not_dvd_sub
+padicValNat_three_cube_sub_eq_padicValNat_three_S0_nat_of_not_dvd_sub
+```
+
+### `DkMath.Petal.PrimitiveBridge`
+
+Connects degree-three primitive-prime witnesses to `S0_nat`.
+
+Important names:
+
+```lean
+primitive_prime_dvd_S0_nat
+primitive_prime_padicValNat_cube_sub_eq_S0_nat
+primitiveOnS0_of_prime_dvd_cube_sub_not_dvd_sub
+exists_primitiveOnS0_of_not_three_dvd_sub
+exists_prime_dvd_S0_nat_of_not_three_dvd_sub
+```
+
+### `DkMath.Petal.ReducedSupport`
+
+Introduces the reduced-support vocabulary for anchor-prime observations.
+
+Important names:
+
+```lean
+HasNoPrimeBelow
+HasAnchorPrime
+hasAnchorPrime_prime
+hasAnchorPrime_anchor_dvd
+hasAnchorPrime_no_smaller_prime
+```
+
 ### `DkMath.Petal.Counting`
 
 Defines the fixed and dynamic counting layer.
@@ -323,20 +374,18 @@ how GN degree 3 becomes the Petal S0 face
 The next reasonable implementation directions are:
 
 ```text
-1. connect strict prime-base orbits to a concrete prime enumeration
-2. add Petal-facing gcd / p-adic bridge files
-3. use Petal address decomposition in nested observations
-4. connect GN / Petal divisibility persistence to primitive-factor statements
+1. connect ReducedSupport to GN/S0 carriers
+2. use Petal address decomposition in nested observations
+3. connect strict prime-base orbits to a concrete prime enumeration
+4. decide whether GNPrimitiveCandidate needs a separate vocabulary layer
 ```
 
 The most conservative next theorem work is probably:
 
 ```text
-DkMath.Petal.GcdBridge
+DkMath.Petal.Anchor
 ```
 
-with bridge statements rewritten from existing GN gcd theorems.
-
 The most concrete arithmetic next step is:
 
 ```text
````
`````
