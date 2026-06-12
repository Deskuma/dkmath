# Git diff / Report / Review

## Add: Petal: BoundaryD3, Anchor

gch: 63b7bae682015d632ad523821b5e4202c1777b5e

## Report

実装と整理を進めました。

`DkMath.Petal.Anchor` に reviewer 指摘の projection を追加しました。

- `anchoredS0Carrier_anchor_prime`
- `anchoredGNCarrier_anchor_prime`

新規に [BoundaryD3.lean](/lean/dk_math/DkMath/Petal/BoundaryD3.lean) を追加し、3 次 Petal 境界を固定しました。

- `BoundaryD3Branch`
- `BoundaryD3Reduced`
- `three_dvd_S0_nat_of_three_dvd_sub`
- `three_dvd_sub_of_three_dvd_S0_nat`
- `three_dvd_S0_nat_iff_three_dvd_sub`
- `boundaryD3Reduced_three_not_dvd_S0_nat`
- `boundaryD3Branch_three_dvd_S0_nat`
- `boundaryD3Reduced_coprime_sub_S0_nat`

意味としては、

```text
3 ∣ S0_nat c b  ↔  3 ∣ c - b
```

を Petal 用語として固定し、reduced branch では `S0_nat` と境界 gap の gcd 制御へ接続できる形にしました。

docs も更新済みです。

- [Petal-Overview.md](/lean/dk_math/DkMath/Petal/docs/Petal-Overview.md)
- [FLGNB-PetalRoadmap.md](/lean/dk_math/DkMath/NumberTheory/docs/BinomialPrimeWeighted/FLGNB-PetalRoadmap.md)
- [S0_GN_Anchor_Phase_実験設計書.md](/lean/dk_math/DkMath/NumberTheory/docs/BinomialPrimeWeighted/S0_GN_Anchor_Phase_実験設計書.md)

検証:

```sh
lake build DkMath.Petal
git diff --check
```

どちらも成功です。既存の `ZsigmondyCyclotomicResearch.lean` の `sorry` 警告だけ出ていますが、今回追加分では新しい `sorry` はありません。

## Review

うむ、これは **かなり重要な節目** じゃ。
`BoundaryD3.lean` の追加で、ずっと懸念だった **S0 (d=3) の 3 例外** が、Research の反例処理から本線 API へ昇格し始めた。

結論から言うと、この差分は **採用でよい**。
しかも、ここまで来ると `GcdNextResearch.lean` 側の反例固定は、かなり「本線に吸い上げ可能」になっておる。

## 1. `Anchor` projection 追加は妥当

追加された二つは素直に良い。

```lean
anchoredS0Carrier_anchor_prime
anchoredGNCarrier_anchor_prime
```

これで下流では、

```lean
anchoredS0Carrier_anchor h
```

から `HasPositiveAnchorPrime` を取り出して、さらに `Nat.Prime r` へ辿る必要が減る。

`AnchoredS0Carrier` / `AnchoredGNCarrier` は今後、primitive witness や boundary split の入力になっていくので、`anchor_prime` はほぼ必須 API じゃ。

## 2. `BoundaryD3` は方向性がかなり良い

今回の中心はここじゃな。

```lean
def BoundaryD3Branch (c b : ℕ) : Prop :=
  3 ∣ c - b

def BoundaryD3Reduced (c b : ℕ) : Prop :=
  ¬ 3 ∣ c - b
```

これは良い。
`q ≠ 3` を散らすのではなく、まず三次境界を

```text
3-boundary branch
reduced branch
```

として名前付き分岐にした。これにより、今後の証明で

```lean
by_cases h3 : 3 ∣ c - b
```

が単なる場合分けではなく、

```lean
BoundaryD3Branch c b
BoundaryD3Reduced c b
```

という意味を持った分岐になる。

## 3. `3 ∣ S0 ↔ 3 ∣ c-b` の固定は大きい

今回の API の核はこれじゃ。

```lean
three_dvd_S0_nat_iff_three_dvd_sub
```

意味は、

```text
3 ∣ S0_nat c b  iff  3 ∣ (c - b)
```

これは、S0 (d=3) の例外処理に対してかなり決定的じゃ。

今までは、

```text
3 が例外として出てしまう
```

だったものが、今は

```text
3 は S0 と boundary gap の接触成分であり、
その接触は 3 ∣ c-b と完全に同値
```

になった。

これは「反例処理」から「構造分類」への昇格じゃ。

## 4. `boundaryD3Reduced_coprime_sub_S0_nat` は本線 API として良い

```lean
theorem boundaryD3Reduced_coprime_sub_S0_nat
    {c b : ℕ} (hbc : b < c) (hcop : Nat.Coprime c b)
    (h : BoundaryD3Reduced c b) :
    Nat.Coprime (c - b) (S0_nat c b)
```

これは downstream でかなり使いやすい。

意味は、

```text
reduced branch では、境界 gap と S0 は互いに素
```

じゃ。
これがあることで、

```text
primitive witness は boundary ではなく S0/GN 側にいる
```

を語りやすくなる。

特に `exists_anchoredS0Carrier_of_not_three_dvd_sub` と並ぶと、

```text
BoundaryD3Reduced
  -> S0 と boundary は分離
  -> primitive witness exists on S0
  -> witness can be read as AnchoredS0Carrier
```

という導線ができておる。

## 5. 一点だけ気になるところ

`three_dvd_S0_nat_of_three_dvd_sub` の証明は現状でも通っているので問題ないが、手作業の式変形が少し重い。

```lean
rcases h3 with ⟨k, hk⟩
have hc_eq : c = 3 * k + b := by
...
refine ⟨b ^ 2 + 3 * k * b + 3 * k ^ 2, ?_⟩
rw [hc_eq]
unfold S0_nat
ring
```

これは悪くない。
ただし将来、似た補題が増えるなら、より基礎的な mod 3 lemma に寄せる案もある。

例えば概念的には、

```text
c ≡ b mod 3
  -> c^2 + cb + b^2 ≡ 3b^2 ≡ 0 mod 3
```

じゃな。

今はこのままでよい。
ただ、後で `EisensteinBridge` に進むなら、この補題は Eisenstein norm / mod 3 route で再利用できるかもしれぬ。

## 6. import 方針も良い

```lean
import DkMath.Petal.GcdBridge
```

だけで `BoundaryD3` を作っているのは良い。
`*Research.lean` を import していない。これが最重要。

`open DkMath.FLT.PetalDetect` はまだ残っているが、これは `S0_nat` の現在地の問題じゃな。今すぐ NG ではない。
ただし、将来的には Petal 側で `S0_nat` を再 export / alias して、`BoundaryD3.lean` が FLT namespace を意識しないようにするのが綺麗じゃ。

## 7. 次に足すなら

`BoundaryD3` に、分岐の排中・判定補題を足すと使いやすくなるかもしれぬ。

```lean
theorem boundaryD3Branch_or_reduced
    (c b : ℕ) :
    BoundaryD3Branch c b ∨ BoundaryD3Reduced c b := by
  by_cases h : 3 ∣ c - b
  · exact Or.inl h
  · exact Or.inr h
```

または reduced から branch でないこと。

```lean
theorem not_boundaryD3Branch_of_reduced
    {c b : ℕ} (h : BoundaryD3Reduced c b) :
    ¬ BoundaryD3Branch c b :=
  h
```

ただし、これは薄い wrapper なので、今すぐ必須ではない。
もし downstream で case split を頻繁にするなら足せばよい。

より価値が高そうなのは、`Anchor` と `BoundaryD3` の接続じゃ。

```lean
theorem exists_anchoredS0Carrier_of_boundaryD3Reduced
    {c b : ℕ} (hbc : b < c) (hb : 0 < b)
    (hcop : Nat.Coprime c b)
    (hred : BoundaryD3Reduced c b) :
    ∃ q : ℕ, AnchoredS0Carrier q c b q ∧ ¬ q ∣ c - b
```

これは既存の

```lean
exists_anchoredS0Carrier_of_not_three_dvd_sub
```

を `BoundaryD3Reduced` 名で包むだけじゃが、API としてはかなり美しい。

`BoundaryD3Reduced` を使う downstream では、`¬ 3 ∣ c-b` に戻さず済む。

## 8. 判定

```text
Anchor projection
  -> 採用可

BoundaryD3Branch / BoundaryD3Reduced
  -> 採用可

3 ∣ S0 iff 3 ∣ boundary
  -> S0 d=3 例外分類の本線 API として重要

Reduced branch coprime theorem
  -> downstream 向けに強い

Research import 排除
  -> 達成

次の推奨
  -> BoundaryD3Reduced から anchored S0 witness への wrapper
```

## 結論

これは **GcdNextResearch の反例固定を本線 API に昇格する第一段として成功** じゃ。

今の到達点はこう言える。

```text
S0 d=3 の 3 例外は、もはや場当たり的な例外ではない。
BoundaryD3Branch と BoundaryD3Reduced によって、
3-primary contact と reduced S0 surface として分類された。
```

ここからは `BoundaryD3` を入口にして、

```text
BoundaryD3Reduced
  -> coprime boundary/S0
  -> anchored primitive S0 witness
  -> future FLT / Zsigmondy-facing API
```

へ繋ぐのが自然じゃ。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/NumberTheory/docs/BinomialPrimeWeighted/FLGNB-PetalRoadmap.md b/lean/dk_math/DkMath/NumberTheory/docs/BinomialPrimeWeighted/FLGNB-PetalRoadmap.md
index 067ce600..31b06f18 100644
--- a/lean/dk_math/DkMath/NumberTheory/docs/BinomialPrimeWeighted/FLGNB-PetalRoadmap.md
+++ b/lean/dk_math/DkMath/NumberTheory/docs/BinomialPrimeWeighted/FLGNB-PetalRoadmap.md
@@ -841,11 +841,13 @@ Implemented names:
 AnchoredS0Carrier
 AnchoredGNCarrier
 anchoredS0Carrier_anchor
+anchoredS0Carrier_anchor_prime
 anchoredS0Carrier_dvd_S0
 anchoredS0Carrier_pos
 anchoredS0Carrier_ne_zero
 anchoredS0Carrier_anchor_le_of_prime_dvd
 anchoredGNCarrier_anchor
+anchoredGNCarrier_anchor_prime
 anchoredGNCarrier_dvd_GN
 anchoredGNCarrier_pos
 anchoredGNCarrier_ne_zero
@@ -858,6 +860,44 @@ exists_anchoredS0Carrier_of_not_three_dvd_sub
 This layer is the first place where `ReducedSupport` imports meet the S0/GN
 surface.  `ReducedSupport` itself remains independent.
 
+### `DkMath.Petal.BoundaryD3`
+
+Purpose:
+
+```text
+record the degree-three split between the 3-boundary branch and the reduced
+S0 branch
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
+BoundaryD3Branch
+BoundaryD3Reduced
+three_dvd_S0_nat_of_three_dvd_sub
+three_dvd_sub_of_three_dvd_S0_nat
+three_dvd_S0_nat_iff_three_dvd_sub
+boundaryD3Reduced_three_not_dvd_S0_nat
+boundaryD3Branch_three_dvd_S0_nat
+boundaryD3Reduced_coprime_sub_S0_nat
+```
+
+This layer makes the cubic contact prime explicit:
+
+```text
+3 | S0_nat c b  iff  3 | (c - b)
+```
+
+In the reduced branch, and under `Nat.Coprime c b`, the boundary gap is
+coprime to `S0_nat c b`.  This is the usable S0 surface for primitive and
+Zsigmondy-facing arguments.
+
 ### `DkMath.Petal.EisensteinBridge`
 
 Purpose:
@@ -1076,6 +1116,8 @@ Implemented:
 ```lean
 AnchoredS0Carrier
 AnchoredGNCarrier
+anchoredS0Carrier_anchor_prime
+anchoredGNCarrier_anchor_prime
 anchoredGNCarrier_of_anchoredS0Carrier
 anchoredS0Carrier_of_anchoredGNCarrier
 exists_anchoredS0Carrier_of_not_three_dvd_sub
@@ -1088,6 +1130,34 @@ lake build DkMath.Petal.Anchor
 lake build DkMath.Petal
 ```
 
+### Step 5.7: Add `DkMath.Petal.BoundaryD3`
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
+BoundaryD3Branch
+BoundaryD3Reduced
+three_dvd_S0_nat_of_three_dvd_sub
+three_dvd_sub_of_three_dvd_S0_nat
+three_dvd_S0_nat_iff_three_dvd_sub
+boundaryD3Reduced_three_not_dvd_S0_nat
+boundaryD3Branch_three_dvd_S0_nat
+boundaryD3Reduced_coprime_sub_S0_nat
+```
+
+Expected validation:
+
+```sh
+lake build DkMath.Petal.BoundaryD3
+lake build DkMath.Petal
+```
+
 ### Step 6: Add `DkMath.Petal.EisensteinBridge`
 
 Status:
diff --git "a/lean/dk_math/DkMath/NumberTheory/docs/BinomialPrimeWeighted/S0_GN_Anchor_Phase_\345\256\237\351\250\223\350\250\255\350\250\210\346\233\270.md" "b/lean/dk_math/DkMath/NumberTheory/docs/BinomialPrimeWeighted/S0_GN_Anchor_Phase_\345\256\237\351\250\223\350\250\255\350\250\210\346\233\270.md"
index f7fb0300..e99103fc 100644
--- "a/lean/dk_math/DkMath/NumberTheory/docs/BinomialPrimeWeighted/S0_GN_Anchor_Phase_\345\256\237\351\250\223\350\250\255\350\250\210\346\233\270.md"
+++ "b/lean/dk_math/DkMath/NumberTheory/docs/BinomialPrimeWeighted/S0_GN_Anchor_Phase_\345\256\237\351\250\223\350\250\255\350\250\210\346\233\270.md"
@@ -285,7 +285,7 @@ DkMath.FLT.cube_sub_eq_mul_sub_S0
 
 ## 4.2. Phase B. 三例外の構造分離
 
-Status: **[DONE FOR S0] / [ACTIVE FOR GENERAL REDUCED SUPPORT]**
+Status: **[DONE FOR S0] / [PACKAGE API IMPLEMENTED AS `DkMath.Petal.BoundaryD3`]**
 
 目的は、\(3\) が S0 と境界にまたがることを明示することである。
 
@@ -322,6 +322,19 @@ DkMath.Petal.gcd_sub_S0_nat_dvd_three
 DkMath.Petal.coprime_sub_S0_nat_of_coprime_of_not_dvd_three
 ```
 
+BoundaryD3 package names:
+
+```lean
+DkMath.Petal.BoundaryD3Branch
+DkMath.Petal.BoundaryD3Reduced
+DkMath.Petal.three_dvd_S0_nat_of_three_dvd_sub
+DkMath.Petal.three_dvd_sub_of_three_dvd_S0_nat
+DkMath.Petal.three_dvd_S0_nat_iff_three_dvd_sub
+DkMath.Petal.boundaryD3Reduced_three_not_dvd_S0_nat
+DkMath.Petal.boundaryD3Branch_three_dvd_S0_nat
+DkMath.Petal.boundaryD3Reduced_coprime_sub_S0_nat
+```
+
 The stronger gcd formula makes the original one-way experiment less important:
 
 ```text
@@ -330,9 +343,21 @@ gcd(c - b, S0(c,b)) = gcd(c - b, 3)
 
 This is the desired "3-primary contact" observation for the cubic Petal face.
 
+The current `BoundaryD3` layer packages this as a branch/reduced-branch
+interface:
+
+```text
+BoundaryD3Branch c b   := 3 | (c - b)
+BoundaryD3Reduced c b  := not 3 | (c - b)
+```
+
+Thus the experiment is no longer only a proposed calculation.  It is now a
+named Petal package layer that can be imported by primitive or Zsigmondy-facing
+files.
+
 ## 4.3. Phase C. (r)-anchor reduced support
 
-Status: **[ACTIVE]**
+Status: **[INITIAL API IMPLEMENTED AS `DkMath.Petal.ReducedSupport`]**
 
 目的は、\(3,5,7,11,\dots\) から始まる世界を、射影・同型的な観測面として Lean に置くことである。
 
@@ -420,9 +445,15 @@ This is the B-plan for the `0` carrier issue.  The wide predicate keeps the
 entrance broad, while the positive predicate is used when strict prime-support
 semantics are required.
 
+The initial API has been implemented in:
+
+```text
+lean/dk_math/DkMath/Petal/ReducedSupport.lean
+```
+
 ## 4.4. Phase D. GN primitive candidate
 
-Status: **[PARTIAL]**
+Status: **[PARTIAL] / [ANCHOR CARRIER SURFACE IMPLEMENTED]**
 
 目的は、GN 側に現れる素因子を primitive candidate として包装することである。
 
diff --git a/lean/dk_math/DkMath/Petal.lean b/lean/dk_math/DkMath/Petal.lean
index 93f041dc..5e60e74b 100644
--- a/lean/dk_math/DkMath/Petal.lean
+++ b/lean/dk_math/DkMath/Petal.lean
@@ -16,6 +16,7 @@ import DkMath.Petal.GcdBridge
 import DkMath.Petal.PadicBridge
 import DkMath.Petal.PrimitiveBridge
 import DkMath.Petal.Anchor
+import DkMath.Petal.BoundaryD3
 
 #print "file: DkMath.Petal"
 
diff --git a/lean/dk_math/DkMath/Petal/Anchor.lean b/lean/dk_math/DkMath/Petal/Anchor.lean
index e6126f62..9eee2b26 100644
--- a/lean/dk_math/DkMath/Petal/Anchor.lean
+++ b/lean/dk_math/DkMath/Petal/Anchor.lean
@@ -45,6 +45,12 @@ theorem anchoredS0Carrier_anchor
     HasPositiveAnchorPrime r n :=
   h.1
 
+/-- The anchor of an anchored `S0_nat` carrier is prime. -/
+theorem anchoredS0Carrier_anchor_prime
+    {r c b n : ℕ} (h : AnchoredS0Carrier r c b n) :
+    Nat.Prime r :=
+  hasPositiveAnchorPrime_prime h.1
+
 /-- Extract the divisibility statement from an anchored `S0_nat` carrier. -/
 theorem anchoredS0Carrier_dvd_S0
     {r c b n : ℕ} (h : AnchoredS0Carrier r c b n) :
@@ -76,6 +82,12 @@ theorem anchoredGNCarrier_anchor
     HasPositiveAnchorPrime r n :=
   h.1
 
+/-- The anchor of an anchored GN carrier is prime. -/
+theorem anchoredGNCarrier_anchor_prime
+    {r d x u n : ℕ} (h : AnchoredGNCarrier r d x u n) :
+    Nat.Prime r :=
+  hasPositiveAnchorPrime_prime h.1
+
 /-- Extract the divisibility statement from an anchored GN carrier. -/
 theorem anchoredGNCarrier_dvd_GN
     {r d x u n : ℕ} (h : AnchoredGNCarrier r d x u n) :
diff --git a/lean/dk_math/DkMath/Petal/BoundaryD3.lean b/lean/dk_math/DkMath/Petal/BoundaryD3.lean
new file mode 100644
index 00000000..b088b24c
--- /dev/null
+++ b/lean/dk_math/DkMath/Petal/BoundaryD3.lean
@@ -0,0 +1,91 @@
+/-
+Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
+Released under MIT license as described in the file LICENSE.
+Authors: D. and Wise Wolf.
+-/
+
+import DkMath.Petal.GcdBridge
+
+#print "file: DkMath.Petal.BoundaryD3"
+
+/-!
+# Petal Boundary D3
+
+This file records the degree-three boundary behavior of the Petal detector
+`S0_nat`.
+
+The central observation is that, on the cubic Petal face, the prime `3` is
+exactly the contact component between the boundary gap `c - b` and `S0_nat`.
+-/
+
+namespace DkMath
+namespace Petal
+
+open DkMath.FLT.PetalDetect
+
+/-- The degree-three boundary branch: `3` divides the boundary gap. -/
+def BoundaryD3Branch (c b : ℕ) : Prop :=
+  3 ∣ c - b
+
+/-- The degree-three reduced branch: `3` does not divide the boundary gap. -/
+def BoundaryD3Reduced (c b : ℕ) : Prop :=
+  ¬ 3 ∣ c - b
+
+/--
+On the degree-three boundary branch, `3` divides the Petal detector `S0_nat`.
+-/
+theorem three_dvd_S0_nat_of_three_dvd_sub
+    {c b : ℕ} (hbc : b < c) (h3 : 3 ∣ c - b) :
+    3 ∣ S0_nat c b := by
+  rcases h3 with ⟨k, hk⟩
+  have hc_eq : c = 3 * k + b := by
+    calc
+      c = (c - b) + b := (Nat.sub_add_cancel hbc.le).symm
+      _ = 3 * k + b := by rw [hk]
+  refine ⟨b ^ 2 + 3 * k * b + 3 * k ^ 2, ?_⟩
+  rw [hc_eq]
+  unfold S0_nat
+  ring
+
+/--
+If `3` divides `S0_nat`, then `3` must divide the boundary gap.
+-/
+theorem three_dvd_sub_of_three_dvd_S0_nat
+    {c b : ℕ} (hbc : b < c) (h3S0 : 3 ∣ S0_nat c b) :
+    3 ∣ c - b := by
+  by_contra h3sub
+  exact (three_not_dvd_S0_nat_of_not_dvd_sub hbc h3sub) h3S0
+
+/--
+The cubic Petal detector has `3` exactly on the boundary branch.
+-/
+theorem three_dvd_S0_nat_iff_three_dvd_sub
+    {c b : ℕ} (hbc : b < c) :
+    3 ∣ S0_nat c b ↔ 3 ∣ c - b :=
+  ⟨three_dvd_sub_of_three_dvd_S0_nat hbc,
+    three_dvd_S0_nat_of_three_dvd_sub hbc⟩
+
+/-- On the reduced branch, `3` does not divide `S0_nat`. -/
+theorem boundaryD3Reduced_three_not_dvd_S0_nat
+    {c b : ℕ} (hbc : b < c) (h : BoundaryD3Reduced c b) :
+    ¬ 3 ∣ S0_nat c b :=
+  three_not_dvd_S0_nat_of_not_dvd_sub hbc h
+
+/-- On the boundary branch, `3` divides `S0_nat`. -/
+theorem boundaryD3Branch_three_dvd_S0_nat
+    {c b : ℕ} (hbc : b < c) (h : BoundaryD3Branch c b) :
+    3 ∣ S0_nat c b :=
+  three_dvd_S0_nat_of_three_dvd_sub hbc h
+
+/--
+In coprime Petal coordinates, the reduced branch makes the boundary gap
+coprime to `S0_nat`.
+-/
+theorem boundaryD3Reduced_coprime_sub_S0_nat
+    {c b : ℕ} (hbc : b < c) (hcop : Nat.Coprime c b)
+    (h : BoundaryD3Reduced c b) :
+    Nat.Coprime (c - b) (S0_nat c b) :=
+  coprime_sub_S0_nat_of_coprime_of_not_dvd_three hbc hcop h
+
+end Petal
+end DkMath
diff --git a/lean/dk_math/DkMath/Petal/docs/Petal-Overview.md b/lean/dk_math/DkMath/Petal/docs/Petal-Overview.md
index d05df3d4..e46005b3 100644
--- a/lean/dk_math/DkMath/Petal/docs/Petal-Overview.md
+++ b/lean/dk_math/DkMath/Petal/docs/Petal-Overview.md
@@ -252,12 +252,45 @@ Important names:
 AnchoredS0Carrier
 AnchoredGNCarrier
 anchoredS0Carrier_dvd_S0
+anchoredS0Carrier_anchor_prime
 anchoredGNCarrier_dvd_GN
+anchoredGNCarrier_anchor_prime
 anchoredGNCarrier_of_anchoredS0Carrier
 anchoredS0Carrier_of_anchoredGNCarrier
 exists_anchoredS0Carrier_of_not_three_dvd_sub
 ```
 
+### `DkMath.Petal.BoundaryD3`
+
+Records the degree-three boundary split for the cubic Petal detector.
+
+Important names:
+
+```lean
+BoundaryD3Branch
+BoundaryD3Reduced
+three_dvd_S0_nat_of_three_dvd_sub
+three_dvd_sub_of_three_dvd_S0_nat
+three_dvd_S0_nat_iff_three_dvd_sub
+boundaryD3Reduced_three_not_dvd_S0_nat
+boundaryD3Branch_three_dvd_S0_nat
+boundaryD3Reduced_coprime_sub_S0_nat
+```
+
+Conceptually, this says:
+
+```text
+3 divides S0_nat c b exactly on the boundary branch 3 | (c - b).
+```
+
+The reduced branch therefore gives the usable cubic Petal surface:
+
+```text
+BoundaryD3Reduced c b
+  -> not 3 | S0_nat c b
+  -> Coprime (c - b) (S0_nat c b), assuming Coprime c b
+```
+
 ### `DkMath.Petal.Counting`
 
 Defines the fixed and dynamic counting layer.
@@ -373,6 +406,9 @@ Fixed Petal counting
   -> prefix divisibility persistence
   -> Petal address decomposition
   -> GN degree-three bridge
+  -> S0/GN primitive bridge
+  -> reduced-support anchor carriers
+  -> degree-three boundary split
 ```
 
 This means the package can already express:
@@ -383,6 +419,8 @@ an adopted prime base remains visible in later prime-base products
 strict prime-base sequences preserve order and non-repetition
 one Petal address step is a quotient-remainder decomposition
 S0 is a visible degree-three Petal face of GN
+primitive S0 witnesses can be read as anchored carriers
+the cubic 3-contact is exactly the boundary branch
 ```
 
 ## What This Does Not Claim Yet
@@ -398,6 +436,7 @@ where factors are stored
 which factors persist across later layers
 how Petal addresses split a layer into channels
 how GN degree 3 becomes the Petal S0 face
+how reduced cubic support excludes the boundary prime 3
 ```
 
 ## Next Directions
@@ -407,14 +446,15 @@ The next reasonable implementation directions are:
 ```text
 1. connect AnchoredS0Carrier to the primitive S0 witnesses
 2. use Petal address decomposition in nested observations
-3. connect strict prime-base orbits to a concrete prime enumeration
-4. decide whether GNPrimitiveCandidate needs a separate vocabulary layer
+3. expose the Eisenstein norm route through `DkMath.Petal.EisensteinBridge`
+4. connect strict prime-base orbits to a concrete prime enumeration
+5. decide whether GNPrimitiveCandidate needs a separate vocabulary layer
 ```
 
 The most conservative next theorem work is probably:
 
 ```text
-DkMath.Petal.Anchor plus PrimitiveBridge
+DkMath.Petal.EisensteinBridge
 ```
 
 The most concrete arithmetic next step is:
````
`````
