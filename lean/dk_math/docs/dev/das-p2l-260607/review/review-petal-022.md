# Git diff / Report / Review

## Update: Petal.ReducedSupport

gch: d374f2ff45debf3478be162d38898f4882b35949

## Report

追加しました。

[ReducedSupport.lean](/lean/dk_math/DkMath/Petal/ReducedSupport.lean:91) に以下を追加:

```lean
theorem hasPositiveAnchorPrime_ne_zero
    {r n : ℕ} (h : HasPositiveAnchorPrime r n) :
    n ≠ 0

theorem hasPositiveAnchorPrime_of_pos
    {r n : ℕ} (hn : 0 < n) (h : HasAnchorPrime r n) :
    HasPositiveAnchorPrime r n
```

あわせて docs の API リストも同期しました。

確認:

- `lake build DkMath.Petal.ReducedSupport` 成功
- `lake build DkMath.Petal` 成功
- `git diff --check` 成功

今回も追加分に `sorry` はありません。

## Review

うむ、これは **区切りでよい** 。
`Petal.ReducedSupport` の初期 API としては、かなり綺麗に閉じた。

今回の追加で、`ReducedSupport` は次の三段が揃った。

```text
raw carrier:
  HasAnchorPrime

strict positive support:
  HasPositiveAnchorPrime

実用 elimination:
  anchor ≤ any prime divisor of carrier
```

特に、

```lean
hasPositiveAnchorPrime_ne_zero
hasPositiveAnchorPrime_of_pos
```

を足したことで、`0 < n` と `n ≠ 0` の行き来、raw から strict への昇格が明示的になった。これは下流でかなり効く。Lean ではこういう小さな補題がないだけで、証明が妙に引っかかるからの。

## 判定

```text
Petal.ReducedSupport
  -> 初期実装完了

raw / strict の分離
  -> 完了

0 carrier 問題
  -> 設計上解決

S0/GN 非依存
  -> 維持成功

docs 同期
  -> 完了
```

なので、ここで一旦 commit 単位として切ってよい。

次へ進むなら、もう `ReducedSupport` 内で欲張らず、

```text
DkMath.Petal.Anchor
```

または

```text
DkMath.Petal.ReducedSupportBridge
```

のような別ファイルで、`ReducedSupport` と `S0/GN` を接続するのが安全じゃ。

## 次段の候補

次に狙うなら、たぶんこれじゃ。

```lean
def AnchoredS0Carrier (r c b n : ℕ) : Prop :=
  HasPositiveAnchorPrime r n ∧ n ∣ S0_nat c b
```

あるいは GN 一般寄りに、

```lean
def AnchoredGNCarrier (r d x u n : ℕ) : Prop :=
  HasPositiveAnchorPrime r n ∧ n ∣ GN d x u
```

ただし、ここからは `GN` / `S0` import が入るので、`ReducedSupport.lean` には混ぜない方がよい。

結論として、今回の `d374f2f...` は **ReducedSupport 初期 API 完了 checkpoint** として十分じゃ。
よい区切りじゃよ、D.。次は Anchor と GN の接続橋を別塔で建てる段じゃな。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/NumberTheory/docs/BinomialPrimeWeighted/FLGNB-PetalRoadmap.md b/lean/dk_math/DkMath/NumberTheory/docs/BinomialPrimeWeighted/FLGNB-PetalRoadmap.md
index 0ba5db7d..ca1853c2 100644
--- a/lean/dk_math/DkMath/NumberTheory/docs/BinomialPrimeWeighted/FLGNB-PetalRoadmap.md
+++ b/lean/dk_math/DkMath/NumberTheory/docs/BinomialPrimeWeighted/FLGNB-PetalRoadmap.md
@@ -798,6 +798,8 @@ hasAnchorPrime_anchor_dvd
 hasAnchorPrime_no_smaller_prime
 hasAnchorPrime_anchor_le_of_prime_dvd
 hasPositiveAnchorPrime_pos
+hasPositiveAnchorPrime_ne_zero
+hasPositiveAnchorPrime_of_pos
 hasPositiveAnchorPrime_prime
 hasPositiveAnchorPrime_anchor_dvd
 hasPositiveAnchorPrime_no_smaller_prime
@@ -1007,6 +1009,8 @@ hasAnchorPrime_anchor_dvd
 hasAnchorPrime_no_smaller_prime
 hasAnchorPrime_anchor_le_of_prime_dvd
 hasPositiveAnchorPrime_pos
+hasPositiveAnchorPrime_ne_zero
+hasPositiveAnchorPrime_of_pos
 hasPositiveAnchorPrime_prime
 hasPositiveAnchorPrime_anchor_dvd
 hasPositiveAnchorPrime_no_smaller_prime
diff --git "a/lean/dk_math/DkMath/NumberTheory/docs/BinomialPrimeWeighted/S0_GN_Anchor_Phase_\345\256\237\351\250\223\350\250\255\350\250\210\346\233\270.md" "b/lean/dk_math/DkMath/NumberTheory/docs/BinomialPrimeWeighted/S0_GN_Anchor_Phase_\345\256\237\351\250\223\350\250\255\350\250\210\346\233\270.md"
index 821f1a24..e612fcfc 100644
--- "a/lean/dk_math/DkMath/NumberTheory/docs/BinomialPrimeWeighted/S0_GN_Anchor_Phase_\345\256\237\351\250\223\350\250\255\350\250\210\346\233\270.md"
+++ "b/lean/dk_math/DkMath/NumberTheory/docs/BinomialPrimeWeighted/S0_GN_Anchor_Phase_\345\256\237\351\250\223\350\250\255\350\250\210\346\233\270.md"
@@ -398,6 +398,8 @@ theorem hasAnchorPrime_anchor_dvd
 theorem hasAnchorPrime_no_smaller_prime
 theorem hasAnchorPrime_anchor_le_of_prime_dvd
 theorem hasPositiveAnchorPrime_pos
+theorem hasPositiveAnchorPrime_ne_zero
+theorem hasPositiveAnchorPrime_of_pos
 theorem hasPositiveAnchorPrime_prime
 theorem hasPositiveAnchorPrime_anchor_dvd
 theorem hasPositiveAnchorPrime_no_smaller_prime
diff --git a/lean/dk_math/DkMath/Petal/ReducedSupport.lean b/lean/dk_math/DkMath/Petal/ReducedSupport.lean
index 993ae91c..18348535 100644
--- a/lean/dk_math/DkMath/Petal/ReducedSupport.lean
+++ b/lean/dk_math/DkMath/Petal/ReducedSupport.lean
@@ -87,6 +87,18 @@ theorem hasPositiveAnchorPrime_pos
     0 < n :=
   h.1

+/-- Positive anchored carriers are nonzero. -/
+theorem hasPositiveAnchorPrime_ne_zero
+    {r n : ℕ} (h : HasPositiveAnchorPrime r n) :
+    n ≠ 0 :=
+  Nat.ne_of_gt h.1
+
+/-- Build a positive anchored carrier from positivity and the raw anchor predicate. -/
+theorem hasPositiveAnchorPrime_of_pos
+    {r n : ℕ} (hn : 0 < n) (h : HasAnchorPrime r n) :
+    HasPositiveAnchorPrime r n :=
+  ⟨hn, h⟩
+
 /-- The anchor in `HasPositiveAnchorPrime r n` is prime. -/
 theorem hasPositiveAnchorPrime_prime
     {r n : ℕ} (h : HasPositiveAnchorPrime r n) :
diff --git a/lean/dk_math/DkMath/Petal/docs/Petal-Overview.md b/lean/dk_math/DkMath/Petal/docs/Petal-Overview.md
index b68d0842..b768dee3 100644
--- a/lean/dk_math/DkMath/Petal/docs/Petal-Overview.md
+++ b/lean/dk_math/DkMath/Petal/docs/Petal-Overview.md
@@ -228,6 +228,8 @@ hasAnchorPrime_anchor_dvd
 hasAnchorPrime_no_smaller_prime
 hasAnchorPrime_anchor_le_of_prime_dvd
 hasPositiveAnchorPrime_pos
+hasPositiveAnchorPrime_ne_zero
+hasPositiveAnchorPrime_of_pos
 hasPositiveAnchorPrime_prime
 hasPositiveAnchorPrime_anchor_dvd
 hasPositiveAnchorPrime_no_smaller_prime
````
`````
