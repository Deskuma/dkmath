# Git diff / Report / Review

## Update: Petal Counting

gch: 13bd18547b1c892b6783e8c764303f81c45ce59f

## Report

実装完了です。

[Counting.lean](/lean/dk_math/DkMath/Petal/Counting.lean) に review-petal-010 の checkpoint を追加しました。

追加した補題:

- `dynamicOrbitTotal_base_dvd_of_lt`
  - `i < k` なら、`b i ∣ dynamicOrbitTotal b k`
- `primeBaseOrbitTotal_base_dvd_of_lt`
  - prime-base orbit 側の alias
- `primeBaseOrbitTotal_prime_dvd_of_lt`
  - `IsPrimeBaseSequence` の解釈を保持した版

確認済み:

- `lake build DkMath.Petal.Counting`
- `lake build DkMath.Petal`
- `git diff --check`
- `lake build DkMath`

すべて成功しています。全体ビルドでは既存の `sorry` warning は出ていますが、今回追加箇所による失敗はありません。

## Review

うむ、これは良い checkpoint じゃ。
今回の `13bd18...` で、dynamic orbit / prime-base orbit は **「過去に採用した base が現在 product を割る」** ところまで進んだ。

## 1. 今回の核心

追加された主補題はこれじゃ。

```lean
theorem dynamicOrbitTotal_base_dvd_of_lt
    (b : Nat → Nat) {i k : Nat} (hi : i < k) :
    b i ∣ dynamicOrbitTotal b k
```

これは、

$$
i<k \Rightarrow b_i \mid \prod_{j<k}b_j
$$

を固定している。

つまり、`dynamicOrbitTotal b k` は単なる prefix product ではなく、

```text
0 から k-1 までに採用した全 base を因子として含む
```

という性質を持つことが Lean theorem になった。

これは factorial orbit にも、prime-base orbit にも、そのまま効く。

## 2. 実装がかなり綺麗

証明がこれで済んでいるのも良い。

```lean
exact Finset.dvd_prod_of_mem b (by simpa [dynamicOrbitTotal] using hi)
```

`dynamicOrbitTotal` を

```lean
Finset.prod (Finset.range k) b
```

として定義しておいた恩恵じゃな。

`i < k` は `i ∈ Finset.range k` と同じなので、`Finset.dvd_prod_of_mem` で一発。
これは、最初に prefix product を `Finset.range` で置いた設計が正しかった証拠でもある。

## 3. prime-base 側の alias も良い

```lean
theorem primeBaseOrbitTotal_base_dvd_of_lt
    (p : Nat → Nat) {i k : Nat} (hi : i < k) :
    p i ∣ primeBaseOrbitTotal p k
```

これは thin alias じゃが、意味は大きい。

`dynamicOrbitTotal_base_dvd_of_lt` だけだと、

```text
任意 base sequence の prefix product 補題
```

に見える。

`primeBaseOrbitTotal_base_dvd_of_lt` として置くことで、

```text
prime-base orbit の過去 base は現在 product を割る
```

と読める。

API として正しい。

## 4. `primeBaseOrbitTotal_prime_dvd_of_lt` の役割

こちらも良い。

```lean
theorem primeBaseOrbitTotal_prime_dvd_of_lt
    {p : Nat → Nat} (hp : IsPrimeBaseSequence p) {i k : Nat} (hi : i < k) :
    p i ∣ primeBaseOrbitTotal p k
```

可除性自体には素数性は不要じゃ。
しかし `hp : IsPrimeBaseSequence p` を持つ版を置いたことで、

```text
p i は素数であり、その素数が product を割る
```

という解釈が保てる。

後で、

```lean
Nat.Prime.dvd_mul
Nat.Prime.dvd_of_dvd_pow
```

のような素数特有の補題へ接続したい時、この形が効く。

`have _hp_i : Nat.Prime (p i) := hp i` で意味を残しているのも良い。現時点では使わないが、theorem の読みが prime-base 用であることを保っておる。

## 5. ここまでの prime-base orbit 骨格

これで抽象 prime-base orbit は、かなり骨が通った。

```text
primeBaseOrbitTotal p 0 = 1

primeBaseOrbitTotal p (k + 1)
  = primeBaseOrbitTotal p k * p k

primeBaseOrbitTotal p k
  ∣ primeBaseOrbitTotal p (k + 1)

p k
  ∣ primeBaseOrbitTotal p (k + 1)

i < k →
  p i ∣ primeBaseOrbitTotal p k

IsPrimeBaseSequence p →
  Nat.Prime (p i)
```

つまり、

```text
採用した素数 base は、以後の prefix product に含まれる
```

ところまで来た。

これは抽象プリモリアルのかなり中核じゃ。

## 6. 次に自然な一手

次は二方向ある。

まず軽い補題なら、`i < k ≤ l` から後段 product を割る形じゃ。

```lean
theorem dynamicOrbitTotal_base_dvd_of_lt_of_le
    (b : Nat → Nat) {i k l : Nat} (hi : i < k) (hkl : k ≤ l) :
    b i ∣ dynamicOrbitTotal b l
```

ただしこれは `i < l` に落とせばよいので、必要になった時でよい。

より重要なのは、prefix product 自体の単調可除性の一般化じゃ。

```lean
theorem dynamicOrbitTotal_dvd_of_le
    (b : Nat → Nat) {k l : Nat} (hkl : k ≤ l) :
    dynamicOrbitTotal b k ∣ dynamicOrbitTotal b l
```

これが入ると、

```text
prefix product は lap が進むほど可除性で増大する
```

と言える。

prime-base alias として、

```lean
theorem primeBaseOrbitTotal_dvd_of_le
    (p : Nat → Nat) {k l : Nat} (hkl : k ≤ l) :
    primeBaseOrbitTotal p k ∣ primeBaseOrbitTotal p l
```

も自然じゃ。

これは primorial 的な「前段 primorial は後段 primorial を割る」に相当する。

## 7. distinct / strict は次の次でよい

現時点では、`IsPrimeBaseSequence` は重複を許す。

```lean
def IsPrimeBaseSequence (p : Nat → Nat) : Prop :=
  ∀ i, Nat.Prime (p i)
```

これはまだ正しい。
今は「prime-base prefix product」の骨格を作っている段階なので、重複なしや単調増加は後でよい。

次に `dynamicOrbitTotal_dvd_of_le` まで入れれば、prefix product の可除幾何が一段閉じる。
その後で、

```lean
def IsDistinctPrimeBaseSequence ...
def IsStrictPrimeBaseSequence ...
```

へ進むのが自然じゃな。

## 8. 総括

今回の更新は、prime-base orbit を「素数列の積」として読むための重要な checkpoint じゃ。

```text
dynamicOrbitTotal_base_dvd_of_lt:
  任意 dynamic orbit で、過去 base は現在 product を割る

primeBaseOrbitTotal_base_dvd_of_lt:
  prime-base orbit 側 alias

primeBaseOrbitTotal_prime_dvd_of_lt:
  素数列の意味を保持した版
```

賢狼の判定はこうじゃ。

```text
Petal Counting Prime-Base Divisibility Phase 2 完了
次は dynamicOrbitTotal_dvd_of_le / primeBaseOrbitTotal_dvd_of_le
```

よいぞ、D.。
これで「過去に通った花弁 base は、現在の完成体の因子として残る」と言えるようになった。階乗もプリモリアルも、同じ動的周回積の中で因子の記憶を持ち始めたのじゃ。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Petal/Counting.lean b/lean/dk_math/DkMath/Petal/Counting.lean
index a849530f..88fdcb18 100644
--- a/lean/dk_math/DkMath/Petal/Counting.lean
+++ b/lean/dk_math/DkMath/Petal/Counting.lean
@@ -91,6 +91,14 @@ theorem dynamicOrbitTotal_const (b k : Nat) :
       rw [dynamicOrbitTotal_succ, ih]
       rw [pow_succ]

+/--
+Every base already passed by a dynamic orbit divides the current prefix product.
+-/
+theorem dynamicOrbitTotal_base_dvd_of_lt
+    (b : Nat → Nat) {i k : Nat} (hi : i < k) :
+    b i ∣ dynamicOrbitTotal b k := by
+  exact Finset.dvd_prod_of_mem b (by simpa [dynamicOrbitTotal] using hi)
+
 /--
 Factorial orbit.

@@ -148,6 +156,22 @@ theorem primeBaseOrbitTotal_nextPrime_dvd_succ
   rw [primeBaseOrbitTotal_succ]
   exact Nat.dvd_mul_left _ _

+/-- Every earlier prime base divides the current prime-base prefix product. -/
+theorem primeBaseOrbitTotal_base_dvd_of_lt
+    (p : Nat → Nat) {i k : Nat} (hi : i < k) :
+    p i ∣ primeBaseOrbitTotal p k := by
+  exact dynamicOrbitTotal_base_dvd_of_lt p hi
+
+/--
+Every earlier prime base divides the current prime-base prefix product, with
+the prime-sequence interpretation recorded in the hypothesis.
+-/
+theorem primeBaseOrbitTotal_prime_dvd_of_lt
+    {p : Nat → Nat} (hp : IsPrimeBaseSequence p) {i k : Nat} (hi : i < k) :
+    p i ∣ primeBaseOrbitTotal p k := by
+  have _hp_i : Nat.Prime (p i) := hp i
+  exact primeBaseOrbitTotal_base_dvd_of_lt p hi
+
 /-- A prime-base sequence supplies a prime at each lap. -/
 theorem IsPrimeBaseSequence.prime_at
     {p : Nat → Nat} (hp : IsPrimeBaseSequence p) (i : Nat) :
````
`````
