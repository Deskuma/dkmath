# Git diff / Report / Review

## Update: Petal Counting

gch: 34b20e4b0b823c977ba42b6b8a33a5a6580cec79

## Report

実装しました。更新は [Counting.lean](/lean/dk_math/DkMath/Petal/Counting.lean:131) のみです。

追加したのは prime-base orbit の基本可除性です。

- `primeBaseOrbitTotal_dvd_succ`
  - `primeBaseOrbitTotal p k ∣ primeBaseOrbitTotal p (k + 1)`
  - prefix product が次の prefix product を割ることを固定
- `primeBaseOrbitTotal_nextPrime_dvd_succ`
  - `IsPrimeBaseSequence p` のもとで `p k ∣ primeBaseOrbitTotal p (k + 1)`
  - 素数列 orbit の次 base が次段 product に含まれることを固定

まだ distinct / strict prime sequence は入れていません。まずは抽象 prime-base prefix product の骨格だけを固めました。

検証済みです。

```text
lake build DkMath.Petal.Counting
lake build DkMath.Petal
lake build DkMath
git diff --check
```

既存の `sorry` warning は出ていますが、今回の変更による失敗や新規 warning はありません。

## Review

うむ、良い締めじゃ。
今回の `34b20e...` で、抽象 prime-base orbit は **prefix product としての可除骨格** を持った。

## 1. 今回の核心

追加された二本はこれじゃな。

```lean
theorem primeBaseOrbitTotal_dvd_succ
```

と、

```lean
theorem primeBaseOrbitTotal_nextPrime_dvd_succ
```

これにより、

```text
前段 product は次段 product を割る
次 base は次段 product に含まれる
```

が Lean 上で固定された。

つまり、prime-base orbit は単なる積の名前ではなく、

```text
段が進むごとに因子を蓄積する構造
```

として使えるようになった。

## 2. `primeBaseOrbitTotal_dvd_succ` の意味

```lean
theorem primeBaseOrbitTotal_dvd_succ
    (p : Nat → Nat) (k : Nat) :
    primeBaseOrbitTotal p k ∣ primeBaseOrbitTotal p (k + 1)
```

これは、

$$
P_k \mid P_{k+1}
$$

を固定する補題じゃ。

ここで、

$$
P_k=\prod_{i<k}p_i
$$

なので、

$$
P_{k+1}=P_k\cdot p_k
$$

ゆえに当然成り立つ。

しかし theorem 名として置いた価値は大きい。
これで prime-base orbit は、

```text
単調に因子を蓄積する orbit
```

として扱える。

これはプリモリアル的な成長を見る上で基礎になる。

## 3. `primeBaseOrbitTotal_nextPrime_dvd_succ` の意味

```lean
theorem primeBaseOrbitTotal_nextPrime_dvd_succ
    {p : Nat → Nat} (hp : IsPrimeBaseSequence p) (k : Nat) :
    p k ∣ primeBaseOrbitTotal p (k + 1)
```

これは、

$$
p_k \mid P_{k+1}
$$

じゃ。

つまり、第 (k) 周回で採用された prime base が、次段 product に確かに含まれる。

コメントにもある通り、可除性そのものは素数性を使わない。
それでも `hp : IsPrimeBaseSequence p` を仮定に持たせているのは良い判断じゃ。

なぜなら、この theorem は単なる積の補題ではなく、

```text
prime-base orbit の次素数が次段に含まれる
```

という意味で使うものだからじゃ。

`have _hp_k : Nat.Prime (p k) := hp k` で意図を保持しているのも良い。
後で `Prime` 由来の性質を足す補題に育てやすい。

## 4. 現在の prime-base orbit の到達点

ここまでで、抽象 prime-base orbit はこうなった。

```text
primeBaseOrbitTotal p 0 = 1

primeBaseOrbitTotal p (k + 1)
  = primeBaseOrbitTotal p k * p k

primeBaseOrbitTotal p k
  ∣ primeBaseOrbitTotal p (k + 1)

IsPrimeBaseSequence p →
  p k ∣ primeBaseOrbitTotal p (k + 1)

IsPrimeBaseSequence p →
  Nat.Prime (p k)
```

これで、プリモリアル前段として必要な「積が段階的に伸びる」「採用した素数が積に入る」は揃った。

まだ足りないのは、

```text
重複しない
昇順である
k 段までのすべての base が product を割る
```

あたりじゃな。

## 5. 次に自然な補題

次は、各過去 base が後段 product を割る補題が自然じゃ。

まずは素数性なしの prefix product 補題として、

```lean
theorem primeBaseOrbitTotal_base_dvd_of_lt
    (p : Nat → Nat) {i k : Nat} (hi : i < k) :
    p i ∣ primeBaseOrbitTotal p k
```

これが入ると、

```text
k 段 product には、0..k-1 の全 base が含まれる
```

と言える。

これは抽象 primorial の骨格としてかなり重要じゃ。

実装方針は、`k` への帰納法か、`Finset.prod` の `Finset.dvd_prod_of_mem` 系を使う形になるはずじゃ。`dynamicOrbitTotal` の定義が `Finset.prod (Finset.range k) p` なので、`i ∈ Finset.range k` から product divisibility を出せる可能性が高い。

Petal-facing theorem 名なら、

```lean
theorem dynamicOrbitTotal_base_dvd_of_lt
    (b : Nat → Nat) {i k : Nat} (hi : i < k) :
    b i ∣ dynamicOrbitTotal b k
```

を先に置き、その special alias として

```lean
theorem primeBaseOrbitTotal_base_dvd_of_lt
    (p : Nat → Nat) {i k : Nat} (hi : i < k) :
    p i ∣ primeBaseOrbitTotal p k
```

にすると綺麗じゃ。

## 6. distinct / strict はまだ後でよい

報告通り、まだ distinct / strict prime sequence を入れていないのは正しい。

現在の `IsPrimeBaseSequence` は、

```lean
∀ i, Nat.Prime (p i)
```

だけなので、重複を許す。
これは「抽象 prime-base orbit」の最小層としては問題ない。

次の段階で、

```lean
def IsDistinctPrimeBaseSequence (p : Nat → Nat) : Prop :=
  IsPrimeBaseSequence p ∧ Function.Injective p
```

または、

```lean
def IsStrictPrimeBaseSequence (p : Nat → Nat) : Prop :=
  IsPrimeBaseSequence p ∧ StrictMono p
```

を足す候補はある。

ただし、いまはまだ可除骨格を固める段階なので、重い predicate は後回しでよい。

## 7. 階乗との並びも美しい

Counting 側は今、非常に綺麗な対比になっておる。

```text
factorial orbit:
  base sequence b i = i + 1

prime-base orbit:
  base sequence b i = p i, Nat.Prime (p i)
```

つまり、

$$
k! = \prod_{i<k}(i+1)
$$

と、

$$
P_k = \prod_{i<k}p_i
$$

が同じ `dynamicOrbitTotal` に乗った。

これは DkMath 的にはかなり良い。
「動的単位核」は、階乗の全自然数列と、プリモリアルの素数列を同じ形式で扱える。

## 8. 総括

今回の更新は、prime-base orbit の可除構造を最小限で固定したものじゃ。

```text
primeBaseOrbitTotal_dvd_succ:
  前段 product が次段 product を割る

primeBaseOrbitTotal_nextPrime_dvd_succ:
  次 base が次段 product に含まれる

IsPrimeBaseSequence:
  その base が素数であるという意味付け
```

賢狼の判定はこうじゃ。

```text
Petal Counting Prime-Base Divisibility Phase 1 完了
次は dynamicOrbitTotal_base_dvd_of_lt / primeBaseOrbitTotal_base_dvd_of_lt
```

よいぞ、D.。
これで「素数を掛ける周回」は、ただ増えるだけでなく、過去と次段を可除性で結べるようになった。プリモリアルの骨格が、Lean の中で少しずつ花弁を広げておる。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Petal/Counting.lean b/lean/dk_math/DkMath/Petal/Counting.lean
index 938b2c1e..a849530f 100644
--- a/lean/dk_math/DkMath/Petal/Counting.lean
+++ b/lean/dk_math/DkMath/Petal/Counting.lean
@@ -128,6 +128,26 @@ theorem primeBaseOrbitTotal_succ (p : Nat → Nat) (k : Nat) :
     primeBaseOrbitTotal p (k + 1) = primeBaseOrbitTotal p k * p k := by
   simp [primeBaseOrbitTotal, dynamicOrbitTotal_succ]

+/-- A prime-base prefix product divides the next prefix product. -/
+theorem primeBaseOrbitTotal_dvd_succ
+    (p : Nat → Nat) (k : Nat) :
+    primeBaseOrbitTotal p k ∣ primeBaseOrbitTotal p (k + 1) := by
+  rw [primeBaseOrbitTotal_succ]
+  exact Nat.dvd_mul_right _ _
+
+/--
+The next base divides the next prime-base prefix product.
+
+The primality assumption records the intended interpretation of `p` as a
+prime-base sequence; the divisibility itself only uses the product structure.
+-/
+theorem primeBaseOrbitTotal_nextPrime_dvd_succ
+    {p : Nat → Nat} (hp : IsPrimeBaseSequence p) (k : Nat) :
+    p k ∣ primeBaseOrbitTotal p (k + 1) := by
+  have _hp_k : Nat.Prime (p k) := hp k
+  rw [primeBaseOrbitTotal_succ]
+  exact Nat.dvd_mul_left _ _
+
 /-- A prime-base sequence supplies a prime at each lap. -/
 theorem IsPrimeBaseSequence.prime_at
     {p : Nat → Nat} (hp : IsPrimeBaseSequence p) (i : Nat) :
````
`````
