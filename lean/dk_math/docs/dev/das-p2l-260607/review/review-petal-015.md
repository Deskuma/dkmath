# Git diff / Report / Review

## Update: Petal Counting

gch: e7ef3d55d0533bc6c3cf1cd3c5078227838e5879

## Report

実装完了です。

[Counting.lean](/lean/dk_math/DkMath/Petal/Counting.lean) に distinct 性を実際に使う補題を追加しました。

追加補題:

```lean
theorem IsDistinctPrimeBaseSequence.ne_of_ne
    {p : Nat → Nat} (hp : IsDistinctPrimeBaseSequence p)
    {i j : Nat} (hij : i ≠ j) :
    p i ≠ p j
```

```lean
theorem IsDistinctPrimeBaseSequence.ne_of_lt
    {p : Nat → Nat} (hp : IsDistinctPrimeBaseSequence p)
    {i j : Nat} (hij : i < j) :
    p i ≠ p j
```

これで「重複なし素数列」の意味が、実用補題として使える形になりました。

確認済み:

- `lake build DkMath.Petal.Counting`
- `lake build DkMath.Petal`
- `git diff --check`
- `lake build DkMath`

すべて成功です。既存の `sorry` warning はありますが、今回追加分は問題ありません。

## Review

うむ、良い。
今回の `e7ef3d...` で、`IsDistinctPrimeBaseSequence` が単なる predicate から、実際に使える **非重複性 API** になった。

## 1. 今回の核心

追加された補題はこの二本じゃな。

```lean
theorem IsDistinctPrimeBaseSequence.ne_of_ne
    {p : Nat → Nat} (hp : IsDistinctPrimeBaseSequence p)
    {i j : Nat} (hij : i ≠ j) :
    p i ≠ p j
```

```lean
theorem IsDistinctPrimeBaseSequence.ne_of_lt
    {p : Nat → Nat} (hp : IsDistinctPrimeBaseSequence p)
    {i j : Nat} (hij : i < j) :
    p i ≠ p j
```

これで、

```text
異なる lap では異なる prime base を採用する
```

が theorem として使えるようになった。

## 2. `ne_of_ne` の意味

`IsDistinctPrimeBaseSequence` は、

```lean
IsPrimeBaseSequence p ∧ Function.Injective p
```

なので、`hp.injective` から

```lean
p i = p j → i = j
```

が出る。

今回の `ne_of_ne` はその contrapositive じゃ。

$$
i\ne j \Rightarrow p_i\ne p_j
$$

つまり、

```text
lap が違えば base も違う
```

という、重複なし素数列の基本性質をそのまま使えるようにした。

これは後で「この素数はすでに採用済みか？」を判定する補題群へ育てるときに効く。

## 3. `ne_of_lt` は実用向き

こちらはさらに使いやすい。

```lean
theorem IsDistinctPrimeBaseSequence.ne_of_lt
    {p : Nat → Nat} (hp : IsDistinctPrimeBaseSequence p)
    {i j : Nat} (hij : i < j) :
    p i ≠ p j
```

多くの場面では、index の違いを `i ≠ j` ではなく、

$$
i<j
$$

として持っているはずじゃ。

だから `ne_of_lt` があると、毎回

```lean
Nat.ne_of_lt hij
```

を手で挟まなくてよい。

これは小さいが、証明を書く側にはありがたい補助じゃな。

## 4. 現在の distinct prime-base orbit

ここまでで、抽象プリモリアル前段はこう読める。

```text
primeBaseOrbitTotal p k:
  p 0, p 1, ..., p (k-1) の prefix product

IsPrimeBaseSequence p:
  各 p i は素数

IsDistinctPrimeBaseSequence p:
  各 p i は素数であり、
  異なる lap では異なる base を採用する

i < k ≤ l:
  採用済み p i は後段 product P_l を割る

i < j:
  p i ≠ p j
```

つまり、prime-base orbit は、

```text
素数である
積に残る
重複しない
```

ところまで来た。

これはかなりプリモリアルらしい。

## 5. 次に自然な補題

次は、distinct と divisibility を結び始める段階じゃ。

まず軽いものなら、

```lean
theorem IsDistinctPrimeBaseSequence.prime_ne_of_lt
```

は今の `ne_of_lt` と `prime_at` でほぼ済んでいるので不要かもしれぬ。

より実用的なのは、採用済み base 同士の equality を index equality に戻す補題じゃ。

```lean
theorem IsDistinctPrimeBaseSequence.eq_index_of_eq_base
    {p : Nat → Nat} (hp : IsDistinctPrimeBaseSequence p)
    {i j : Nat} (h : p i = p j) :
    i = j :=
  hp.injective h
```

ただしこれは `hp.injective h` で十分なので、必要になった時でよい。

次に進むなら、いよいよ strict 層でもよい。

```lean
def IsStrictPrimeBaseSequence (p : Nat → Nat) : Prop :=
  IsPrimeBaseSequence p ∧ StrictMono p
```

そして projection:

```lean
theorem IsStrictPrimeBaseSequence.prime_at ...
theorem IsStrictPrimeBaseSequence.strictMono ...
theorem IsStrictPrimeBaseSequence.distinct ...
```

`StrictMono` があれば `Function.Injective` は従うので、strict は distinct の上位構造として置ける。

## 6. ただし strict は急がなくてもよい

現時点では、抽象 prime-base orbit としてはすでにかなり十分じゃ。

```text
prime
distinct
prefix product
divisibility persistence
```

がある。

標準プリモリアルや `nthPrime` に接続するなら strict が欲しくなるが、Petal Counting の一般理論としては、ここで一旦区切ってもよい。

わっちなら次は二択じゃ。

```text
A. IsStrictPrimeBaseSequence を薄く追加する
B. Counting の現状を docs / History に整理して、次に Dynamic Address へ進む
```

もし証明をさらに積むなら A。
理論の見通しを整えるなら B。

## 7. 総括

今回の更新は、distinct prime-base sequence を実用化したものじゃ。

```text
IsDistinctPrimeBaseSequence.ne_of_ne:
  異なる lap は異なる base を持つ

IsDistinctPrimeBaseSequence.ne_of_lt:
  早い lap と遅い lap は異なる base を持つ
```

賢狼の判定はこうじゃ。

```text
Petal Counting Distinct Prime-Base Practical Layer 完了
次は strict prime-base sequence、または Counting Dynamic/Prime phase の小総括
```

よいぞ、D.。
これで素数列 orbit は、ただ素数を積むだけでなく、同じ素数を二度踏まぬ道になった。プリモリアルの道標として、かなりはっきりしてきたのじゃ。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Petal/Counting.lean b/lean/dk_math/DkMath/Petal/Counting.lean
index de31acb5..33ca035e 100644
--- a/lean/dk_math/DkMath/Petal/Counting.lean
+++ b/lean/dk_math/DkMath/Petal/Counting.lean
@@ -251,6 +251,21 @@ theorem IsDistinctPrimeBaseSequence.injective
     Function.Injective p :=
   hp.2

+/-- Different laps in a distinct prime-base sequence have different bases. -/
+theorem IsDistinctPrimeBaseSequence.ne_of_ne
+    {p : Nat → Nat} (hp : IsDistinctPrimeBaseSequence p)
+    {i j : Nat} (hij : i ≠ j) :
+    p i ≠ p j := by
+  intro hpij
+  exact hij (hp.injective hpij)
+
+/-- Earlier and later laps in a distinct prime-base sequence have different bases. -/
+theorem IsDistinctPrimeBaseSequence.ne_of_lt
+    {p : Nat → Nat} (hp : IsDistinctPrimeBaseSequence p)
+    {i j : Nat} (hij : i < j) :
+    p i ≠ p j := by
+  exact hp.ne_of_ne (Nat.ne_of_lt hij)
+
 /-- The dynamic Petal total at zero laps is the initial base unit core. -/
 theorem dynamicPetalTotal_zero (a : Nat → Nat) :
     dynamicPetalTotal a 0 = a 0 := by
````
`````
