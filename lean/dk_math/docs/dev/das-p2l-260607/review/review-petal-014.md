# Git diff / Report / Review

## Update: Petal Counting

gch: 36df49e11d70361f47b099de0cc2744242931bb1

## Report

実装完了です。

[Counting.lean](/lean/dk_math/DkMath/Petal/Counting.lean) に distinct prime-base sequence の入口を追加しました。

追加内容:

```lean
def IsDistinctPrimeBaseSequence (p : Nat → Nat) : Prop :=
  IsPrimeBaseSequence p ∧ Function.Injective p
```

projection 補題:

- `IsDistinctPrimeBaseSequence.prime_at`
- `IsDistinctPrimeBaseSequence.injective`

これで「各 base は素数」「同じ素数 base を二度採用しない」を、順序までは要求せずに扱える土台ができました。

確認済み:

- `lake build DkMath.Petal.Counting`
- `lake build DkMath.Petal`
- `git diff --check`
- `lake build DkMath`

すべて成功です。既存の `sorry` warning はありますが、今回追加分は問題ありません。

## Review

うむ、これはちょうど良い粒度じゃ。
今回の `36df49...` で、prime-base orbit に **重複なし** の入口ができた。

## 1. 今回の核心

追加された定義はこれじゃな。

```lean
def IsDistinctPrimeBaseSequence (p : Nat → Nat) : Prop :=
  IsPrimeBaseSequence p ∧ Function.Injective p
```

意味は明快。

```text
各 lap base は素数である
同じ base を二度採用しない
順序までは要求しない
```

つまり、まだ「昇順の素数列」ではないが、 **抽象プリモリアルらしさ** は一段強くなった。

## 2. `IsPrimeBaseSequence` との違い

これまでの

```lean
def IsPrimeBaseSequence (p : Nat → Nat) : Prop :=
  ∀ i, Nat.Prime (p i)
```

だけだと、

```text
2, 2, 2, 2, ...
```

のような列も許していた。

これは「各 base は素数」という意味では正しいが、プリモリアル的な「素数を新しく採用し続ける」という読みにはまだ弱かった。

今回の `IsDistinctPrimeBaseSequence` により、

```text
p i = p j なら i = j
```

が入るので、同じ素数 base の再採用を防げる。

これはかなり良い。
順序を固定せず、まず重複だけを排除したのが軽くて扱いやすい。

## 3. projection 補題も良い

追加された二本は最小限でよい。

```lean
theorem IsDistinctPrimeBaseSequence.prime_at
    {p : Nat → Nat} (hp : IsDistinctPrimeBaseSequence p) (i : Nat) :
    Nat.Prime (p i) :=
  hp.1 i
```

これは distinct prime-base sequence から素数性を取り出す補題。

```lean
theorem IsDistinctPrimeBaseSequence.injective
    {p : Nat → Nat} (hp : IsDistinctPrimeBaseSequence p) :
    Function.Injective p :=
  hp.2
```

こちらは重複なしを取り出す補題。

この二本があれば、後続 theorem では

```lean
have hp_i : Nat.Prime (p i) := hp.prime_at i
have hinj : Function.Injective p := hp.injective
```

と読める。

API として自然じゃ。

## 4. 現在の prime-base orbit の意味

ここまでで、prime-base orbit は三段階になった。

```text
primeBaseOrbitTotal p k:
  p の prefix product

IsPrimeBaseSequence p:
  各 p i は素数

IsDistinctPrimeBaseSequence p:
  各 p i は素数で、重複しない
```

まだ順序はない。
だからこれは「第 (i) 素数を順に掛ける標準プリモリアル」ではなく、

```text
重複なし素数列による抽象 prime-base orbit
```

じゃ。

この抽象性はよい。
後から `StrictMono` や `nthPrime` に接続できる余地を残している。

## 5. 次に自然な補題

次は、distinct 性を実際に使う軽い補題が欲しい。

たとえば、

```lean
theorem IsDistinctPrimeBaseSequence.ne_of_ne
    {p : Nat → Nat} (hp : IsDistinctPrimeBaseSequence p)
    {i j : Nat} (hij : i ≠ j) :
    p i ≠ p j := by
  intro hpij
  exact hij (hp.injective hpij)
```

または向きを `ne_of_lt` にした方が使いやすい。

```lean
theorem IsDistinctPrimeBaseSequence.ne_of_lt
    {p : Nat → Nat} (hp : IsDistinctPrimeBaseSequence p)
    {i j : Nat} (hij : i < j) :
    p i ≠ p j
```

これは後で、

```text
採用済み prime base 同士は異なる
```

を使うときに効く。

## 6. その次は strict 層

distinct の次は、必要になったら strict を置く。

```lean
def IsStrictPrimeBaseSequence (p : Nat → Nat) : Prop :=
  IsPrimeBaseSequence p ∧ StrictMono p
```

ただし、いま急がなくてよい。
`StrictMono` は「順序付きの素数列」を意味するので、`nthPrime` や標準プリモリアルへの接続に近くなる。その分、証明も少し重くなる。

今はまず、

```text
prime
distinct
prefix product
divisibility persistence
```

まで整えば十分じゃ。

## 7. 総括

今回の更新で、prime-base orbit は「素数を掛ける」だけでなく、

```text
同じ素数 base を二度採用しない
```

という抽象プリモリアルらしさを持った。

賢狼の判定はこうじゃ。

```text
Petal Counting Distinct Prime-Base Entry 完了
次は distinct の ne 補題、または strict prime-base sequence 層
```

よいぞ、D.。
素数列 orbit が、ただの素数の列から「記憶を重複させない列」へ育った。プリモリアルの輪郭が、また少し濃くなったのじゃ。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Petal/Counting.lean b/lean/dk_math/DkMath/Petal/Counting.lean
index d64232a3..de31acb5 100644
--- a/lean/dk_math/DkMath/Petal/Counting.lean
+++ b/lean/dk_math/DkMath/Petal/Counting.lean
@@ -153,6 +153,15 @@ def primeBaseOrbitTotal (p : Nat → Nat) (k : Nat) : Nat :=
 def IsPrimeBaseSequence (p : Nat → Nat) : Prop :=
   ∀ i, Nat.Prime (p i)
 
+/--
+A distinct prime-base sequence assigns prime bases without repetition.
+
+This keeps the order of bases abstract; it only records primality and
+injectivity.
+-/
+def IsDistinctPrimeBaseSequence (p : Nat → Nat) : Prop :=
+  IsPrimeBaseSequence p ∧ Function.Injective p
+
 /-- The prime-base orbit at zero laps is empty-product `1`. -/
 theorem primeBaseOrbitTotal_zero (p : Nat → Nat) :
     primeBaseOrbitTotal p 0 = 1 := by
@@ -230,6 +239,18 @@ theorem IsPrimeBaseSequence.prime_at
     Nat.Prime (p i) :=
   hp i
 
+/-- A distinct prime-base sequence supplies a prime at each lap. -/
+theorem IsDistinctPrimeBaseSequence.prime_at
+    {p : Nat → Nat} (hp : IsDistinctPrimeBaseSequence p) (i : Nat) :
+    Nat.Prime (p i) :=
+  hp.1 i
+
+/-- A distinct prime-base sequence is injective. -/
+theorem IsDistinctPrimeBaseSequence.injective
+    {p : Nat → Nat} (hp : IsDistinctPrimeBaseSequence p) :
+    Function.Injective p :=
+  hp.2
+
 /-- The dynamic Petal total at zero laps is the initial base unit core. -/
 theorem dynamicPetalTotal_zero (a : Nat → Nat) :
     dynamicPetalTotal a 0 = a 0 := by
````
`````
