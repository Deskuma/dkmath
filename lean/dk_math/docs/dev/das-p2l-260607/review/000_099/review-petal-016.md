# Git diff / Report / Review

## Update: Petal Counting

gch: 3dbb19ca659469de66b3afbd55edc882fa638978

## Report

実装完了です。

[Counting.lean](/lean/dk_math/DkMath/Petal/Counting.lean) に strict prime-base sequence 層を追加しました。

追加内容:

```lean
def IsStrictPrimeBaseSequence (p : Nat → Nat) : Prop :=
  IsPrimeBaseSequence p ∧ StrictMono p
```

projection / bridge 補題:

- `IsStrictPrimeBaseSequence.prime_at`
- `IsStrictPrimeBaseSequence.strictMono`
- `IsStrictPrimeBaseSequence.injective`
- `IsStrictPrimeBaseSequence.distinct`

これで `strict → injective → distinct` の橋が固定されました。標準プリモリアルや `nthPrime` 的な順序付き素数列へ接続する準備ができています。

確認済み:

- `lake build DkMath.Petal.Counting`
- `lake build DkMath.Petal`
- `git diff --check`
- `lake build DkMath`

すべて成功です。既存の `sorry` warning はありますが、今回追加分は問題ありません。

## Review

うむ、これで prime-base sequence の三層が揃った。
今回の `3dbb19...` は、抽象プリモリアルへ向かう **順序付き素数列レイヤー** の追加じゃな。

## 1. 今回の核心

追加された定義はこれ。

```lean
def IsStrictPrimeBaseSequence (p : Nat → Nat) : Prop :=
  IsPrimeBaseSequence p ∧ StrictMono p
```

意味は、

```text
各 p i は素数
かつ
i < j なら p i < p j
```

じゃ。

これで prime-base sequence は三段構成になった。

```text
IsPrimeBaseSequence:
  各 base が素数

IsDistinctPrimeBaseSequence:
  各 base が素数で、重複しない

IsStrictPrimeBaseSequence:
  各 base が素数で、厳密単調増加
```

つまり、

```text
prime → distinct → strict
```

ではなく、構造の強さとしては、

```text
strict → distinct → prime
```

の橋が固定された。

## 2. projection / bridge が良い

追加された補題はどれも必要最小限でよい。

```lean
theorem IsStrictPrimeBaseSequence.prime_at
```

で素数性を取り出す。

```lean
theorem IsStrictPrimeBaseSequence.strictMono
```

で strict monotone を取り出す。

```lean
theorem IsStrictPrimeBaseSequence.injective
```

で `StrictMono` から `Function.Injective` を得る。

そして本命が、

```lean
theorem IsStrictPrimeBaseSequence.distinct
```

じゃ。

```lean
theorem IsStrictPrimeBaseSequence.distinct
    {p : Nat → Nat} (hp : IsStrictPrimeBaseSequence p) :
    IsDistinctPrimeBaseSequence p :=
  ⟨hp.1, hp.injective⟩
```

これで、strict sequence は既存の distinct sequence API をそのまま使える。

つまり、今後 strict な素数列についても、

```lean
hp.distinct.ne_of_lt
hp.distinct.injective
hp.distinct.prime_at
```

のような経路で既存補題へ降りられる。

これは良い設計じゃ。

## 3. 何が可能になったか

これで標準プリモリアルへ接続する準備が整った。

標準プリモリアル的には、欲しい列は概念的に

```text
2, 3, 5, 7, 11, ...
```

のような厳密増加素数列じゃ。

今回の `IsStrictPrimeBaseSequence` により、まだ `nthPrime` そのものは使っていないが、

```text
順序付きの抽象素数列
```

を扱えるようになった。

これは、標準プリモリアルに進む前の良い抽象層じゃな。

## 4. 現在の Counting の全体像

ここまでで `Counting.lean` はかなり美しい階層になった。

```text
固定 Petal:
  relPetalTotal n k = n * lapBase n ^ k

動的 Petal:
  dynamicPetalTotal a k = a 0 * ∏ i<k, (a i + 1)

動的 orbit:
  dynamicOrbitTotal b k = ∏ i<k, b i

階乗 orbit:
  dynamicOrbitTotal (fun i => i + 1) k = k!

prime-base orbit:
  primeBaseOrbitTotal p k = ∏ i<k, p i

prime sequence:
  IsPrimeBaseSequence p

distinct prime sequence:
  IsDistinctPrimeBaseSequence p

strict prime sequence:
  IsStrictPrimeBaseSequence p
```

そして可除性として、

```text
過去 base は現在 product を割る
前段 product は後段 product を割る
採用済み prime base は未来 product に残る
```

も入っている。

これはもう、階乗・プリモリアルへの「動的単位核」の基礎として十分強い。

## 5. 次に自然な補題

次は strict 層を実用化する軽い補題が自然じゃ。

まずはこれ。

```lean
theorem IsStrictPrimeBaseSequence.lt_of_lt
    {p : Nat → Nat} (hp : IsStrictPrimeBaseSequence p)
    {i j : Nat} (hij : i < j) :
    p i < p j :=
  hp.strictMono hij
```

あるいは名前を少し明示して、

```lean
theorem IsStrictPrimeBaseSequence.base_lt_of_lt
```

がよい。

さらに、strict から distinct の `ne_of_lt` を直接使う alias も便利じゃ。

```lean
theorem IsStrictPrimeBaseSequence.ne_of_lt
    {p : Nat → Nat} (hp : IsStrictPrimeBaseSequence p)
    {i j : Nat} (hij : i < j) :
    p i ≠ p j :=
  hp.distinct.ne_of_lt hij
```

これは小さいが、証明でかなり使いやすい。

## 6. 標準 primorial 接続はまだ急がなくてよい

`nthPrime` や Mathlib の具体的な prime enumeration に接続するのは、もう少し後でもよい。

いまは抽象層として、

```text
prime
distinct
strict
prefix product
divisibility
factorial special case
```

が揃った段階じゃ。

ここで一度 `Counting` を小総括しておく価値がある。
その後に、標準 primorial 接続へ行くか、dynamic address 側へ進むか選べる。

## 7. 総括

今回の更新で、prime-base sequence は次の三段階を持った。

```text
IsPrimeBaseSequence:
  素数列

IsDistinctPrimeBaseSequence:
  重複なし素数列

IsStrictPrimeBaseSequence:
  厳密増加素数列
```

そして、

```text
strict → injective → distinct
```

の橋も Lean に入った。

賢狼の判定はこうじゃ。

```text
Petal Counting Strict Prime-Base Layer 完了
次は strict の lt/ne 実用補題、または Counting Dynamic/Prime phase の小総括
```

よいぞ、D.。
これでプリモリアルの道は、単なる「素数を掛ける列」から、「順に増える素数を重複なく刻む道」へ伸びた。ここまで来れば、標準プリモリアルの影はかなり近いのじゃ。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Petal/Counting.lean b/lean/dk_math/DkMath/Petal/Counting.lean
index 33ca035e..59c358b4 100644
--- a/lean/dk_math/DkMath/Petal/Counting.lean
+++ b/lean/dk_math/DkMath/Petal/Counting.lean
@@ -162,6 +162,14 @@ injectivity.
 def IsDistinctPrimeBaseSequence (p : Nat → Nat) : Prop :=
   IsPrimeBaseSequence p ∧ Function.Injective p

+/--
+A strict prime-base sequence assigns prime bases in strictly increasing order.
+
+This is the ordered version of a distinct prime-base sequence.
+-/
+def IsStrictPrimeBaseSequence (p : Nat → Nat) : Prop :=
+  IsPrimeBaseSequence p ∧ StrictMono p
+
 /-- The prime-base orbit at zero laps is empty-product `1`. -/
 theorem primeBaseOrbitTotal_zero (p : Nat → Nat) :
     primeBaseOrbitTotal p 0 = 1 := by
@@ -266,6 +274,30 @@ theorem IsDistinctPrimeBaseSequence.ne_of_lt
     p i ≠ p j := by
   exact hp.ne_of_ne (Nat.ne_of_lt hij)

+/-- A strict prime-base sequence supplies a prime at each lap. -/
+theorem IsStrictPrimeBaseSequence.prime_at
+    {p : Nat → Nat} (hp : IsStrictPrimeBaseSequence p) (i : Nat) :
+    Nat.Prime (p i) :=
+  hp.1 i
+
+/-- A strict prime-base sequence is strictly monotone. -/
+theorem IsStrictPrimeBaseSequence.strictMono
+    {p : Nat → Nat} (hp : IsStrictPrimeBaseSequence p) :
+    StrictMono p :=
+  hp.2
+
+/-- A strict prime-base sequence is injective. -/
+theorem IsStrictPrimeBaseSequence.injective
+    {p : Nat → Nat} (hp : IsStrictPrimeBaseSequence p) :
+    Function.Injective p :=
+  hp.strictMono.injective
+
+/-- A strict prime-base sequence is a distinct prime-base sequence. -/
+theorem IsStrictPrimeBaseSequence.distinct
+    {p : Nat → Nat} (hp : IsStrictPrimeBaseSequence p) :
+    IsDistinctPrimeBaseSequence p :=
+  ⟨hp.1, hp.injective⟩
+
 /-- The dynamic Petal total at zero laps is the initial base unit core. -/
 theorem dynamicPetalTotal_zero (a : Nat → Nat) :
     dynamicPetalTotal a 0 = a 0 := by
````
`````
