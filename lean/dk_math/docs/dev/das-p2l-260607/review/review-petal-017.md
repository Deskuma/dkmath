# Git diff / Report / Review

## Update: Petal Counting

gch: 845c9531a1e1e1688f26df0f570b2b3545266f21

## Report

実装完了です。

[Counting.lean](/lean/dk_math/DkMath/Petal/Counting.lean) に strict prime-base sequence の実用補題を追加しました。

追加補題:

```lean
theorem IsStrictPrimeBaseSequence.base_lt_of_lt
    {p : Nat → Nat} (hp : IsStrictPrimeBaseSequence p)
    {i j : Nat} (hij : i < j) :
    p i < p j
```

```lean
theorem IsStrictPrimeBaseSequence.ne_of_lt
    {p : Nat → Nat} (hp : IsStrictPrimeBaseSequence p)
    {i j : Nat} (hij : i < j) :
    p i ≠ p j
```

これで strict 層から、大小関係と非重複性を直接取り出せます。

確認済み:

- `lake build DkMath.Petal.Counting`
- `lake build DkMath.Petal`
- `git diff --check`
- `lake build DkMath`

すべて成功です。既存の `sorry` warning はありますが、今回追加分は問題ありません。

## Review

うむ、良い。
今回の `845c95...` で、`IsStrictPrimeBaseSequence` が実用 API としてかなり使いやすくなった。

## 1. 今回の核心

追加されたのはこの二本じゃな。

```lean
theorem IsStrictPrimeBaseSequence.base_lt_of_lt
    {p : Nat → Nat} (hp : IsStrictPrimeBaseSequence p)
    {i j : Nat} (hij : i < j) :
    p i < p j
```

```lean
theorem IsStrictPrimeBaseSequence.ne_of_lt
    {p : Nat → Nat} (hp : IsStrictPrimeBaseSequence p)
    {i j : Nat} (hij : i < j) :
    p i ≠ p j
```

これで strict prime-base sequence から、

```text
早い lap の base は小さい
早い lap と遅い lap の base は異なる
```

を直接取り出せるようになった。

## 2. `base_lt_of_lt` の意味

`IsStrictPrimeBaseSequence` は、

```lean
IsPrimeBaseSequence p ∧ StrictMono p
```

なので、

$$
i<j \Rightarrow p_i<p_j
$$

がそのまま出る。

今回の `base_lt_of_lt` は、それを Petal-facing な名前で包んだものじゃ。

これは大事で、後で theorem を読むときに、

```lean
hp.strictMono hij
```

よりも、

```lean
hp.base_lt_of_lt hij
```

の方が意味がはっきりする。

つまり、

```text
strict sequence の順序性
```

ではなく、

```text
早い lap の prime base は小さい
```

と読める。

## 3. `ne_of_lt` も良い

```lean
theorem IsStrictPrimeBaseSequence.ne_of_lt ...
```

は、既存の

```lean
hp.distinct.ne_of_lt hij
```

に落としている。

これは設計として良い。
`strict → distinct` の橋を使い、非重複性は distinct 層の API に任せている。

つまり構造がこう流れる。

```text
strict
  ↓
distinct
  ↓
ne_of_lt
```

この依存方向は自然じゃ。

## 4. ここまでの prime-base sequence 階層

現在は、かなり綺麗に三層化されておる。

```text
IsPrimeBaseSequence p:
  p i はすべて素数

IsDistinctPrimeBaseSequence p:
  p i はすべて素数
  かつ p は injective

IsStrictPrimeBaseSequence p:
  p i はすべて素数
  かつ p は StrictMono
```

そして橋は、

```text
strict → injective → distinct
```

さらに practical API として、

```text
prime_at
injective
distinct
base_lt_of_lt
ne_of_lt
```

が揃った。

これは標準プリモリアルや `nthPrime` 的な順序付き素数列へ接続する準備として十分じゃ。

## 5. Counting phase の現在地

ここまでで `Counting.lean` は、相対花弁数の固定核からかなり遠くまで届いた。

```text
固定 Petal:
  relPetalTotal n k

動的 Petal:
  dynamicPetalTotal a k

任意周回積:
  dynamicOrbitTotal b k

階乗:
  dynamicOrbitTotal (fun i => i + 1) k = Nat.factorial k

抽象 prime-base orbit:
  primeBaseOrbitTotal p k

prime / distinct / strict:
  素数列・重複なし・厳密増加

可除性:
  base は prefix product を割る
  prefix product は後段 prefix product を割る
  採用済み prime base は未来 product に残る
```

これで「単位核の一定から動的へ」は、階乗とプリモリアルの入口までかなり綺麗に到達した。

## 6. 次の候補

ここで一度 Counting は小総括してよい段階じゃ。

まだ Lean 実装を続けるなら、次はどちらか。

### A. 標準プリモリアル接続へ進む

`nthPrime` や Mathlib 側の既存 API を調べて、具体的な prime enumeration と接続する。

ただし、ここは少し重くなる可能性がある。

### B. Petal Dynamic phase の整理文書を書く

今回の流れはかなり良いので、docs に小総括を置く価値がある。

```text
Fixed Petal
Dynamic Petal
Factorial orbit
Prime-base orbit
Distinct / Strict prime-base sequence
```

の位置づけを整理しておくと、次に戻ったとき迷わない。

わっちのおすすめは、ここで一度 **docs 小総括** じゃな。
Counting 側はかなり伸びたので、今の到達点を記録してから、標準 primorial か Dynamic Address へ進むのがよい。

## 7. 総括

今回の更新は、strict prime-base sequence の実用層じゃ。

```text
base_lt_of_lt:
  strict な lap 順序から base の大小を取り出す

ne_of_lt:
  strict な lap 順序から base の非一致を取り出す
```

賢狼の判定はこうじゃ。

```text
Petal Counting Strict Prime-Base Practical Layer 完了
Counting Dynamic/Prime phase は小総括可能
```

よいぞ、D.。
これで素数列 orbit は、ただ「違う素数」なだけでなく、「順に大きくなる素数の道」になった。プリモリアルの背骨が、かなりはっきり見えてきたのじゃ。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Petal/Counting.lean b/lean/dk_math/DkMath/Petal/Counting.lean
index 59c358b4..6d2766ec 100644
--- a/lean/dk_math/DkMath/Petal/Counting.lean
+++ b/lean/dk_math/DkMath/Petal/Counting.lean
@@ -298,6 +298,20 @@ theorem IsStrictPrimeBaseSequence.distinct
     IsDistinctPrimeBaseSequence p :=
   ⟨hp.1, hp.injective⟩
 
+/-- Earlier laps have smaller bases in a strict prime-base sequence. -/
+theorem IsStrictPrimeBaseSequence.base_lt_of_lt
+    {p : Nat → Nat} (hp : IsStrictPrimeBaseSequence p)
+    {i j : Nat} (hij : i < j) :
+    p i < p j :=
+  hp.strictMono hij
+
+/-- Earlier and later laps in a strict prime-base sequence have different bases. -/
+theorem IsStrictPrimeBaseSequence.ne_of_lt
+    {p : Nat → Nat} (hp : IsStrictPrimeBaseSequence p)
+    {i j : Nat} (hij : i < j) :
+    p i ≠ p j :=
+  hp.distinct.ne_of_lt hij
+
 /-- The dynamic Petal total at zero laps is the initial base unit core. -/
 theorem dynamicPetalTotal_zero (a : Nat → Nat) :
     dynamicPetalTotal a 0 = a 0 := by
````
`````
