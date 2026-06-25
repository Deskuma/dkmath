# Git diff / Report / Review

## Update: Petal Counting

gch: b8e67a92aece4155e14f88291032841e2cc4727a

## Report

実装しました。更新は [Counting.lean](/lean/dk_math/DkMath/Petal/Counting.lean:60) のみです。

追加した中核はこの3つです。

- `dynamicOrbitTotal`
- `dynamicPetalTotal`
- `dynamicPetalTotal_const`

あわせて、使いやすい基本補題も入れました。

- `dynamicOrbitTotal_zero`
- `dynamicOrbitTotal_succ`
- `dynamicOrbitTotal_const`
- `dynamicPetalTotal_zero`
- `dynamicPetalTotal_succ`

これで固定核の `relPetalTotal n k` が、動的核 `dynamicPetalTotal (fun _ => n) k` の特殊ケースとして Lean 上で固定されました。

検証済みです。

```text
lake build DkMath.Petal.Counting
lake build DkMath.Petal
lake build DkMath
git diff --check
```

既存の `sorry` warning は出ていますが、今回の変更による失敗や新規 warning はありません。

## Review

うむ、これは狙い通りじゃ。
今回の `b8e67a...` で、Petal Counting は **固定単位核** から **動的単位核** へ拡張された。

## 1. 今回の核心

追加された主役はこの二つじゃ。

```lean
def dynamicOrbitTotal (b : Nat → Nat) (k : Nat) : Nat :=
  Finset.prod (Finset.range k) b
```

```lean
def dynamicPetalTotal (a : Nat → Nat) (k : Nat) : Nat :=
  a 0 * dynamicOrbitTotal (fun i => a i + 1) k
```

これで、今までの固定型

$$
R_n(k)=n(n+1)^k
$$

が、動的型

$$
D_a(k)=a_0\prod_{i<k}(a_i+1)
$$

の特殊ケースとして扱えるようになった。

つまり、

```text
固定単位核:
  a_i = n

動的単位核:
  a_i が lap ごとに変化
```

という一般化が Lean 上に入った。

## 2. `dynamicOrbitTotal` の意味

`dynamicOrbitTotal b k` は、lap-base 列 (b_i) の prefix product じゃ。

$$
\prod_{i<k} b_i
$$

この形にしたのは正しい。
階乗・プリモリアルは、むしろ `dynamicPetalTotal` よりこちら側に自然に乗る。

階乗なら、

$$
b_i=i+1
$$

として、

$$
\prod_{i<k}(i+1)=k!
$$

プリモリアルなら、

$$
b_i=p_i
$$

として、

$$
\prod_{i<k}p_i
$$

になる。

つまり `dynamicOrbitTotal` は、Petal を超えて **動的周回積の共通基盤** になっておる。

## 3. `dynamicPetalTotal` の意味

一方 `dynamicPetalTotal a k` は、

$$
a_0\prod_{i<k}(a_i+1)
$$

じゃ。

ここでは `a i + 1` が、固定 Petal での

$$
n+1
$$

に対応する。

つまり、以前の

```text
基底単位核 + 継承口
```

を、lap ごとに

```text
動的単位核 a_i + 継承口 1
```

へ一般化した。

これはかなり良い。
`+1` を潰さず、`a i + 1` として残しているので、継承口構造が動的版にも残っておる。

## 4. 基本補題も良い

今回入った補題は、どれも後続の証明で効く。

```lean
theorem dynamicOrbitTotal_zero
theorem dynamicOrbitTotal_succ
```

これで `dynamicOrbitTotal` は、

```text
zero:
  空積 1

succ:
  前段 total に b k を掛ける
```

という再帰構造を持つ。

```lean
theorem dynamicOrbitTotal_const
```

これは重要じゃ。

$$
\prod_{i<k} b=b^k
$$

を固定しているので、固定型への bridge に使える。

そして、

```lean
theorem dynamicPetalTotal_zero
theorem dynamicPetalTotal_succ
```

により、動的 Petal も

```text
zero:
  a 0

succ:
  前段 total に a k + 1 を掛ける
```

と読めるようになった。

## 5. `dynamicPetalTotal_const` が本丸

今回の本丸はこれじゃな。

```lean
theorem dynamicPetalTotal_const (n k : Nat) :
    dynamicPetalTotal (fun _ => n) k = relPetalTotal n k
```

これで、

```text
固定単位核 Petal は、動的単位核 Petal の定数列特化
```

が Lean 上で固定された。

これは設計上の大きな節目じゃ。

つまり、既存の `relPetalTotal` を捨てずに、

```text
relPetalTotal
  固定単位核 API

dynamicPetalTotal
  動的単位核 API
```

として共存させられる。

後続では、固定核 theorem を dynamic theorem の special case として読めるようになる。

## 6. 階乗への道

次に自然なのは、やはり階乗 bridge じゃ。

候補はこれ。

```lean
theorem dynamicOrbitTotal_succIndex_eq_factorial (k : Nat) :
    dynamicOrbitTotal (fun i => i + 1) k = Nat.factorial k
```

数学的には、

$$
\prod_{i<k}(i+1)=k!
$$

じゃ。

Lean では `Nat.factorial_succ` まわりの向きに合わせる必要がある。
`dynamicOrbitTotal_succ` が

```lean
dynamicOrbitTotal b (k + 1) = dynamicOrbitTotal b k * b k
```

なので、帰納法でかなり素直に通るはずじゃ。

## 7. プリモリアルへの道

プリモリアルは、最初から「第 (i) 素数」を具体化すると重くなる。
まずは抽象列でよい。

```lean
def primeBaseOrbitTotal (p : Nat → Nat) (k : Nat) : Nat :=
  dynamicOrbitTotal p k
```

そして step 補題。

```lean
theorem primeBaseOrbitTotal_succ (p : Nat → Nat) (k : Nat) :
    primeBaseOrbitTotal p (k + 1) =
      primeBaseOrbitTotal p k * p k
```

さらに仮定付きで、

```lean
∀ i, Nat.Prime (p i)
```

を持たせれば、

```text
各 lap base が素数である orbit
```

として扱える。

具体的な `nthPrime` 接続は後でよい。
まずは抽象 prime-base orbit を作る方が安全じゃ。

## 8. Address 側との接続

今回の Dynamic は Counting 側だけじゃが、Address 側の設計とも相性が良い。

固定型では block size が、

$$
R_n(lap-1)
$$

だった。

動的型では、おそらく block size は、

$$
dynamicPetalTotal(a,lap-1)
$$

または lap-base driven なら、

$$
dynamicOrbitTotal(b,lap-1)
$$

になる。

つまり、固定 Address の形式はそのまま

```text
relPetalTotal を dynamicPetalTotal に置き換える
```

ことで動的 address へ一般化できる可能性がある。

ただし、動的版 address は少し後でよい。
まずは階乗・プリモリアル counting を固めるのが先じゃ。

## 9. 総括

今回の更新で、Petal Counting は次の段階へ進んだ。

```text
Before:
  relPetalTotal n k = n * (n + 1)^k

After:
  dynamicOrbitTotal b k = ∏ i<k, b i
  dynamicPetalTotal a k = a 0 * ∏ i<k, (a i + 1)
  relPetalTotal n k は dynamicPetalTotal の定数列特化
```

賢狼の判定はこうじゃ。

```text
Petal Counting Dynamic Core 完了
次は factorial orbit、その後 abstract primorial orbit
```

よいぞ、D.。
固定された花弁から、周回ごとに姿を変える花弁列へ進んだ。これで階乗の道、プリモリアルの道が同じ `dynamicOrbitTotal` の上に乗る。ここはかなり良い登山道じゃ。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Petal/Counting.lean b/lean/dk_math/DkMath/Petal/Counting.lean
index e1f6b27e..27cf4116 100644
--- a/lean/dk_math/DkMath/Petal/Counting.lean
+++ b/lean/dk_math/DkMath/Petal/Counting.lean
@@ -54,6 +54,58 @@ theorem relPetalTotal_succ (n lap : Nat) :
     relPetalTotal n (lap + 1) = relPetalTotal n lap * lapBase n := by
   simp [relPetalTotal, pow_succ, Nat.mul_assoc]

+/--
+Dynamic orbit total.
+
+This is the product of a lap-base sequence over the first `k` laps.
+-/
+def dynamicOrbitTotal (b : Nat → Nat) (k : Nat) : Nat :=
+  Finset.prod (Finset.range k) b
+
+/--
+Dynamic Petal total.
+
+The base unit core is allowed to vary by lap.  The initial core is `a 0`, and
+each lap uses the dynamic lap base `a i + 1`.
+-/
+def dynamicPetalTotal (a : Nat → Nat) (k : Nat) : Nat :=
+  a 0 * dynamicOrbitTotal (fun i => a i + 1) k
+
+/-- The dynamic orbit total at zero laps is empty-product `1`. -/
+theorem dynamicOrbitTotal_zero (b : Nat → Nat) :
+    dynamicOrbitTotal b 0 = 1 := by
+  simp [dynamicOrbitTotal]
+
+/-- One more dynamic lap multiplies by the next lap base. -/
+theorem dynamicOrbitTotal_succ (b : Nat → Nat) (k : Nat) :
+    dynamicOrbitTotal b (k + 1) = dynamicOrbitTotal b k * b k := by
+  simp [dynamicOrbitTotal, Finset.prod_range_succ]
+
+/-- A constant dynamic orbit is an ordinary power. -/
+theorem dynamicOrbitTotal_const (b k : Nat) :
+    dynamicOrbitTotal (fun _ => b) k = b ^ k := by
+  induction k with
+  | zero =>
+      simp [dynamicOrbitTotal_zero]
+  | succ k ih =>
+      rw [dynamicOrbitTotal_succ, ih]
+      rw [pow_succ]
+
+/-- The dynamic Petal total at zero laps is the initial base unit core. -/
+theorem dynamicPetalTotal_zero (a : Nat → Nat) :
+    dynamicPetalTotal a 0 = a 0 := by
+  simp [dynamicPetalTotal, dynamicOrbitTotal_zero]
+
+/-- One more dynamic Petal lap multiplies by the next dynamic lap base. -/
+theorem dynamicPetalTotal_succ (a : Nat → Nat) (k : Nat) :
+    dynamicPetalTotal a (k + 1) = dynamicPetalTotal a k * (a k + 1) := by
+  simp [dynamicPetalTotal, dynamicOrbitTotal_succ, Nat.mul_assoc]
+
+/-- Fixed-core Petal counting is the constant-core dynamic Petal total. -/
+theorem dynamicPetalTotal_const (n k : Nat) :
+    dynamicPetalTotal (fun _ => n) k = relPetalTotal n k := by
+  simp [dynamicPetalTotal, dynamicOrbitTotal_const, relPetalTotal, lapBase_eq_succ, baseUnitCore]
+
 /-- The one-lap total is the relative polygon kernel. -/
 theorem relPetalTotal_one (n : Nat) :
     relPetalTotal n 1 = relPolygonKernel n := by
````
`````
