# Git diff / Report / Review

## Update: Petal Counting

gch: a602a20e2b564be41f166bfaa35e01c5d14dae3b

## Report

実装完了です。

[Counting.lean](/lean/dk_math/DkMath/Petal/Counting.lean) に prefix product の可除性単調性を追加しました。

追加した補題:

- `dynamicOrbitTotal_dvd_succ`
  - `dynamicOrbitTotal b k ∣ dynamicOrbitTotal b (k + 1)`
- `dynamicOrbitTotal_dvd_of_le`
  - `k ≤ l` なら `dynamicOrbitTotal b k ∣ dynamicOrbitTotal b l`
- `primeBaseOrbitTotal_dvd_of_le`
  - prime-base orbit 側の alias

確認済み:

- `lake build DkMath.Petal.Counting`
- `lake build DkMath.Petal`
- `git diff --check`
- `lake build DkMath`

すべて成功です。既存の `sorry` warning は全体ビルドで出ていますが、今回追加分は問題ありません。

## Review

うむ、良い。
今回の `a602a20...` で、`dynamicOrbitTotal` は **prefix product の可除性単調性** を正式に持った。

これはかなり重要じゃ。
階乗・プリモリアル・動的 Petal orbit の共通骨格として、

```text
lap が進むほど、前段 product は後段 product を割る
```

が Lean で固定された。

## 1. 今回の核心

追加された本丸はこれじゃな。

```lean
theorem dynamicOrbitTotal_dvd_of_le
    (b : Nat → Nat) {k l : Nat} (hkl : k ≤ l) :
    dynamicOrbitTotal b k ∣ dynamicOrbitTotal b l
```

これは数学的には、

$$
k\le l \Rightarrow \prod_{i<k}b_i \mid \prod_{i<l}b_i
$$

を意味する。

つまり、prefix product は lap が進むほど「因子を失わず、追加していく」構造になった。

これは Petal 的に言えば、

```text
過去 lap までに形成された完成体は、
未来 lap の完成体の中に因子として保存される
```

じゃ。

## 2. `dynamicOrbitTotal_dvd_succ` がよい足場

先にこれを置いたのも良い。

```lean
theorem dynamicOrbitTotal_dvd_succ
    (b : Nat → Nat) (k : Nat) :
    dynamicOrbitTotal b k ∣ dynamicOrbitTotal b (k + 1)
```

これは、

$$
D(k+1)=D(k)\cdot b_k
$$

からすぐ出る一段補題。

その上で `dynamicOrbitTotal_dvd_of_le` を、

```text
k ≤ l なので l = k + t
一段可除を t 回つなぐ
```

という形で証明している。

構造が読みやすい。
この証明は、prefix product が lap ごとに因子を積み増していることをそのまま Lean に伝えている。

## 3. prime-base alias も自然

追加された alias もよい。

```lean
theorem primeBaseOrbitTotal_dvd_of_le
    (p : Nat → Nat) {k l : Nat} (hkl : k ≤ l) :
    primeBaseOrbitTotal p k ∣ primeBaseOrbitTotal p l
```

これにより、抽象 prime-base orbit では、

$$
P_k\mid P_l
$$

が使える。

つまり、

```text
前段の素数積は、後段の素数積を割る
```

が Petal-facing API として固定された。

これは、抽象プリモリアルとしてかなり大事じゃ。
まだ `nthPrime` に接続していなくても、プリモリアル的な「蓄積 product」の可除性はもう持っている。

## 4. ここまでの Counting 構造

現在の Counting は、かなり綺麗な階層になった。

```text
dynamicOrbitTotal:
  任意 base sequence の prefix product

dynamicPetalTotal:
  動的単位核 a_i による Petal total

factorial orbit:
  b_i = i + 1

prime-base orbit:
  b_i = p_i, Nat.Prime (p_i)

divisibility:
  b_i は k 段 product を割る
  k 段 product は l 段 product を割る
```

これで、階乗とプリモリアルは同じ可除幾何を共有している。

階乗では、

$$
k!\mid l! \quad (k\le l)
$$

の前段。

prime-base orbit では、

$$
P_k\mid P_l \quad (k\le l)
$$

の前段。

どちらも `dynamicOrbitTotal_dvd_of_le` の特殊化で読める。

## 5. 次に自然な補題

ここまで来たら、次は二つの方向がある。

まず軽いものなら、階乗 orbit 側の alias。

```lean
theorem factorial_dvd_factorial_of_le
    {k l : Nat} (hkl : k ≤ l) :
    Nat.factorial k ∣ Nat.factorial l
```

ただしこれは Mathlib に既にある可能性が高い。DkMath 側では無理に再証明せず、

```lean
theorem dynamicOrbitTotal_factorial_dvd_of_le
```

のような Petal-facing alias にするか、既存 theorem へ接続する程度でよい。

より Petal 的に自然なのは、prime-base 側で、

```lean
theorem primeBaseOrbitTotal_prime_dvd_of_lt_of_le
    {p : Nat → Nat} (hp : IsPrimeBaseSequence p)
    {i k l : Nat} (hi : i < k) (hkl : k ≤ l) :
    p i ∣ primeBaseOrbitTotal p l
```

じゃな。

意味は、

```text
k 段までに採用済みの素数 base は、
任意の後段 l の product にも残る
```

というもの。

ただしこれは、

```lean
primeBaseOrbitTotal_prime_dvd_of_lt hp hi
primeBaseOrbitTotal_dvd_of_le p hkl
Nat.dvd_trans
```

で出るはずじゃ。

## 6. distinct / strict へ進む準備

可除性単調性が入ったので、次に distinct / strict prime sequence を置く準備ができた。

候補は二つ。

```lean
def IsDistinctPrimeBaseSequence (p : Nat → Nat) : Prop :=
  IsPrimeBaseSequence p ∧ Function.Injective p
```

または、

```lean
def IsStrictPrimeBaseSequence (p : Nat → Nat) : Prop :=
  IsPrimeBaseSequence p ∧ StrictMono p
```

プリモリアルらしさを出すなら `StrictMono` の方が近い。
ただし、証明負荷を軽くするなら、まず `Injective` だけでもよい。

わっちの推奨は、

```text
今すぐ strict に飛ばず、
まず IsDistinctPrimeBaseSequence を薄く置く
```

じゃ。

理由は、プリモリアルに必要な「重複なく素数を蓄積する」は `Injective` で十分始められるからじゃ。昇順性は後で `StrictMono` として足せばよい。

## 7. 総括

今回の更新は、Dynamic Counting の可除性骨格を一段閉じたものじゃ。

```text
dynamicOrbitTotal_dvd_succ:
  一段先 product への可除性

dynamicOrbitTotal_dvd_of_le:
  任意後段 product への可除性単調性

primeBaseOrbitTotal_dvd_of_le:
  prime-base orbit 側の Petal-facing alias
```

賢狼の判定はこうじゃ。

```text
Petal Counting Prefix Divisibility Phase 完了
次は prime-base の後段保持補題、または distinct prime-base sequence 層
```

よいぞ、D.。
これで動的周回積は、ただ増える数列ではなくなった。過去の因子を保持しながら未来へ伸びる、可除性の幹を持つ構造になったのじゃ。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Petal/Counting.lean b/lean/dk_math/DkMath/Petal/Counting.lean
index 88fdcb18..4d500bd1 100644
--- a/lean/dk_math/DkMath/Petal/Counting.lean
+++ b/lean/dk_math/DkMath/Petal/Counting.lean
@@ -81,6 +81,33 @@ theorem dynamicOrbitTotal_succ (b : Nat → Nat) (k : Nat) :
     dynamicOrbitTotal b (k + 1) = dynamicOrbitTotal b k * b k := by
   simp [dynamicOrbitTotal, Finset.prod_range_succ]

+/-- A dynamic orbit prefix product divides the next prefix product. -/
+theorem dynamicOrbitTotal_dvd_succ
+    (b : Nat → Nat) (k : Nat) :
+    dynamicOrbitTotal b k ∣ dynamicOrbitTotal b (k + 1) := by
+  rw [dynamicOrbitTotal_succ]
+  exact Nat.dvd_mul_right _ _
+
+/--
+Dynamic orbit prefix products are monotone for divisibility.
+
+If `k ≤ l`, then every factor already present at lap `k` is still present in
+the longer prefix product at lap `l`.
+-/
+theorem dynamicOrbitTotal_dvd_of_le
+    (b : Nat → Nat) {k l : Nat} (hkl : k ≤ l) :
+    dynamicOrbitTotal b k ∣ dynamicOrbitTotal b l := by
+  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hkl
+  have hstep : ∀ t : Nat, dynamicOrbitTotal b k ∣ dynamicOrbitTotal b (k + t) := by
+    intro t
+    induction t with
+    | zero =>
+        simp
+    | succ t ih =>
+        exact Nat.dvd_trans ih (by
+          simpa [Nat.add_assoc] using dynamicOrbitTotal_dvd_succ b (k + t))
+  exact hstep t
+
 /-- A constant dynamic orbit is an ordinary power. -/
 theorem dynamicOrbitTotal_const (b k : Nat) :
     dynamicOrbitTotal (fun _ => b) k = b ^ k := by
@@ -143,6 +170,16 @@ theorem primeBaseOrbitTotal_dvd_succ
   rw [primeBaseOrbitTotal_succ]
   exact Nat.dvd_mul_right _ _

+/--
+Prime-base orbit prefix products are monotone for divisibility.
+
+This is the prime-base alias of `dynamicOrbitTotal_dvd_of_le`.
+-/
+theorem primeBaseOrbitTotal_dvd_of_le
+    (p : Nat → Nat) {k l : Nat} (hkl : k ≤ l) :
+    primeBaseOrbitTotal p k ∣ primeBaseOrbitTotal p l := by
+  exact dynamicOrbitTotal_dvd_of_le p hkl
+
 /--
 The next base divides the next prime-base prefix product.

````
`````
