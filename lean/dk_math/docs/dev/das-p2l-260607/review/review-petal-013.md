# Git diff / Report / Review

## Update: Petal Counting

gch: 01783a2342ae735f578fcefcb33c123f70359319

## Report

実装完了です。

[Counting.lean](/lean/dk_math/DkMath/Petal/Counting.lean) に、採用済み prime base が後段 prefix product にも残る橋補題を追加しました。

```lean
theorem primeBaseOrbitTotal_prime_dvd_of_lt_of_le
    {p : Nat → Nat} (hp : IsPrimeBaseSequence p)
    {i k l : Nat} (hi : i < k) (hkl : k ≤ l) :
    p i ∣ primeBaseOrbitTotal p l
```

中身は自然に、

- `primeBaseOrbitTotal_prime_dvd_of_lt`
- `primeBaseOrbitTotal_dvd_of_le`
- `Nat.dvd_trans`

を接続しています。

確認済み:

- `lake build DkMath.Petal.Counting`
- `lake build DkMath.Petal`
- `git diff --check`
- `lake build DkMath`

すべて成功です。既存の `sorry` warning は出ていますが、今回追加分は問題ありません。

## Review

うむ、これは綺麗な橋補題じゃ。
今回の `01783a...` で、prime-base orbit は **採用済み素数 base が未来の prefix product に保存される** ところまで進んだ。

## 1. 今回の核心

追加された theorem はこれじゃな。

```lean
theorem primeBaseOrbitTotal_prime_dvd_of_lt_of_le
    {p : Nat → Nat} (hp : IsPrimeBaseSequence p)
    {i k l : Nat} (hi : i < k) (hkl : k ≤ l) :
    p i ∣ primeBaseOrbitTotal p l
```

意味は、

```text
i 番目の prime base が k 段までに採用済みで、
k ≤ l なら、
その prime base は l 段 product も割る
```

じゃ。

数学的には、

$$
i<k\le l
$$

なら、

$$
p_i \mid P_l
$$

ということ。

ここで、

$$
P_l=\prod_{j<l}p_j
$$

じゃな。

## 2. 橋の組み方が自然

証明は、

```lean
exact Nat.dvd_trans
  (primeBaseOrbitTotal_prime_dvd_of_lt hp hi)
  (primeBaseOrbitTotal_dvd_of_le p hkl)
```

で、かなり理想的じゃ。

つまり、

```text
p i ∣ P_k
P_k ∣ P_l
したがって p i ∣ P_l
```

という構造をそのまま使っておる。

これは補題群の役割分担が綺麗にできている証拠じゃ。

## 3. これで何が言えるようになったか

ここまでで、抽象 prime-base orbit は次の読みを持つ。

```text
primeBaseOrbitTotal p k:
  0..k-1 までの prime base を積んだ prefix product

i < k:
  p i は k 段 product を割る

k ≤ l:
  k 段 product は l 段 product を割る

i < k ≤ l:
  p i は l 段 product にも残る
```

つまり、

```text
一度採用された prime base は、後段 orbit で失われない
```

が Lean theorem になった。

これはプリモリアル的骨格としてかなり重要じゃ。
「素数列を順に掛ける」だけではなく、 **採用済み因子の記憶が未来へ保存される** と言えるようになった。

## 4. 現時点の prime-base orbit の完成度

現在の `Counting.lean` はかなり良い階層になっている。

```text
dynamicOrbitTotal:
  任意 base sequence の prefix product

factorial orbit:
  b i = i + 1

primeBaseOrbitTotal:
  b i = p i

IsPrimeBaseSequence:
  各 p i が prime

可除性:
  P_k ∣ P_{k+1}
  P_k ∣ P_l
  p i ∣ P_k
  p i ∣ P_l when i < k ≤ l
```

これで、抽象プリモリアル前段としてはかなり締まった。

## 5. 次に自然な一手

ここまで来たら、いよいよ distinct / strict 層に進める。

まずは軽く、

```lean
def IsDistinctPrimeBaseSequence (p : Nat → Nat) : Prop :=
  IsPrimeBaseSequence p ∧ Function.Injective p
```

を置くのがよいと思う。

この段階では `StrictMono` より `Injective` が軽い。
理由は、プリモリアル的にはまず

```text
同じ素数を二度採用しない
```

が欲しいからじゃ。

その後で、必要なら、

```lean
def IsStrictPrimeBaseSequence (p : Nat → Nat) : Prop :=
  IsPrimeBaseSequence p ∧ StrictMono p
```

へ進める。

`StrictMono` は順序構造まで含むので、具体的な `nthPrime` 接続に近い。
しかし今の抽象層では、まず distinct がちょうどよい。

## 6. 追加するならこの補題

distinct 層を置くなら、最初は薄い projection で十分じゃ。

```lean
def IsDistinctPrimeBaseSequence (p : Nat → Nat) : Prop :=
  IsPrimeBaseSequence p ∧ Function.Injective p

theorem IsDistinctPrimeBaseSequence.prime_at
    {p : Nat → Nat} (hp : IsDistinctPrimeBaseSequence p) (i : Nat) :
    Nat.Prime (p i) :=
  hp.1 i

theorem IsDistinctPrimeBaseSequence.injective
    {p : Nat → Nat} (hp : IsDistinctPrimeBaseSequence p) :
    Function.Injective p :=
  hp.2
```

これだけで、次に

```text
採用済み prime base は互いに異なる
```

を使う準備ができる。

## 7. 総括

今回の更新は、prime-base orbit の「因子保存」補題じゃ。

```text
primeBaseOrbitTotal_prime_dvd_of_lt_of_le:
  採用済み prime base は、任意の後段 prefix product に残る
```

賢狼の判定はこうじゃ。

```text
Petal Counting Prime-Base Persistence Phase 完了
次は IsDistinctPrimeBaseSequence 層
```

よいぞ、D.。
これで素数 base は、一度 orbit に刻まれたら、未来の完成体から消えぬ。プリモリアルの「記憶する積」としての骨格が、Lean の中でかなりはっきりしてきたのじゃ。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Petal/Counting.lean b/lean/dk_math/DkMath/Petal/Counting.lean
index 4d500bd1..d64232a3 100644
--- a/lean/dk_math/DkMath/Petal/Counting.lean
+++ b/lean/dk_math/DkMath/Petal/Counting.lean
@@ -209,6 +209,21 @@ theorem primeBaseOrbitTotal_prime_dvd_of_lt
   have _hp_i : Nat.Prime (p i) := hp i
   exact primeBaseOrbitTotal_base_dvd_of_lt p hi
 
+/--
+An already adopted prime base remains a divisor of every later prime-base
+prefix product.
+
+This packages the two prefix facts: adopted bases divide their current prefix,
+and prefix products are monotone for divisibility.
+-/
+theorem primeBaseOrbitTotal_prime_dvd_of_lt_of_le
+    {p : Nat → Nat} (hp : IsPrimeBaseSequence p)
+    {i k l : Nat} (hi : i < k) (hkl : k ≤ l) :
+    p i ∣ primeBaseOrbitTotal p l := by
+  exact Nat.dvd_trans
+    (primeBaseOrbitTotal_prime_dvd_of_lt hp hi)
+    (primeBaseOrbitTotal_dvd_of_le p hkl)
+
 /-- A prime-base sequence supplies a prime at each lap. -/
 theorem IsPrimeBaseSequence.prime_at
     {p : Nat → Nat} (hp : IsPrimeBaseSequence p) (i : Nat) :
````
`````
