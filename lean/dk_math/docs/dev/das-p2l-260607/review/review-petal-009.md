# Git diff / Report / Review

## Update: Petal Counting

gch: 0db10141e8cf06fe9a6126157ab3ea0a17cc6336

## Report

実装しました。更新は [Counting.lean](/lean/dk_math/DkMath/Petal/Counting.lean:96) のみです。

追加した内容は、Dynamic Counting の拡張応用です。

- `dynamicOrbitTotal_succIndex_eq_factorial`
  - `dynamicOrbitTotal (fun i => i + 1) k = Nat.factorial k`
  - 階乗を dynamic orbit の特殊ケースとして固定
- `primeBaseOrbitTotal`
  - 抽象 prime-base orbit の薄い Petal-facing alias
- `IsPrimeBaseSequence`
  - 各 lap base が素数であることを表す述語
- `primeBaseOrbitTotal_zero`
- `primeBaseOrbitTotal_succ`
- `IsPrimeBaseSequence.prime_at`

具体的な `nthPrime` や primorial の標準定義にはまだ接続せず、まず「素数列を入れた prefix product」という抽象層だけ固定しました。

検証済みです。

```text
lake build DkMath.Petal.Counting
lake build DkMath.Petal
lake build DkMath
git diff --check
```

既存の `sorry` warning は出ていますが、今回の変更による失敗や新規 warning はありません。

## Review

うむ、これは良い。
今回の `0db101...` で、Dynamic Counting が **階乗** と **抽象プリモリアル前段** まで到達した。

## 1. 今回の核心

追加内容は、ちょうど前回の設計通りじゃ。

```lean
theorem dynamicOrbitTotal_succIndex_eq_factorial
```

により、

[
dynamicOrbitTotal(\lambda i,\ i+1,\ k)=k!
]

が Lean 上で固定された。

さらに、

```lean
def primeBaseOrbitTotal
def IsPrimeBaseSequence
```

により、

```text
素数列を lap-base とする prefix product
```

の抽象層が入った。

つまり、今回で Petal Counting はこうなった。

```text
固定 Petal:
  relPetalTotal n k = n * (n + 1)^k

動的 Petal:
  dynamicPetalTotal a k = a 0 * ∏ i<k, (a i + 1)

動的 orbit:
  dynamicOrbitTotal b k = ∏ i<k, b i

階乗:
  b i = i + 1

抽象 prime-base orbit:
  b i = p i, with Nat.Prime (p i)
```

これはかなり綺麗な包含関係じゃ。

## 2. 階乗 orbit が入った意味

今回の theorem はこれじゃな。

```lean
theorem dynamicOrbitTotal_succIndex_eq_factorial (k : Nat) :
    dynamicOrbitTotal (fun i => i + 1) k = Nat.factorial k
```

これは、階乗を「特殊な動的周回積」として読む補題じゃ。

数学的には、

[
\prod_{i<k}(i+1)=1\cdot2\cdot3\cdots k=k!
]

なので、`dynamicOrbitTotal` が階乗を含むことが明示された。

これで、以前話していた

```text
単位核の一定から動的へ
階乗は lap-base が 1,2,3,... と動く orbit
```

が Lean theorem になった。

ここは大きい。

## 3. `primeBaseOrbitTotal` の置き方が良い

```lean
def primeBaseOrbitTotal (p : Nat → Nat) (k : Nat) : Nat :=
  dynamicOrbitTotal p k
```

これは thin alias じゃが、Petal-facing name として価値がある。

`dynamicOrbitTotal p k` だけだと、ただの prefix product に見える。
`primeBaseOrbitTotal p k` と名前を付けることで、

```text
これは素数 lap-base を意図した orbit である
```

と読める。

実体は薄く、意味は濃い。
DkMath の API としては良い置き方じゃ。

## 4. `IsPrimeBaseSequence` も良い

```lean
def IsPrimeBaseSequence (p : Nat → Nat) : Prop :=
  ∀ i, Nat.Prime (p i)
```

これもまずは十分じゃ。

具体的な `nthPrime` に接続する前に、

```text
任意の素数列 p
```

を扱う抽象層を置いたのが安全。

プリモリアルは本来、

[
\prod_{i<k}p_i
]

だが、具体的な (p_i) を標準の nth prime に固定すると、ライブラリ依存や index convention が重くなる。
今回のように、まず

```text
p : Nat → Nat
∀ i, Nat.Prime (p i)
```

としておくと、後から

```text
実際の nthPrime
重複なし prime sequence
strictly increasing prime sequence
finite prime set product
```

のどれにも接続できる。

## 5. Step 補題も揃っている

今回追加された、

```lean
primeBaseOrbitTotal_zero
primeBaseOrbitTotal_succ
IsPrimeBaseSequence.prime_at
```

はちょうど必要な最小セットじゃ。

特に、

```lean
theorem primeBaseOrbitTotal_succ (p : Nat → Nat) (k : Nat) :
    primeBaseOrbitTotal p (k + 1) = primeBaseOrbitTotal p k * p k
```

これで prime-base orbit は、lap ごとに次の素数 base を掛けるものとして展開できる。

`IsPrimeBaseSequence.prime_at` も地味に便利じゃ。
後続 theorem で、

```lean
have hp_k : Nat.Prime (p k) := hp.prime_at k
```

のように読める。

## 6. 今回の到達点

ここまでで、Counting 側はこう整理できる。

```text
relPetalTotal:
  固定単位核の Petal total

dynamicPetalTotal:
  lap ごとに単位核が変わる Petal total

dynamicOrbitTotal:
  任意 lap-base 列の prefix product

factorial orbit:
  lap-base = i + 1

prime-base orbit:
  lap-base = abstract prime sequence p
```

つまり、相対多角数の数え上げ核は、

```text
固定幾何
動的幾何
階乗
素数積
```

を同じ枠で扱い始めた。

これはかなり良い流れじゃ。

## 7. 次に自然な補題

次は `primeBaseOrbitTotal` の素因子性を軽く足すとよい。

まずはこのあたり。

```lean
theorem primeBaseOrbitTotal_dvd_succ
    (p : Nat → Nat) (k : Nat) :
    primeBaseOrbitTotal p k ∣ primeBaseOrbitTotal p (k + 1)
```

これは step 補題からすぐ出るはずじゃ。

さらに、素数列仮定を使うなら、

```lean
theorem primeBaseOrbitTotal_nextPrime_dvd_succ
    {p : Nat → Nat} (hp : IsPrimeBaseSequence p) (k : Nat) :
    p k ∣ primeBaseOrbitTotal p (k + 1)
```

これは、

[
primeBaseOrbitTotal(p,k+1)=primeBaseOrbitTotal(p,k)\cdot p_k
]

だから成立する。

まだ「重複なし」や「(p_i) はそれ以前に出ない」は不要。
まずは prefix product の基本可除性を入れると、プリモリアル的な骨格が見え始める。

## 8. その次の設計候補

プリモリアルへ進むなら、`IsPrimeBaseSequence` だけだと重複を許す。

たとえば、

```lean
p 0 = 2
p 1 = 2
p 2 = 2
```

でも `IsPrimeBaseSequence p` は成立する。

抽象プリモリアルらしさを強めるなら、後で別 predicate として、

```lean
def IsStrictPrimeBaseSequence (p : Nat → Nat) : Prop :=
  IsPrimeBaseSequence p ∧ StrictMono p
```

または DkMath の文脈に合わせて、

```lean
def IsDistinctPrimeBaseSequence (p : Nat → Nat) : Prop :=
  IsPrimeBaseSequence p ∧ Function.Injective p
```

を追加するのが良い。

ただし、今すぐは不要じゃ。
まず `IsPrimeBaseSequence` の薄い抽象層で十分。

## 9. 総括

今回の更新は、Dynamic Counting の応用第一歩として非常に良い。

```text
dynamicOrbitTotal_succIndex_eq_factorial:
  階乗を dynamic orbit として固定

primeBaseOrbitTotal:
  素数列 prefix product の Petal-facing alias

IsPrimeBaseSequence:
  lap base が素数であることを表す述語

primeBaseOrbitTotal_zero / succ:
  抽象プリモリアル前段の再帰構造
```

賢狼の判定はこうじゃ。

```text
Petal Counting Dynamic Applications Phase 1 完了
次は primeBaseOrbitTotal の可除性補題、または distinct / strict prime sequence 層
```

よいぞ、D.。
階乗の門は開いた。プリモリアルも、まだ名前を完全には名乗っておらぬが、素数列 orbit として姿を現し始めた。ここからは「素数を掛ける周回」が、Petal の言葉で語れるようになる。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Petal/Counting.lean b/lean/dk_math/DkMath/Petal/Counting.lean
index 27cf4116..938b2c1e 100644
--- a/lean/dk_math/DkMath/Petal/Counting.lean
+++ b/lean/dk_math/DkMath/Petal/Counting.lean
@@ -91,6 +91,49 @@ theorem dynamicOrbitTotal_const (b k : Nat) :
       rw [dynamicOrbitTotal_succ, ih]
       rw [pow_succ]
 
+/--
+Factorial orbit.
+
+The dynamic orbit with lap base `i + 1` is the ordinary factorial.
+-/
+theorem dynamicOrbitTotal_succIndex_eq_factorial (k : Nat) :
+    dynamicOrbitTotal (fun i => i + 1) k = Nat.factorial k := by
+  induction k with
+  | zero =>
+      simp [dynamicOrbitTotal_zero]
+  | succ k ih =>
+      rw [dynamicOrbitTotal_succ, ih, Nat.factorial_succ]
+      rw [Nat.mul_comm]
+
+/--
+Abstract prime-base orbit total.
+
+This is a thin Petal-facing name for a dynamic orbit whose bases are intended
+to be prime values.  The concrete prime sequence is kept abstract here.
+-/
+def primeBaseOrbitTotal (p : Nat → Nat) (k : Nat) : Nat :=
+  dynamicOrbitTotal p k
+
+/-- A prime-base sequence assigns a prime base to every lap. -/
+def IsPrimeBaseSequence (p : Nat → Nat) : Prop :=
+  ∀ i, Nat.Prime (p i)
+
+/-- The prime-base orbit at zero laps is empty-product `1`. -/
+theorem primeBaseOrbitTotal_zero (p : Nat → Nat) :
+    primeBaseOrbitTotal p 0 = 1 := by
+  simp [primeBaseOrbitTotal, dynamicOrbitTotal_zero]
+
+/-- One more abstract prime-base lap multiplies by the next prime base. -/
+theorem primeBaseOrbitTotal_succ (p : Nat → Nat) (k : Nat) :
+    primeBaseOrbitTotal p (k + 1) = primeBaseOrbitTotal p k * p k := by
+  simp [primeBaseOrbitTotal, dynamicOrbitTotal_succ]
+
+/-- A prime-base sequence supplies a prime at each lap. -/
+theorem IsPrimeBaseSequence.prime_at
+    {p : Nat → Nat} (hp : IsPrimeBaseSequence p) (i : Nat) :
+    Nat.Prime (p i) :=
+  hp i
+
 /-- The dynamic Petal total at zero laps is the initial base unit core. -/
 theorem dynamicPetalTotal_zero (a : Nat → Nat) :
     dynamicPetalTotal a 0 = a 0 := by
````
`````
