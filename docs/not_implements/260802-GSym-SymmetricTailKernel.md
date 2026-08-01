# GSym 対称 Tail 核 実装予定

作成日: 2026-08-02  
状態: **未実装 / Lean 判定待ち**  
対象: `GTail`, `GN`, 素数次数 `d = p`, 対称内部核, Fermat quotient, Wieferich depth

---

## 1. 目的

本資料は、DkMath に既存の一般 Tail 構造 `GTail` と、その `r = 1` 特殊化である `GN` に対し、二項展開の左右両端を同時に除去した対称内部核を追加する実装予定を記録する。

仮称を、

```text
GSym
```

とする。

既存の `GN` は、

$$
(x+u)^d-u^d=x\,GN_d(x,u)
$$

として、`u^d` 側の境界を一つ除去する片側正規化 Tail である。

これに対し `GSym` は、

$$
x^d
$$

と、

$$
u^d
$$

の両境界を同時に除去し、残る全中間項から `xu` を取り出した中央核として設計する。

中心候補式は、

$$
(x+u)^d=x^d+u^d+xu\,GSym_d(x,u)
$$

である。

詳細な端点条件、型クラス、添字処理、係数除算、因子定理の実装方法は、実装時に Lean に判定させる。

---

## 2. 既存実装との位置関係

現在の一般 Tail は、概念的に、

```lean
GTail d r x u
```

として実装されている。

その基本形は、

$$
(x+u)^d
=
\sum_{j<r}\binom djx^ju^{d-j}
+
x^r\,GTail(d,r,x,u)
$$

である。

`r = 1` では、

$$
GN_d(x,u)=GTail(d,1,x,u)
$$

と読み、

$$
(x+u)^d=u^d+x\,GN_d(x,u)
$$

となる。

`GSym` は高次 Tail `r = 2` の単なる別名ではない。

`GTail(d,2,x,u)` は `x` 側から先頭二層を剥がす一方向 Tail であるのに対し、`GSym` は二項展開の両端、

```text
u^d
x^d
```

を除去した対称内部部分を主語にする。

したがって概念配置は、

```text
GTail
  └─ r = 1
      └─ GN              片側境界除去
          └─ GSym        両側境界除去・中央対称核
```

となる。

---

## 3. `GSym` の定義候補

`CommSemiring` 上で減算や除算を使わずに定義する第一候補は、次の有限和である。

```lean
@[simp] def GSym
    {R : Type _} [CommSemiring R]
    (d : ℕ) (x u : R) : R :=
  ∑ k ∈ Finset.range (d - 1),
    (Nat.choose d (k + 1) : R) *
      x ^ k * u ^ (d - 2 - k)
```

数学的には、

$$
GSym_d(x,u)
=
\sum_{k=0}^{d-2}
\binom d{k+1}x^ku^{d-2-k}
$$

である。

同値な添字表示は、

$$
GSym_d(x,u)
=
\sum_{j=1}^{d-1}
\binom djx^{j-1}u^{d-j-1}
$$

となる。

Lean 実装では、次を監査する。

1. `d = 0`, `d = 1` を total definition としてどう扱うか。
2. 主恒等式の仮定を `1 ≤ d` とするか、`2 ≤ d` とするか。
3. `d - 2 - k` の自然数切り捨てを、空の `Finset.range` によって安全に封じられるか。
4. `Finset.Icc 1 (d - 1)` 型の定義の方が再添字証明に適するか。
5. 既存 `GTail` の和を再利用する補題を先に作るべきか。

定義の最終形は、証明コストと再利用性を比較して決める。

---

## 4. 最初に閉じる主恒等式

減算を使わない標準形を優先する。

```lean
theorem add_pow_eq_left_right_add_mul_GSym
    {R : Type _} [CommSemiring R]
    (d : ℕ) (x u : R)
    (hd : 1 ≤ d) :
    (x + u) ^ d =
      x ^ d + u ^ d + x * u * GSym d x u
```

数学的には、

$$
(x+u)^d=x^d+u^d+xu\,GSym_d(x,u)
$$

である。

`CommRing` 上では、減算形も追加する。

```lean
theorem add_pow_sub_boundaries_eq_mul_GSym
    {R : Type _} [CommRing R]
    (d : ℕ) (x u : R)
    (hd : 1 ≤ d) :
    (x + u) ^ d - x ^ d - u ^ d =
      x * u * GSym d x u
```

式の並びと結合順は、既存の宇宙式 API と `simp` 正規形に合わせて調整する。

---

## 5. `GN` との接続

`GSym` は独立した新しい多項式というより、左右二つの `GN` に共通する中央核として扱う。

第一の接続候補は、

$$
GN_d(x,u)=x^{d-1}+u\,GSym_d(x,u)
$$

である。

Lean theorem 候補:

```lean
theorem GN_eq_pow_add_u_mul_GSym
    {R : Type _} [CommSemiring R]
    (d : ℕ) (x u : R)
    (hd : 1 ≤ d) :
    GTail d 1 x u =
      x ^ (d - 1) + u * GSym d x u
```

反対側からは、

$$
GN_d(u,x)=u^{d-1}+x\,GSym_d(x,u)
$$

を狙う。

```lean
theorem GN_swap_eq_pow_add_x_mul_GSym
    {R : Type _} [CommSemiring R]
    (d : ℕ) (x u : R)
    (hd : 1 ≤ d) :
    GTail d 1 u x =
      u ^ (d - 1) + x * GSym d x u
```

この接続により、

```text
GN(x,u) の最上位境界 x^(d-1) を除去
  ↓
u * GSym(x,u)
```

および、

```text
GN(u,x) の最上位境界 u^(d-1) を除去
  ↓
x * GSym(x,u)
```

という左右対称な読みが得られる。

---

## 6. 対称性

名称 `GSym` の中心定理は、変数交換対称性である。

```lean
theorem GSym_comm
    {R : Type _} [CommSemiring R]
    (d : ℕ) (x u : R) :
    GSym d x u = GSym d u x
```

数学的には、二項係数の対称性、

$$
\binom dj=\binom d{d-j}
$$

と、添字変換、

$$
j\longleftrightarrow d-j
$$

から従う。

実装候補は二つある。

### Route A: 有限和の直接再添字

- `Finset.range` または `Finset.Icc` を反転する。
- `Nat.choose_symm` 系の既存補題を使う。
- `omega` で指数の差分を整える。

### Route B: 主恒等式からの導出

左右交換した主恒等式を比較する。

ただし一般 `CommSemiring` では `x * u` のキャンセルができないため、完全な一般性では Route A が本命となる。

多項式環上で先に証明し、評価写像で一般環へ移す設計も候補に残す。

---

## 7. 素数次数 `d = p` の係数層

素数 `p` と、

$$
1\le j\le p-1
$$

に対し、

$$
p\mid\binom pj
$$

である。

したがって `GSym p x u` の全係数は `p` を含む。

数学的には、

$$
GSym_p(x,u)=p\,GSymPrimeReduced_p(x,u)
$$

を狙う。

ここで重要なのは、一般環上で直接 `/ p` を行わないことである。

まず自然数係数として、

```lean
def primeChooseQuotient (p j : ℕ) : ℕ :=
  Nat.choose p j / p
```

のような係数商を置き、素数性と内部添字条件から、

```lean
theorem choose_eq_prime_mul_primeChooseQuotient
```

を証明する。

その後、係数を任意の `CommSemiring` へ cast して、

```lean
def GSymPrimeReduced
    {R : Type _} [CommSemiring R]
    (p : ℕ) (x u : R) : R :=
  ∑ k ∈ Finset.range (p - 1),
    (primeChooseQuotient p (k + 1) : R) *
      x ^ k * u ^ (p - 2 - k)
```

を定義する案がある。

主定理候補:

```lean
theorem GSym_eq_prime_mul_reduced
    {R : Type _} [CommSemiring R]
    {p : ℕ} (hp : Nat.Prime p)
    (x u : R) :
    GSym p x u =
      (p : R) * GSymPrimeReduced p x u
```

これにより、

$$
(x+u)^p-x^p-u^p
=
p\,xu\,GSymPrimeReduced_p(x,u)
$$

が得られる。

---

## 8. 奇素数で現れる追加因子 `x + u`

`p` が奇数なら、整数または多項式環上で `u = -x` を代入すると、

$$
(x-x)^p-x^p-(-x)^p=0
$$

となる。

したがって因子定理により、

$$
x+u
$$

が追加因子になる。

最終候補形は、

$$
(x+u)^p-x^p-u^p
=
p\,xu(x+u)Q_p(x,u)
$$

である。

ここで `Q_p` の仮称候補は、

```text
GSymOddQuotient
GSymPrimeOddReduced
GSymCyclotomicCore
```

などである。

名称は、実装後の利用先を見て決定する。

### 重要な補正

`x + u` が因子になる理由を、数値としての、

```text
xu と x+u が互いに素
```

に求めてはならない。

一般に `xu` と `x+u` は互いに素ではない。

正しい根拠は、

```text
多項式として u = -x で零になる
  ↓
因子定理により x + u が割り切る
```

である。

この層は、自然数の可除性だけで無理に処理せず、次のいずれかを使う。

1. `Polynomial` または `MvPolynomial` 上の因子定理。
2. 整数係数の明示的な quotient 多項式。
3. 係数 recurrence により `Q_p` を直接構成する。

---

## 9. `Q_p` の明示係数候補

`GSymPrimeReduced` の係数を、

$$
a_k=\frac1p\binom p{k+1}
$$

と置く。

`Q_p` を、

$$
Q_p(x,u)=\sum_{k=0}^{p-3}b_kx^ku^{p-3-k}
$$

と置けば、

$$
a_k=b_k+b_{k-1}
$$

という recurrence が現れる。ただし境界は、

$$
b_{-1}=0
$$

と読む。

したがって形式的には、

$$
b_k=a_k-b_{k-1}
$$

または、

$$
b_k=\sum_{i=0}^{k}(-1)^{k-i}a_i
$$

となる。

この route は明示定義を作れる利点がある一方、自然数係数としての非負性証明が追加で必要になる可能性がある。

初期実装では `ℤ` 係数で quotient を構成し、後から係数非負性を分離する方が安全かもしれない。

---

## 10. 小次数の検算

Lean の `example` または専用 test theorem として、少なくとも次を固定する。

### `d = 1`

$$
GSym_1(x,u)=0
$$

$$
(x+u)-x-u=0
$$

### `d = 2`

$$
GSym_2(x,u)=2
$$

$$
(x+u)^2-x^2-u^2=2xu
$$

### `p = 3`

$$
GSym_3(x,u)=3(x+u)
$$

$$
(x+u)^3-x^3-u^3=3xu(x+u)
$$

したがって、

$$
Q_3(x,u)=1
$$

### `p = 5`

$$
GSym_5(x,u)
=
5(x+u)(x^2+xu+u^2)
$$

$$
(x+u)^5-x^5-u^5
=
5xu(x+u)(x^2+xu+u^2)
$$

したがって、

$$
Q_5(x,u)=x^2+xu+u^2
$$

### `p = 7`

候補検算式:

$$
Q_7(x,u)
=
x^4+2x^3u+3x^2u^2+2xu^3+u^4
$$

$$
(x+u)^7-x^7-u^7
=
7xu(x+u)Q_7(x,u)
$$

これらは `ring` / `norm_num` による有限検算として先に固定できる。

---

## 11. `x = u = 1` と Fermat quotient

奇素数 `p` の factorization に、

$$
x=u=1
$$

を代入すると、

$$
2^p-2=2p\,Q_p(1,1)
$$

となる。

したがって、

$$
Q_p(1,1)
=
\frac{2^{p-1}-1}{p}
$$

である。

右辺は base `2` の Fermat quotient、

$$
q_p(2)=\frac{2^{p-1}-1}{p}
$$

である。

Lean API 候補:

```lean
def fermatQuotientTwo (p : ℕ) : ℕ :=
  (2 ^ (p - 1) - 1) / p
```

ただし既存 Mathlib または DkMath に同義 API が存在する可能性があるため、新規定義前に検索する。

接続定理候補:

```lean
theorem GSymOddQuotient_one_one_eq_fermatQuotientTwo
    {p : ℕ}
    (hp : Nat.Prime p)
    (hpOdd : Odd p) :
    GSymOddQuotient p 1 1 = fermatQuotientTwo p
```

さらに、

$$
p\mid Q_p(1,1)
$$

は、

$$
p^2\mid 2^{p-1}-1
$$

という base `2` Wieferich 条件に対応する。

このため `GSym` は、

```text
二項係数の共通 prime p
  ↓
対称内部核
  ↓
追加 p-adic depth
  ↓
Fermat quotient / Wieferich condition
```

を直接接続する可能性がある。

---

## 12. 想定モジュール配置

一般代数層と素数数論層を分離する。

第一候補:

```text
DkMath/Lib/Cosmic/GSym.lean
DkMath/NumberTheory/GSymPrime.lean
DkMath/NumberTheory/GSymWieferich.lean
```

役割:

### `DkMath.Lib.Cosmic.GSym`

- `GSym`
- 両境界 Tail 恒等式
- `GN` との左右接続
- `GSym_comm`
- 小次数の純代数補題

### `DkMath.NumberTheory.GSymPrime`

- `primeChooseQuotient`
- 素数行の全係数 `p` 可除性
- `GSymPrimeReduced`
- 奇素数での `x + u` factor
- `Q_p` 相当の quotient

### `DkMath.NumberTheory.GSymWieferich`

- `x = u = 1`
- Fermat quotient との一致
- Wieferich 条件との同値
- `padicValNat` bridge

初期 checkpoint ではファイルを分けすぎず、一般 `GSym` と prime specialization の二枚で開始してもよい。

---

## 13. 実装 checkpoint 案

### GSYM-001: 定義と主恒等式

目標:

```lean
def GSym
add_pow_eq_left_right_add_mul_GSym
add_pow_sub_boundaries_eq_mul_GSym
```

検証:

- `d = 0,1,2` の端点
- `CommSemiring` / `CommRing` の最小仮定
- `Nat` 減算の安全性

### GSYM-002: `GN` 接続

目標:

```lean
GN_eq_pow_add_u_mul_GSym
GN_swap_eq_pow_add_x_mul_GSym
```

検証:

- 現在の canonical `GN` 名への接続
- `GTail d 1` を直接主語にするか
- `simp` 正規形

### GSYM-003: 対称性

目標:

```lean
GSym_comm
```

検証:

- `Finset` 反転再添字
- `Nat.choose` 対称性
- 多項式 route の方が短いか

### GSYM-004: 素数係数商

目標:

```lean
primeChooseQuotient
choose_eq_prime_mul_primeChooseQuotient
GSymPrimeReduced
GSym_eq_prime_mul_reduced
```

検証:

- 既存 Mathlib 補題
- `/ p` の exactness
- cast 後の積正規化

### GSYM-005: 奇素数 factor

目標:

```lean
GSymOddQuotient
GSymPrimeReduced_eq_add_mul_oddQuotient
prime_add_pow_sub_boundaries_factor
```

検証:

- `Polynomial` / `MvPolynomial` / 明示 recurrence の比較
- `x + u` 因子の証明
- quotient の係数型を `ℕ`, `ℤ`, generic ring のどこに置くか

### GSYM-006: Fermat quotient bridge

目標:

```lean
GSymOddQuotient_one_one_eq_fermatQuotientTwo
prime_dvd_GSymOddQuotient_one_one_iff_wieferich
```

検証:

- 既存 Fermat quotient 定義
- `p^2 ∣ 2^(p-1)-1` と `p^2 ∣ 2^p-2` の bridge
- `padicValNat` による深度表現

### GSYM-007: 利用先の偵察

候補:

```text
FLT3 / FLT5 / FLT7
ABC GN valuation flow
WeightedBinomial / Petal
Pascal-Zsigmondy Bridge
Wieferich / NoLift
```

この checkpoint までは、各予想や完成証明へ直接接続しない。

まず `GSym` 自体の API が安定してから bridge を作る。

---

## 14. 実装時の注意事項

### 14.1. `GSym` を `GN(x,u) - GN(u,x)` と定義しない

`GSym` は左右 `GN` の差ではない。

左右両方に共通する内部核である。

差を取ると対称核ではなく反対称成分が現れるため、目的が変わる。

### 14.2. 一般環で係数除算をしない

素数 `p` による係数除去は、自然数係数で exact quotient を構成してから cast する。

### 14.3. `x + u` 因子を gcd で説明しない

これは多項式因子定理の層である。

### 14.4. `d = p` と `p ∣ x,u` を混同しない

係数に現れる `p` は Pascal 行 `d = p` の構造であり、入力値 `x,u` の可除性とは独立である。

### 14.5. Wieferich 接続は特殊化である

`Q_p(1,1)` が Fermat quotient になることは重要だが、`GSym` 全体の定義目的を `x=u=1` に限定しない。

`GSym` の本体は二変数の対称内部核である。

---

## 15. 期待される概念地図

```text
二項 Big
  (x+u)^d
      │
      ├─ u^d を除去
      │    └─ x * GN_d(x,u)
      │
      ├─ x^d を除去
      │    └─ u * GN_d(u,x)
      │
      └─ x^d と u^d を同時除去
           └─ x*u*GSym_d(x,u)
                    │
                    ├─ d = p prime
                    │    └─ p * x*u*GSymPrimeReduced_p
                    │
                    ├─ p odd
                    │    └─ p*x*u*(x+u)*Q_p
                    │
                    └─ x = u = 1
                         └─ Fermat quotient q_p(2)
                              └─ Wieferich depth
```

この構造では、`GSym` は単なる補助和ではない。

`GN(x,u)` と `GN(u,x)` の左右世界を接着し、Pascal 素数行の共通係数を、奇対称因子と Fermat quotient へ運ぶ中央対称核として働く。

---

## 16. 現時点の結論

実装予定として固定する中心方針は、次である。

1. `GSym` を左右両境界除去後の中央核として新設する。
2. 最初は generic な二項恒等式と `GN` bridge だけを閉じる。
3. 素数係数商は自然数係数上で構成し、一般環で除算しない。
4. 奇素数の `x + u` 因子は、多項式因子定理または明示 quotient で証明する。
5. `x = u = 1` で Fermat quotient と接続する。
6. Wieferich、FLT、ABC、Petal への接続は、基礎 API 完成後の別 checkpoint とする。

詳細な theorem statement と proof route は、既存 Mathlib API および DkMath の現在の正規形を調査したうえで、Lean の判定に従って確定する。
