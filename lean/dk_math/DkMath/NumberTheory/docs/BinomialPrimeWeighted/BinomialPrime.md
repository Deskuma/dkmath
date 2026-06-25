# BinomialPrime

[BinomialPrime.lean](/lean/dk_math/DkMath/NumberTheory/BinomialPrime.lean)

## 概要

この Lean は、**「素数 `p` のパスカル三角形の第 `p` 行では、端を除く二項係数がすべて `p` で割り切れる」** という基本事実を、あとで使いやすい API 形に整理したものです。

### 解説

中心命題はこれです。

```lean
theorem prime_allInnerChooseDivisible_self
    {p : ℕ} (hp : p.Prime) :
    AllInnerChooseDivisible p p := by
  intro k hk0 hkp
  exact hp.dvd_choose_self hk0.ne' hkp
```

数学的には、

\[
p \text{ prime},\quad 0 < k < p
\quad\Longrightarrow\quad
p \mid {p \choose k}
\]

です。

---

## import

```lean
import Mathlib.Data.Nat.Choose.Dvd
```

これは `Nat.choose`、つまり二項係数に関する割り切り定理を使うための import です。

特にここでは次を使っています。

```lean
hp.dvd_choose_self
```

これは素数 `p` について、内側の二項係数 `Nat.choose p k` が `p` で割り切れる、という mathlib 側の定理です。

---

## 名前空間

```lean
namespace DkMath
namespace NumberTheory
```

このファイル内の定義や定理を、

```lean
DkMath.NumberTheory.prime_dvd_inner_choose
```

のような名前で管理するためのものです。

最後に、

```lean
end NumberTheory
end DkMath
```

で閉じています。

---

## AllInnerChooseDivisible

```lean
def AllInnerChooseDivisible (d m : ℕ) : Prop :=
  ∀ k, 0 < k → k < d → m ∣ Nat.choose d k
```

これは、

> 第 `d` 行の内側の二項係数がすべて `m` で割り切れる

という性質です。

「内側」とは、

```lean
0 < k
k < d
```

を満たす `k` のことです。

つまり端の

```lean
Nat.choose d 0
Nat.choose d d
```

は除外しています。端はどちらも `1` なので、一般には `m` で割り切れないからです。

数学的には、

\[
\forall k,\quad 0 < k < d \Rightarrow m \mid {d \choose k}
\]

です。

---

## InnerRowSupportPrime

```lean
def InnerRowSupportPrime (d p : ℕ) : Prop :=
  p.Prime ∧ AllInnerChooseDivisible d p
```

これは、

> `p` は素数で、かつ第 `d` 行の内側の二項係数すべてを割る

という性質です。

つまり、

\[
p \text{ is prime}
\]

かつ

\[
\forall k,\quad 0 < k < d \Rightarrow p \mid {d \choose k}
\]

です。

`p` がその行の「共通の素因数」として観測される、という意味の名前になっています。

---

## RowBirthPrime

```lean
def RowBirthPrime (d p : ℕ) : Prop :=
  InnerRowSupportPrime d p ∧ p ∣ d
```

これはさらに、

> `p` は第 `d` 行の内側の二項係数すべてを割る素数であり、しかも `d` 自身も割る

という性質です。

つまり、

\[
p \text{ prime}
\]

\[
\forall k,\quad 0 < k < d \Rightarrow p \mid {d \choose k}
\]

\[
p \mid d
\]

をまとめたものです。

コメントにもある通り、これは **`d` が素数であることまでは主張していません**。

たとえば `d = p^a` のような素数冪でも、同じ素数 `p` が行全体に現れることがあります。なのでこのファイルでは逆向き、

```lean
AllInnerChooseDivisible d d → d.Prime
```

のような主張は扱っていません。

---

## prime_allInnerChooseDivisible_self

```lean
theorem prime_allInnerChooseDivisible_self
    {p : ℕ} (hp : p.Prime) :
    AllInnerChooseDivisible p p := by
  intro k hk0 hkp
  exact hp.dvd_choose_self hk0.ne' hkp
```

このファイルの主定理です。

`hp : p.Prime` から、

```lean
AllInnerChooseDivisible p p
```

を示します。

展開するとゴールは、

```lean
∀ k, 0 < k → k < p → p ∣ Nat.choose p k
```

です。

証明の流れは：

```lean
intro k hk0 hkp
```

で任意の `k` と仮定

```lean
hk0 : 0 < k
hkp : k < p
```

を導入します。

その後、

```lean
exact hp.dvd_choose_self hk0.ne' hkp
```

で mathlib の既存定理を使っています。

ここで、

```lean
hk0.ne'
```

は

```lean
0 < k
```

から

```lean
k ≠ 0
```

を作っています。

`hp.dvd_choose_self` は、おおよそ次の形の定理です。

```lean
hp.dvd_choose_self : k ≠ 0 → k < p → p ∣ Nat.choose p k
```

なので、`hk0.ne'` と `hkp` を渡せば終わります。

---

## prime_dvd_inner_choose

```lean
theorem prime_dvd_inner_choose
    {p k : ℕ} (hp : p.Prime) (hk0 : 0 < k) (hkp : k < p) :
    p ∣ Nat.choose p k :=
  prime_allInnerChooseDivisible_self hp k hk0 hkp
```

これは先ほどの定理の別名 API です。

`AllInnerChooseDivisible p p` というまとめた形ではなく、直接

```lean
p ∣ Nat.choose p k
```

を返す形にしています。

初心者向けに言うと、使うときはこっちの方が便利です。

```lean
exact prime_dvd_inner_choose hp hk0 hkp
```

のように使えます。

---

## allInnerChooseDivisible_dvd_choose

```lean
theorem allInnerChooseDivisible_dvd_choose
    {d m k : ℕ}
    (h : AllInnerChooseDivisible d m) (hk0 : 0 < k) (hkd : k < d) :
    m ∣ Nat.choose d k :=
  h k hk0 hkd
```

これは `AllInnerChooseDivisible` を具体的な `k` に適用する補助定理です。

`h` の中身はもともと、

```lean
∀ k, 0 < k → k < d → m ∣ Nat.choose d k
```

なので、

```lean
h k hk0 hkd
```

でそのまま結論が出ます。

---

## innerRowSupportPrime_dvd_choose

```lean
theorem innerRowSupportPrime_dvd_choose
    {d p k : ℕ}
    (h : InnerRowSupportPrime d p) (hk0 : 0 < k) (hkd : k < d) :
    p ∣ Nat.choose d k :=
  h.2 k hk0 hkd
```

`InnerRowSupportPrime d p` は定義上、

```lean
p.Prime ∧ AllInnerChooseDivisible d p
```

です。

なので、

```lean
h.1
```

は

```lean
p.Prime
```

で、

```lean
h.2
```

は

```lean
AllInnerChooseDivisible d p
```

です。

ここでは割り切りが欲しいので、

```lean
h.2 k hk0 hkd
```

を使っています。

---

## innerRowSupportPrime_prime

```lean
theorem innerRowSupportPrime_prime
    {d p : ℕ} (h : InnerRowSupportPrime d p) :
    p.Prime :=
  h.1
```

これは `InnerRowSupportPrime d p` から、保存されている素数性を取り出す定理です。

```lean
h.1
```

がそのまま `p.Prime` です。

---

## prime_innerRowSupportPrime_self

```lean
theorem prime_innerRowSupportPrime_self
    {p : ℕ} (hp : p.Prime) :
    InnerRowSupportPrime p p :=
  ⟨hp, prime_allInnerChooseDivisible_self hp⟩
```

これは、

> 素数 `p` の第 `p` 行には、サポート素数 `p` がある

という定理です。

`InnerRowSupportPrime p p` は、

```lean
p.Prime ∧ AllInnerChooseDivisible p p
```

なので、ペアを作ればよいです。

```lean
⟨hp, prime_allInnerChooseDivisible_self hp⟩
```

第1成分が `hp`、第2成分が先ほどの主定理です。

---

## prime_rowBirthPrime_self

```lean
theorem prime_rowBirthPrime_self
    {p : ℕ} (hp : p.Prime) :
    RowBirthPrime p p :=
  ⟨prime_innerRowSupportPrime_self hp, dvd_rfl⟩
```

これは、

> 素数 `p` の第 `p` 行では、`p` が行番号 `p` 自身から生まれたサポート素数である

という定理です。

`RowBirthPrime p p` は定義上、

```lean
InnerRowSupportPrime p p ∧ p ∣ p
```

です。

第1成分は、

```lean
prime_innerRowSupportPrime_self hp
```

第2成分は、

```lean
dvd_rfl
```

です。

`dvd_rfl` は任意の数について、

```lean
p ∣ p
```

を示す反射律です。

---

## rowBirthPrime_innerRowSupportPrime

```lean
theorem rowBirthPrime_innerRowSupportPrime
    {d p : ℕ} (h : RowBirthPrime d p) :
    InnerRowSupportPrime d p :=
  h.1
```

`RowBirthPrime d p` から、内側係数のサポート素数性を取り出します。

定義上、

```lean
RowBirthPrime d p
```

は

```lean
InnerRowSupportPrime d p ∧ p ∣ d
```

なので、`h.1` です。

---

## rowBirthPrime_prime

```lean
theorem rowBirthPrime_prime
    {d p : ℕ} (h : RowBirthPrime d p) :
    p.Prime :=
  h.1.1
```

これは `RowBirthPrime d p` から `p.Prime` を取り出します。

構造はこうです。

```lean
h : RowBirthPrime d p
```

つまり、

```lean
h : InnerRowSupportPrime d p ∧ p ∣ d
```

なので、

```lean
h.1 : InnerRowSupportPrime d p
```

さらに、

```lean
h.1 : p.Prime ∧ AllInnerChooseDivisible d p
```

なので、

```lean
h.1.1 : p.Prime
```

です。

---

## rowBirthPrime_dvd_row

```lean
theorem rowBirthPrime_dvd_row
    {d p : ℕ} (h : RowBirthPrime d p) :
    p ∣ d :=
  h.2
```

これは `RowBirthPrime d p` の第2成分、

```lean
p ∣ d
```

を取り出します。

---

## rowBirthPrime_dvd_choose

```lean
theorem rowBirthPrime_dvd_choose
    {d p k : ℕ}
    (h : RowBirthPrime d p) (hk0 : 0 < k) (hkd : k < d) :
    p ∣ Nat.choose d k :=
  innerRowSupportPrime_dvd_choose h.1 hk0 hkd
```

これは `RowBirthPrime d p` から、具体的な二項係数が `p` で割り切れることを取り出す定理です。

`h : RowBirthPrime d p` から、

```lean
h.1 : InnerRowSupportPrime d p
```

が得られます。

それを

```lean
innerRowSupportPrime_dvd_choose
```

に渡して、

```lean
p ∣ Nat.choose d k
```

を得ています。

---

## 全体の設計意図

このファイルは、単に一つの定理を証明しているだけではなく、あとで使いやすいように性質を段階化しています。

```lean
AllInnerChooseDivisible d m
```

は、内側の二項係数がすべて `m` で割れるという一般的な性質。

```lean
InnerRowSupportPrime d p
```

は、それを素数 `p` に限定した性質。

```lean
RowBirthPrime d p
```

は、さらに `p ∣ d`、つまりその素数が行番号にも含まれるという性質。

関係はこうです。

```lean
RowBirthPrime d p
  → InnerRowSupportPrime d p
  → AllInnerChooseDivisible d p
  → p ∣ Nat.choose d k
```

ただし最後は `0 < k` と `k < d` が必要です。

---

## このファイルで一番大事な使い方

素数 `p` と内側の `k` があるとき、

```lean
example {p k : ℕ} (hp : p.Prime) (hk0 : 0 < k) (hkp : k < p) :
    p ∣ Nat.choose p k := by
  exact prime_dvd_inner_choose hp hk0 hkp
```

または、行全体の性質として使うなら、

```lean
example {p : ℕ} (hp : p.Prime) :
    AllInnerChooseDivisible p p := by
  exact prime_allInnerChooseDivisible_self hp
```

です。

---

## 初心者向けポイント

`h.1` や `h.2` は、`∧` の左側・右側を取り出す記法です。

たとえば、

```lean
h : A ∧ B
```

なら、

```lean
h.1 : A
h.2 : B
```

です。

さらに、

```lean
h : (A ∧ B) ∧ C
```

なら、

```lean
h.1 : A ∧ B
h.1.1 : A
h.1.2 : B
h.2 : C
```

になります。

このファイルではその形がよく出ています。

---

## まとめ

このファイルは、

```lean
p.Prime → ∀ k, 0 < k → k < p → p ∣ Nat.choose p k
```

という標準事実を、次の3段階の概念に分けて保存しています。

```lean
AllInnerChooseDivisible
InnerRowSupportPrime
RowBirthPrime
```

特に今後のファイルでは、

```lean
prime_dvd_inner_choose
rowBirthPrime_dvd_choose
```

あたりが使いやすい API になります。
