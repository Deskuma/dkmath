# twoTail と巡回指数積の閉構造

## 1. 概要

本メモは、`twoTail` が

\[
\text{「平方殻を 2 枚はがし、その先の余剰指数だけを取り出す作用」}
\]

として振る舞うことを、巡回指数積

\[
M(a,b,c) := a^b\, b^c\, c^a
\]

に対して明示するための設計メモである。

特に、\(a,b,c\) を **相異なる素数** とすると、`twoTail` はこの積に対して

- 底 \(a,b,c\) を保ち
- 指数を一様に 2 ずつ減らす

という形で作用する。  
この意味で、巡回指数積は `twoTail` のもとで **固定底・指数平行移動型の閉構造** を持つ。

---

## 2. 背景

`twoTail` は自然数 \(c\) に対し、各素数 \(p\) の指数 \(v_p(c)\) から 2 を引いた余剰

\[
\max(v_p(c)-2,\,0)
\]

を集める関数である。Lean では次で定義されている。

```lean
/-- The "two-tail" of a natural number: `∏_{p|c} p^{max(v_p(c)-2, 0)}`.
    This extracts only the "excess beyond square" part from the factorization. -/
def twoTail (c : ℕ) : ℕ :=
  c.factorization.support.prod (fun p => p ^ (c.factorization p - 2))
```

このとき各素数指数は

\[
v_p(c) =
1_{\{v_p(c)\ge 2\}}
+
1_{\{v_p(c)\ge 1\}}
+
\bigl(v_p(c)-2\bigr)
\]

と分割できるので、

\[
c = \pi\mathrm{SqRad}(c)\,\operatorname{rad}(c)\,\operatorname{twoTail}(c)
\]

という分解が得られる。

---

## 3. 巡回指数積

ここで次を定義する。

\[
M(a,b,c) := a^b\, b^c\, c^a
\]

これは指数が

\[
a \to b,\qquad b \to c,\qquad c \to a
\]

と巡回している積である。  
Lean の説明例

\[
2^3 \cdot 3^5 \cdot 5^2
\]

はちょうど

\[
M(2,3,5)=2^3\,3^5\,5^2
\]

になっている。

つまりこの例は、単なる素因数分解の例ではなく、巡回指数積の具体例として読むことができる。

---

## 4. 基本観察

\(a,b,c\) を相異なる素数とする。  
このとき \(M(a,b,c)\) の各素数指数はそのまま読み取れて

\[
v_a(M)=b,\qquad
v_b(M)=c,\qquad
v_c(M)=a
\]

となる。

特に \(a,b,c \ge 2\) なので、各素数は少なくとも 2 回ずつ現れる。したがって

\[
\operatorname{rad}(M)=abc,
\qquad
\pi\mathrm{SqRad}(M)=abc
\]

であり、さらに `twoTail` は指数から 2 を引くので

\[
\operatorname{twoTail}(M) =
a^{b-2} b^{c-2} c^{a-2}.
\]

ゆえに

\[
M(a,b,c) =
(abc)\,(abc)\,a^{b-2} b^{c-2} c^{a-2}
\]

すなわち

\[
M(a,b,c) =
(abc)^2\, \operatorname{twoTail}(M(a,b,c)).
\]

これは、巡回指数積が **平方殻 \((abc)^2\)** と、その先の tail に分解されることを意味する。

---

## 5. 閉構造の意味

ここで重要なのは、`twoTail` を 1 回適用した後も

\[
a^{b-2} b^{c-2} c^{a-2}
\]

という形になっており、**底 \(a,b,c\) は不変** だという点である。  
変わるのは指数だけで、しかも

\[
(b,c,a) \mapsto (b-2,\ c-2,\ a-2)
\]

という **一様平行移動** になっている。

したがって、固定された底 \(a,b,c\) に対する積の族

\[
\mathcal{F}_{a,b,c}
:=
\left\{
a^x b^y c^z \mid x,y,z \in \mathbb{N}
\right\}
\]

は `twoTail` に関して閉じている。  
そして巡回指数積 \(M(a,b,c)\) はその族の中の特別な点

\[
(x,y,z)=(b,c,a)
\]

として理解できる。

この意味で、巡回指数積は `twoTail` のもとで

\[
\text{固定底・指数層剥離型の閉構造}
\]

を持つ。

---

## 6. 反復適用

`twoTail` を \(k\) 回繰り返し適用すると、毎回指数が 2 ずつ減る。よって

\[
\operatorname{twoTail}^{\,k}(M(a,b,c)) =
a^{b-2k} b^{c-2k} c^{a-2k}
\]

が期待される。  
ただしこれは当然、

\[
b-2k \ge 0,\qquad c-2k \ge 0,\qquad a-2k \ge 0
\]

すなわち

\[
2k \le \min(a,b,c)
\]

の範囲で成り立つ。

このとき

\[
M(a,b,c) =
(abc)^{2k}\,\operatorname{twoTail}^{\,k}(M(a,b,c))
\]

となり、巡回指数積は **平方殻を 2 層ずつ剥いでいく塔構造** を持つ。

---

## 7. 定理の形

### 定理 A. 巡回指数積の `twoTail` 分解

\(a,b,c\) を相異なる素数とする。  
このとき

\[
M(a,b,c):=a^b b^c c^a
\]

に対して

\[
\operatorname{rad}(M)=abc,
\qquad
\pi\mathrm{SqRad}(M)=abc,
\qquad
\operatorname{twoTail}(M)=a^{b-2} b^{c-2} c^{a-2}
\]

が成り立つ。特に

\[
M=(abc)^2\,\operatorname{twoTail}(M)
\]

である。

### 定理 B. 反復 `twoTail` 閉包

上と同じ仮定のもと、\(k \ge 0\) かつ

\[
2k \le \min(a,b,c)
\]

ならば

\[
\operatorname{twoTail}^{\,k}(M)=a^{b-2k} b^{c-2k} c^{a-2k}
\]

かつ

\[
M=(abc)^{2k}\,\operatorname{twoTail}^{\,k}(M)
\]

が成り立つ。

---

## 8. 証明の見取り図

### 8.1. `rad` と `piSqRad`

\(a,b,c\) は相異なる素数なので、\(M=a^b b^c c^a\) の support はちょうど

\[
\{a,b,c\}
\]

である。  
したがって `rad` は

\[
\operatorname{rad}(M)=abc
\]

となる。

また \(a,b,c\) 自身が素数ゆえ \(a,b,c \ge 2\) であり、指数 \(b,c,a\) はすべて 2 以上である。ゆえに `piSqRad` も support 全体を取り

\[
\pi\mathrm{SqRad}(M)=abc
\]

となる。

### 8.2. `twoTail`

各素数について指数から 2 を引くと

\[
v_a(M)-2=b-2,\qquad
v_b(M)-2=c-2,\qquad
v_c(M)-2=a-2
\]

なので、

\[
\operatorname{twoTail}(M)=a^{b-2} b^{c-2} c^{a-2}
\]

が従う。

### 8.3. 分解恒等式

`c = piSqRad(c) * rad(c) * twoTail(c)` を \(c=M\) に適用すると

\[
M=(abc)(abc)\operatorname{twoTail}(M)=(abc)^2\operatorname{twoTail}(M)
\]

となる。

---

## 9. 例

\[
(a,b,c)=(2,3,5)
\]

とすると

\[
M(2,3,5)=2^3 3^5 5^2
\]

であり、

\[
\operatorname{rad}(M)=2\cdot3\cdot5=30,
\qquad
\pi\mathrm{SqRad}(M)=30
\]

さらに

\[
\operatorname{twoTail}(M)=2^{3-2}3^{5-2}5^{2-2}=2^1 3^3 5^0=54.
\]

よって

\[
2^3 3^5 5^2 = 30 \cdot 30 \cdot 54
\]

が成り立つ。

これは `twoTail` の説明例であると同時に、巡回指数積の最初の具体例にもなっている。

---

## 10. 一般自然数版との違い

この議論がきれいに通るのは、\(a,b,c\) を **相異なる素数** に制限しているからである。  
もし \(a,b,c\) を一般自然数に広げると、

- \(a,b,c\) の素因数 support が重なる
- \(a^b\), \(b^c\), \(c^a\) の素因数寄与が同じ素数に合流する
- \(v_p(M)\) が単純な \(b,c,a\) では書けなくなる

という問題が生じる。

したがって、最初の定理化は **相異なる素数版** として行うのが最も自然である。

---

## 11. Lean 実装方針

まずは定義を置く。

```lean
/-- Cyclic power product on three natural numbers. -/
def cyclicPowProd (a b c : ℕ) : ℕ :=
  a^b * b^c * c^a
```

次に以下の順で補題を積む。

### 11.1. 素因数 support の確定

- `factorization` 上で、相異なる素数 \(a,b,c\) 以外では指数が 0
- \(a,b,c\) ではそれぞれ指数が \(b,c,a\)

### 11.2. `rad` の計算

```lean
lemma rad_cyclicPowProd_of_distinct_primes
    {a b c : ℕ}
    (ha : Nat.Prime a) (hb : Nat.Prime b) (hc : Nat.Prime c)
    (hab : a ≠ b) (hbc : b ≠ c) (hca : c ≠ a) :
    Nat.rad (cyclicPowProd a b c) = a * b * c := by
  sorry
```

### 11.3. `piSqRad` の計算

```lean
lemma piSqRad_cyclicPowProd_of_distinct_primes
    {a b c : ℕ}
    (ha : Nat.Prime a) (hb : Nat.Prime b) (hc : Nat.Prime c)
    (hab : a ≠ b) (hbc : b ≠ c) (hca : c ≠ a) :
    piSqRad (cyclicPowProd a b c) = a * b * c := by
  sorry
```

### 11.4. `twoTail` の計算

```lean
lemma twoTail_cyclicPowProd_of_distinct_primes
    {a b c : ℕ}
    (ha : Nat.Prime a) (hb : Nat.Prime b) (hc : Nat.Prime c)
    (hab : a ≠ b) (hbc : b ≠ c) (hca : c ≠ a) :
    twoTail (cyclicPowProd a b c) = a^(b-2) * b^(c-2) * c^(a-2) := by
  sorry
```

### 11.5. 分解恒等式

```lean
lemma cyclicPowProd_eq_sq_shell_mul_twoTail
    {a b c : ℕ}
    (ha : Nat.Prime a) (hb : Nat.Prime b) (hc : Nat.Prime c)
    (hab : a ≠ b) (hbc : b ≠ c) (hca : c ≠ a) :
    cyclicPowProd a b c = (a * b * c)^2 * twoTail (cyclicPowProd a b c) := by
  sorry
```

---

## 12. 反復版の見通し

将来的には `Nat.iterate` を用いて

```lean
lemma twoTail_iterate_cyclicPowProd
    {a b c k : ℕ}
    ...
```

のような形で

\[
\operatorname{twoTail}^{\,k}(M)=a^{b-2k} b^{c-2k} c^{a-2k}
\]

を定理化できる。  
ただし、自然数の指数減少では

\[
b-2k,\quad c-2k,\quad a-2k
\]

の非負条件処理が要るので、最初の段階では 1 回版を確立し、その後に反復版へ進むのが安全である。

---

## 13. 命名案

この構造には次のような名前が考えられる。

- **巡回指数積の平方殻閉包**
- **twoTail による指数層剥離閉構造**
- **cyclic power product square-shell decomposition**
- **cyclic exponent tail closure**

Lean の lemma 名としては、簡潔さを優先して `cyclicPowProd` 系で揃えるのがよい。

---

## 14. まとめ

巡回指数積

\[
M(a,b,c)=a^b\,b^c\,c^a
\]

に対して、\(a,b,c\) を相異なる素数とすると

\[
\operatorname{twoTail}(M)=a^{b-2}b^{c-2}c^{a-2}
\]

となり、`twoTail` は底を変えず、指数を一様に 2 だけ減らす。  
したがって

\[
M=(abc)^2\,\operatorname{twoTail}(M)
\]

という平方殻分解が成り立ち、この族は `twoTail` のもとで閉じている。

これは `twoTail` の説明例

\[
2^3 3^5 5^2
\]

に、単なる検算を超えた **巡回指数構造としての意味付け** を与えるものである。
