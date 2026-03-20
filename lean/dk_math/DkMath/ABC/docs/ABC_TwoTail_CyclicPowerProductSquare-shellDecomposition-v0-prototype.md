# 巡回指数積と `twoTail` の閉構造

## 1. 目的

本メモの目的は、`twoTail` の説明例として現れた

\[
2^3 \cdot 3^5 \cdot 5^2
\]

が、実は一般形

\[
M(a,b,c) := a^b \, b^c \, c^a
\]

という「巡回指数積」の具体例になっていることを明示し、
この族が `twoTail` に対して自然な閉構造を持つことを整理することである。

特に、`twoTail` は「平方殻を 2 枚はがす作用」として働き、
相異なる素数を底に持つ巡回指数積に対して、

\[
a^b b^c c^a \mapsto a^{b-2} b^{c-2} c^{a-2}
\]

という形で、底を保ったまま指数だけを一様に減少させる。

---

## 2. 基本定義

### 2.1. `twoTail`

自然数 \(n\) に対し、`twoTail n` は各素数指数 \(v_p(n)\) のうち

\[
v_p(n) - 2
\]

の部分だけを集めたものとみなす。

Lean の定義は次である。

```lean
/-- The "two-tail" of a natural number: `∏_{p|c} p^{max(v_p(c)-2, 0)}`. -/
def twoTail (c : ℕ) : ℕ :=
  c.factorization.support.prod (fun p => p ^ (c.factorization p - 2))
```

ここで自然数の減算は切り捨て減算なので、指数 \(<2\) の場合は \(0\) になる。

---

### 2.2. 巡回指数積

相異なる自然数 \(a,b,c\) に対して、巡回指数積を

\[
M(a,b,c) := a^b \, b^c \, c^a
\]

と定義する。

これは「底」と「指数」が輪状に接続した指数積であり、

- \(a \to b\)
- \(b \to c\)
- \(c \to a\)

という循環構造を持つ。

---

## 3. 具体例の再解釈

`twoTail` の説明例

\[
2^3 \cdot 3^5 \cdot 5^2
\]

は、ちょうど

\[
a=2,\qquad b=3,\qquad c=5
\]

を代入した

\[
M(2,3,5)=2^3 \cdot 3^5 \cdot 5^2
\]

そのものである。

このとき素数指数は

\[
v_2(M)=3,\qquad v_3(M)=5,\qquad v_5(M)=2
\]

であるから、

\[
\operatorname{twoTail}(M)=2^{3-2}3^{5-2}5^{2-2}=2^1 3^3 5^0=54
\]

となる。

また、

\[
\operatorname{rad}(M)=2\cdot3\cdot5=30
\]

であり、各指数がすべて \(2\) 以上なので

\[
\pi\mathrm{SqRad}(M)=2\cdot3\cdot5=30
\]

も成り立つ。よって

\[
M=\pi\mathrm{SqRad}(M)\,\operatorname{rad}(M)\,\operatorname{twoTail}(M)
\]

は

\[
2^3 3^5 5^2 = 30 \cdot 30 \cdot 54
\]

となり、検算が一致する。

---

## 4. 巡回指数積に対する `twoTail` の閉構造

## 4.1. 素数版の基本観察

以後、\(a,b,c\) を相異なる素数とする。

このとき

\[
M(a,b,c)=a^b b^c c^a
\]

に対して、各素数の付値はただちに

\[
v_a(M)=b,\qquad v_b(M)=c,\qquad v_c(M)=a
\]

である。

したがって

\[
\operatorname{rad}(M)=abc
\]

であり、さらに \(a,b,c \ge 2\) より各指数は 2 以上なので

\[
\pi\mathrm{SqRad}(M)=abc
\]

も成り立つ。

---

## 4.2. `twoTail` の像

同じ仮定の下で、

\[
\operatorname{twoTail}(M) =
a^{b-2} b^{c-2} c^{a-2}
\]

が成り立つ。

これは各素数について指数を 2 だけ減らす、という `twoTail` の定義そのものから従う。

特に、

\[
M=(abc)(abc)\,a^{b-2}b^{c-2}c^{a-2}
\]

すなわち

\[
M=(abc)^2 \operatorname{twoTail}(M)
\]

を得る。

---

## 4.3. 閉構造としての意味

重要なのは、`twoTail` を 1 回作用させた後も

\[
a^{b-2} b^{c-2} c^{a-2}
\]

という形で、底 \(a,b,c\) がそのまま保たれることである。

つまり、固定底の族

\[
\mathcal{F}_{a,b,c}
:=
\left\{
a^x b^y c^z \;\middle|\; x,y,z \in \mathbb{N}
\right\}
\]

は `twoTail` によって保たれる。

巡回指数積 \(M(a,b,c)\) はこの族の特別な点

\[
(x,y,z)=(b,c,a)
\]

であり、`twoTail` はこの指数ベクトルに対し

\[
(b,c,a)\mapsto (b-2,c-2,a-2)
\]

として働く。

よって `twoTail` は、巡回指数積を「固定底・指数平行移動」型の閉構造の中で扱う作用になっている。

---

## 5. 反復 `twoTail`

`twoTail` を \(k\) 回繰り返し適用すると、各回で指数が 2 ずつ減るので、

\[
\operatorname{twoTail}^{\,k}(M(a,b,c)) =
a^{b-2k} b^{c-2k} c^{a-2k}
\]

が期待される。
ただしこれは

\[
2k \le \min(a,b,c)
\]

の範囲で自然に成り立つ形である。

そのとき

\[
M(a,b,c)=(abc)^{2k}\operatorname{twoTail}^{\,k}(M(a,b,c))
\]

と書ける。

これは、巡回指数積が

- 外殻としての平方部分
- 残差としての tail 部分

に分かれ、それを 2 層ずつはがしていけることを示している。

---

## 6. 定理としての記述案

## 6.1. 定理 A. 巡回指数積の `twoTail` 分解

相異なる素数 \(a,b,c\) に対し

\[
M(a,b,c):=a^b b^c c^a
\]

とおく。
このとき

\[
\operatorname{rad}(M)=abc,
\qquad
\pi\mathrm{SqRad}(M)=abc,
\qquad
\operatorname{twoTail}(M)=a^{b-2} b^{c-2} c^{a-2}.
\]

特に

\[
M=(abc)^2 \operatorname{twoTail}(M)
\]

が成り立つ。

---

## 6.2. 定理 B. 反復 `twoTail` 閉包

同じ仮定のもと、整数 \(k \ge 0\) が

\[
2k \le \min(a,b,c)
\]

を満たすなら

\[
\operatorname{twoTail}^{\,k}(M)=a^{b-2k} b^{c-2k} c^{a-2k}
\]

かつ

\[
M=(abc)^{2k}\operatorname{twoTail}^{\,k}(M)
\]

が成り立つ。

---

## 7. 注意点

この綺麗な形は、\(a,b,c\) を相異なる素数としたからこそ直接に書ける。

もし \(a,b,c\) を一般自然数まで広げると、

- \(a,b,c\) 自身が複合数になりうる
- 同じ素数が複数の項にまたがって現れる
- 付値 \(v_p\) の寄与が合流する

ため、

\[
v_a(M)=b
\]

のような単純表示は一般には崩れる。

したがって、まずは「相異なる素数版」として定理化し、その後必要なら一般自然数版へ拡張するのが実装上も数学上も自然である。

---

## 8. Lean 実装設計

## 8.1. 定義

```lean
/-- Cyclic power product on three natural numbers. -/
def cyclicPowProd (a b c : ℕ) : ℕ :=
  a^b * b^c * c^a
```

---

## 8.2. 実装したい補題群

```lean
/--
For distinct primes `a,b,c`, the radical of `a^b * b^c * c^a` is `a * b * c`.
-/
lemma rad_cyclicPowProd_of_distinct_primes
    {a b c : ℕ}
    (ha : Nat.Prime a) (hb : Nat.Prime b) (hc : Nat.Prime c)
    (hab : a ≠ b) (hbc : b ≠ c) (hca : c ≠ a) :
    Nat.rad (cyclicPowProd a b c) = a * b * c := by
  sorry

/--
For distinct primes `a,b,c`, the square-radical part is also `a * b * c`.
-/
lemma piSqRad_cyclicPowProd_of_distinct_primes
    {a b c : ℕ}
    (ha : Nat.Prime a) (hb : Nat.Prime b) (hc : Nat.Prime c)
    (hab : a ≠ b) (hbc : b ≠ c) (hca : c ≠ a)
    (ha2 : 2 ≤ a) (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) :
    piSqRad (cyclicPowProd a b c) = a * b * c := by
  sorry

/--
For distinct primes `a,b,c`, `twoTail` subtracts `2` from each cyclic exponent.
-/
lemma twoTail_cyclicPowProd_of_distinct_primes
    {a b c : ℕ}
    (ha : Nat.Prime a) (hb : Nat.Prime b) (hc : Nat.Prime c)
    (hab : a ≠ b) (hbc : b ≠ c) (hca : c ≠ a)
    (ha2 : 2 ≤ a) (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) :
    twoTail (cyclicPowProd a b c) = a^(b-2) * b^(c-2) * c^(a-2) := by
  sorry

/--
Square-shell decomposition of the cyclic power product.
-/
lemma cyclicPowProd_eq_sq_shell_mul_twoTail
    {a b c : ℕ}
    (ha : Nat.Prime a) (hb : Nat.Prime b) (hc : Nat.Prime c)
    (hab : a ≠ b) (hbc : b ≠ c) (hca : c ≠ a)
    (ha2 : 2 ≤ a) (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) :
    cyclicPowProd a b c = (a * b * c)^2 * twoTail (cyclicPowProd a b c) := by
  sorry
```

---

## 8.3. 反復版の設計案

```lean
/--
Iterated twoTail on the cyclic power product subtracts `2*k` from each exponent,
as long as those exponents remain nonnegative.
-/
lemma iter_twoTail_cyclicPowProd_of_distinct_primes
    {a b c k : ℕ}
    (ha : Nat.Prime a) (hb : Nat.Prime b) (hc : Nat.Prime c)
    (hab : a ≠ b) (hbc : b ≠ c) (hca : c ≠ a)
    (hk : 2 * k ≤ a)
    (hk' : 2 * k ≤ b)
    (hk'' : 2 * k ≤ c) :
    (Nat.iterate twoTail k (cyclicPowProd a b c))
      = a^(b - 2*k) * b^(c - 2*k) * c^(a - 2*k) := by
  sorry
```

実際には `Nat.iterate` をそのまま使うか、専用の反復作用を定義するかは要検討である。

---

## 9. 実装順序の提案

Lean 実装は次の順で進めるのが安全である。

1. `cyclicPowProd` の定義
2. `factorization` 上での各素数付値の計算
3. `rad` の計算
4. `piSqRad` の計算
5. `twoTail` の計算
6. 分解恒等式
   \[
   M=(abc)^2\operatorname{twoTail}(M)
   \]

7. 必要なら反復版へ進む

---

## 10. まとめ

`twoTail` の説明例

\[
2^3\cdot3^5\cdot5^2
\]

は、単なる一例ではなく、巡回指数積

\[
M(a,b,c)=a^b b^c c^a
\]

の具体例として理解できる。

この族は、相異なる素数を底に持つ場合、

\[
\operatorname{twoTail}(M)=a^{b-2}b^{c-2}c^{a-2}
\]

を満たし、`twoTail` に対して底を保つ閉構造を持つ。
したがって `twoTail` は、巡回指数積に対する「平方殻剥離作用」として自然に解釈できる。

この観点は、

- `twoTail` の概念説明
- 巡回指数構造の一般化
- Lean 上での補題群整理

の三者を橋渡しする、よい基礎設計になる。
