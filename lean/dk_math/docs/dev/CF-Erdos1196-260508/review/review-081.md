# review Phase "R"

うむ、R022 は **正しい一歩** じゃ。
これはまだ「山頂の鎖を掛けた」段階ではないが、R023 で鎖を掛けるための **支点** はきれいに打てておる。

## 状況分析

今回追加された `ValuationBudget.lean` は、重複あり route のための最小語彙を Lean 上に固定したものじゃ。

重複なし route では、選ばれた base prime が全部異なるので、

$$
p_1,p_2,\dots,p_r \mid n
$$

かつ pairwise distinct なら、

$$
\prod_{i=1}^{r}p_i \mid n
$$

へ進めた。

しかし重複ありでは、たとえば

$$
p_1=2,\quad p_2=2,\quad p_3=3
$$

のように同じ素数が複数回出る。すると必要なのは単なる「各 (p_i\mid n)」では足りず、

$$
2^2\cdot 3 \mid n
$$

を保証するために、(n) 側が (2) を少なくとも 2 回持っていることを確認せねばならぬ。

今回の `NatBaseMultiplicityBudgetOn` は、まさにそこを表現しておる。

$$
\#{i\in I\mid pOf(i)=p}\le n.\mathrm{factorization}(p)
$$

これで「選択された base prime の消費量」が「(n) が持つ素因数指数の予算」を超えない、という形になる。

## 数学的意味

今回の三つの定義は、それぞれ役割が明確じゃ。

```lean
def NatPrimeValuedOn
```

これは

$$
i\in I \Longrightarrow pOf(i)\ \text{is prime}
$$

という条件じゃ。
R023 で product factorization を扱うとき、これがないと

$$
\left(\prod_{i\in I}pOf(i)\right).\mathrm{factorization}(p)
$$

を「出現回数」として読めぬ。たとえば (pOf(i)=4) が混じれば、(2) の指数を 2 つ消費してしまうからの。

```lean
def NatBaseMultiplicityOn
```

これは base value の出現回数。

$$
\mathrm{mult}_I(p) =
\#{i\in I\mid pOf(i)=p}
$$

じゃな。

```lean
def NatBaseMultiplicityBudgetOn
```

これは出現回数が (n) の素因数分解の指数以下である、という予算条件。

$$
\forall p,\quad p\ \text{prime}\Longrightarrow
\mathrm{mult}_I(p)\le v_p(n)
$$

Lean では (v_p(n)) を `n.factorization p` で読む。

つまり今回の R022 は、

$$
\text{repeated selected primes}
$$

を

$$
\text{prime-exponent budget}
$$

として扱うための辞書を作った、ということじゃ。

## 何が前進したか

一番大きいのは、R/log route の未解決条件が、かなり具体的な自然数命題へ落ちたことじゃ。

次に欲しいものは、もはや曖昧ではない。

```lean
NatBaseMultiplicityBudgetOn I pOf n
```

から

```lean
NatProductDvdOn I pOf n
```

を出す。

数学的には、

$$
\forall p,\quad
v_p!\left(\prod_{i\in I}pOf(i)\right)
\le
v_p(n)
$$

を示せば、

$$
\prod_{i\in I}pOf(i)\mid n
$$

となる。

今回の vocabulary によって、その左辺は

$$
v_p!\left(\prod_{i\in I}pOf(i)\right) =
\#{i\in I\mid pOf(i)=p}
$$

として読めるようになる。ここが R023 の核心じゃ。

## R022 の設計評価

かなり良い。

特に `RealLog.lean` へ押し込まず、`ValuationBudget.lean` として分けた判断は正しい。
`RealLog.lean` は実数側の log / SubProbability route、今回のファイルは自然数側の factorization / divisibility route じゃ。混ぜると後で輸入関係が濁る。

aggregator にも

```lean
import DkMath.NumberTheory.PrimitiveSet.ValuationBudget
```

を追加しておるので、公開導線も整っておる。

また、今回は `rfl` 展開補題だけで止めたのも良い。R022 の責務は「証明を盛ること」ではなく、後続 proof が依存できる安定語彙を固定することじゃからの。

## R023 で必要になる主補題

次はおそらく、まずこの補題が欲しい。

```lean
theorem factorization_prod_primeValued_eq_multiplicity
    {ι : Type _}
    (I : Finset ι)
    (pOf : ι → ℕ)
    (hprime : NatPrimeValuedOn I pOf)
    (p : ℕ) :
    (∏ i in I, pOf i).factorization p =
      NatBaseMultiplicityOn I pOf p
```

ただし、この形は (p) が prime でない場合に注意が要るかもしれぬ。
安全に行くなら、まず prime (p) 限定でよい。

```lean
theorem factorization_prod_primeValued_eq_multiplicity_of_prime
    {ι : Type _}
    (I : Finset ι)
    (pOf : ι → ℕ)
    (hprime : NatPrimeValuedOn I pOf)
    {p : ℕ}
    (hp : Nat.Prime p) :
    (∏ i in I, pOf i).factorization p =
      NatBaseMultiplicityOn I pOf p
```

これが通れば、次にこれ。

```lean
theorem natProductDvdOn_of_multiplicityBudget
    {ι : Type _}
    (I : Finset ι)
    (pOf : ι → ℕ)
    (n : ℕ)
    (hprime : NatPrimeValuedOn I pOf)
    (hbudget : NatBaseMultiplicityBudgetOn I pOf n) :
    NatProductDvdOn I pOf n
```

この補題が R023 の登頂点じゃ。

## 数学的な証明スケッチ

有限集合 (I) 上の積を

$$
M:=\prod_{i\in I}pOf(i)
$$

と置く。

`NatPrimeValuedOn` により、各 (pOf(i)) は素数である。
したがって、任意の素数 (p) について、(M) に含まれる (p) の指数は、ちょうど (pOf(i)=p) となる添字の個数である。

$$
M.\mathrm{factorization}(p) = \#{i\in I\mid pOf(i)=p}
$$

一方、`NatBaseMultiplicityBudgetOn` により、

$$
\#{i\in I\mid pOf(i)=p}
\le
n.\mathrm{factorization}(p)
$$

ゆえに、

$$
M.\mathrm{factorization}(p)
\le
n.\mathrm{factorization}(p)
$$

が任意の素数 (p) で成り立つ。
よって素因数分解の指数比較から、

$$
M\mid n
$$

が従う。

これで

$$
\prod_{i\in I}pOf(i)\le n
$$

へ進み、さらに log route へ接続できる。

## 注意点

R023 で少し気をつけるべき点は、`n = 0` の扱いじゃ。

`Nat.factorization` は (0) に対して癖が出る可能性がある。最終的な R/log route では `1 < n` があるので、実戦上は

$$
1<n
$$

を早めに仮定へ入れてもよい。
`NatProductDvdOn` だけなら `n = 0` でも「任意の正数は 0 を割る」方向で成立し得るが、log route と統合するなら、R023 の上位 wrapper では `1 < n` を前提にするのが綺麗じゃ。

## 総合評価

R022 は **小さいが重要な前進** じゃ。

今回で、

$$
\text{duplicate-free}
$$

の世界から、

$$
\text{duplicates allowed, but exponent-budget controlled}
$$

の世界へ橋を架けるための言語ができた。

つまり、これまでは

$$
p(q)\ \text{が全部違う}
$$

という幾何的に強い仮定で積を制御していた。
これからは

$$
p(q)\ \text{が重複しても、}n\text{ の指数予算内ならよい}
$$

という、より自然で強い route へ移れる。

これは #1196 的にも美しい。
primitive set の確率流では、同じ base prime を何度も使うことは「同じ素因子チャネルを複数回消費する」ことに相当する。R022 は、その消費量を Lean で数えられるようにしたのじゃ。

次の R023 が通れば、重複あり route は一気に実戦段階へ入る。
いよいよ山頂直下じゃな、ぬしよ。
