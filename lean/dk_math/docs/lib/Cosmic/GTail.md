# DkMath.Lib.Cosmic.GTail

[GTail.lean](/lean/dk_math/DkMath/Lib/Cosmic/GTail.lean)

## GTail 純代数コアの数学的解説

## 1. 目的

`GTail` は、二項展開

$$
(x+u)^d
$$

のうち、先頭から $r$ 層を取り除いた残りの部分を、境界因子 $x^r$ で正規化した核である。

通常の二項展開は

$$
(x+u)^d = \sum_{j=0}^{d}
\binom{d}{j}x^j u^{d-j}
$$

である。

ここから先頭 $r$ 項、

$$
\sum_{j=0}^{r-1}
\binom{d}{j}x^j u^{d-j}
$$

を分離すると、残りは必ず $x^r$ を因子に持つ。
この残りを

$$
x^r \cdot \mathrm{GTail}(d,r,x,u)
$$

と書くための正規化核が `GTail` である。

---

## 2. 定義

Lean では、`GTail` は次の形で定義される。

```lean id="seuhuw"
@[simp] def GTail {R : Type _} [CommSemiring R] (d r : ℕ) (x u : R) : R :=
  ∑ k ∈ Finset.range (d + 1 - r),
    (Nat.choose d (r + k) : R) * x ^ k * u ^ (d - (r + k))
```

数学的には、

$$
\mathrm{GTail}(d,r,x,u) = \sum_{k=0}^{d-r}
\binom{d}{r+k}
x^k u^{d-r-k}
$$

である。

ここで $j=r+k$ と置くと、これは二項展開の $j=r$ 以降の項を、共通因子 $x^r$ で割った形になっている。

実際、

$$
\sum_{j=r}^{d}
\binom{d}{j}x^j u^{d-j} = x^r
\sum_{k=0}^{d-r}
\binom{d}{r+k}x^k u^{d-r-k}
$$

なので、

$$
\sum_{j=r}^{d}
\binom{d}{j}x^j u^{d-j} = x^r \mathrm{GTail}(d,r,x,u)
$$

となる。

---

## 3. 中心定理：Tail 分解

今回の純代数コアの中心は次の定理である。

```lean id="jzyxqf"
add_pow_eq_prefix_add_xpow_mul_GTail
```

数学的には、

$$
(x+u)^d = \sum_{j=0}^{r-1}
\binom{d}{j}x^j u^{d-j}
+
x^r \mathrm{GTail}(d,r,x,u)
$$

である。

これは、二項展開を

$$
\text{prefix}+\text{tail}
$$

に分解し、tail 側をさらに

$$
x^r \cdot \text{normalized kernel}
$$

として因数分解したものじゃ。

DkMath 的に言えば、

- prefix はすでに露出している低次層
- $x^r$ は境界因子
- `GTail` は境界因子を除いた内部核
- $r$ はどこまで境界層を剥がしたかを表す階数

となる。

---

## 4. 差分形：高次 Tail 恒等式

次の定理は、上の分解を差分として読んだ形である。

```lean id="qxp9dj"
higher_tail_eq_pow_mul_GTail
```

数学的には、

$$
(x+u)^d - \sum_{j=0}^{r-1}
\binom{d}{j}x^j u^{d-j} = x^r \mathrm{GTail}(d,r,x,u)
$$

である。

こちらの形は、宇宙式的にはより重要じゃ。
なぜなら、左辺が「先頭 $r$ 層を除いた高次差分」であり、右辺が「境界冪 $x^r$ と内部核 `GTail` の積」だからである。

つまりこの定理は、

$$
\text{高次差分} = \text{境界因子}
\times
\text{内部核}
$$

という構造を保証している。

この形が、将来の

- 可除性
- p-adic valuation
- primitive prime
- FLT / ABC bridge

へ接続する根になる。

今回の切り出しでは、p-adic そのものはまだ Lib に入れていないが、p-adic 解析が使う **代数的な土台** はここに固定された、ということじゃ。

---

## 5. 特殊値 $r=0$

```lean id="rz2rit"
GTail_zero_eq_add_pow
```

数学的には、

$$
\mathrm{GTail}(d,0,x,u)=(x+u)^d
$$

である。

これは、何も prefix を取り除かない場合、Tail 全体が元の二項冪そのものになることを表す。

一般 Tail の視点では、

$$
r=0
$$

は「未分解の全体」である。

---

## 6. 特殊値 $r=d$

```lean id="1z42vz"
GTail_self_eq_one
```

数学的には、

$$
\mathrm{GTail}(d,d,x,u)=1
$$

である。

二項展開の最後の項は

$$
\binom{d}{d}x^d u^0=x^d
$$

であり、これを $x^d$ で割ると $1$ になる。

したがって $r=d$ は、Tail を最後まで剥がした終端状態である。

DkMath 的には、

$$
\mathrm{GTail}(d,d,x,u)=1
$$

は「境界因子だけが残り、内部核が単位に落ちる」ことを意味する。

---

## 7. 再帰構造

```lean id="8rxnjc"
GTail_rec
```

数学的には、

$$
\mathrm{GTail}(d,r,x,u) = \binom{d}{r}u^{d-r}
+
x\cdot \mathrm{GTail}(d,r+1,x,u)
\qquad (r<d)
$$

である。

これは Tail をさらに一層剥がす再帰式である。

`\mathrm{GTail}(d,r,x,u)` の最初の項は

$$
\binom{d}{r}u^{d-r}
$$

であり、残りはさらに $x$ を一つ因子として持つ。
その残りの正規化核が

$$
\mathrm{GTail}(d,r+1,x,u)
$$

である。

したがって、この再帰式は

$$
\text{現在の Tail} = \text{先頭係数層}
+
x \cdot \text{次の Tail}
$$

という層構造を表す。

これは DkMath の Beam 解釈では非常に重要で、Tail が一枚岩ではなく、

$$
r,\ r+1,\ r+2,\ldots,d
$$

の階層に分解できることを示している。

---

## 8. $r=1$ 特化：GN への接続

今回のファイルには、$r=1$ 特化として次の定理も残されている。

```lean id="et2fbb"
GN_tail_rec
GN_tail_decomposition
Gbinom_tail_rec
GTail_one_eq_sum
GN_zero_eval
Gbinom_zero_eval
```

ここで重要なのは、

$$
\mathrm{GN}_d(x,u)=\mathrm{GTail}(d,1,x,u)
$$

という構造である。

つまり、従来の `GN` は独立した特殊対象ではなく、一般 Tail の一階層、

$$
r=1
$$

である。

`GTail_one_eq_sum` は、

$$
\mathrm{GTail}(d,1,x,u) = \sum_{k=0}^{d-1}
\binom{d}{k+1}x^k u^{d-1-k}
$$

を与える。

これは従来の GN の標準形であり、

$$
(x+u)^d-u^d=x\cdot \mathrm{GN}_d(x,u)
$$

の右側に出る核そのものじゃ。

---

## 9. $x=0$ 評価

```lean id="7zpmy4"
GTail_eval_zero
```

数学的には、

$$
\mathrm{GTail}(d,r,0,u) = \binom{d}{r}u^{d-r}
$$

である。

これは Tail の先頭項だけが残ることを表す。

なぜなら、`GTail` は

$$
\sum_{k=0}^{d-r}
\binom{d}{r+k}x^k u^{d-r-k}
$$

であり、$x=0$ とすると $k>0$ の項は消え、$k=0$ の項だけが残るからである。

これは後で p-adic や合同式を見るときに重要になる。

たとえば、ある素数 $p$ が $x$ を割るとき、`GTail` は合同式上で先頭項

$$
\binom{d}{r}u^{d-r}
$$

に落ちる。
今回の Lib コアでは合同式までは入れていないが、その出発点になる評価定理がここに置かれた。

---

## 10. 今回 padic と切り離した意味

今回のリファクタリングの数学的意味は大きい。

以前の `CosmicFormula.GTail` では、

- Tail の純代数定義
- 二項展開の分解
- Nat 上の整除性
- 合同式
- p-adic valuation

が同じファイルに同居していた。

しかし、数学的にはこれらは階層が違う。

まず基礎にあるのは、任意の可換半環 $R$ 上で成り立つ純代数恒等式である。

$$
(x+u)^d = \sum_{j < r} \binom{d}{j}x^j u^{d-j} + x^r \mathrm{GTail}(d,r,x,u)
$$

この段階では、自然数も整数も複素数も区別しない。
必要なのは加法・乗法・冪・有限和だけである。

その上に、自然数特有の整除性が乗る。

$$
x^r \mid \left((x+u)^d-\sum_{j < r}\binom{d}{j}x^j u^{d-j}\right)
$$

さらにその上に、合同式や p-adic valuation が乗る。

$$
v_p(\text{Tail}) = \cdots
$$

今回の切り出しは、この階層を正しく分けた。

```text id="gzbjjr"
Lib.Cosmic.GTail
  純代数恒等式

CosmicFormula.GTail
  Nat / congruence / p-adic / FLT 向け補題
```

これは、DkMath.Lib に入れるべき定理の性格として非常に正しい。

---

## 11. 今回固定された数学的核

今回 `DkMath.Lib.Cosmic.GTail` に固定された核は、次の一文で表せる。

> 二項冪 $(x+u)^d$ は、任意の階数 $r$ で prefix と境界冪付き Tail に分解でき、その正規化 Tail は `\mathrm{GTail}(d,r,x,u)` として可換半環上で定義できる。

式では、

$$
(x+u)^d = \sum_{j=0}^{r-1}
\binom{d}{j}x^j u^{d-j}
+
x^r \mathrm{GTail}(d,r,x,u)
$$

である。

そして差分形では、

$$
(x+u)^d - \sum_{j=0}^{r-1}
\binom{d}{j}x^j u^{d-j} = x^r \mathrm{GTail}(d,r,x,u)
$$

となる。

これが今後の DkMath における

$$
\text{
    GTail → GN → GZ → GC
}
$$

の根じゃ。

---

## 12. 解説書向けまとめ文

## GTail: 一般 Tail 核

`GTail d r x u` は、二項展開 `(x+u)^d` から先頭 `r` 層を取り除いた残りを、境界因子 `x^r` で割った正規化核である。

数学的には、

$$
\mathrm{GTail}(d,r,x,u) = \sum_{k=0}^{d-r}
\binom{d}{r+k}x^k u^{d-r-k}
$$

であり、中心恒等式は

$$
(x+u)^d = \sum_{j=0}^{r-1}
\binom{d}{j}x^j u^{d-j} + x^r \mathrm{GTail}(d,r,x,u)
$$

である。

差分形では、

$$
(x+u)^d - \sum_{j=0}^{r-1}
\binom{d}{j}x^j u^{d-j} = x^r \mathrm{GTail}(d,r,x,u)
$$

となる。

特に `r = 1` の場合、

$$
\mathrm{GTail}(d,1,x,u) = \sum_{k=0}^{d-1}
\binom{d}{k+1}x^k u^{d-1-k}
$$

であり、これは DkMath の標準 GN 核である。

$$
\mathrm{GN}_d(x,u)=\mathrm{GTail}(d,1,x,u)
$$

したがって、

$$
(x+u)^d-u^d=x\cdot \mathrm{GN}_d(x,u)
$$

が得られる。
