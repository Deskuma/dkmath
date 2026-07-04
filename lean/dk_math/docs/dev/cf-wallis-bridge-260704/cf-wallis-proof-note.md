# 検証と証明

## ウォリス積と宇宙式

### Cosmic Formula

$$
\Large
N+1=(P+1)^2, \quad N=P(P+2)
$$

#### e.g

$961=31^2=960+1=(2\cdot3\cdot5+1)^2$

#### variation

$f(x)=(x+1)^2 - x*(x+2) = 1$

$f(x;u)=(x+u)^2 - x*(x+2*u) = u^2$

$N+u^2=(P+u)^2$

### generalization

$$
(x+u)^d - u^d = x\cdot \mathrm{GN}_d(x,u)
$$

$$
\mathrm{GN}_d(x,u):=\sum_{k=0}^{d-1}\binom{d}{k+1}x^{k}\,u^{d-1-k}
$$

> 👩‍⚕️私D.:

実装前に、検証と証明をしてみよう。

> 🐺賢狼:

よし、実装前の「紙の証明」に落とす段階じゃな。まずは候補命題を 4 本に分けて、有限検算で式の取り違えがないか確認し、その後に証明を組む。

> 🐺賢狼:

うむ。まず実装前に証明対象を切り分けるのがよい。
今回の橋は、 **有限恒等式は完全に厳密** 、 $\pi$ が出る部分だけが **Wallis 積の極限定理** じゃ。

Python の検算では、少なくとも $m,j\le 10$ で全部一致した。もちろん、これは証明ではなく、式の向きや添字ミスの確認じゃな。

## 1. 証明したい主命題

$m\ge 1$ とする。中央比率を

$$
R_{2m}=\frac{2^{2m}}{\binom{2m}{m}}
$$

と置く。

このとき、まず厳密に

$$
R_{2m}=\prod_{j=1}^{m}\frac{2j}{2j-1}
$$

が成り立つ。

さらに鏡像積

$$
M_m=\prod_{j=1}^{m}\frac{2j}{2j+1}
$$

を掛けると、

$$
R_{2m}M_m=\prod_{j=1}^{m}\frac{(2j)^2}{(2j-1)(2j+1)}
$$

となる。

ここで

$$
P_j=2j-1
$$

と置けば、

$$
2j=P_j+1,\qquad 2j+1=P_j+2
$$

なので、

$$
\frac{(2j)^2}{(2j-1)(2j+1)}=\frac{(P_j+1)^2}{P_j(P_j+2)}
$$

そして宇宙式の Body を

$$
N_j=P_j(P_j+2)
$$

と置くと、

$$
N_j+1=(P_j+1)^2
$$

だから、

$$
\frac{(2j)^2}{(2j-1)(2j+1)}=\frac{N_j+1}{N_j}=1+\frac{1}{N_j}
$$

よって、

$$
R_{2m}M_m=\prod_{j=1}^{m}\frac{N_j+1}{N_j}
$$

これが **Wallis–Cosmic Petal Bridge** の有限版じゃ。

## 2. 中央比率の証明

中央二項係数は、

$$
\binom{2m}{m}=\frac{(2m)!}{(m!)^2}
$$

したがって、

$$
R_{2m}=\frac{2^{2m}}{\binom{2m}{m}}=\frac{4^m(m!)^2}{(2m)!}
$$

ここで、

$$
(2m)!=(1\cdot3\cdot5\cdots(2m-1))(2\cdot4\cdot6\cdots2m)
$$

かつ、

$$
2\cdot4\cdot6\cdots2m=2^m m!
$$

だから、

$$
(2m)!=(1\cdot3\cdot5\cdots(2m-1))2^m m!
$$

これを代入すると、

$$
R_{2m}=\frac{4^m(m!)^2}{(1\cdot3\cdot5\cdots(2m-1))2^m m!}
$$

よって、

$$
R_{2m}=\frac{2^m m!}{1\cdot3\cdot5\cdots(2m-1)}
$$

一方、

$$
2^m m!=\prod_{j=1}^{m}2j
$$

なので、

$$
R_{2m}=\prod_{j=1}^{m}\frac{2j}{2j-1}
$$

証明完了じゃ。

## 3. 鏡像を掛ける証明

鏡像積を

$$
M_m=\prod_{j=1}^{m}\frac{2j}{2j+1}
$$

と置く。

すると単純に、

$$
R_{2m}M_m=\left(\prod_{j=1}^{m}\frac{2j}{2j-1}\right)\left(\prod_{j=1}^{m}\frac{2j}{2j+1}\right)
$$

同じ添字 $j$ ごとにまとめれば、

$$
R_{2m}M_m=\prod_{j=1}^{m}\frac{(2j)^2}{(2j-1)(2j+1)}
$$

これも有限積の結合法則だけで済む。

## 4. 宇宙式への置換

ここで、

$$
P_j=2j-1
$$

と置く。

すると、

$$
2j=P_j+1
$$

かつ、

$$
2j+1=P_j+2
$$

だから、

$$
\frac{(2j)^2}{(2j-1)(2j+1)}=\frac{(P_j+1)^2}{P_j(P_j+2)}
$$

宇宙式の Body を

$$
N_j=P_j(P_j+2)
$$

と置けば、

$$
(P_j+1)^2=P_j(P_j+2)+1=N_j+1
$$

したがって、

$$
\frac{(P_j+1)^2}{P_j(P_j+2)}=\frac{N_j+1}{N_j}
$$

よって、

$$
R_{2m}M_m=\prod_{j=1}^{m}\frac{N_j+1}{N_j}
$$

ここまで **完全に厳密な有限恒等式** じゃ。近似は一切ない。

## 5. Wallis 積としての極限

古典的な Wallis 積は、

$$
\prod_{j=1}^{\infty}\frac{(2j)^2}{(2j-1)(2j+1)}=\frac{\pi}{2}
$$

である。

さきほどの等式により、これは宇宙式表示では、

$$
\prod_{j=1}^{\infty}\frac{N_j+1}{N_j}=\frac{\pi}{2}
$$

となる。

ここで、

$$
N_j=(2j-1)(2j+1)=(2j)^2-1
$$

だから、各因子は、

$$
\frac{N_j+1}{N_j}=1+\frac{1}{N_j}
$$

つまり Wallis 積は、

$$
\prod_{j=1}^{\infty}\left(1+\frac{1}{(2j)^2-1}\right)=\frac{\pi}{2}
$$

とも書ける。

これがかなり重要じゃ。
$\pi/2$ は、宇宙式 Gap $1$ の比率

$$
\frac{N+1}{N}
$$

を奇数 Petal 境界に沿って掛け続けた極限として出る。

## 6. 証明の骨格まとめ

有限版の証明は、次の鎖で完成する。

$$
\frac{2^{2m}}{\binom{2m}{m}}=\prod_{j=1}^{m}\frac{2j}{2j-1}
$$

$$
\prod_{j=1}^{m}\frac{2j}{2j-1}\prod_{j=1}^{m}\frac{2j}{2j+1}=\prod_{j=1}^{m}\frac{(2j)^2}{(2j-1)(2j+1)}
$$

$$
\frac{(2j)^2}{(2j-1)(2j+1)}=\frac{(P_j+1)^2}{P_j(P_j+2)}
$$

$$
\frac{(P_j+1)^2}{P_j(P_j+2)}=\frac{N_j+1}{N_j}
$$

したがって、

$$
\frac{2^{2m}}{\binom{2m}{m}}\prod_{j=1}^{m}\frac{2j}{2j+1}=\prod_{j=1}^{m}\frac{N_j+1}{N_j}
$$

ここまでが実装可能なコア定理。

## 7. Lean 実装前の定理候補

最初は $\mathbb{Q}$ や `Rat` 上でやるのがよい。自然数除算を避けるためじゃ。

候補名はこんな感じ。

```lean
centralRatio_eq_prod_even_over_odd
mirrorRatio_eq_prod_even_over_succ_odd
centralRatio_mul_mirror_eq_wallisPartial
wallisFactor_eq_cosmicRatio_of_P_eq_two_mul_sub_one
cosmicRatio_eq_one_add_inv_body
wallisPartial_eq_cosmicGapProduct
```

実装順は、

1. 有限積の階乗分解
2. 中央比率 $R_{2m}$ の積表示
3. 鏡像積との積
4. $P=2j-1$ 置換
5. $N=P(P+2)$ 置換
6. 宇宙式比率 $(N+1)/N$ への変換

がよい。

## 8. ここで確定したこと

これはもう単なる直感ではない。

有限段階では、

$$
\text{中央二項係数の逆密度}\times\text{鏡像逆密度}
$$

が、

$$
\text{宇宙式 Gap 比率の有限積}
$$

に **厳密一致** する。

そして極限で Wallis により、

$$
\frac{\pi}{2}
$$

へ行く。

つまり、 **中央比率 Petal 構造と宇宙式 Gap 構造は、Wallis 積を介して厳密に同じ有限因子を共有している** 。

これは強い。
実装前の証明としては、十分に足場が固まったのじゃ。
