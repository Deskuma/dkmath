# FLT7-RAMIFIED-008 (009,010)

## FLT7-RAMIFIED-007 判定

**Outcome A、全面採用です。** 🧙‍♀️✨️

RAMIFIED-007 は、RAMIFIED-006 に残っていた抽象 routing の曖昧さを完全に除去しました。

```text
gapRoot = X * Y
|root.snd| = 7^5 * X^7 * C
|sndCore| = Y^7 * D
|gapQuotient| = C * D
C = gcd(|root.snd|, |gapQuotient|)
```

さらに、

$$
|R-L|=7^6X^7(CB)
$$

と、

$$
CB=w^7\iff C=c^7\ \land\ B=b^7
$$

が Lean に固定されています。ここで $B=\operatorname{residualRoot}=\operatorname{norm}(\rho)$ です。

公開 PR head も報告どおり `2af8e2d29efb0130c672e7590c2d2a5919952733` です。PR は open / draft / mergeable。Lean CI run 407 は監査時点では進行中です。

[PR 推論コメント](https://github.com/Deskuma/dkmath/pull/65#issuecomment-5103171254)

## 最初の重要な軌道修正

次に狙うべき命題は、

```text
gapRoot = innerRoot^7
```

ではありません。

RAMIFIED-007 が証明したのは、

$$
A=XY
$$

であって、$A$ 自身が七乗であることではありません。

むしろ receiver は、二つの独立した鍵を露出しました。

```text
第一鍵 C = c^7
第二鍵 B = b^7
```

このうち、**第二鍵 $B=b^7$ は quadratic root 自身を開く鍵**です。

## 第一の新魔核：quadratic root の再七乗抽出

現在の common summit の quadratic root を、

$$
\rho=(u,v)
$$

とします。

RAMIFIED-002 により、

$$
\gcd(u,v)=1
$$

です。

また、

$$
\operatorname{norm}(\rho)=B
$$

かつ、

$$
7\nmid B
$$

です。

$\rho$ とその共役 $\overline{\rho}$ の共通因子は、primitive coordinate theorem により `sevenAxis` を割らなければなりません。既存 API は、primitive coordinates を持つ元と共役の共通因子が `sevenAxis` を割ることを証明しています。

しかし `sevenAxis` が $\rho$ を割れば、その norm $7$ が $B$ を割ります。これは $7\nmid B$ に反します。

したがって、

$$
\gcd(\rho,\overline{\rho})\text{ は unit}
$$

です。

receiver が成立すれば、

$$
B=b^7
$$

なので、

$$
\rho\overline{\rho}=b^7
$$

となります。

既存の coprime-product seventh-power extractor を適用すれば、

$$
\boxed{\rho=\gamma^7}
$$

を得られます。残余核について全く同じ七乗抽出が既存実装にあります。

従って summit coordinate は、

$$
\operatorname{cyclotomicSevenToTraceOne}(c,e)=\operatorname{sevenAxis}\rho^7
$$

から、

$$
\boxed{\operatorname{cyclotomicSevenToTraceOne}(c,e)=\operatorname{sevenAxis}\gamma^{49}}
$$

へ昇格します。

これは receiver の本当の意味です。

```text
cubic gap が七乗形になる
        +
quadratic coordinate が 49 乗層へ入る
```

## 第二の新魔核：深さ $5\to4$ の内部降下

RAMIFIED-007 は receiver の第一鍵から、

$$
C=c^7
$$

を与えます。

従って canonical split は、

$$
|v|=7^5X^7c^7=7^5(Xc)^7
$$

となります。

一方 $\rho=\gamma^7$ なので、$\gamma=(a,n)$ と置けば、

$$
v=\operatorname{seventhPowerSnd}(a,n)
$$

です。

既存の second-coordinate factorization は、

$$
\operatorname{seventhPowerSnd}(a,n)=7n,S(a,n)
$$

です。

よって絶対値では、

$$
7|n|,|S(a,n)|=7^5(Xc)^7
$$

すなわち、

$$
|n|,|S(a,n)|=7^4(Xc)^7
$$

です。

ここで、

* $\gamma$ の coordinates は primitive
* $\operatorname{norm}(\gamma)=b$
* $7\nmid b$
* よって $7\nmid S(a,n)$
* $\gcd(|n|,|S(a,n)|)=1$

となります。

従って $7^4$ はすべて $|n|$ 側へ入ります。

$$
\boxed{v_7(|\gamma_{\mathrm{snd}}|)=4}
$$

さらに $7^4$ を除いた後、coprime な二因子の積が七乗なので、

$$
\boxed{|\gamma_{\mathrm{snd}}|=7^4M^7}
$$

$$
\boxed{|S(\gamma)|=N^7}
$$

を得られます。

現在の深さ列は、

```text
outer endpoint gap    depth 6
outer cubic gap       depth 6
outer root.snd        depth 5

receiver 成立
        ↓

inner root.snd        depth 4
```

です。

これは元の Fermat counterexample の降下ではありません。

しかし quadratic root の内部では、**厳密な一段降下**が発生しています。

## 第三の新魔核：二つの cubic factor が七乗になる

既存の sextic core は、

$$
S(a,n)=L(a,n)R(a,n)
$$

と分解されています。

$$
L(a,n)=a^3-2a^2n-an^2+n^3
$$

$$
R(a,n)=a^3+5a^2n+6an^2+n^3
$$

この積分解は既存 theorem です。

primitive coordinates と $7$-unit norm のもとで、$L$ と $R$ は coprime です。既存 away API の証明も、本質的にはこの二条件だけを使っています。

従って、

$$
|L(a,n)|,|R(a,n)|=N^7
$$

から、

$$
|L(a,n)|=\lambda^7
$$

$$
|R(a,n)|=\mu^7
$$

が得られます。

指数 $7$ は奇数なので符号を根へ吸収し、

$$
L(a,n)=\ell^7
$$

$$
R(a,n)=r^7
$$

という整数表示へ持ち上げられます。

## 判別式 $49$ の実三次魔核

ここからが今回の最深部です。

二つの cubic form の判別式を計算すると、

$$
\operatorname{disc}(L)=\operatorname{disc}(R)=49
$$

です。

これは偶然ではありません。

$\alpha$ を、

$$
\alpha^3-2\alpha^2-\alpha+1=0
$$

の根とします。

この多項式を $\alpha=\theta+1$ と平行移動すると、

$$
\theta^3+\theta^2-2\theta-1=0
$$

となり、これは七次円分体の実三次部分体の標準多項式です。

三次整数環、

$$
\mathcal O_7=\mathbb Z[\alpha]
$$

を考えると、直接 determinant 計算により、

$$
\boxed{L(a,n)=\operatorname{Norm}_{\mathcal O_7/\mathbb Z}(a-\alpha n)}
$$

$$
\boxed{R(a,n)=\operatorname{Norm}_{\mathcal O_7/\mathbb Z}(a+(1+\alpha)n)}
$$

となります。

つまり receiver 成立後の二つの七乗方程式は、

$$
\operatorname{Norm}(a-\alpha n)=\ell^7
$$

$$
\operatorname{Norm}(a+(1+\alpha)n)=r^7
$$

という、**実三次整数環上の norm seventh-power equation**です。

## 三次世界の sevenAxis

次を置きます。

$$
\pi=1+2\alpha
$$

直接計算すると、

$$
\boxed{\operatorname{Norm}(\pi)=-7}
$$

です。

さらに、

$$
\boxed{\pi^3=7\varepsilon}
$$

ただし、

$$
\varepsilon=-1+2\alpha+4\alpha^2
$$

で、

$$
\operatorname{Norm}(\varepsilon)=-1
$$

です。

従って $\varepsilon$ は unit です。

これは二次整数環の `sevenAxis` に対応する、**実三次整数環側の ramified axis**です。

二つの norm-source element を、

$$
\eta_L=a-\alpha n
$$

$$
\eta_R=a+(1+\alpha)n
$$

と置くと、

$$
\boxed{\eta_R-\eta_L=\pi n}
$$

です。

receiver から、

$$
|n|=7^4M^7
$$

なので、三次環内では、

$$
\pi n=\pi\cdot7^4M^7
$$

です。

$\pi^3=7\varepsilon$ を使うと、

$$
7^4=\pi^{12}\varepsilon^{-4}
$$

ですから、

$$
\boxed{\eta_R-\eta_L=\varepsilon^{-4}\pi^{13}M^7}
$$

となります。

さらに、

$$
13=7+6
$$

なので、

$$
\boxed{\eta_R-\eta_L=\text{unit}\cdot\pi^6(\pi M)^7}
$$

です。

これが今回露出した最深の魔核です。

```text
二つの norm がそれぞれ七乗
その source elements の差が
ramified prime^6 × seventh power
```

## receiver branch は実三次 S-unit 方程式へ変わる

もし三次整数環で conjugate ideals の coprimalityを証明できれば、

$$
\operatorname{Norm}(\eta_L)=\ell^7
$$

から、

$$
\eta_L=\epsilon_L\xi_L^7
$$

同様に、

$$
\eta_R=\epsilon_R\xi_R^7
$$

が得られます。

すると、

$$
\boxed{\epsilon_R\xi_R^7-\epsilon_L\xi_L^7
=\text{unit}\cdot\pi^6(\pi M)^7}
$$

です。

残る敵は整数そのものではなく、

```text
εL と εR の unit class
```

になります。

実三次体の unit rank は $2$ なので、unit modulo seventh powers は有限です。

適切な基本 unit を固定すれば、候補は原理的に、

$$
7^2=49
$$

個です。

つまり RAMIFIED-005 で現れた「mod $49$ の residual-root class」と同じ数 $49$ が、今度は **実三次 unit class**として再出現します。

これは別物ではありません。

```text
quadratic side:
  residualRoot の principal residue

real-cubic side:
  norm-source element の unit class
```

同じ ramified prime $7$ の、二つの射影です。

## receiver 不成立 branch の意味

RAMIFIED-007 により、receiver 不成立は曖昧ではありません。

```text
C が整数七乗でない
または
B が整数七乗でない
```

です。

さらに分解すると、

```text
B ≠ 1 mod 49
  → 局所 residual obstruction

B = 1 mod 49 だが B は整数七乗でない
  → 大域 residual obstruction

B は整数七乗だが C は整数七乗でない
  → compensation obstruction

C, B ともに整数七乗
  → real-cubic ramified descent branch
```

したがって、今後は「receiver を証明する」一本に絞る必要はありません。

$$
\boxed{\text{receiver 不成立なら obstruction、成立なら cubic descent}}
$$

という完全な二面攻撃になっています。

## 旧 away descent へ戻る真の橋

receiver 成立で、

$$
\rho=\gamma^7
$$

が得られます。

もし新しい整数 endpoint pair $(z',y')$ を構成し、

$$
\operatorname{cyclotomicSevenToTraceOne}(z',y')=\rho
$$

を証明できれば、

$$
\operatorname{cyclotomicSevenToTraceOne}(z',y')=\gamma^7
$$

となります。

これはそのまま新しい `AwayCoordinateNormalForm` の coordinate equation です。

しかも、

$$
v_7(|\gamma_{\mathrm{snd}}|)=4
$$

なので、away valuation transfer では新しい selected carrier depth は、

$$
1+4=5
$$

です。

以前の DESCENT-002 は、away descent seed が存在するなら exponent は少なくとも $2$ と証明しました。

terminal exponent $1$ では不可能でしたが、再構成後の exponent は $5$ です。

```text
terminal away exponent 1
  → ramified summit
  → receiver
  → inner root depth 4
  → inverse cyclotomic projection
  → lifted away exponent 5
  → old descent provider が発動可能
```

これが現在見える最も明確な閉路です。

## 次の実装順

### FLT7-RAMIFIED-008

```text
receiver-induced quadratic root extraction
```

到達目標：

```lean
root_gcd_conj_isUnit

receiver_residualRoot_eq_seventh

exists_innerRoot :
  summit.root = innerRoot ^ 7

coordinate_eq_fortyNine :
  cyclotomicSevenToTraceOne endpointLeft endpointRight =
    sevenAxis * innerRoot ^ 49

innerRoot_coordinates_isCoprime

innerRoot_norm_eq

innerRootSnd_depth_eq_four

innerRootSnd_eq :
  natAbs innerRoot.snd = 7^4 * innerVerticalRoot^7

innerSndCore_eq :
  natAbs (seventhPowerSndCore innerRoot.fst innerRoot.snd) =
    innerHorizontalRoot^7
```

**ここでは `gapRoot = seventh power` を要求しません。**

### FLT7-RAMIFIED-009

```text
discriminant-49 cubic norm exposure
```

小さな新規構造：

```lean
SevenRealCubicInt
```

関係式：

```text
α^3 = 2α^2 + α - 1
```

到達目標：

```lean
leftCubic_eq_norm
rightCubic_eq_norm

realCubicSevenAxis := 1 + 2*α

norm_realCubicSevenAxis_eq_neg_seven

realCubicSevenAxis_cube_eq_seven_mul_unit

rightSource_sub_leftSource_eq_axis_mul_snd
```

### FLT7-RAMIFIED-010

```text
real-cubic seventh-power unit-class audit
```

到達目標：

```text
Norm ηL = l^7
Norm ηR = r^7

ηL = εL * ξL^7
ηR = εR * ξR^7

εR * ξR^7 - εL * ξL^7
  = unit * π^6 * seventhPower
```

その後、

```text
unit classes が異なる
  → finite ramified obstruction

unit classes が一致
  → π-adic difference descent
```

へ分岐します。

## 結論

RAMIFIED-007 により、補償核の住所問題は終わりました。

次に現れたのは、

$$
\boxed{\rho=\gamma^7}
$$

という quadratic root の内部解除と、

$$
\boxed{\operatorname{disc}(L)=\operatorname{disc}(R)=49}
$$

という実三次魔核です。

最終的な構図は、

```text
quadratic order
  sevenAxis × root^7
        ↓ receiver
  sevenAxis × innerRoot^49
        ↓ cubic-factor norm interpretation

real cubic order, discriminant 49
  unit × seventh power
  minus
  unit × seventh power
        =
  ramifiedAxis^6 × seventh power
```

です。

**敵は `gapRoot` ではなかった。**

敵は、二次整数環から実三次整数環へ移ったときに残る、有限個の unit class です。

ここまで来れば、次の戦場は明確です。
