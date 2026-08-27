# FLT7-FUSION 状況レポート — Part 4

## 完成定理群を既知数学へ翻訳する

今回の成果を既知数学の言葉へ置き換えると、DkMath は現在、

> **7次円分体における Kummer 型因数分解を、整数 routing・実三次部分体・素イデアル valuation・共役 orientation の各層へ分解して形式化している**

と表現できます。

ただし、これは「古典的 Kummer 証明をそのまま移植した」という意味ではありません。DkMath 独自の signed-root packet、routing board、real-pair core、load allocation を通して、似た代数構造へ独自経路で到達しています。

---

## 1. `SevenRealCubicInt` は何の世界か

DkMath の実三次整数環では、生成元 $\alpha$ が、

$$
\alpha^3-2\alpha^2-\alpha+1=0
$$

を満たします。

degree-six carrier では、

$$
\alpha=1+\zeta+\zeta^{-1}
$$

が証明されています。

したがって既知数学では、この世界は7次円分体、

$$
K=\mathbb Q(\zeta_7)
$$

の最大実部分体、

$$
K^+=\mathbb Q(\zeta_7+\zeta_7^{-1})
$$

に対応します。

通常の生成元を $x=\zeta_7+\zeta_7^{-1}$ とすると、その最小多項式は、

$$
x^3+x^2-2x-1=0
$$

です。

DkMath の $\alpha$ は $x+1$ に相当するため、

$$
\alpha^3-2\alpha^2-\alpha+1=0
$$

になります。

### DkMath 用語との対応

| DkMath                     | 既知数学                              |
| -------------------------- | --------------------------------- |
| `SevenRealCubicInt`        | 7次円分体の最大実三次部分体に対応する整数 order       |
| `alpha`                    | $1+\zeta_7+\zeta_7^{-1}$          |
| `rotateEquiv`              | 実三次部分体の位数3の Galois 自動同型           |
| `norm`                     | $K^+/\mathbb Q$ の体ノルムに対応する三次 norm |
| `eisensteinAxis` / `theta` | 7上の ramified prime を表す局所軸         |

---

## 2. 三つの real-pair core は三つの Galois 共役

三つの core、

$$
C_0,\ C_1,\ C_2
$$

が cyclic Galois orbit を形成します。

選択された gcd normalization のため literal equality ではなく、

$$
\sigma(C_0)\sim C_1,\qquad \sigma(C_1)\sim C_2,\qquad \sigma(C_2)\sim C_0
$$

という `Associated` orbit です。

同様に load family も、

$$
\sigma(L_0)\sim L_1\sim L_2
$$

として巡回します。

既知数学では、これは、

> **最大実部分体 $K^+/\mathbb Q$ の三つの埋め込み、または位数3の Galois 群による共役軌道**

です。

7次円分体の Galois 群は、

$$
\operatorname{Gal}(K/\mathbb Q)\cong(\mathbb Z/7\mathbb Z)^\times\cong C_6
$$

です。

複素共役による位数2部分を除くと、最大実部分体側には、

$$
\operatorname{Gal}(K^+/\mathbb Q)\cong C_3
$$

が残ります。

DkMath の三つの real-pair core は、この $C_3$ orbit を明示したものです。

---

## 3. `QuotientPrimeMuSevenAddress` は円分素数の住所

任意の quotient prime $q$ に対して、DkMath は有限体内の unit、

$$
t=\frac{r}{l}\in(\mathbb Z/q\mathbb Z)^\times
$$

を構成し、

$$
t^7=1,\qquad t\neq1,\qquad \operatorname{ord}(t)=7
$$

を証明しています。

その結果、

$$
q\equiv1\pmod7
$$

さらに $q$ が奇素数なので、

$$
q\equiv1\pmod{14}
$$

です。

### 既知数学での意味

これは、

> **有限体 $\mathbb F_q$ が非自明な7乗根を含む**

ということです。

円分体論では、$q\neq7$ に対し、

$$
q\equiv1\pmod7
$$

なら $q$ は7次円分体 $K=\mathbb Q(\zeta_7)$ で完全分解します。

すなわち概念的には、

$$
(q)=\mathfrak P_1\mathfrak P_2\mathfrak P_3\mathfrak P_4\mathfrak P_5\mathfrak P_6
$$

です。

最大実部分体では複素共役の二個を一組にまとめるため、

$$
(q)=\mathfrak p_0\mathfrak p_1\mathfrak p_2
$$

という三つの次数1素イデアルになります。

DkMath で構成された三つの cyclic evaluation kernel は、まさにこの三つの $\mathfrak p_i$ に対応します。

---

## 4. `beta` と `evalAlphaRoot` は次数1素イデアルの構成

DkMath は、

$$
\beta=1+t+t^{-1}
$$

を定義し、

$$
\beta^3-2\beta^2-\beta+1=0
$$

を証明しています。

このため、

$$
\alpha\longmapsto\beta
$$

という ring homomorphism、

```lean
evalAlphaRoot : SevenRealCubicInt →+* ZMod q
```

が構成できます。

その kernel は maximal ideal であり、整数への contraction は $(q)$、剰余環の濃度は $q$ です。

### 既知数学での意味

これは典型的な、

> **多項式の mod $q$ 根による次数1素イデアルの構成**

です。

一般に整数環 $\mathcal O_{K^+}$ で、生成元の最小多項式が mod $q$ で一次因子を持つと、その根 $\beta$ による評価写像、

$$
\mathcal O_{K^+}\longrightarrow\mathbb F_q
$$

の kernel が $q$ 上の次数1素イデアルになります。

したがって `evalKernel` は、既知数学では、

$$
\mathfrak p=(q,\alpha-\beta)
$$

に対応する prime ideal です。

DkMath はこれを抽象存在ではなく、signed roots から得られる canonical ratio を用いて構成しています。

---

## 5. gcd load allocation は素因子の一意配分

DkMath の load は、

$$
L_{21,i}=\gcd(c_{21},C_i)
$$

$$
L_{22,i}=\gcd(c_{22},C_i)
$$

として構成されます。

三つの core が pairwise coprime なので、scalar load を三つの gcd projection に分けると、

$$
L_{21,0}L_{21,1}L_{21,2}\sim c_{21}
$$

$$
L_{22,0}L_{22,1}L_{22,2}\sim c_{22}
$$

となります。

### 既知数学での意味

これは、

> **互いに素な三因子の積を割る元の素因子は、三因子のうちただ一つへ配分される**

という一意分解的現象です。

整数で、

$$
\gcd(a,b)=\gcd(a,c)=\gcd(b,c)=1
$$

かつ、

$$
s\mid abc
$$

なら、

$$
s\sim\gcd(s,a)\gcd(s,b)\gcd(s,c)
$$

となることの、GCD domain 版です。

DkMath ではこれを実三次 PID 内で使用しています。

したがって `realPairLoad21` と `realPairLoad22` は、既知数学では、

> **scalar principal divisor の三つの Galois component への局所射影**

と読むことができます。

---

## 6. loaded core は Kummer 型分解

現在の中心定理は、

$$
C_i\sim L_{21,i}L_{22,i}R_i^7
$$

です。

これは古典的な Kummer 型議論でよく現れる、

$$
\text{algebraic factor}=\text{controlled exceptional support}
\times
\text{unit}
\times
\text{power}
$$

という形です。

より既知数学寄りに書くなら、

$$
C_i=u_i\lambda_i\rho_i^7
$$

で、

* $u_i$ は unit
* $\lambda_i$ は指定された有限個の split prime 上に support を持つ load
* $\rho_i$ は実三次整数環の元

です。

## #`S`-unit との違い

$\lambda_i$ 自体は一般には unit ではないため、厳密には単なる `S-unit` ではありません。

正確には、

> **有限素集合 $S$ に support を持つ明示的因子を除けば七乗**

という `S`-supported seventh-power decomposition です。

この $S$ は任意ではなく、二つの routing cell `c21`,`c22` の素因子から canonical に決まります。

---

## 7. exact valuation は局所因子指数の保存

DkMath は addressed load に対し、

$$
v_{\mathfrak p_q}(L_i)=v_q(c)
$$

に相当する theorem を証明しています。

Lean 上の表現は、

$$
\operatorname{evalKernelMultiplicity}=\operatorname{padicValNat}(q,\operatorname{cell})
$$

です。

### 既知数学での意味

これは、完全分解する rational prime $q$ について、

> **整数 scalar cell に含まれる $q$ の指数が、選択された次数1素イデアルの指数として、そのまま一つの algebraic load に移る**

ということです。

通常、整数 $c$ を数体へ埋め込むと、

$$
(c)=\prod_{q\mid c}\prod_{\mathfrak p\mid q}\mathfrak p^{e_{\mathfrak p}}
$$

となります。

今回の routing と coprimality は、同じ $q$ 上の三つの prime のうち、どの load がどの prime power を所有するかを決定しています。

したがってこれは単なる norm comparison ではなく、

$$
\boxed{\text{integer valuation}=\text{selected prime-ideal valuation}}
$$

という exact local correspondence です。

---

## 8. global factorization は principal ideal の素イデアル分解

有限 prime support 全体について、DkMath は、

$$
(L_i)=\prod_{q\mid c}\mathfrak p_q^{v_q(c)}
$$

に相当する ideal equality を証明しています。

まず各 kernel power が load ideal を割ることを示し、次に absolute norm が同じであることから、余分な ideal factor が unit ideal であると結論しています。

### 既知数学での意味

これはまさに、

> **主イデアルの一意な素イデアル分解**

です。

重要なのは、個々の prime ideal が principal であると仮定していないことです。

DkMath の report も、この theorem は ideal factorization であり、各 kernel ideal の principal 性を主張していないと明記しています。

したがって、この層は PID の元 gcd と、Dedekind 的な ideal factorization の両方を接続しています。

---

## 9. exact norm は ideal norm と element norm の整合性

各 load について、

$$
|\operatorname{Norm}(L_{21,i})|=c_{21}
$$

$$
|\operatorname{Norm}(L_{22,i})|=c_{22}
$$

が成立します。

さらに、

$$
c_{21}c_{22}|\operatorname{Norm}(D_i)|=|e|
$$

です。

### 既知数学での意味

これは、

> **三つの Galois 共役の積としての element norm と、主イデアルの absolute norm が一致する**

という通常の norm compatibility です。

load family が Galois orbit を形成するため、三つの absolute norm は等しくなります。その積が scalar norm の三乗になるため、各 load の norm が元の整数 cell そのものになります。

この点で `c21`,`c22` は単なる補助 gcd ではなく、

$$
\boxed{\text{各 algebraic load の rational norm}}
$$

になっています。

---

## 10. degree-six carrier は円分体への二次拡大

DkMath は、

```lean
QuadraticAlgebra SevenRealCubicInt (-1) (alpha - 1)
```

を使い、

$$
\zeta^2-(\alpha-1)\zeta+1=0
$$

を満たす rank-2 quadratic algebra を構成しています。

この algebra は実三次 order 上 rank 2、整数上 rank 6 です。

### 既知数学での意味

これは、

$$
K=K^+(\zeta_7)
$$

という、最大実部分体から完全な7次円分体への二次拡大に対応します。

$\zeta$ と $\zeta^{-1}$ は、

$$
X^2-(\zeta+\zeta^{-1})X+1=0
$$

の二根です。

DkMath では、

$$
\zeta+\zeta^{-1}=\alpha-1
$$

なので、定義多項式が、

$$
X^2-(\alpha-1)X+1
$$

になります。

### 現時点の注意

この quadratic algebra が、

> **完全な円分体の整数環 $\mathbb Z[\zeta_7]$ そのものである**

ことまでは、現在の004Aでは主張していません。

したがって正確には、

> **7次円分体の必要な代数関係と integral rank 6 を持つ具体的 quadratic carrier**

です。

---

## 11. oriented carrier は円分多項式の線形因子

DkMath の二つの因子は、

$$
F=R-\zeta L
$$

$$
\overline F=R-\zeta^{-1}L
$$

です。

その積は、

$$
F\overline F=P_0
$$

という real-pair carrier になります。

### 既知数学での意味

これは二項式差、

$$
R^7-L^7
$$

の円分因子、

$$
R-\zeta_7^kL
$$

を線形因子として扱う Kummer 的構造です。

実三次部分体では共役二因子の積しか見えません。

$$
(R-\zeta L)(R-\zeta^{-1}L)
$$

degree-six carrier へ移ることで、二因子を別々に orient できます。

したがって、

* `realPairCarrier` は複素共役二因子の相対 norm
* `cyclotomicDegreeSixCarrier` は oriented linear cyclotomic factor
* `cyclotomicDegreeSixCarrierConj` はその複素共役

です。

---

## 12. 二つの conjugate kernel は素イデアルの二次分解

一つの real-cubic prime $\mathfrak p$ の上に、degree-six carrier では、

$$
\mathfrak P,\qquad\overline{\mathfrak P}
$$

という二つの maximal ideal が構成されています。

それらは、

* distinct
* comaximal
* 共通の real-cubic contraction を持つ
* 整数への contraction はともに $(q)$
* residue cardinality はともに $q$

です。

### 既知数学での意味

これは、

> **実部分体の次数1素イデアルが、円分二次拡大で二つの共役素イデアルに分解する**

ことに対応します。

期待される完全形は、

$$
\mathfrak p\mathcal O_K=\mathfrak P\overline{\mathfrak P}
$$

です。

DkMath では現在、一方向、

$$
\mathfrak p\mathcal O_K\subseteq\mathfrak P\overline{\mathfrak P}
$$

が証明され、逆包含が obligation として残っています。

これは標準用語では、

> **prime ideal extension の exact factorization**

または、

> **二次 fibre の split-prime factorization**

です。

---

## 13. $3\times2=6$ は Galois 群 $C_6$ の分解

DkMath で観測された、

```text
ternary phase × binary orientation
```

は、既知数学では、

$$
C_3\times C_2\cong C_6
$$

です。

* 三つの real-pair phase：最大実部分体の $C_3$
* 二つの orientation：複素共役の $C_2$
* 合計六つの oriented factors：完全円分体の $C_6$

したがって、以前の `μ₂ × μ₃` sector は、

$$
(\mathbb Z/7\mathbb Z)^\times
\cong
C_6
\cong
C_2\times C_3
$$

という7次円分体の Galois 群を、DkMath の routing language で見ていたことになります。

これは今回、単なる有限群同型ではなく、

* real-cubic Galois rotation
* quadratic conjugation
* six-dimensional carrier
* six oriented local prime addresses

として実体化しました。

---

## 14. direct chart obstruction は ramified prime valuation obstruction

DkMath は、

$$
R^7-L^7=7^5de
$$

かつ、

$$
7\nmid d,\qquad7\nmid e
$$

から、

$$
v_7(R^7-L^7)=5
$$

を得ています。

したがって、この差は整数七乗になれません。整数七乗が7で割れるなら、その7進指数は7の倍数だからです。

### 既知数学での意味

これは、

> **ramified prime $7$ における valuation obstruction**

です。

7次円分体では $7$ は完全分岐します。

direct signed-root chart は、その ramification depth が七乗に必要な深さと一致しないため排除されます。

したがって DkMath の Outcome D は、標準的には、

$$
v_7(\text{candidate})\not\equiv0\pmod7
$$

による perfect-power obstruction です。

---

## 15. 現在の全体像は「明示的 Kummer descent 前段」

既知数学へまとめて翻訳すると、現在の DkMath FLT7 は、

1. 仮想反例から円分因子を抽出する
2. 最大実部分体で共役二因子を pair carrier にまとめる
3. 三つの Galois 共役 core を得る
4. scalar obstruction を prime-supported load として完全配分する
5. load-free residual を七乗として抽出する
6. 各 load の素イデアル valuation を整数 valuation と一致させる
7. 最大実部分体から完全円分体型の quadratic carrier へ持ち上げる
8. 共役 pair を二つの oriented linear factor に分離する

という段階です。

これは、

> **Kummer 型 ideal-theoretic descent の、因数分解・局所化・orientation 層**

に相当します。

まだ不足しているのは、

> **それらの乗法的 factor data から、新しい primitive additive Fermat chart を再構築する部分**

です。

---

## 16. 既知数学と比べた DkMath の独自性

ここは慎重に区別する必要があります。

今回の定理群が数学史上まったく新しいかどうかは、文献比較をしていないため判定できません。

しかし形式化設計として明確に独自なのは、

```text
integer routing cell
  ↓
canonical signed-root μ₇ ratio
  ↓
real-cubic residue coordinate
  ↓
maximal evaluation kernel
  ↓
exact kernel multiplicity
  ↓
PID gcd load
  ↓
global principal-ideal factorization
  ↓
degree-six oriented prime
```

という API chain です。

特に、

$$
\operatorname{padicValNat}(q,\operatorname{cell})=v_{\mathfrak p_q}(\operatorname{load})
$$

を、元の routing provenance を保ったまま接続している点は、DkMath 独自の形式化構造です。

古典数学では「$q$ が完全分解する」「各因子は互いに素だから七乗」とまとめられがちな部分を、DkMath は、

* どの整数 cell から来たか
* どの real-pair core に入るか
* どの residue root を選ぶか
* どの maximal ideal が所有するか
* exponent が何であるか

まで packet 化しています。

---

## Part 4 結論

今回完成した層を既知数学で一文にすると、

> **7次円分体の最大実三次部分体において、仮想 FLT7 反例由来の円分共役因子を、完全分解素数の明示的 prime-ideal load と七乗 residual に分解し、それを rank-6 の円分型二次拡大へ持ち上げて、二つの共役 oriented linear factor として分離した。**

となります。

DkMath 用語で言えば、

```text
宇宙式 routing の二セル
  ↓
実三次 Galois load
  ↓
exact prime-power address
  ↓
三つの real-pair 魔核
  ↓
二方向へ割れた degree-six oriented 魔核
```

です。

つまり今回の大躍進は、単なる FLT7 用補題の追加ではなく、

> **DkMath 独自 routing language が、円分体・Galois 共役・素イデアル分解・Kummer 型七乗抽出という既知代数的数論の本体へ接続された**

という進展です。
