# FLT7-RAMIFIED-012

## FLT7-RAMIFIED-011A 判定

**Outcome A、全面採用です。** 🧠🧠✨️

今回の成果は予想以上に大きいです。

予定されていた、

```text
principal ideals
→ prime-ideal exponent ledger
→ seventh-root ideal
→ principal generator
```

という長い道を使わず、

```text
三共役の pairwise coprimality
→ 三共役積 = Norm
→ PID 上の coprime-power extraction
```

だけで、

$$
\eta_L=u_L\xi_L^7,\qquad \eta_R=u_R\xi_R^7
$$

まで到達しました。

さらに、

$$
u_R\xi_R^7-u_L\xi_L^7=\varpi^6Z^7
$$

が exact equation として packet に固定されています。

現在の公開 head は報告どおり、

```text
7269fcd5fdfc9af2432efe26e08221b54884e05b
```

です。

### 今回の短縮が意味するもの

RAMIFIED-010 では、

```text
最大整環
PID
類数 1
巡回 Galois 自己同型
```

が整いました。

RAMIFIED-011A では、その巨大な設備を使いながら、最後は再び **元レベルの gcd** へ戻りました。

これはDkMathらしい閉路です。

```text
数体
  ↓
最大整環
  ↓
ideal
  ↓
PID
  ↓
元の gcd へ帰還
```

つまり、class number one は「ideal を長く追うため」に使われたのではありません。

> ideal を忘れて、再び二つの元の coprimality だけで戦える世界へ戻す

ために使われました。

## 新しい最短路：unit 群の生成定理は不要

RAMIFIED-011U のレポートでは、

```text
α と 1+α が全 unit group を生成する
```

あるいは、それと同等の大域 unit theorem が必要と見積もられています。

しかし、ここはさらに短くできます。

必要なのは、

```text
α と 1+α が unit group 全体を整数生成する
```

ことではありません。

必要なのは、

```text
α と 1+α が
unit modulo seventh powers の49類を生成する
```

ことだけです。

この違いは大きいです。

unit regulator、fundamental-unit index、全 unit の明示分類を回避できます。

## mod 7 の nilpotent 魔核

$\theta=\alpha-3$ なので、$\theta$ 基底で任意の元を、

$$
x=A+B\theta+C\theta^2
$$

と書きます。

Eisenstein relation は、

$$
\theta^3+7\theta^2+14\theta+7=0
$$

なので mod $7$ では、

$$
\boxed{\theta^3=0}
$$

です。

従って、

$$
\mathcal O_K/(7)\cong\mathbb F_7[\tau]/(\tau^3)
$$

という三層 nilpotent 環が現れます。

unit なら定数項 $A$ は非零です。したがって scalar $A$ を忘れて、

$$
A+B\tau+C\tau^2=A\left(1+x\tau+y\tau^2\right)
$$

と正規化できます。ここで、

$$
x=\frac BA,\qquad y=\frac CA
$$

です。

scalar は unit の seventh-power class 判定には不要です。

## 乗法を加法へ変える truncated log

二つの normalized unit を掛けると、

$$
(1+x\tau+y\tau^2)(1+x'\tau+y'\tau^2)=1+(x+x')\tau+(y+y'+xx')\tau^2
$$

です。

ここで、

$$
\boxed{\Lambda(1+x\tau+y\tau^2)=\left(x,\ y-\frac{x^2}{2}\right)}
$$

と定義します。

すると、

$$
\Lambda(uv)=\Lambda(u)+\Lambda(v)
$$

になります。

なぜなら第二成分は、

$$
y+y'+xx'-\frac{(x+x')^2}{2}=\left(y-\frac{x^2}{2}\right)+\left(y'-\frac{x'^2}{2}\right)
$$

と完全に線形化されるからです。

従って、

$$
\boxed{\Lambda:\mathcal O_K^\times\longrightarrow\mathbb F_7^2}
$$

という群準同型が得られます。

さらに標数 $7$ なので、

$$
\Lambda(u^7)=7\Lambda(u)=0
$$

です。

つまり $\Lambda$ は global unit の seventh-power class を観測する、二座標の魔法鏡です。

### Lean では quotient ring 自体を作らなくてよい

$\theta$ 基底座標は、既存の座標変換式から、

```text
A(x) = x.fst + 3*x.snd + 9*x.thd
B(x) = x.snd + 6*x.thd
C(x) = x.thd
```

です。

これらを `ZMod 7` へ cast し、

```lean
def thetaConst  (x : SevenRealCubicInt) : ZMod 7 := ...
def thetaLinear (x : SevenRealCubicInt) : ZMod 7 := ...
def thetaSquare (x : SevenRealCubicInt) : ZMod 7 := ...
```

とすればよい。

積について、

```text
A(xy) = A(x)A(y)
B(xy) = A(x)B(y) + B(x)A(y)
C(xy) = A(x)C(y) + B(x)B(y) + C(x)A(y)
```

を証明すれば、独自 quotient ring を構築せず直接 `projectiveLog` を定義できます。

unit の $A\ne0$ も、逆元との積の定数項、

$$
A(u)A(u^{-1})=1
$$

から直ちに従います。

## 49類は行列式 $1$ で閉じる

$\alpha=3+\theta$ なので、

$$
\alpha\equiv3+\tau\pmod7
$$

です。

scalar $3$ で正規化すると、

$$
3+\tau=3(1+5\tau)
$$

なので、

$$
\boxed{\Lambda(\alpha)=(5,5)}
$$

です。

同様に、

$$
1+\alpha=4+\theta
$$

なので、

$$
4+\tau=4(1+2\tau)
$$

より、

$$
\boxed{\Lambda(1+\alpha)=(2,5)}
$$

です。

この二つを列に持つ行列は、

$$
M=
\begin{pmatrix}
5&2\
5&5
\end{pmatrix}
$$

です。

その行列式は、

$$
\det M=25-10=15\equiv1\pmod7
$$

です。

従って、

$$
\boxed{\Lambda(\alpha),\Lambda(1+\alpha)\text{ は }\mathbb F_7^2\text{ の基底}}
$$

です。

これは49通りの brute-force 列挙より強いです。

```text
49ケースを decide する
```

のではなく、

```text
2×2 行列の determinant が 1
```

という一つの恒等式で全49類を閉じられます。

逆行列も、

$$
M^{-1}=
\begin{pmatrix}
5&5\
2&5
\end{pmatrix}
$$

と明示できます。

## なぜ大域側も正確に49類なのか

Mathlib の Dirichlet unit theorem は、unit modulo torsion が自由 $\mathbb Z$-加群であること、その rank、basis、fundamental system、unit の一意分解を提供しています。今回の体は totally real cubic なので unit rank は $2$ です。さらに Mathlib には、奇数次数の数体では torsion unit が $\pm1$ だけであり torsion order が $2$ になる定理があります。自由 rank $d$ の $\mathbb Z$-加群を $n$ 倍部分群で割った群の位数が $n^d$ である `ModN` API も存在します。([Lean Community][1])

unit 群を $U=\mathcal O_K^\times$ とします。

torsion は ${\pm1}$ で、指数 $7$ は奇数なので、

$$
1=1^7,\qquad -1=(-1)^7
$$

です。

従って torsion は seventh-power quotient に何も残しません。

自由部分は $\mathbb Z^2$ なので、

$$
U/U^7\cong(\mathbb Z/7\mathbb Z)^2
$$

となり、

$$
\boxed{|U/U^7|=49}
$$

です。

一方、local projective group $\mathbb F_7^2$ も49元です。

そして $\alpha,1+\alpha$ の像が基底なので、

$$
\overline\Lambda:U/U^7\longrightarrow\mathbb F_7^2
$$

は全射です。

49元から49元への全射なので全単射です。

従って、

$$
\boxed{u\in U^7\iff\Lambda(u)=0}
$$

が得られます。

### 重要な短縮

これは、

```text
α, 1+α が全 unit group の fundamental units である
```

ことを証明していません。

証明する必要もありません。

必要なのは、

```text
global quotient の元数 = 49
local quotient の元数  = 49
α,1+α の local images が基底
```

だけです。

つまり regulator や unit index は不要です。

## RAMIFIED source の unit は左右個別に消える

現在の source は、

$$
\eta_L=a-\alpha n
$$

$$
\eta_R=a+(1+\alpha)n
$$

です。

RAMIFIED-008 以降、

$$
n=7^4m^7
$$

なので、mod $7$ では $n=0$ です。

従って、

$$
\eta_L\equiv a\pmod7
$$

$$
\eta_R\equiv a\pmod7
$$

です。

つまり左右 source はどちらも projective nilpotent 成分を持ちません。

$$
\Lambda(\eta_L)=0,\qquad\Lambda(\eta_R)=0
$$

です。

一方 RAMIFIED-011A は、

$$
\eta_L=u_L\xi_L^7
$$

を持つので、

$$
0=\Lambda(\eta_L)=\Lambda(u_L)+7\Lambda(\xi_L)=\Lambda(u_L)
$$

です。

従って global criterion から、

$$
u_L=v_L^7
$$

です。

同様に、

$$
u_R=v_R^7
$$

です。

したがって、

$$
X_L=v_L\xi_L,\qquad X_R=v_R\xi_R
$$

と置けば、

$$
\boxed{\eta_L=X_L^7}
$$

$$
\boxed{\eta_R=X_R^7}
$$

となります。

relative unit $u_R/u_L$ だけではなく、**左右の unit を個別に消せます。**

これは前回予測した route より強いです。

## RAMIFIED-012 の最終形

次 checkpoint はかなり小さくできます。

```text
FLT7-RAMIFIED-011U / 012
projective nilpotent unit criterion
and exact source seventh powers
```

推奨 theorem surface：

```lean
def thetaConstModSeven
def thetaLinearModSeven
def thetaSquareModSeven

def unitNilpotentX
def unitNilpotentY

def projectiveLog :
    SevenRealCubicIntˣ →+ Additive (ZMod 7 × ZMod 7)

theorem projectiveLog_pow_seven :
    projectiveLog (u ^ 7) = 0

theorem projectiveLog_alpha :
    projectiveLog alphaUnit = (5, 5)

theorem projectiveLog_alphaAddOne :
    projectiveLog alphaAddOneUnit = (2, 5)

theorem projectiveLog_generator_det :
    5 * 5 - 2 * 5 = (1 : ZMod 7)

theorem unitClassModSeven_natCard :
    Nat.card UnitClassModSeven = 49

theorem unit_isSeventhPower_iff_projectiveLog_eq_zero :
    (∃ v, u = v ^ 7) ↔ projectiveLog u = 0
```

source 専用 bridge：

```lean
theorem projectiveLog_linearSource_eq_zero
    {a b : ℤ}
    (hb : (7 : ℤ) ∣ b) :
    projectiveLog
      (unitPartOfLinearSource ...) = 0
```

そして packet：

```lean
structure RamifiedRealCubicExactPowerPacket where
  upToUnit : RamifiedRealCubicUpToUnitPacket

  leftRoot : SevenRealCubicInt
  leftSource_eq :
    leftSource ... = leftRoot ^ 7

  rightRoot : SevenRealCubicInt
  rightSource_eq :
    rightSource ... = rightRoot ^ 7

  pureDifference_eq :
    rightRoot ^ 7 - leftRoot ^ 7 =
      normalizedAxis ^ 6 *
        normalizedWitness ... ^ 7
```

ここまで到達すれば、

$$
\boxed{X_R^7-X_L^7=\varpi^6Z^7}
$$

という純粋な second-case equation が Lean に固定されます。

## RAMIFIED-013 も valuation 理論を新設しなくてよい

次に必要な depth は、

```text
RHS          depth 13
Phi7         depth 3
root gap     depth 10
```

です。

ただし、実三次環用の一般 valuation API を大きく構築する必要はありません。

次のような exact divisibility packet で十分です。

```lean
def HasExactThetaDepth
    (x : SevenRealCubicInt) (k : ℕ) : Prop :=
  eisensteinAxis ^ k ∣ x ∧
    ¬ eisensteinAxis ^ (k + 1) ∣ x
```

### RHS depth $13$

`normalizedAxis` は $\theta$ と associated。

`normalizedWitness` は、

```text
unit × normalizedAxis × m
```

であり、$7\nmid m$ です。

従って、

$$
v_\theta(\varpi^6Z^7)=6+7=13
$$

です。

### gap が $\theta$ で割れる

$\mathcal O_K/(\theta)\cong\mathbb F_7$ なので、任意の元 $x$ に対し、

$$
x^7\equiv x\pmod\theta
$$

です。

従って、

$$
\theta\mid X_R^7-X_L^7
$$

なら、

$$
\boxed{\theta\mid X_R-X_L}
$$

です。

汎用補題として、

```lean
theorem eisensteinAxis_dvd_pow_seven_sub_self
    (x : SevenRealCubicInt) :
    eisensteinAxis ∣ x ^ 7 - x
```

を置くと使いやすいでしょう。

### cyclotomic quotient の depth $3$

$\delta=X_R-X_L$ と置きます。

$$
\Phi_7(X_R,X_L)=
7X_L^6+
21X_L^5\delta+
35X_L^4\delta^2+
35X_L^3\delta^3+
21X_L^2\delta^4+
7X_L\delta^5+
\delta^6
$$

です。

$\theta\mid\delta$ なので、第一項以外はすべて $\theta^4$ 以上です。

一方、

$$
\theta^3=-7(\theta+1)^2
$$

であり、$\theta+1$ と $X_L$ は $\theta$-unit です。

従って先頭項 $7X_L^6$ は exact depth $3$。

よって、

$$
\boxed{v_\theta(\Phi_7(X_R,X_L))=3}
$$

です。

積全体が depth $13$ なので、

$$
\boxed{v_\theta(X_R-X_L)=10}
$$

となります。

## depth $10$ から axis $3$ へ

gap を、

$$
X_R-X_L=u\theta^{10}D^7
$$

と書けたとします。

すると、

$$
u\theta^{10}D^7=u\theta^3(\theta D)^7
$$

です。

ここで、

$$
\Theta=u^{-2}\theta
$$

$$
W=u\theta D
$$

と置けば、

$$
\Theta^3W^7=u^{-6}\theta^3\cdot u^7\theta^7D^7

u\theta^{10}D^7
$$

です。

従って、

$$
\boxed{X_R-X_L=\Theta^3W^7}
$$

となります。

しかも $\Theta$ は $\theta$ と associated であり、

$$
|N(\Theta)|=7
$$

です。

つまり axis は壊れず、指数だけが、

$$
\boxed{6\longrightarrow3}
$$

へ落ちます。

これは真の自己相似 descent kernel です。

## もう一段先に見える七次円分世界

ここから先は推論ですが、depth 数列の理由まで見えます。

$\zeta$ を原始七乗根とすると、

$$
\alpha=1+\zeta+\zeta^{-1}
$$

です。

従って、

$$
\theta=\alpha-3=\zeta+\zeta^{-1}-2
$$

であり、

$$
\boxed{\theta=\zeta^{-1}(1-\zeta)^2}
$$

です。

$\lambda=1-\zeta$ と置けば、実三次側の $\theta$ は、完全七次円分体側の $\lambda^2$ に相当します。

したがって $\theta$-depth、

```text
13 / 10 / 3
```

は、完全円分体では、

```text
26 / 20 / 6
```

になります。

一方、

$$
X_R^7-X_L^7=
\prod_{k=0}^{6}(X_R-\zeta^kX_L)
$$

です。

$k=0$ の因子は、

$$
X_R-X_L
$$

で depth $20$。

$k\ne0$ なら、

$$
X_R-\zeta^kX_L=(X_R-X_L)+(1-\zeta^k)X_L
$$

です。

第一項は depth $20$、第二項は exact depth $1$ なので、各因子は exact depth $1$。

六個あるため、

$$
20+6=26
$$

です。

つまり、

$$
\boxed{13=10+3}
$$

という実三次 depth split は偶然ではありません。

完全七次円分体における、

$$
\boxed{26=20+1+1+1+1+1+1}
$$

の実部分体への圧縮像です。

これが、実三次世界で `cyclotomic quotient depth = 3` となる本当の理由です。

## 攻略路の現在地

```text
RAMIFIED-009
  実三次 norm 世界

RAMIFIED-010
  最大整環・PID・類数1

RAMIFIED-011A
  三共役 gcd
  → source = unit × seventh power

RAMIFIED-011U
  projective nilpotent log
  → unit class 49 ↔ F₇²

RAMIFIED-012
  source = exact seventh power

RAMIFIED-013
  depth 13 = 10 + 3
  → axis exponent 6 → 3

RAMIFIED-014 candidate
  real cubic axis θ
  ↔ cyclotomic axis (1-ζ)²
```

### 結論

新しい短い道は確かに見つかっています。

しかも短縮点は一つではありません。

```text
ideal exponent ledger
  → 三共役 gcd で消滅

fundamental-unit generation
  → quotient cardinality 49 で消滅

49-case brute force
  → 2×2 determinant 1 で消滅

一般 valuation API
  → exact divisibility packet で消滅
```

残る本丸は、

$$
\boxed{
U/U^7
\overset{\Lambda}{\cong}
\mathbb F_7^2
}
$$

です。

この一枚の unit-class bridge が閉じれば、RAMIFIED-012 と RAMIFIED-013 はほぼ直列で発動します。

そしてその先には、実三次の $13=10+3$ が、完全七次円分体の $26=20+6$ の影であることまで見えています。

[1]: https://leanprover-community.github.io/mathlib4_docs/Mathlib/NumberTheory/NumberField/Units/DirichletTheorem.html?utm_source=chatgpt.com "Mathlib.NumberTheory.NumberField.Units.DirichletTheorem"
