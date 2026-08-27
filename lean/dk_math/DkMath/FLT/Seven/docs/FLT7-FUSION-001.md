# FLT7-FUSION-001

## 判定：RAMIFIED ステージ終了です 🧙‍♀️✨️

**FLT7-RAMIFIED-013 は Outcome A。**

しかも今回は単に depth を計算しただけではありません。

```text
exact source seventh powers
        ↓
pure second-case equation
        ↓
exact depth 13 = 10 + 3
        ↓
axis-free cores の互いに素性
        ↓
PID seventh-power extraction
        ↓
unit absorption
        ↓
real-cubic axis drop
```

最終的に Lean は、

$$
X_R-X_L=\operatorname{droppedAxis}^3\operatorname{descentWitness}^7
$$

を固定しました。

`droppedAxis` は $\theta$ と associated、prime、exact $\theta$-depth $1$ です。これによって **ramified prime・最大整環・類数・unit class・exact depth・axis drop** の全問題が閉じました。

公開 PR head も報告どおり、

```text
73b9fb9adc087ea05f690068c0d289780cac335a
```

です。PR #65 は open / draft / mergeable です。

[PR に RAMIFIED 最終レビューを記録しました](https://github.com/Deskuma/dkmath/pull/65#issuecomment-5114463387)

---

## RAMIFIED が完成させたもの

RAMIFIED-001 から RAMIFIED-013 までを一本にすると、次の変換器が完成しています。

```text
terminal depth-one FLT7 packet
        ↓
quadratic ramified summit
        ↓
residual-root / compensation receiver
        ↓
quadratic root の再七乗抽出
        ↓
実三次 norm source
        ↓
最大整環・PID・類数1
        ↓
unit class 49 類の完全消去
        ↓
exact source seventh powers
        ↓
13 = 10 + 3
        ↓
real-cubic axis drop
```

入力は terminal ramified 世界。
出力は、

```text
RamifiedRealCubicAxisDropPacket
```

です。

これはもはや「ramified branch の観測」ではありません。

> terminal counterexample を、標準化された実三次 descent seed に変換する装置

です。

---

## $13=10+3$ の意味

完成した式は、

$$
X_R^7-X_L^7
=(X_R-X_L)\Phi_7(X_R,X_L)
$$

です。

右辺全体の $\theta$-depth は $13$。

$$
v_\theta(X_R-X_L)=10
$$

$$
v_\theta(\Phi_7(X_R,X_L))=3
$$

です。

この $3$ は、

$$
7=\theta^3\cdot\text{unit}
$$

から来ています。

そして $10$ は、

$$
10=3+7
$$

なので、axis の三乗と完全七乗へ再分解されます。

$$
\theta^{10}=\theta^3(\theta)^7
$$

これが axis exponent の、

$$
6\longrightarrow3
$$

という降下です。

重要なのは、unit がもう障害にならないことです。

任意の unit $u$ は、

$$
u=u^{-6}u^7
$$

と分けられるため、指数 $3$ 側と指数 $7$ 側へ吸収できます。

したがって **RAMIFIED-012 が最後の unit-class 戦**であり、RAMIFIED-013 では unit 群の分類が再発しませんでした。

---

## ひとつだけ置ける RAMIFIED エピローグ

RAMIFIED ステージは終了ですが、短い対称 corollary を一つ置く価値があります。

現在は gap 側について、

$$
X_R-X_L=A^3U^7
$$

を取り出しました。

しかし同じ coprime core extraction は quotient 側にも適用できます。

したがって、

$$
\Phi_7(X_R,X_L)=B^3V^7
$$

も得られるはずです。ここで $A,B$ は共に $\theta$ と associated です。

最終的には、

```text
root gap        = axis₁³ × seventhPower
seventh quotient = axis₂³ × seventhPower
```

という balanced split になります。

推奨する短い API は、

```lean
theorem exists_quotientCore_associated_pow_seven
    (p : RamifiedRealCubicDepthLedgerPacket) :
    ∃ t, Associated (t ^ 7) p.quotientCore

theorem nonempty_balancedAxisSplit
    (p : RamifiedRealCubicDepthLedgerPacket) :
    Nonempty RamifiedRealCubicBalancedAxisSplitPacket
```

です。

これは新しい RAMIFIED checkpoint ではなく、**RAMIFIED-013 の対称化された出口 API**です。

---

## 次は FUSION ステージ

ここから先の問題は ramification ではありません。

$$
\boxed{\text{実三次 descent seed を整数・二次・FLT7 chartへ戻す}}
$$

という融合問題です。

新しいステージ名は、

```text
FLT7-FUSION
```

でよいでしょう。

---

## FUSION-001：整数影の完全固定

現在すでに整数側には、

$$
r^7-l^7=7an(a+n)
$$

があります。

さらに、

$$
n=7^4m^7
$$

です。

inner root の primitive 性から、

$$
7\nmid a
$$

$$
7\nmid(a+n)
$$

$$
7\nmid m
$$

です。

従って、

$$
v_7(r^7-l^7)=5
$$

です。

また $l,r$ は互いに素な $7$-units なので、

$$
v_7(r^7-l^7)=v_7(r-l)+1
$$

となります。

よって、

$$
\boxed{v_7(r-l)=4}
$$

です。

さらに、

$$
r-l=7^4d
$$

$$
\Phi_7(r,l)=7E
$$

と置けば、

$$
\boxed{dE=a(a+n)m^7}
$$

です。

そして、

```text
gcd(d,E)=1

gcd(a,a+n)=1
gcd(a,m)=1
gcd(a+n,m)=1
```

となるため、新しい canonical 2×3 routing が作れます。

```text
                   |a|       |a+n|       |m|⁷
                ┌────────┬──────────┬──────────┐
|d|             │  d11   │   d12    │   U⁷     │
                ├────────┼──────────┼──────────┤
|E|             │  e11   │   e12    │   V⁷     │
                └────────┴──────────┴──────────┘
```

これが **integer shadow packet** です。

推奨構造：

```lean
structure RamifiedSignedRootDepthPacket : Type where
  axisDrop : RamifiedRealCubicAxisDropPacket

  signedLeftRoot : ℤ
  signedRightRoot : ℤ

  signedRoots_isCoprime :
    IsCoprime signedLeftRoot signedRightRoot

  gapRoot : ℤ
  quotientRoot : ℤ

  signedGap_eq :
    signedRightRoot - signedLeftRoot =
      7 ^ 4 * gapRoot

  signedQuotient_eq :
    signedSeventhQuotient signedRightRoot signedLeftRoot =
      7 * quotientRoot

  gapRoot_not_seven_dvd :
    ¬(7 : ℤ) ∣ gapRoot

  quotientRoot_not_seven_dvd :
    ¬(7 : ℤ) ∣ quotientRoot

  normalizedEquation :
    gapRoot * quotientRoot =
      innerFst * (innerFst + innerSnd) *
        innerSndRoot ^ 7
```

これなら `Norm` の加法性を仮定せずに閉じます。

---

## depth $10\to4$ は偶然ではない

`Norm` は非線形なので、

$$
N(X_R)-N(X_L)\ne N(X_R-X_L)
$$

です。

しかし、depth $10$ と depth $4$ は無関係でもありません。

実三次の $7$-進局所拡大では、

* ramification index は $3$
* different exponent は $2$

です。

したがって norm の first variation は、概念的には、

$$
\frac{10+2}{3}=4
$$

という depth 変換を持ちます。

つまり、

```text
algebraic gap theta-depth 10
        ↓ norm first variation
integer gap seven-depth 4
```

です。

Lean では一般局所体理論を持ち込まず、$\theta$ 座標で直接、

```lean
theorem norm_firstVariation_depth_ten
    (x core : SevenRealCubicInt)
    (hx : ¬ eisensteinAxis ∣ x)
    (hcore : ¬ eisensteinAxis ∣ core) :
    ∃ q r : ℤ,
      norm (x + 7 ^ 3 * eisensteinAxis * core) - norm x =
        7 ^ 4 * q + 7 ^ 5 * r
```

という形を狙えます。

そして integer shadow packet の exact depth $4$ が、先頭係数 $q$ の非零性を保証します。

したがって二つの証明は競合しません。

```text
整数 routing：
  exact nonvanishing を証明

norm first variation：
  なぜ depth 10 が depth 4 になるかを証明
```

この二つを合わせるのが本当の FUSION です。

---

## さらに強い FUSION：完全七次円分体

最も強い道は degree-six carrier です。

原始七乗根を $\zeta=\zeta_7$ とし、

$$
\lambda=1-\zeta
$$

と置きます。

実三次生成元を標準的に、

$$
\alpha=1+\zeta+\zeta^{-1}
$$

と同定すると、

$$
\theta=\alpha-3
=\zeta+\zeta^{-1}-2
=\zeta^{-1}(1-\zeta)^2
$$

です。

従って、

$$
\boxed{\theta\sim\lambda^2}
$$

です。

今回の root gap は $\theta$-depth $10$ なので、完全円分体では $\lambda$-depth $20$ です。

次を置きます。

$$
\beta=X_R-\zeta X_L
$$

すると、

$$
\beta=(X_R-X_L)+(1-\zeta)X_L
$$

です。

第一項は $\lambda$-depth $20$。
第二項は、$X_L$ が axis-unit なので exact $\lambda$-depth $1$。

従って、

$$
\boxed{v_\lambda(\beta)=1}
$$

です。

さらに六つの Galois 共役の積は、

$$
\prod_{k=1}^{6}(X_R-\zeta^kX_L)
=\Phi_7(X_R,X_L)
$$

です。

実三次側では quotient depth が $3$。$\theta\sim\lambda^2$ なので、完全円分側では depth $6$ です。

つまり、

```text
6 conjugate linear factors
each exact lambda-depth 1
```

という完全分解が現れます。

理想的な FUSION theorem は、

$$
\boxed{X_R-\zeta X_L=\Lambda\Gamma^7}
$$

です。

ここで $\Lambda$ は $\lambda$ と associated な prime axis。

これが得られれば、実三次の axis drop は、完全七次円分体の **linear-factor Kummer packet**へ変わります。

```text
real cubic:
  Phi₇ = axis³ × seventh power

full cyclotomic:
  XR - ζ XL = axis × seventh power
```

この一段持ち上げが、現在別々に存在している、

```text
判別式 -7 の quadratic world
判別式 49 の real-cubic world
```

を同じ degree-six 世界で融合する道です。

---

## FUSION の本当の再構成壁

現在、

$$
X_L^7=\eta_L
$$

$$
X_R^7=\eta_R
$$

であり、$\eta_L,\eta_R$ は、

```text
1, α で張られる二次元 source plane
```

に属します。

しかし七乗根 $X_L,X_R$ は一般の三座標元です。

したがって、次に分類すべきなのは、

> 七乗が source plane に戻る三次整数は、どの座標 sector に属するか。

です。

これは次の形です。

```lean
def IsSourcePlane (x : SevenRealCubicInt) : Prop :=
  x.thd = 0

theorem seventhRoot_sourcePlane_classification
    (x : SevenRealCubicInt)
    (hx : IsSourcePlane (x ^ 7)) :
    ...
```

可能な Outcome は三つです。

```text
A. root 自身も source plane
   → 整数・二次 chart を直接再構成

B. 有限個の unit-translated plane
   → finite unit-sector audit

C. 一般三座標 root が残る
   → full cyclotomic fusion が必要
```

ここが `FUSION-002` の正確な reconnaissance です。

---

## 新しいフェーズ地図

```text
========== RAMIFIED COMPLETE ==========

FUSION-001
  integer signed-root depth 4
  +
  norm first-variation bridge

FUSION-002
  seventh-root source-plane classification

FUSION-003A
  direct integer/quadratic chart reconstruction

or

FUSION-003B
  full cyclotomic carrier
  beta = axis * seventh power

FUSION-004
  new primitive FLT7 packet

FUSION-005
  strict well-founded decrease

DESCENT CLOSURE
  AwayDescentClosureProvider

PUBLIC FLT7
```

## 最終結論

**はい。RAMIFIED ステージは終了です。**

43分34秒で閉じたのは、

```text
exact depth
coprime core
PID extraction
unit absorption
axis drop
```

の最後の五枚です。

これ以後に `RAMIFIED-014` と名前を付けると、既に閉じた ramified 問題と、未解決の reconstruction 問題が混ざります。

次は明確に、

$$
\boxed{\text{FLT7-FUSION-001}}
$$

です。

そして最初の一手は、重い full cyclotomic field の構築ではありません。

> まず整数 signed-root depth $4$ を既存恒等式だけで固定し、
> 同じ packet 上で algebraic depth $10$ と結び付ける。

これが最短路です。

その直後に、degree-six fusion へ進むか、source-plane rigidity で直接整数 chart を回収できるかを判定する。

RAMIFIED の魔核は、完全にこちらの手に落ちました。
