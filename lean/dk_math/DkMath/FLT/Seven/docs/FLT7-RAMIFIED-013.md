# FLT7-RAMIFIED-013

## RAMIFIED-012 総合判定

**Outcome A、完全採用です。** 🧙‍♀️✨️

予測した最短路が、そのまま Lean に認可されました。

```text
unit × seventh power
        ↓ projectiveLog
49 global classes ≃ F₇²
        ↓ zero class
exact seventh power
```

そして左右の source が個別に、

$$
\eta_L=X_L^7
$$

$$
\eta_R=X_R^7
$$

へ昇格し、純粋な second-case equation、

$$
X_R^7-X_L^7=\varpi^6Z^7
$$

が完成しました。

PR head も報告どおり `5394efd26624761bbc30ee39bdd1390a9e38d0d6`。PR #65 は open・draft・mergeable です。

[PR にレビューを記録しました](https://github.com/Deskuma/dkmath/pull/65#issuecomment-5110497305)

## 結論：RAMIFIED は、あと一門で終わる

正確には、

```text
RAMIFIED-012
  unit/class obstruction の終点

RAMIFIED-013
  ramified axis arithmetic の終点
```

です。

したがって、**RAMIFIED-012 だけではまだ終了ではない**。

しかし RAMIFIED-013 が、

```text
depth 13 = depth 10 + depth 3
root gap = axis³ × seventh power
```

まで閉じれば、**ramified algebra phase は終了**と宣言してよいです。

その後の敵は ramified arithmetic ではありません。

```text
real-cubic descent seed
        ↓
integer / quadratic / away packet への再構成
```

という別フェーズです。

現行 ROADMAP も、RAMIFIED-013 の depth split と axis drop を、新しい Fermat counterexampleや recursive descent closure とは分離して扱う方針です。

## RAMIFIED-013 は二段に分けるべき

一つ重要な補正があります。

単に、

$$
v_\theta(X_R-X_L)=10
$$

まで証明しても、まだ、

$$
X_R-X_L=\text{unit}\cdot\theta^{10}T^7
$$

とは言えません。

付値 $10$ は「$\theta$ の住所」しか決めません。
$\theta$ 以外の素因子が七乗単位で配置されていることも必要です。

従って RAMIFIED-013 は内部的に二段です。

### RAMIFIED-013A — exact depth ledger

記号を、

$$
\Delta=X_R-X_L
$$

$$
\Phi_7(X_R,X_L)=\frac{X_R^7-X_L^7}{X_R-X_L}
$$

とします。

証明すべき exact depth は、

$$
v_\theta(\varpi^6Z^7)=13
$$

$$
v_\theta(\Phi_7(X_R,X_L))=3
$$

$$
v_\theta(\Delta)=10
$$

です。

現在の `normalizedWitness` は axis を一つ含み、元の整数 witness は $7$-unitです。source difference が `normalizedAxis^6 * normalizedWitness^7` になることは既に固定されています。

#### RHS depth $13$

`normalizedAxis` は $\theta$ と associate、`normalizedWitness` は、

```text
unit × normalizedAxis × 7-unit
```

です。

従って、

$$
6+7\cdot1=13
$$

です。

#### quotient depth $3$

$\delta=X_R-X_L$ とし、$\theta\mid\delta$ を得た後、

$$
\Phi_7(X_R,X_L)=7X_L^6+21X_L^5\delta+35X_L^4\delta^2+\cdots+\delta^6
$$

と展開します。

$X_L$ は $\theta$-unitです。

* 第一項 $7X_L^6$ は exact depth $3$
* 残りはすべて depth $4$ 以上

なので、

$$
v_\theta(\Phi_7)=3
$$

です。

#### root gap depth $10$

積の exact depth が $13$、quotient が $3$ なので、

$$
v_\theta(\Delta)=13-3=10
$$

です。

### RAMIFIED-013B — away-axis seventh-power split

次に必要なのは、

```text
Δ / θ¹⁰
Φ₇ / θ³
```

が互いに素であることです。

そのためにはまず、

$$
\gcd(X_L,X_R)=1
$$

を証明する。

これは短く閉じる見込みです。

左右 source は、

$$
\eta_L=a-\alpha n
$$

$$
\eta_R=a+(1+\alpha)n
$$

であり、差は ramified axis $\times n$ です。

共通素因子が $n$ を割れば $a$ も割り、primitive 性に反します。ramified axis を割る場合も、source は residue field 上で非零 scalar $a$ なので不可能です。

よって source は coprime。さらに、

$$
X_L^7=\eta_L,\qquad X_R^7=\eta_R
$$

なので $X_L,X_R$ も coprime です。

すると一般的な七乗差の gcd 原理により、

$$
\gcd(X_R-X_L,\Phi_7(X_R,X_L))
$$

の非単元部分は ramified axis だけです。

exact depth を除去すれば、

$$
\gcd\left(\frac{\Delta}{\theta^{10}},\frac{\Phi_7}{\theta^3}\right)=1
$$

となります。

一方、両者の積は、unit を除けば七乗です。

PID 上の coprime-power extraction により、

$$
\Delta=u\theta^{10}T^7
$$

を得ます。

ここで、

$$
\theta^{10}=\theta^3(\theta)^7
$$

です。

任意の unit $u$ に対し、

$$
u=u^{-6}u^7
$$

なので、

$$
\Theta=u^{-2}\theta
$$

$$
W=u\theta T
$$

と置けば、

$$
\Theta^3W^7=u\theta^{10}T^7
$$

です。

従って最終的に、

$$
\boxed{X_R-X_L=\Theta^3W^7}
$$

を得ます。

しかも $\Theta$ は $\theta$ と associate で、

$$
|N(\Theta)|=7
$$

です。

## ここで unit 問題は再発しない

これは重要です。

RAMIFIED-012 では source equation が、

$$
\eta=u\xi^7
$$

だったため、unit $u$ 自身が七乗かどうかを決める必要がありました。

しかし RAMIFIED-013 の最終形は、

$$
u\theta^3T^7
$$

です。

指数 $3$ と $7$ は互いに素なので、任意の unit は axis の三乗側と witness の七乗側へ自動的に分配できます。

したがって、

> **RAMIFIED-012 が本当に最後の unit-class checkpoint**

です。

RAMIFIED-013 で第二の Dirichlet unit theorem や49類監査は発生しません。

## 推奨 packet

```lean
structure RamifiedRealCubicAxisDropPacket : Type where
  exactPower : RamifiedRealCubicExactPowerPacket

  rootGap : SevenRealCubicInt
  quotient : SevenRealCubicInt

  roots_isCoprime :
    IsCoprime exactPower.leftRoot exactPower.rightRoot

  factorization :
    exactPower.rightRoot ^ 7 -
        exactPower.leftRoot ^ 7 =
      rootGap * quotient

  rhs_exactDepth :
    HasExactThetaDepth
      (exactPower.upToUnit.normPacket.normalizedAxis ^ 6 *
        exactPower.upToUnit.normPacket.normalizedWitness ^ 7)
      13

  quotient_exactDepth :
    HasExactThetaDepth quotient 3

  rootGap_exactDepth :
    HasExactThetaDepth rootGap 10

  normalizedFactors_isCoprime :
    IsCoprime
      (rootGap / theta ^ 10)
      (quotient / theta ^ 3)

  droppedAxis : SevenRealCubicInt
  descentWitness : SevenRealCubicInt

  droppedAxis_associated :
    Associated droppedAxis theta

  rootGap_eq :
    rootGap = droppedAxis ^ 3 * descentWitness ^ 7
```

Lean では `/` より、存在 witness による因子分解の方が扱いやすいでしょう。

```lean
∃ gapCore quotientCore,
  rootGap = theta^10 * gapCore ∧
  quotient = theta^3 * quotientCore ∧
  IsCoprime gapCore quotientCore
```

と置く形が安全です。

## RAMIFIED-009B は 013 の影になる可能性

ここでも新しい短路があります。

RAMIFIED-009B は、整数 signed roots $l,r$ について、

$$
v_7(r-l)=4
$$

を証明する予定でした。

一方 RAMIFIED-012 の exact roots について、norm の乗法性から、

$$
N(X_L)^7=l^7
$$

$$
N(X_R)^7=r^7
$$

です。

七乗は整数上で単射なので、

$$
N(X_L)=l,\qquad N(X_R)=r
$$

となります。

従って、

$$
\boxed{r-l=N(X_R)-N(X_L)}
$$

です。

RAMIFIED-013 が、

$$
v_\theta(X_R-X_L)=10
$$

を与えれば、cubic norm の一次変化を展開することで、

$$
v_7(N(X_R)-N(X_L))=4
$$

が導ける可能性が高い。

つまり、

```text
real-cubic gap depth 10
        ↓ norm projection
integer signed-root gap depth 4
```

です。

この bridge が閉じれば、独立予定だった RAMIFIED-009B の主要 depth theorem は、RAMIFIED-013 の corollary になります。

```text
RAMIFIED-009B Outcome B:
  stronger real-cubic axis-drop theorem made
  the separate integer depth proof unnecessary
```

となる可能性があります。

routing 部分だけを補助 ledger として残せばよい。

## RAMIFIED 後の本当の敵

axis drop が完成しても、まだ FLT7 ではありません。

現在得られるのは、

$$
X_R^7-X_L^7=\varpi^6Z^7
$$

から、

$$
X_R-X_L=\Theta^3W^7
$$

という **real-cubic descent seed**です。

しかし既存の `AwayDescentReconstructionSeed` は、新しい正の自然数 triple、

$$
x'^7+y'^7=z'^7
$$

と、その away coordinate normal form を要求しています。

現在の roots $X_L,X_R$ は三次整数環の元であって、自然数 endpoint ではありません。

既存の descent audit は、terminal exponent $1$ では reconstruction seed が数学的に存在できないこと、lifted branchだけが provider 構成対象になることを既に証明しています。

従って RAMIFIED の後には、明確な新フェーズが必要です。

```text
FLT7-CUBIC-DESCENT / RECONSTRUCTION
```

その中心問題は、

> axis-drop packet を、新しい away packetへ戻せるか。
> 戻せなければ、その失敗自体が terminal obstruction になるか。

です。

## さらに深い構造：二次世界と三次世界の合流

ここからは Lean 未固定の数学的推論ですが、次の道が非常に自然です。

FLT7 ではすでに二つの部分体が現れています。

```text
quadratic side:
  discriminant -7
  TraceOneInt
  quadratic sevenAxis

real-cubic side:
  discriminant 49
  SevenRealCubicInt
  cubic axis theta
```

これらは、七次円分体 $\mathbb Q(\zeta_7)$ の、

* 二次部分体
* 最大実三次部分体

です。

完全円分体の ramified axis を、

$$
\lambda=1-\zeta_7
$$

とすると、実三次 axis は、

$$
\theta=\zeta_7+\zeta_7^{-1}-2=\zeta_7^{-1}(1-\zeta_7)^2
$$

なので、

$$
\theta\sim\lambda^2
$$

です。

一方、quadratic sevenAxis は完全円分体内で、

$$
\text{quadraticAxis}\sim\lambda^3
$$

になるはずです。

つまりDkMathは既に、

```text
λ² を観測する実三次脳
λ³ を観測する二次脳
```

を別々に構築しています。

そして、

$$
\gcd(2,3)=1
$$

です。

これは極めて示唆的です。

> 二次 axis と三次 axis を同じ degree-six carrier に埋めれば、primitive axis $\lambda$ 自身を復元できる。

これが、ramified descent seed を元の FLT7 endpoint 世界へ戻す欠落橋である可能性があります。

## 次フェーズ候補

RAMIFIED-013 完了後は、`RAMIFIED-014` と延命するより、別名へ切り替えるのがよいです。

```text
FLT7-CYCLOTOMIC-FUSION-000
```

まず read-only reconnaissance。

目標は二経路の比較です。

### Route A — source-plane rigidity

```text
XL^7 と XR^7 は 〈1, α〉source plane 上
        ↓
XL, XR 自身の可能な座標 sector を分類
        ↓
新しい整数 endpoint を復元
```

これが短く閉じるなら、full cyclotomic carrier は不要です。

### Route B — degree-six fusion

```text
TraceOneInt(-2)
      ↘
       SevenCyclotomicInt
      ↗
SevenRealCubicInt
```

証明目標：

```text
quadratic axis ↦ unit * lambda^3
cubic axis     ↦ unit * lambda^2
theta          ↦ unit * lambda^2
```

その後、

$$
X_R^7-X_L^7=\prod_{k=0}^{6}(X_R-\zeta_7^kX_L)
$$

を使います。

実三次側の、

$$
13=10+3
$$

は、完全円分体では、

$$
26=20+1+1+1+1+1+1
$$

の圧縮像です。

* $k=0$ の gap factor が depth $20$
* 残る六因子が各 depth $1$

という完全な linear-factor ledgerになります。

この構造は reconstruction / Kummer descent へ最も自然につながります。

## フェーズ境界

最もきれいな区切りはこれです。

```text
RAMIFIED-012
  exact source seventh powers

RAMIFIED-013A
  exact depth 13/10/3

RAMIFIED-013B
  away-axis coprime splitting
  axis exponent 6 → 3

RAMIFIED-013C
  optional norm-shadow bridge
  cubic depth 10 → integer depth 4

========== RAMIFIED PHASE COMPLETE ==========

CYCLOTOMIC-FUSION / RECONSTRUCTION
  quadratic axis λ³
  real-cubic axis λ²
  full axis λ
  smaller packet or terminal obstruction
```

## 最終結論

**RAMIFIED-012 は理想どおり完全決着。**

そして、

$$
\boxed{\text{RAMIFIED は RAMIFIED-013B で終了できる}}
$$

です。

ただし、その意味は、

```text
ramified branch contradiction completed
```

ではありません。

正確には、

```text
ramified terminal counterexample
        ↓
canonical real-cubic descent seed
```

への変換が完成する、という意味です。

その後は敵の名前が変わります。

> ramified prime の分析ではなく、
> 二次・三次の二つの部分世界から、degree-six の完全な七次円分世界を再構成する問題。

わっちらは、知らぬ間に Kummer 世界の二つの半身を別々に完成させていました。

RAMIFIED-013 は、その二つをつなぐ扉の前まで運ぶ、最後の ramified 術式です。
