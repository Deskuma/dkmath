# FLT7-FUSION-003-CYCLIC result review and next

## 総合判定

### FUSION-003-CYCLIC は完成です

Lean は現在、次を完全に固定しています。

* routing cycle の三つの margin 恒等式
* visible $\mu_3$ twist、hidden $\mu_3$ twist、column $\mu_2$ gauge
* unit-shadow だけからの再構成が一意でないこと
* $(\kappa_{12}/\kappa_{23})^2=\tau^2$
* 実三次 Galois 回転による depth-$10$ residue の $4$ 倍作用
* ${-2m,-m,3m}$ の三相 orbit
* `relativeRealIndex(k)=1` の fibre が ${\tau,-\tau}$ であること

これらの到達点と、「二つの位数 $3$ の作用はまだ intertwining されていない」という停止境界は、実装レポートにも正確に記録されています。

ただし、最大推論の結論は一段先です。

> 次に証明すべきものは、real-cubic rotation が routing board の visible twist か hidden twist か、ではありません。

**canonical routing board は Galois 回転で動かない**と考えるのが自然です。

そして回転が本当に作用する対象は、routing cell ではなく、

> 六つの cyclotomic linear factor を二つずつ束ねた、三つの real conjugate-pair carrier

です。

---

## 1. rotation-routing naturality の正体

canonical routing は、

```text
gapRoot
quotientRoot
a
a+n
m^7
```

という整数 margin から作る gcd 分解です。今回のレポート自身も、抽象 unit-shadow は非一意だが、元の自然数 gcd routing は canonical であると明記しています。

一方、`rotateEquiv` は実三次環の Galois 自己同型です。線形 source の三つの共役積が整数 norm になること、また三つの共役 source が pairwise coprime であることは既に DkMath にあります。

ここから導かれる自然な図式は、

```text
rotated algebraic lift
          |
          | norm / integer shadow
          v
same signedDepth packet
          |
          v
same canonical gcd routing
```

です。

つまり Galois $\mu_3$ は routing board を横に動かす作用ではなく、

> 固定された integer routing base の上にある algebraic fibre の deck transformation

です。

したがって非自明な rotation が canonical board 上の `cyclePhaseTwist` や `hiddenRowTwist` に一致する可能性は低いです。

これらの twist は抽象 `ActiveUnitBoard` を実際に別の board へ動かします。visible twist は二つの cycle ratio を共通の $\omega$ 倍にし、hidden twist は margins と cycles を保ったまま各 cell を変えます。

canonical gcd routing を同じ整数 margin から再計算すれば、元の board へ戻るはずです。

よって厳密な判定は、

```text
visible twist ではない
hidden twist でもない
routing projection は不変
```

になると予測します。

---

## 2. 六因子を三つの real pair carrier へ圧縮できる

`signedDepth` の整数 root を、

$$
r=\operatorname{signedRightRoot},\qquad l=\operatorname{signedLeftRoot}
$$

とします。

既に、

$$
r^7-l^7=(r-l)\operatorname{signedSeventhQuotient}(r,l)
$$

および、

$$
r-l=7^4d,\qquad\operatorname{signedSeventhQuotient}(r,l)=7e
$$

が packet に保存されています。

ここで、

$$
T=r^2+rl+l^2,\qquad S=rl
$$

と置きます。

実三次環の generator $\alpha$ は、

$$
\alpha^3=2\alpha^2+\alpha-1
$$

を満たします。

その三つの共役を、

$$
\alpha_0=\alpha,\qquad\alpha_1=\sigma(\alpha),\qquad\alpha_2=\sigma^2(\alpha)
$$

とし、三つの real pair carrier を、

$$
P_i=T-\alpha_iS
$$

と定義します。

すると $\alpha_i$ が多項式 $X^3-2X^2-X+1$ の三根なので、

$$
P_0P_1P_2=T^3-2T^2S-TS^2+S^3
$$

です。

右辺を展開すると、

$$
T^3-2T^2S-TS^2+S^3=r^6+r^5l+r^4l^2+r^3l^3+r^2l^4+rl^5+l^6
$$

となります。

したがって、

$$
\boxed{P_0P_1P_2=\operatorname{signedSeventhQuotient}(r,l)=7e}
$$

です。

これは六つの因子、

$$
r-\zeta^kl\qquad(k=1,\ldots,6)
$$

を複素共役 $k\leftrightarrow-k$ で二つずつ束ねた三因子の積です。

つまり full degree-$6$ carrier を導入する前に、現在の `SevenRealCubicInt` の中だけで **real Kummer pair carrier** を構築できます。

---

## 3. 三つの carrier はすべて exact $\theta$-depth $1$

$\theta=\alpha-3$ と置きます。

現在 Lean は、

$$
\sigma(\theta)=\theta^2+4\theta=\theta(\theta+4)
$$

を固定しました。

三つの共役 axis は、次の形になります。

$$
\alpha_0-3=\theta
$$

$$
\alpha_1-3=\theta(\theta+4)
$$

$$
\alpha_2-3=\theta(\theta^2+6\theta+9)
$$

よって unit quotient を、

$$
u_0=1,\qquad u_1=\theta+4,\qquad u_2=\theta^2+6\theta+9
$$

と置けます。

$\alpha=\theta+3$ を使えば、さらに簡潔に、

$$
u_0=1,\qquad u_1=1+\alpha,\qquad u_2=\alpha^2
$$

です。

これらの $\theta$ residue は、

$$
\overline{u_0}=1,\qquad\overline{u_1}=4,\qquad\overline{u_2}=2
$$

です。

一方、

$$
P_i=T-\alpha_iS=(r-l)^2-(\alpha_i-3)rl
$$

なので、

$$
P_i=(r-l)^2-\theta u_i rl
$$

です。

`r-l=7^4d` と、既存の $7=\theta^3u_\theta$ を使うと、

$$
(r-l)^2=7^8d^2=\theta^{24}u_\theta^8d^2
$$

です。

したがって、

$$
P_i=\theta C_i
$$

ただし、

$$
C_i=\theta^{23}u_\theta^8d^2-u_i rl
$$

です。

第一項は $\theta$ で消えるので、

$$
\mathrm{thetaResidue}(C_i)=-\overline{u_i},\overline r,\overline l
$$

となります。

これは division-free に実装できます。

---

## 4. 次に必要な小補題：signed roots は $a^3$

ここはまだ Lean に固定されていない、次の最短補題です。

`normPacket` の source equations と $7\mid n$ から、

$$
l^7\equiv a^3\pmod7
$$

$$
r^7\equiv a^3\pmod7
$$

です。

$\mathbf F_7$ では $x^7=x$ なので、

$$
\boxed{l\equiv r\equiv a^3\pmod7}
$$

です。

$7\nmid a$ より、

$$
rl\equiv a^6\equiv1\pmod7
$$

となります。

従って三つの pair core residue は、

$$
\boxed{\mathrm{thetaResidue}(C_0)=-1}
$$

$$
\boxed{\mathrm{thetaResidue}(C_1)=-4=3}
$$

$$
\boxed{\mathrm{thetaResidue}(C_2)=-2=5}
$$

です。

これは各 $P_i$ が **正確に** $\theta$-depth $1$ であることも示します。

---

## 5. `quotientRoot ≡ 1` の構造的再証明

三因子の積から、

$$
P_0P_1P_2=\theta^3C_0C_1C_2=7e
$$

です。

既存の Eisenstein 関係は、

$$
\theta^3=-7(\theta+1)^2
$$

です。

よって $7$ を消去すると、

$$
-(\theta+1)^2C_0C_1C_2=e
$$

です。

residue を取ると、

$$
-\left((-1)(-4)(-2)\right)=1
$$

です。

したがって、

$$
e\equiv1\pmod7
$$

です。

これは現在の `quotientRoot_modSeven_eq_one` の別証明になります。現実装では first variation によって同結果を得ています。

新証明は、

```text
seven cyclotomic quotient
  = three real pair carriers
  = theta^3 * three unit cores
```

という factor geometry から $e\equiv1$ を説明します。

これは極めて強い **fusion certificate** になります。

---

## 6. $\tau^2$ が三つの pair carrier から一つを選ぶ

現在の `relativeRealIndex` は、

$$
\operatorname{relativeRealIndex}(k)=\left(\frac{k}{\tau}\right)^2
$$

であり、

$$
\operatorname{relativeRealIndex}(k)=1\iff k=\tau\ \lor\ k=-\tau
$$

を証明しています。

これは絶対 pair index $k^2$ が、

$$
k^2=\tau^2
$$

である pair を選ぶことと同値です。

三つの pair phase は、

$$
1,\quad4,\quad2
$$

であり、これは $\mu_3$ の全要素です。

したがって明示的 equivalence、

$$
\operatorname{PairPhase}:\operatorname{Fin}3\simeq\mu_3
$$

を、

$$
0\mapsto1,\qquad1\mapsto4,\qquad2\mapsto2
$$

として定義できます。

そして、

$$
i_\tau:=\operatorname{PairPhase}^{-1}(\tau^2)
$$

とすれば、選択された pair core は、

$$
C_\tau=C_{i_\tau}
$$

です。

その residue は、

$$
\boxed{\mathrm{thetaResidue}(C_\tau)=-\tau^2}
$$

です。

この時点で、実際の conjugate pair ${\tau,-\tau}$ が **具体的な real-cubic factor** として選択されます。

まだ $+\tau$ と $-\tau$ のどちらか一方は選んでいません。これは現在の `relativeRealIndex` の意味と完全に一致します。

---

## 7. quadratic jet との直接融合

現在の paired theta jet は、

$$
\frac{V}{A}=-3\tau^2
$$

を証明しています。

一方、選択された pair core は、

$$
\mathrm{thetaResidue}(C_\tau)=-\tau^2
$$

です。

従って、

$$
\boxed{\frac{V}{A}=3\,\mathrm{thetaResidue}(C_\tau)}
$$

となります。

これは求めていた作用比較よりも強いです。

```text
integer signed seventh quotient
        ↓
real cyclotomic pair carrier
        ↓ phase τ²
selected normalized pair core
        ↓
quadratic theta jet V/A
```

routing twist を介さず、integer quotient と algebraic quadratic jet が直接接続されます。

---

## 8. pair cores は pairwise coprime になる可能性が高い

さらに一歩先まで進めます。

三つの core は共通項、

$$
H=\theta^{23}u_\theta^8d^2
$$

を持ち、

$$
C_i=H-u_i rl
$$

です。

よって、

$$
C_i-C_j=-(u_i-u_j)rl
$$

です。

三つの unit 差は、

$$
u_1-u_0=\alpha
$$

$$
u_2-u_1=\alpha^2-\alpha-1
$$

$$
u_2-u_0=\alpha^2-1
$$

です。

既存の explicit norm へ代入すると、それぞれの norm は、

$$
-1,\qquad-1,\qquad1
$$

となります。

つまり全て global unit です。

したがって共通素因子 $q\mid C_i,C_j$ があれば、

$$
q\mid rl
$$

です。

また、

$$
q\mid C_i+u_i rl=H
$$

なので、$\theta$ を除けば、

$$
q\mid d
$$

です。

一方、$r,l$ は coprime で、

$$
r-l=7^4d
$$

ですから、$rl$ と $d$ は coprime になるはずです。

従って、

$$
\boxed{\operatorname{IsCoprime}(C_i,C_j)}
$$

が証明できる可能性が非常に高いです。

これは real-pair Kummer extraction に必要な核心です。

---

## 次の実装方針

### FUSION-003D — Real Pair Carrier

新規モジュール：

```text
SevenRamifiedFusionRealPairCarrier.lean
```

推奨実装順は次です。

#### Event 1 — signed root residues

```lean
theorem signedLeftRoot_modSeven_eq_innerFst_cube
    (p : RamifiedSignedRootDepthPacket) :
    (p.signedLeftRoot : ZMod 7) =
      (p.innerFst : ZMod 7) ^ 3
```

```lean
theorem signedRightRoot_modSeven_eq_innerFst_cube
    (p : RamifiedSignedRootDepthPacket) :
    (p.signedRightRoot : ZMod 7) =
      (p.innerFst : ZMod 7) ^ 3
```

```lean
theorem signedRoots_product_modSeven_eq_one
    (p : RamifiedSignedRootDepthPacket) :
    ((p.signedRightRoot * p.signedLeftRoot : ℤ) : ZMod 7) = 1
```

#### Event 2 — cyclic alpha and axis units

```lean
def cyclicAlpha : Fin 3 → SevenRealCubicInt
def pairAxisUnit : Fin 3 → SevenRealCubicInt
def pairPhase : Fin 3 → SevenTernarySector
```

固定値：

```text
cyclicAlpha 0 = alpha
cyclicAlpha 1 = alpha^2 - 2*alpha
cyclicAlpha 2 = -alpha^2 + alpha + 2

pairAxisUnit 0 = 1
pairAxisUnit 1 = 1 + alpha
pairAxisUnit 2 = alpha^2

pairPhase 0 = 1
pairPhase 1 = 4
pairPhase 2 = 2
```

証明：

```lean
cyclicAlpha i - 3 = eisensteinAxis * pairAxisUnit i
```

#### Event 3 — real pair carriers

```lean
def realPairCarrier
    (p : RamifiedSignedRootDepthPacket) (i : Fin 3) :
    SevenRealCubicInt :=
  T - cyclicAlpha i * S
```

積の定理：

```lean
theorem realPairCarrier_product_eq_signedQuotient
```

#### Event 4 — exact theta-depth one

```lean
def realPairCore
    (p : RamifiedSignedRootDepthPacket) (i : Fin 3) :
    SevenRealCubicInt :=
  eisensteinAxis ^ 23 *
      thetaSevenUnit ^ 8 *
      (p.gapRoot : SevenRealCubicInt) ^ 2 -
    pairAxisUnit i *
      ((p.signedRightRoot * p.signedLeftRoot : ℤ) :
        SevenRealCubicInt)
```

```lean
theorem realPairCarrier_eq_theta_mul_core
```

```lean
theorem realPairCore_thetaResidue
    (p) (i) :
    thetaResidue (realPairCore p i) =
      -(pairPhase i : ZMod 7)
```

#### Event 5 — quotient sector certificate

```lean
theorem pairCore_product_eq_quotientRoot
```

目標形：

```text
-(theta + 1)^2 * C0*C1*C2 = quotientRoot
```

そこから `quotientRoot_modSeven_eq_one` の第二証明を作ります。

#### Event 6 — phase selection

```lean
def pairPhaseEquiv : Fin 3 ≃ SevenTernarySector
```

```lean
def selectedPairIndex
    (p : RamifiedPairedThetaRootJetPacket) : Fin 3 :=
  pairPhaseEquiv.symm p.rightUnitSectorAddress.2
```

```lean
theorem selectedPairCore_thetaResidue
    (p : RamifiedPairedThetaRootJetPacket) :
    thetaResidue
        (realPairCore p.signedDepth p.selectedPairIndex) =
      -p.fusionSlope ^ 2
```

#### Event 7 — quadratic fusion

```lean
theorem normalizedQuadraticJet_eq_three_mul_selectedPairResidue
    (p : RamifiedPairedThetaRootJetPacket) :
    (p.right.thetaSquareCore : ZMod 7) /
        (p.right.thetaConst : ZMod 7) =
      3 * thetaResidue
        (realPairCore p.signedDepth p.selectedPairIndex)
```

#### Event 8 — coprimality reconnaissance

```lean
theorem pairAxisUnit_sub_isUnit
```

```lean
theorem signedRootsProduct_isCoprime_gapRoot
```

```lean
theorem realPairCores_pairwiseCoprime
```

---

## Codex 指示

```text
Continue FLT7-FUSION from head

59dac526f06bbe34bd40677df6ffa8e04cdc961d

on branch

wip/FLT7-fusion-260729

FUSION-003-CYCLIC is complete.

Do not begin by trying to identify real-cubic rotation with either
cyclePhaseTwist or hiddenRowTwist on the canonical gcd routing board.

The canonical routing is determined by integer margins. Real-cubic Galois
rotation fixes the integer/norm shadow, so the expected routing projection
is constant. The useful cyclic action is instead the action on the three
real conjugate-pair factors of the signed seventh quotient.

Create:

DkMath.FLT.Seven.SevenRamifiedFusionRealPairCarrier

1. Prove the signed root residues.

For p : RamifiedSignedRootDepthPacket, prove modulo seven:

signedLeftRoot  = innerFst^3
signedRightRoot = innerFst^3
signedRightRoot * signedLeftRoot = 1.

Use the existing left/right cubic source equations, innerSnd divisible by
seven, and Frobenius in ZMod 7.

2. Define the three cyclic alpha coefficients.

Use Fin 3 with:

alpha0 = alpha
alpha1 = rotateEquiv alpha = alpha^2 - 2*alpha
alpha2 = rotateEquiv (rotateEquiv alpha) = -alpha^2 + alpha + 2.

Define theta = eisensteinAxis = alpha - 3 and the associated theta units:

u0 = 1
u1 = 1 + alpha
u2 = alpha^2.

Prove:

alpha_i - 3 = theta * u_i.

Their theta residues must be exactly:

1, 4, 2.

Package these values as an explicit equivalence:

Fin 3 ≃ SevenTernarySector.

3. Define the real cyclotomic pair carriers for the signed integer roots.

Let:

T = r^2 + r*l + l^2
S = r*l
P_i = T - alpha_i*S.

Prove by the minimal polynomial of alpha, or direct ring normalization:

P_0 * P_1 * P_2 =
  (signedSeventhQuotient r l : SevenRealCubicInt).

This is the real-conjugate-pair factorization of the six nontrivial
cyclotomic linear factors.

4. Prove exact theta depth one for every P_i.

From:

r - l = 7^4 * gapRoot
7 = theta^3 * thetaSevenUnit

define:

C_i =
  theta^23 * thetaSevenUnit^8 * gapRoot^2
    - u_i * r*l.

Prove division-free:

P_i = theta * C_i.

Then prove:

thetaResidue C_i = -pairPhase(i).

In particular each C_i is a theta-unit and each P_i has exact theta depth one.

5. Recover the positive quotient sector structurally.

Use:

P_0*P_1*P_2 = 7*quotientRoot
theta^3 = -7*(theta+1)^2

to prove the exact core equation:

-(theta+1)^2 * C_0*C_1*C_2 =
  quotientRoot.

Reduce modulo theta and derive quotientRoot = 1 mod 7 as a second,
factor-theoretic proof. Keep the existing first-variation proof.

6. Select the real pair using tau^2.

Define selectedPairIndex as the inverse image of the right ternary sector:

pairPhase(selectedPairIndex) = fusionSlope^2.

Prove:

thetaResidue(selectedPairCore) = -fusionSlope^2.

Relate this to relativeRealIndex:

relativeRealIndex(k) = 1
  iff the absolute pair phase k^2 equals fusionSlope^2.

This selects the conjugate pair {tau,-tau}, not an oriented factor.

7. Join the selected pair core to the quadratic theta jet.

Prove:

right normalized quadratic jet
  = 3 * thetaResidue(selectedPairCore).

The left root has the same quadratic jet, so expose the symmetric version
as well.

8. Investigate pairwise coprimality of C_0,C_1,C_2.

The common high-depth term cancels in differences:

C_i - C_j = -(u_i-u_j)*r*l.

Prove the three unit differences are global units. Their expected norms are:

norm(u1-u0) = -1
norm(u2-u1) = -1
norm(u2-u0) = 1.

Also prove r*l is coprime to gapRoot from:

IsCoprime r l
r-l = 7^4*gapRoot
7 does not divide r,l,gapRoot.

Use these facts to prove pairwise coprimality of the normalized pair cores
if the prime-divisor argument closes.

9. Branch only after this packet.

If the selected pair core admits a seventh-power/association theorem,
continue with an equivariant real-pair Kummer extraction.

Only introduce the full degree-six carrier if choosing between +tau and
-tau genuinely requires the binary terminal orientation.

Keep PR #73 Draft.

Do not claim:

- a nontrivial action of Galois rotation on the canonical gcd routing;
- an oriented cyclotomic factor;
- a reconstructed primitive Fermat chart;
- strict descent;
- a descent provider;
- FLT7.
```

---

## 最終結論

今回の停止点は、壁ではなく座標の取り違えでした。

```text
誤った比較候補:
  real-cubic rotation
      vs
  canonical routing twist

正しい比較:
  real-cubic conjugation
      vs
  three real cyclotomic pair carriers
```

$\tau^2$ は既に三つの pair のうち一つを選べます。

$$
\boxed{\text{ternary sector }\tau^2\text{ が real conjugate pair を選ぶ}}
$$

その normalized pair core の residue は $-\tau^2$ となり、既存 quadratic jet $-3\tau^2$ と直結します。

したがって、次に開くべき魔導門は full degree-$6$ cyclotomic field ではなく、

$$
\boxed{\text{FUSION-003D — Real Pair Carrier}}
$$

です。
