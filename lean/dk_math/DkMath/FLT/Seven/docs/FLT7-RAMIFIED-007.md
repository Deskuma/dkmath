# RAMIFIED-007 (008,009)

うむ。RAMIFIED-006 で固定された事実を並べ直すと、**次の魔核は一つではなく、二段構造**になっています。

第一段は抽象 routing の正規化。
第二段は receiver 成立時に始まる **quadratic root 内部の七乗降下**です。

RAMIFIED-006 は terminal carrier を summit に戻し、深さ $5,6,6$、整数等式、五つの coprimality、2×3 routing、compensation receiver まで Lean で固定しました。残件は routing cell の canonical 同定だけです。

## 1. 抽象 routing は実際には一意である

現在の `CoprimeTripleRouting` は cell を field として保持し、

```text
row factorization
column factorization
各 row / column 内の pairwise coprimality
```

を記録しています。存在証明の内部では、最初から、

```lean
cij := Nat.gcd ai bj
```

として構成されています。

ただし theorem が opaque なので、`Classical.choice` 後に定義簡約で gcd へ戻れない。それが現在の停止理由です。

しかし数学的には、元の三行と三列が pairwise coprime なら、**任意の routing** について、

$$
c_{ij}=\gcd(a_i,b_j)
$$

が従います。

例えば $c_{13}$ は $a_1$ と $b_3$ の双方を割ります。逆に $\gcd(a_1,b_3)$ の素因子が $c_{13}$ 以外の cell に入ると、異なる row の $a_i$ 同士、または異なる column の $b_j$ 同士の coprimality に衝突します。

したがって次に追加すべきなのは RAMIFIED 専用補題ではなく、汎用 API です。

```lean
theorem CoprimeTripleRouting.c11_eq_gcd ...
theorem CoprimeTripleRouting.c12_eq_gcd ...
...
theorem CoprimeTripleRouting.c33_eq_gcd ...
```

あるいは index 化した、

```lean
theorem CoprimeTripleRouting.cell_eq_gcd
```

です。

これを一度作れば、away・ramified 双方の九セルがすべて canonical address になります。

## 2. 2×3 board の完全正規形

次の記号を置きます。

```text
V := |root.snd|
S := |seventhPowerSndCore(root)|
A := gapRoot
Q := |gapQuotient|
B := residualRoot = norm(root)

C := gcd(V,Q)
D := gcd(S,Q)
```

RAMIFIED-006 の整数等式は、

$$
V,S=7^5A^7Q
$$

です。

左右の factor family は pairwise coprime です。

```text
gcd(V,S) = 1

gcd(7^5,A^7) = 1
gcd(7^5,Q)   = 1
gcd(A^7,Q)   = 1
```

canonical cell を回収すると、board は必ず次の形になります。

```text
                    7^5          A^7          Q
                 ┌────────┬────────────┬────────┐
V                │  7^5   │   X^7      │   C    │
                 ├────────┼────────────┼────────┤
S                │   1    │   Y^7      │   D    │
                 ├────────┼────────────┼────────┤
1                │   1    │    1       │   1    │
                 └────────┴────────────┴────────┘
```

ここで、

$$
A=XY
$$

$$
Q=CD
$$

$$
V=7^5X^7C
$$

$$
S=Y^7D
$$

です。

$A^7$ 列については、$c_{12}c_{22}=A^7$ かつ $\gcd(c_{12},c_{22})=1$ なので、既存の `seventh_power_factor_split` と同じ機構で、それぞれが七乗になります。既存実装でも、coprime な二因子の積が七乗なら双方を七乗へ分離する API が使われています。

したがって RAMIFIED-006 の残件は単なる、

```text
c13 = C
c12 = X^7
```

ではありません。

最終的には上の**四本の完全等式**を packet 化するのがよいです。

```lean
structure RamifiedSecondCoordinateCanonicalSplit where
  verticalGapRoot : ℕ
  horizontalGapRoot : ℕ
  compensationCore : ℕ
  quotientRemainder : ℕ

  gapRoot_eq :
    A = verticalGapRoot * horizontalGapRoot

  rootSnd_eq :
    V = 7^5 * verticalGapRoot^7 * compensationCore

  sndCore_eq :
    S = horizontalGapRoot^7 * quotientRemainder

  gapQuotient_eq :
    Q = compensationCore * quotientRemainder
```

## 3. cubic gap の正体

ramified cubic difference は、

$$
R-L=7vB
$$

です。

したがって絶対値では、

$$
|R-L|=7VB
$$

です。

正規形を代入すると、

$$
\boxed{|R-L|=7^6X^7CB}
$$

となります。

これが RAMIFIED-006 の最終表示式です。

現在の receiver、

$$
CB=w^7
$$

が成立すれば、

$$
|R-L|=7^6(Xw)^7
$$

です。

逆方向も成立します。

もし、

$$
|R-L|=7^6W^7
$$

なら、

$$
X^7CB=W^7
$$

です。

しかも $X$ は $A$ を割り、$C$ は $Q$ を割り、RAMIFIED-006 は $\gcd(A,Q)=1$ と $\gcd(A,B)=1$ を持つので、

$$
\gcd(X,CB)=1
$$

です。

よって power split により $CB$ 自身が七乗になります。

したがって receiver は、root-cubic gap shape の単なる十分条件ではありません。

$$
\boxed{CB\text{ が七乗}\iff |R-L|=7^6\times\text{七乗}}
$$

という**完全同値**です。

## 4. receiver は二つの独立した鍵へ分裂する

RAMIFIED-006 は、

$$
\gcd(B,V)=1
$$

を証明しています。

$C\mid V$ なので、

$$
\gcd(C,B)=1
$$

です。

したがって、

$$
CB=w^7
$$

なら、coprime power split により、

$$
\boxed{C=c^7,\qquad B=b^7}
$$

へ分離します。

逆も明らかです。

つまり receiver の正体は、

```text
Lock 1:
  compensationCore C が整数七乗

Lock 2:
  residualRoot B が整数七乗
```

です。

RAMIFIED-005 の、

$$
B\equiv1\pmod{49}
$$

は Lock 2 の局所的必要条件にすぎません。

完全な branch は実際には四つあります。

```text
Branch I
  B ≠ 1 mod 49
  → residual local obstruction

Branch II
  B = 1 mod 49
  だが B は整数七乗でない
  → residual global obstruction

Branch III
  B は整数七乗
  だが C は整数七乗でない
  → compensation obstruction

Branch IV
  B = b^7 かつ C = c^7
  → root 内部降下
```

ここまで分けると、Hensel lift だけでは Branch II と III を処理できない理由も明確になります。

## 5. receiver 成立時、quadratic root 自身が再び七乗になる

Branch IV を仮定します。

$$
B=b^7
$$

であり、

$$
B=\operatorname{norm}(\rho)
$$

です。$\rho$ は現在の quadratic root です。

RAMIFIED-002 は $\rho$ の二座標が coprime であることを証明しています。任意の $\rho$ と $\overline{\rho}$ の共通因子は、座標 coprimality により `sevenAxis` を割ります。これは既存の一般補題です。

しかし、

$$
7\nmid\operatorname{norm}(\rho)=B
$$

なので `sevenAxis` は $\rho$ を割れません。

従って、

$$
\gcd(\rho,\overline{\rho})
$$

は unit です。

さらに、

$$
\rho,\overline{\rho}=B=b^7
$$

です。

既存の seventh-power extraction theorem を適用すると、

$$
\boxed{\rho=\gamma^7}
$$

となります。既存コードでも、残余核と共役が coprime で、その積が七乗なら残余核自身を七乗として抽出しています。

よって summit の coordinate equation は、

$$
\operatorname{cyclotomicSevenToTraceOne}(c,e)
=\operatorname{sevenAxis}\rho^7
=\operatorname{sevenAxis}\gamma^{49}
$$

へ上がります。

これは大きい。

$$
\boxed{\text{receiver 成立}\Rightarrow\text{quadratic coordinate は }49\text{乗層へ入る}}
$$

## 6. root second coordinate の深さが $5\to4$ へ下がる

$C=c^7$ でもあるため、

$$
V=7^5X^7C=7^5(Xc)^7
$$

です。

一方 $\rho=\gamma^7$ なので、

$$
\rho_{\mathrm{snd}}
=\operatorname{seventhPowerSnd}(\gamma)
=7\gamma_{\mathrm{snd}}\operatorname{sndCore}(\gamma)
$$

です。

従って絶対値を取り、$7$ を消去すると、

$$
|\gamma_{\mathrm{snd}}|,
|\operatorname{sndCore}(\gamma)|
=7^4(Xc)^7
$$

となります。

$\gamma$ の norm は $b$ であり、$7\nmid b$ です。そのため $\operatorname{sndCore}(\gamma)$ は $7$-unit です。

また $\gamma$ の座標は primitive です。もし素数が両座標を割れば、$\gamma^7=\rho$ の両座標も割り、$\rho$ の primitive 性に反します。

したがって、

$$
\gcd\left(|\gamma_{\mathrm{snd}}|,
|\operatorname{sndCore}(\gamma)|\right)=1
$$

です。

再び coprime power split を行うと、

$$
\boxed{|\gamma_{\mathrm{snd}}|=7^4M^7}
$$

$$
\boxed{|\operatorname{sndCore}(\gamma)|=N^7}
$$

$$
Xc=MN
$$

となります。

つまり receiver は、単なる $49$ 乗表示ではなく、

```text
outer root.snd depth = 5
inner root.snd depth = 4
```

という**厳密な一段降下**を生みます。

## 7. inner cubic も双方が七乗になる

既存恒等式は、

$$
\operatorname{sndCore}(u,v)
=L_0(u,v)R_0(u,v)
$$

です。

さらに primitive root と norm の $7$-unit 性から、この二つの cubic factor は coprime になります。既存 away API では、この coprimality がすでに構築されています。

したがって、

$$
|L_0(\gamma)|,|R_0(\gamma)|=N^7
$$

より、

$$
L_0(\gamma)=\lambda^7
$$

$$
R_0(\gamma)=\mu^7
$$

と符号込みで書けます。指数 $7$ は奇数なので負号も根へ吸収できます。

cubic difference は、

$$
R_0(\gamma)-L_0(\gamma)
=7\gamma_{\mathrm{fst}}\gamma_{\mathrm{snd}}
(\gamma_{\mathrm{fst}}+\gamma_{\mathrm{snd}})
$$

です。

$\gamma_{\mathrm{snd}}$ の深さは $4$、他の二因子は $7$-unit なので、

$$
v_7!\left(\mu^7-\lambda^7\right)=5
$$

です。

mod $7$ では $\mu^7=\mu$、$\lambda^7=\lambda$ なので、

$$
\mu\equiv\lambda\pmod7
$$

です。

七乗差の LTE から、

$$
v_7(\mu^7-\lambda^7)
=v_7(\mu-\lambda)+1
$$

となり、

$$
\boxed{v_7(\mu-\lambda)=4}
$$

を得ます。

ここに新しい深さ ladder が現れます。

```text
endpoint gap              depth 6
outer cubic gap           depth 6
outer root.snd            depth 5

receiver / root extraction

inner cubic-value gap     depth 5
inner seventh-root gap    depth 4
```

これは、元の Fermat counterexample を直接再構成する descent ではありません。

しかし、**quadratic root 内部では確実に深さが一段下がっています。**

## 8. compensation prime にも強い制約がある

別方向もあります。

奇素数 $q$ が $C$ を割るなら、

$$
q\mid v,\qquad q\mid Q
$$

です。

$q\ne7$ であり、$q\nmid A$ です。

$h=7^5A^7$ とし、$t=e/h$ を $\mathbf F_q$ 上で置くと、$Q=0$ から、

$$
t^2+7t+14=0
$$

を得ます。

$s=2t+7$ と置けば、

$$
s^2=-7
$$

です。

さらに first-coordinate equationを mod $q$ へ落とすと、

$$
u^7=7h^3s=-(hs)^3
$$

へ整理できます。

$3$ と $7$ は互いに素なので、有限体の乗法群では、

$$
-hs
$$

自身が七乗になります。

ところが、

$$
-hs=-7^5A^7s=49(As)^7
$$

です。

従って、

$$
49
$$

は mod $q$ の七乗です。よって $7$ も七乗です。

したがって奇 compensation prime は、

```text
-7 が平方剰余
かつ
7 が七乗剰余
```

という二重条件を満たします。

$$
\boxed{\text{compensation prime は判別式 }-7\text{ と Kummer 条件の交点}}
$$

です。

これは即矛盾ではありませんが、$C$ の素因子 support を非常に薄い世界へ閉じ込めます。

## 次の実装順

### FLT7-RAMIFIED-007

```text
canonical second-coordinate routing normalization
```

目標：

```lean
CoprimeTripleRouting.cell_eq_gcd

RamifiedSecondCoordinateCanonicalSplit

rootSnd_eq :
  V = 7^5 * verticalGapRoot^7 * compensationCore

sndCore_eq :
  S = horizontalGapRoot^7 * quotientRemainder

gapRoot_eq :
  A = verticalGapRoot * horizontalGapRoot

gapQuotient_eq :
  Q = compensationCore * quotientRemainder

cubicGap_natAbs_eq :
  |R-L| =
    7^6 * verticalGapRoot^7 *
      (compensationCore * residualRoot)

receiver_iff_cubicGap_seventh_shape
receiver_iff_independent_seventh_powers
```

ここで RAMIFIED-006 は完全な Outcome A になります。

### FLT7-RAMIFIED-008

```text
receiver-induced quadratic root descent
```

目標：

```lean
root_gcd_conj_isUnit

receiver_compensation_eq_seventh
receiver_residualRoot_eq_seventh

exists_innerRoot :
  root = innerRoot^7

coordinate_eq_fortyNine :
  cyclotomicCoordinate =
    sevenAxis * innerRoot^49

innerRootSnd_eq :
  |innerRoot.snd| = 7^4 * innerVerticalRoot^7

innerSndCore_eq :
  |sndCore(innerRoot)| = innerHorizontalRoot^7

innerCubics_eq_seventh

innerCubicRootGap_depth_eq_four
```

### 並行する RAMIFIED-009

```text
compensation-prime splitting/Kummer audit
```

目標：

```lean
OddPrime q
q ∣ compensationCore
  →
IsSquare (-7 : ZMod q)
  ∧ ∃ r : ZMod q, r^7 = 7
```

## 結論

RAMIFIED-006 で露出した魔核は、

$$
C\cdot B
$$

だけではありません。

その内部は、

```text
C:
  gapQuotient から root.snd へ流入した隠れ素因子

B:
  quadratic root の norm

C が七乗
  → root.snd の七乗 tail が完成

B が七乗
  → quadratic root 自身がさらに七乗

両方が七乗
  → sevenAxis × 49th power
  → second-coordinate depth 5 → 4
```

です。

$$
\boxed{\text{receiver は「新しい gap の七乗化」と「root 自身の再七乗化」を同時に意味する}}
$$

次の太い道は higher Hensel ではありません。

**canonical routing を閉じ、receiver を二つの七乗鍵へ分解し、quadratic root 内部の $5\to4$ 降下を Lean に固定する。**

ここから本物の descent 機構が生まれ始めています。
