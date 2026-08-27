
# FLT7-FUSION-003-PREBRIDGE result reviw and next

## 賢狼の総合判定

## FUSION-003 pre-bridge は完了です

今回の Outcome C は、FUSION-002 以前に想定していた「自由な三座標 root が残る」という Outcome C ではありません。

正確には、

```text
FUSION-002:
  controlled exact theta-jet B′

FUSION-003 pre-bridge:
  routing / cyclotomic identificationに
  cyclic phase が一つ残る Outcome Cμ₃
```

です。

現在 Lean は、

$$
\mathrm{thetaResidue}(\operatorname{gapCore})=-2m
$$

まで algebraic gap の先頭係数を確定し、$\mathbf F_7^\times$ を正式に $\mu_2\times\mu_3$ へ分解しました。左右 root は反対の binary sector、同一の ternary sectorです。さらに routing は同じ `signedDepth` packet 上に接続され、第三行、active cell、signed margin、cycle ratio、cyclotomic torsor まで一貫して固定されています。

しかし、ここから最大推論すると、現在提示されている二択は少しだけ修正する必要があります。

> $\kappa_{12},\kappa_{23}$ は二つの独立自由度ではありません。
> だが、両者を $\tau$ で表しても routing board 全体はまだ決まりません。

敵の正体は、**一つの可視 $\mu_3$ phase と、一つの不可視 $\mu_3$ gauge** です。

---

## 1. 二つの cycle ratio は一つの $\mu_3$ へ圧縮される

active unit board を、

$$
U=
\begin{pmatrix}
u_{11}&u_{12}&u_{13}\\
u_{21}&u_{22}&u_{23}
\end{pmatrix}
$$

とします。

row margins と column margins を、

$$
R_1=u_{11}u_{12}u_{13},\qquad R_2=u_{21}u_{22}u_{23}
$$

$$
B_1=u_{11}u_{21},\qquad B_2=u_{12}u_{22},\qquad B_3=u_{13}u_{23}
$$

と置きます。

実装済みの cycle ratios は、

$$
\kappa_{12}=\frac{u_{11}u_{22}}{u_{12}u_{21}},\qquad\kappa_{23}=\frac{u_{12}u_{23}}{u_{13}u_{22}}
$$

です。

$\mathbf F_7^\times$ の全元が六乗で $1$ になることを使うと、純粋な群計算により、

$$
\boxed{\frac{\kappa_{12}}{\kappa_{23}}=\frac{R_1/R_2}{B_2^3}}
$$

$$
\boxed{\kappa_{12}^3=\left(\frac{B_1}{B_2}\right)^3}
$$

$$
\boxed{\kappa_{23}^3=\left(\frac{B_2}{B_3}\right)^3}
$$

です。

従って、$\kappa_{12}$ と $\kappa_{23}$ の binary components は column margins だけで決まります。

さらに両者の比も row / column margins だけで決まります。

よって残る自由度は、

$$
(\kappa_{12},\kappa_{23})\longmapsto(\omega\kappa_{12},\omega\kappa_{23}),\qquad\omega^3=1
$$

という共通 ternary multiplier だけです。

つまり二つの cycle ratio の実質自由度は、

$$
\boxed{\text{one }\mu_3\text{ phase}}
$$

です。

---

## 2. signed FUSION margins へ代入すると比は absolute slope になる

`RamifiedSignedRootRoutingPacket` では、

```text
R₁ = |gapRoot|
R₂ = |quotientRoot|

B₁ = |a|
B₂ = |a+n|
B₃ = |m⁷|
```

です。routing 自体は canonical `CoprimeTripleRouting` として、同じ `signedDepth` に coherent に接続されています。

ここで、

$$
E=\operatorname{quotientRoot}\equiv1\pmod7
$$

$$
n\equiv0\pmod7
$$

$$
dE=a(a+n)m^7
$$

を使います。

$\bar x$ を `Int.natAbs x` の modulo-$7$ unit shadow と書くと、

$$
\bar E^2=1,\qquad\overline{a+n}^{,2}=\bar a^2,\qquad\overline{m^7}=\bar m
$$

です。

先ほどの式に代入すると、

$$
\frac{\kappa_{12}}{\kappa_{23}}=\frac{\bar d/\bar E}{\overline{a+n}^{,3}}=\frac{\bar m}{\bar a}
$$

となります。

この absolute slope を、

$$
\rho:=\frac{\bar m}{\bar a}
$$

と置くと、signed slope $\tau=m/a$ との関係は、

$$
\boxed{\rho^2=\tau^2}
$$

です。

`natAbs` が消した binary sign だけが両者の差です。

従って routing cycle の ternary quotient は、既に Lean 固定済みの jet column $\tau^2$ と同じです。

$$
\boxed{\frac{\kappa_{12}^2}{\kappa_{23}^2}=\tau^2}
$$

これは最優先で Lean 化すべき、新しい margin-to-cycle bridge です。

---

## 3. ただし cycle ratios を確定しても board 全体は決まらない

ここが今回の最大推論の魔核です。

固定 margins を保ったまま、board に少なくとも三種類の gauge action があります。

## 可視 cycle-phase action

$\omega\in\mu_3$ とし、$\eta:=\omega^2$ とします。

$$
\begin{pmatrix}
u_{11}&u_{12}&u_{13}\
u_{21}&u_{22}&u_{23}
\end{pmatrix}
\longmapsto
\begin{pmatrix}
\eta u_{11}&u_{12}&\eta^{-1}u_{13}\
\eta^{-1}u_{21}&u_{22}&\eta u_{23}
\end{pmatrix}
$$

と変換します。

全 row / column margins は不変ですが、

$$
\kappa_{12}\longmapsto\omega\kappa_{12}
$$

$$
\kappa_{23}\longmapsto\omega\kappa_{23}
$$

となります。

これが現在見えている一つの $\mu_3$ cycle phase です。

## 不可視 row-twist action

同じく $\omega^3=1$ として、

$$
u_{1j}\longmapsto\omega u_{1j},\qquad u_{2j}\longmapsto\omega^{-1}u_{2j}
$$

とします。

この変換は、

```text
row margins     unchanged
column margins  unchanged
κ₁₂             unchanged
κ₂₃             unchanged
```

です。

つまり margins と二つの cycle ratios を全部知っても、この $\mu_3$ は見えません。

## column sign gauge

$\varepsilon_j^2=1$ かつ $\varepsilon_1\varepsilon_2\varepsilon_3=1$ として、各 column の上下を同時に $\varepsilon_j$ 倍しても margins と cycles は不変です。

これは $\mu_2^2$ gauge です。

したがって、非空な固定-margin fiber の構造は代数的に、

$$
\boxed{\mu_2^2\times\mu_3^{\mathrm{hidden}}\times\mu_3^{\mathrm{visible}}}
$$

となり、要素数は、

$$
4\cdot3\cdot3=36=|\mathbf F_7^\times|^2
$$

です。

これは $2\times3$ board の二自由度と完全に一致します。

---

## 4. これは direct route の否定ではなく、情報境界の確定

重要なのは、実際の自然数 routing board は既に canonical gcd address だという点です。

したがって actual board が曖昧なわけではありません。

曖昧なのは、

> signed margins、modulo-$7$ cycles、$\tau$ だけから actual gcd board の unit shadow を再構成できるか

です。

答えは **できません**。

少なくとも hidden $\mu_3$ と $\mu_2^2$ gauge は、それらの有限 invariant から完全に消えています。

従って、

```text
κ₁₂ = f(τ)
κ₂₃ = g(τ)
```

だけを証明しても、特定 routing cell の選択根拠にはなりません。

直接 chart route を継続するなら、次のどちらかが必要です。

```text
A. exact integer gcd / prime-support 情報を使う
B. 消えた cyclic phase を別の代数作用から回収する
```

B の候補が、実三次体の Galois rotation です。

---

## 5. 残った $\mu_3$ は実三次体の Galois 回転と同じ動きをする

DkMath には既に、判別式 $49$ の実三次整数環と、その位数 $3$ の環自己同型が存在します。

既存の自己同型 $\sigma$ は、

$$
\sigma(\alpha)=\alpha^2-2\alpha
$$

を満たし、三回作用すると恒等写像に戻ります。

$\theta=\alpha-3$ なので、ここから直接、

$$
\sigma(\theta)=(\theta+3)^2-2(\theta+3)-3=\theta^2+4\theta
$$

すなわち、

$$
\boxed{\sigma(\theta)=\theta(\theta+4)}
$$

を得ます。

`eisensteinAxis` はまさに $\theta=\alpha-3$ であり、

$$
\theta^3=-7(\theta+1)^2
$$

も既に固定されています。

従って、exact theta-depth $d$ の要素、

$$
x=\theta^d g
$$

を回転すると、normalized leading residue は、

$$
\mathrm{thetaResidue}(g)\longmapsto4^d \mathrm{thetaResidue}(g)
$$

と変換されます。

gap は depth $10$ なので、

$$
4^{10}\equiv4\pmod7
$$

です。

よって、

$$
\mathrm{thetaResidue}(\operatorname{gapCore})=-2m
$$

は回転により、

$$
-2m\longmapsto-8m\equiv-m\longmapsto-4m\equiv3m\longmapsto-2m
$$

と三周期で巡回します。

これはまさに $\mu_3$ orbit です。

また root slope に対しては先頭一次係数が $4$ 倍されるため、

$$
\tau\longmapsto4\tau
$$

となります。

binary component は、

$$
(4\tau)^3=4^3\tau^3=\tau^3
$$

で保存されます。

ternary component は、

$$
(4\tau)^2=2\tau^2
$$

となり、${1,2,4}$ を巡回します。

つまり Galois rotation は、

```text
binary row       fixed
ternary column   cyclically rotated
```

という、いま失われている phase と全く同じ型の作用です。

ただし現段階では、これが visible cycle phase なのか、hidden row twist なのかはまだ証明されていません。

> 次に証明すべき対象は「$\kappa$ を $\tau$ の関数にする」より、
> **Galois rotation が routing board のどちらの $\mu_3$ action に対応するか**です。

---

## 6. 残余 phase は未処理の global unit class ではない

ここも既存 DkMath から確定できます。

実三次整数環の unit rank は $2$ で、unit class modulo torsion / seventh powers は $49$ 個です。

DkMath は `projectiveLog` をこの unit class から $\mathbf F_7^2$ への全単射として証明し、projective log がゼロであることと unit が七乗であることを同値にしています。

さらに real-cubic 左右 source に付随する unit は、両方とも projective log がゼロであり、既に七乗 unit として吸収されています。

従って現在残っている $\mu_3$ は、

```text
global unit-class obstruction
```

ではありません。

それは、

```text
routing coordinate phase
real-cubic conjugate phase
cyclotomic index phase
```

の比較で生じたものです。

つまり unit extraction をやり直す必要はありません。

---

## 7. cyclotomic 側では最初から単一因子を選ぶべきではない

full cyclotomic index は $k\in\mathbf F_7^\times$ です。

しかし実三次体は複素共役 $k\leftrightarrow-k$ を識別できません。

したがって real-cubic data が最初に選択できるのは、一つの factor ではなく conjugate pair です。

現在の relative index、

$$
j=\frac{k}{\tau}
$$

から、real relative index を、

$$
\operatorname{relativeRealIndex}(k):=\left(\frac{k}{\tau}\right)^2
$$

と定義します。

すると、

$$
\operatorname{relativeRealIndex}(k)=1
$$

であることは、

$$
\left(\frac{k}{\tau}\right)^2=1
$$

すなわち、

$$
\boxed{k=\tau\ \lor\ k=-\tau}
$$

と同値です。

これは conjugate pair、

$$
\boxed{{\tau,-\tau}}
$$

を正当に選びます。

この段階では binary orientation がないため、$+\tau$ と $-\tau$ のどちらか一方を選ぶべきではありません。

従って cyclotomic route の正しい順序は、

```text
six factors
    ↓ relative square index
three conjugate pairs
    ↓ real-cubic ternary phase
one conjugate pair
    ↓ terminal Y/Z binary orientation
one signed factor, only if necessary
```

です。

現在実装された `relativeCyclotomicIndex(k)=k/\tau` は安全な torsor 座標変換であり、因子選択ではないこともコード上明示されています。

---

## 8. 次フェーズの正式名称

現在の敵を正確に命名するなら、

```text
FUSION-003C — Cyclic Phase Alignment
```

が適切です。

または DkMath 的には、

```text
Outcome Cμ₃ — 三周期魔核
```

です。

これは、

```text
unrestricted cyclotomic ambiguity
```

ではなく、

```text
one visible μ₃ phase
+ one board-invisible μ₃ gauge
+ binary orientation already separately retained
```

という完全に有限な構造です。

---

## 次の Lean 実装順序

### FUSION-003C-1 — cycle margin normal form

新規モジュール候補：

```text
SevenRamifiedFusionCycleNormalForm.lean
```

まず generic `ActiveUnitBoard` 上で次を証明します。

```lean
theorem cycleRatio12_div_cycleRatio23_eq
    (u : ActiveUnitBoard) :
    cycleRatio12 u / cycleRatio23 u =
      (rowMargin1 u / rowMargin2 u) /
        columnMargin2 u ^ 3
```

```lean
theorem cycleRatio12_cube_eq
    (u : ActiveUnitBoard) :
    cycleRatio12 u ^ 3 =
      (columnMargin1 u / columnMargin2 u) ^ 3
```

```lean
theorem cycleRatio23_cube_eq
    (u : ActiveUnitBoard) :
    cycleRatio23 u ^ 3 =
      (columnMargin2 u / columnMargin3 u) ^ 3
```

その後 actual audit packet に特殊化し、

```lean
theorem cycleRatio_div_eq_absoluteFusionSlope
    (p : RamifiedFusionRoutingAuditPacket) :
    p.routing.cycleRatio12 / p.routing.cycleRatio23 =
      p.absoluteFusionSlopeUnit
```

```lean
theorem cycleRatio_square_div_eq_fusionSlope_sq
    (p : RamifiedFusionRoutingAuditPacket) :
    ((p.routing.cycleRatio12 /
      p.routing.cycleRatio23 : (ZMod 7)ˣ) : ZMod 7) ^ 2 =
        p.jet.fusionSlope ^ 2
```

を固定します。

---

### FUSION-003C-2 — 二種類の $\mu_3$ action

```lean
def cyclePhaseTwist
    (ω : SevenTernarySector)
    (u : ActiveUnitBoard) :
    ActiveUnitBoard
```

```lean
def hiddenRowTwist
    (ω : SevenTernarySector)
    (u : ActiveUnitBoard) :
    ActiveUnitBoard
```

を定義します。

証明対象：

```text
cyclePhaseTwist:
  all margins unchanged
  κ₁₂ -> ω*κ₁₂
  κ₂₃ -> ω*κ₂₃

hiddenRowTwist:
  all margins unchanged
  κ₁₂ unchanged
  κ₂₃ unchanged
```

さらに明示的な非自明 $\omega$ を使って、

```lean
theorem margins_do_not_determine_cycles : ...
```

```lean
theorem margins_and_cycles_do_not_determine_board : ...
```

を作ります。

これは current finite API の情報境界を Lean 自身に証明させる重要な checkpoint です。

ただし theorem 名・docstring では、

```text
exact natural gcd routing is not ambiguous;
only reconstruction from the unit-shadow invariants is insufficient
```

と明記します。

---

### FUSION-003C-3 — real-cubic rotation phase

```lean
theorem rotateEquiv_eisensteinAxis :
    rotateEquiv eisensteinAxis =
      eisensteinAxis ^ 2 + 4 * eisensteinAxis
```

をまず固定します。

次に depth-$10$ 専用で十分なので、

```lean
theorem rotate_depthTen_thetaResidue
    {g rotatedCore : SevenRealCubicInt}
    (h :
      rotateEquiv (eisensteinAxis ^ 10 * g) =
        eisensteinAxis ^ 10 * rotatedCore) :
    thetaResidue rotatedCore =
      4 * thetaResidue g
```

を作ります。

そして paired gap へ接続し、

```lean
theorem rotatedGapCore_thetaResidue_eq
```

として三つの residue、

```text
-2*m
-m
3*m
```

を固定します。

その後、

```lean
def FusionRotationPhase := Fin 3
```

または `SevenTernarySector` を用いて、三つの conjugate source-plane charts を packet 化します。

---

### FUSION-003C-4 — relative conjugate pair

```lean
def relativeRealIndex
    (p : RamifiedPairedThetaRootJetPacket)
    (k : (ZMod 7)ˣ) :
    SevenTernarySector
```

を $(k/\tau)^2$ で定義します。

```lean
theorem relativeRealIndex_eq_one_iff
    (p : RamifiedPairedThetaRootJetPacket)
    (k : (ZMod 7)ˣ) :
    p.relativeRealIndex k = 1 ↔
      k = p.fusionSlopeUnit ∨
      k = -p.fusionSlopeUnit
```

を証明します。

次に三つの conjugate pair が `rotateEquiv` の三周期と同じ orbit になることを示します。

---

### FUSION-003C-5 — alignment packet

```lean
structure RamifiedFusionCyclicPhasePacket where
  audit : RamifiedFusionRoutingAuditPacket
  provenance : RamifiedSummitProvenancePacket ...
  cyclePhase : SevenTernarySector
  rotationPhase : Fin 3

  cyclePhase_eq_rotation :
    ...

  binarySector_eq_rowSign :
    ...
```

この packet が inhabited になった地点で、初めて分岐します。

```text
Alignment closes in real cubic:
  -> FUSION-003A chart reconstruction up to rotation

Alignment only selects a conjugate pair:
  -> FUSION-003B full cyclotomic pair/Kummer packet
```

---

## Codex 指示

```text
Continue FLT7-FUSION from head

0ad38e727ce305024d67e70a239377177675458d

on branch

wip/FLT7-fusion-260729

The FUSION-003 pre-bridge is complete. Do not search blindly for two
unrelated formulas kappa12 = f(tau), kappa23 = g(tau).

The next phase is:

FUSION-003C — cyclic phase alignment.

1. Add SevenRamifiedFusionCycleNormalForm.lean.

For an abstract active 2-by-3 unit board, define row and column margins
and prove:

kappa12 / kappa23
  = (row1 / row2) / column2^3

kappa12^3
  = (column1 / column2)^3

kappa23^3
  = (column2 / column3)^3.

Use the exponent-six property of (ZMod 7)ˣ explicitly.

2. Specialize the identities to RamifiedFusionRoutingAuditPacket.

Introduce the unit represented by

|m| / |a| modulo seven

without assigning a signed orientation to natAbs.

Use:

quotientRoot = 1 mod 7
innerSnd = 0 mod 7
gapRoot * quotientRoot = a * (a+n) * m^7

to prove:

cycleRatio12 / cycleRatio23 = |m| / |a|

and then:

(cycleRatio12 / cycleRatio23)^2 = fusionSlope^2.

This theorem should be attached to the coherent audit packet so the
routing and jet share exactly the same signedDepth object.

3. Formalize both ternary actions on ActiveUnitBoard.

Cycle-phase twist:

choose omega^3 = 1 and eta = omega^2, then transform

u11 -> eta*u11
u21 -> eta^-1*u21
u13 -> eta^-1*u13
u23 -> eta*u23

with u12,u22 fixed.

Prove:

- all row margins are preserved;
- all column margins are preserved;
- both cycle ratios are multiplied by omega.

Hidden row twist:

u1j -> omega*u1j
u2j -> omega^-1*u2j.

Prove:

- all margins are preserved;
- both cycle ratios are preserved.

Also formalize the columnwise μ2 sign gauge with product-one signs.

Prove explicit non-uniqueness theorems showing:

- margins alone do not determine the cycle phase;
- margins plus both cycle ratios do not determine the complete unit board.

State carefully that the exact natural gcd routing remains canonical;
the insufficiency concerns reconstruction from its modulo-seven unit
shadow only.

4. Connect the remaining ternary structure to the real-cubic rotation.

Prove in SevenRealCubicInt:

rotateEquiv eisensteinAxis
  = eisensteinAxis^2 + 4*eisensteinAxis.

Then prove the leading-residue action at exact theta depth d, or first
the depth-ten specialization:

thetaResidue(rotatedCore)
  = 4^10 * thetaResidue(core)
  = 4 * thetaResidue(core).

Apply this to the paired root gap and record the three residues:

-2*m, -m, 3*m.

Package the three rotated source planes or rotated gap sectors with a
Fin 3 / SevenTernarySector index.

Do not yet assert whether this rotation is the visible cycle-phase
action or the hidden row-twist action. Prove the comparison explicitly.

5. Do not reopen the real-cubic global unit-class analysis.

The existing projectiveLog theorem already proves the relevant left and
right source units are seventh powers. The remaining μ3 phase is not an
unresolved global-unit class.

6. Refine the cyclotomic torsor to conjugate pairs.

Define:

relativeRealIndex(k) = (k / fusionSlopeUnit)^2.

Prove:

relativeRealIndex(k) = 1
  iff
k = fusionSlopeUnit or k = -fusionSlopeUnit.

Interpret this only as selection of the conjugate pair {tau,-tau}.
Do not select one signed factor until the terminal binary orientation
has been connected to the fusion binary sector.

7. Build a RamifiedFusionCyclicPhasePacket joining:

- the coherent routing audit;
- the retained Y/Z provenance;
- the paired theta jet;
- the visible routing cycle phase;
- the real-cubic rotation phase;
- the relative cyclotomic conjugate-pair address.

The next branch decision is:

A. If the rotation phase aligns the routing unit shadow inside the real
   cubic model, begin chart reconstruction up to cyclic rotation.

B. If only a conjugate pair is selected, begin the full cyclotomic
   Kummer packet equivariantly for that pair.

Keep PR #73 Draft.

Do not claim:

- that kappa12 and kappa23 are independent final parameters;
- that formulas for the cycle ratios alone reconstruct every routing cell;
- that relative index one is already a distinguished Kummer factor;
- a primitive reconstructed Fermat chart;
- strict descent;
- a descent provider;
- FLT7.
```

---

## 最終結論

今回の pre-bridge は、分岐に失敗したのではありません。

むしろ敵を、

```text
two arbitrary routing cycles
six arbitrary cyclotomic factors
```

から、

```text
one visible μ₃ cycle phase
one hidden μ₃ board gauge
one retained binary orientation
three conjugate cyclotomic pairs
```

まで圧縮しました。

そして実三次体の既存 Galois rotation が、その $\mu_3$ と全く同じ周期作用を持っています。

$$
\boxed{\text{次の魔核は }\kappa\text{ ではなく cyclic phase alignment}}
$$

です。

ここが閉じれば、direct chart と full cyclotomic の二択は「推測による分岐」ではなく、Lean が判定する完全な有限分岐になります。
