# FUSION-002-EXACT result review and next

## 総合判定

### FUSION-002 は完了です

今回 Lean が固定したのは、単なる「source plane には戻らなかった」という否定結果ではありません。

七乗 root は必ず、

$$
X=A+7^3U\theta+7^6V\theta^2
$$

という形を持ち、

$$
7\nmid A,\qquad7\nmid U,\qquad7\nmid V
$$

さらに、

$$
U\equiv\pm m\pmod7
$$

$$
AV+3U^2\equiv0\pmod7
$$

を満たします。

三角 lifting は $(k,2k)$ から $(k+1,2k+2)$ へ進み、三回反復して exact $(3,6)$ に到達しています。一般的な valuation 層を導入せず、因子の $7$-coprimality だけで閉じた、非常に良い証明です。

左右 root は同じ packet に統合され、

$$
J_L=(-\tau,-3\tau^2)
$$

$$
J_R=(\tau,-3\tau^2)
$$

という共通 slope から生成されます。

その slope は、

$$
\tau=\frac{m}{a}
$$

だけではなく、

$$
\tau=\frac{\operatorname{gapRoot}}{a^3}
$$

として signed integer shadow にも接続されました。

従って、これは完全な **FUSION theorem** です。

```text
real-cubic exact root
        ↓
theta jet slope τ
        ↓
signed integer gapRoot / a³
```

FUSION-002 の分類結果は、文書どおり controlled finite theta-jet outcome、すなわち **B′** で確定です。

---

## 1. B′ は「有限候補」よりさらに強い

現在の normalized equations は modulo $7$ で、

$$
F_1(U,V)=A^6U-\varepsilon m
$$

$$
F_2(U,V)=A^6V+3A^5U^2
$$

です。

$(U,V)$ に関する Jacobian は、

$$
J=
\begin{pmatrix}
A^6 & 0\
6A^5U & A^6
\end{pmatrix}
$$

です。

その determinant は、

$$
\det J=A^{12}
$$

です。

$7\nmid A$ なので、

$$
\det J\ne0\pmod7
$$

です。

これは非常に強い事実です。

B′ は単なる「六個程度の residue sector のどれか」ではなく、

> 各 $(A,m,\varepsilon)$ に対し、modulo $7$ の jet が高次精度へ一意に持ち上がる可能性を持つ非特異 branch

です。

つまり局所世界では、root は自由に揺れません。

```text
source data (A,m,sign)
        ↓
unique first jet (U,V) mod 7
        ↓
predicted unique lift mod 7²
        ↓
predicted unique 7-adic branch
```

となります。

まだ Hensel lifting 自体は Lean で証明されていませんが、Jacobian の非退化は既に現在の式から直接導けます。

このため、FUSION-003 の核心は「六 sector の総当たり」より、

> この一意 branch が元の整数 chart のどの branch と同一であるか

の識別です。

---

## 2. 現在、三種類の $2\times3$ が存在しています

ここは混同すると危険です。

### A. 旧 RAMIFIED second-coordinate routing

`RamifiedSecondCoordinateCanonicalSplit` を生成した既存 routing です。

この board では既に、

```text
c11 = 7^5
c21 = 1
c31 = c32 = c33 = 1
```

など多数の cell が固定され、vertical/horizontal gap roots と compensation core が抽出されています。

### B. 新 signed FUSION routing

今回の、

```text
rows:
  |gapRoot|
  |quotientRoot|
  1

columns:
  |a|
  |a+n|
  |m^7|
```

を持つ `RamifiedSignedRootRoutingPacket` です。

これは自然数の因子 support board です。

### C. unit-sector grid

今回得られた、

$$
\tau\longmapsto(\tau^3,\tau^2)
$$

です。

これは $\mathbf F_7^\times$ の unit address です。

これらはすべて $2\times3$ 的構造を持ちますが、

> 同じ大きさであることは、同じ cell であることを意味しません。

新 signed routing は `Int.natAbs` を通すため、符号情報を失っています。

一方 $\tau$ は signed unit です。

したがって直接比較の前に、自然数 routing へ **orientation layer** を戻す必要があります。

---

## 3. routing margin との融合は、既に終わっています

「どの routing と接続するかはまだ全く不明」ではありません。

Lean は、

$$
\tau=\frac{\operatorname{gapRoot}}{a^3}
$$

を証明しました。

つまり、

```text
theta jet slope τ
        =
signed routing row margin / first column margin³
```

です。

これは routing の **margin bridge** です。

未証明なのは、margin ではなく cell です。

この区別が重要です。

```text
完了:
  slope ↔ signed row/column margins

未完了:
  slope sector ↔ individual routing cells
```

---

## 4. 一つの slope だけでは一般の $2\times3$ board は決まりません

新 signed routing の第三行は product が $1$ なので、各 cell は自然数上、

$$
c_{31}=c_{32}=c_{33}=1
$$

となるはずです。

残る active board は、

$$
\begin{pmatrix}
c_{11}&c_{12}&c_{13}\
c_{21}&c_{22}&c_{23}
\end{pmatrix}
$$

です。

六個の cell に対し、二つの row product と三つの column productがあります。

ただし全積の一致により一条件重複するため、独立条件数は $4$ です。

従って自由度は、

$$
6-4=2
$$

です。

グラフ的には $K_{2,3}$ の cycle rank、

$$
6-5+1=2
$$

と一致します。

つまり、routing margins を全部知っても二つの cycle parameter が残ります。

代表的には、

$$
\kappa_{12}=
\frac{u_{11}u_{22}}{u_{12}u_{21}}
$$

$$
\kappa_{23}=
\frac{u_{12}u_{23}}{u_{13}u_{22}}
$$

のような cross-ratio です。

一方、$\tau$ は一パラメータです。

従って、

> $\tau$ だけで一般の routing board 全体を一意決定することはできません。

次の課題は、現在の FLT7 packet がこの二自由度をさらに拘束し、

```text
(κ12, κ23) = Φ(τ)
```

という一パラメータ曲線へ落とすかどうかです。

これが直接 chart reconstruction の真の試験です。

---

## 5. ただし away row については、さらに強い近道があります

一般の `EndpointRoutingRow` は、

```text
Y
Z
Sum
```

の三種類です。

既存 terminal unit は、

```text
Y       -> +1
Z, Sum  -> -1
```

しか区別しません。

そのため一般論では $\tau^3\in{1,-1}$ だけでは `Z` と `Sum` を分けられません。

しかし実際の RAMIFIED lineage では、既に Row-Sum は排除されています。

`PrimitiveRamifiedSummitPacket` へ到達できる surviving route は Row-Y または Row-Z だけであり、Row-Sum は contradiction により消えています。

従って、現在の実 packet に限れば binary sector で十分です。

予測すべき bridge は、

$$
\tau^3=
\begin{cases}
1 & \text{Row-Y}\
-1 & \text{Row-Z}
\end{cases}
$$

です。

これが通れば、$\tau^2$ を使わずとも元の surviving away row を回収できます。

ただし問題があります。

RAMIFIED summit は Row-Y と Row-Z を一つの共通 packet に統合したため、途中で provenance を失っている可能性があります。

したがって次に調査すべきは、

```text
Does the current nested packet retain the original Y/Z provenance?
```

です。

失っているなら、

```lean
structure RamifiedSummitProvenancePacket where
  terminal : AwaySevenBaseTerminalUnitSectorPacket ...
  row : EndpointRoutingRow
  row_eq_y_or_z : row = .y ∨ row = .z
  summit : PrimitiveRamifiedSummitPacket
  summit_eq : ...
```

のような薄い provenance packet を追加する価値があります。

---

## 6. $\mathbf F_7^\times$ の六 sector は正式な群同型にすべきです

現在の `SevenUnitGridAddress` は、

```lean
slope
rowComponent = slope^3
columnComponent = slope^2
```

を記録し、

$$
\frac{\text{row}}{\text{column}}=\tau
$$

を証明しています。

ここからさらに、

$$
(\tau^3)^2=1
$$

$$
(\tau^2)^3=1
$$

を固定できます。

したがって、

$$
\mathbf F_7^\times\cong\mu_2\times\mu_3
$$

という CRT decomposition そのものです。

型としては、

```lean
abbrev SevenBinarySector :=
  {u : (ZMod 7)ˣ // u ^ 2 = 1}

abbrev SevenTernarySector :=
  {u : (ZMod 7)ˣ // u ^ 3 = 1}
```

を置き、

```lean
def sevenUnitSectorEquiv :
    (ZMod 7)ˣ ≃* SevenBinarySector × SevenTernarySector
```

まで作るのがよいです。

逆写像は、

$$
(r,c)\longmapsto r/c
$$

です。

左 root の slope は $-\tau$ なので、

$$
(-\tau)^3=-\tau^3
$$

$$
(-\tau)^2=\tau^2
$$

です。

従って左右 root は厳密に、

> 同じ ternary column に属し、反対の binary row に属する

と定理化できます。

---

## 7. 次の最重要 algebraic theorem

paired jet を既存の theta-depth $10$ ledger へ戻すべきです。

左右では、

$$
U_R-U_L\equiv2m\pmod7
$$

です。

また、

$$
V_R-V_L\equiv0\pmod7
$$

です。

従って root gap の最小 theta-depth 成分は linear jet から来ます。

$$
X_R-X_L
=======

(A_R-A_L)
+7^3(U_R-U_L)\theta
+7^6(V_R-V_L)\theta^2
$$

です。

$7=\theta^3u_7$ とし、$u_7$ の theta residue が $-1$ であることを使うと、

$$
7^3\theta=\theta^{10}u_7^3
$$

です。

したがって normalized `gapCore` の先頭 residue は、

$$
\boxed{
\thetaResidue(\operatorname{gapCore})=-2m
}
$$

になると予測されます。

これは非常に価値があります。

現在は、

```text
gapCore is not divisible by theta
```

までですが、これを、

```text
exact leading residue = -2*m
```

へ強化できます。

そして次の可換図が閉じます。

```text
paired theta jets
        ↓
algebraic gapCore leading residue = -2m
        ↓
norm first variation
        ↓
signed gapRoot residue = a²m
```

これは FUSION-001B と FUSION-002 を、さらに一段深く一つにします。

---

## 8. cyclotomic 六因子への正しい入り方

六つの nontrivial factor を、

$$
\beta_k=X_R-\zeta^kX_L
$$

とします。

$k\in\mathbf F_7^\times$ は六個あります。

$\tau$ も $\mathbf F_7^\times$ の元なので、絶対的に「$k=\tau$ が正解の factor」と宣言するより、まず torsor を正規化します。

$$
j=\frac{k}{\tau}
$$

とします。

すると、

$$
k=\tau
$$

が relative index $j=1$ になります。

推奨設計は、

```lean
def relativeCyclotomicIndex
    (p : RamifiedPairedThetaRootJetPacket)
    (k : (ZMod 7)ˣ) : (ZMod 7)ˣ :=
  k / p.fusionSlopeUnit
```

です。

これにより六因子を失わず、

```text
j = 1
j = -1
other four sectors
```

を $\tau$ 基準で配置できます。

その後に、relative identity factor が本当に Kummer extraction の distinguished factor であるかを証明します。

---

## 9. 文書上の一点

`STATUS.md` 上部は現在の到達点へ更新されています。

しかし末尾の歴史 section にはまだ、

```text
FUSION-001 therefore has Outcome A.
Coprimality, routing, norm first variation,
and source-plane classification remain future obligations.
```

という古い記述が残っています。

これは現在の事実と衝突します。

削除ではなく、

```text
Superseded checkpoint
```

と明記して歴史記録として残すのがよいでしょう。

---

## 次の実装順序

### FUSION-003-0A — exact gap-core residue

最優先です。

```lean
theorem pairedThetaRootGap_linearCore_modSeven
    (p : RamifiedPairedThetaRootJetPacket) :
    ((p.right.thetaLinearCore -
      p.left.thetaLinearCore : ℤ) : ZMod 7) =
      2 * innerSndRoot
```

```lean
theorem pairedThetaRootGap_squareCore_modSeven
    (p : RamifiedPairedThetaRootJetPacket) :
    ((p.right.thetaSquareCore -
      p.left.thetaSquareCore : ℤ) : ZMod 7) = 0
```

その後、

```lean
theorem gapCore_thetaResidue_eq
    (p : RamifiedPairedThetaRootJetPacket) :
    SevenRealCubicInt.thetaResidue
      p.signedDepth.balanced.axisDrop.depthLedger.gapCore =
        -2 * (innerSndRoot : ZMod 7)
```

を狙います。

---

### FUSION-003-0B — six-sector group API

```lean
SevenBinarySector
SevenTernarySector
sevenUnitSectorEquiv
```

を追加し、

```lean
left_row_eq_neg_right_row
left_column_eq_right_column
```

を証明します。

---

### FUSION-003-0C — provenance recovery

現在の packet chain が元の Row-Y / Row-Z 情報を保持しているか監査します。

保持しているなら、

```lean
theorem fusionSlope_cube_eq_terminalRowSign
```

を直接証明。

保持していないなら、summit 構築前に provenance packet を追加します。

Row-Sum は既に排除済みなので、これが通れば $\tau^3$ だけで surviving row を完全回収できます。

---

### FUSION-003-0D — signed routing unit shadow

新 signed routing に対して、

```lean
third_row_eq_one
all_active_cells_not_seven_dvd
```

を証明します。

その後、cell の `ZMod 7` unit shadow を作ります。

ただし `natAbs` で符号が消えるため、同時に signed orientation を復元してください。

次に二つの cycle invariant、

```text
κ12
κ23
```

を定義し、$\tau$ との関係を探索します。

---

### FUSION-003-0E — 分岐判断

次のどちらかです。

```text
Outcome Direct:
  routing cycle invariants are functions of τ
  -> reconstruct integer/quadratic chart

Outcome Lift:
  extra routing freedom remains
  -> construct relative cyclotomic index torsor
  -> full Kummer carrier
```

---

## Codex 指示

```text
Continue FLT7-FUSION from head
3cf14cceb3bf8ada880db6fdc59d11007113638f
on branch wip/FLT7-fusion-260729.

FUSION-002 is complete. Do not reopen source-plane classification.
Begin a narrow FUSION-003 pre-bridge phase.

Primary goal:
connect the completed paired theta-jet packet to the existing
theta-depth-ten gap ledger and determine exactly what information
the finite six-sector address supplies to the integer and away routings.

1. Close the paired-root gap residue.

In SevenRamifiedPairedThetaRootJet.lean prove:

- right linear core minus left linear core is 2*m modulo seven;
- right square core minus left square core is zero modulo seven.

Then connect the paired root coordinate decompositions to the existing
RamifiedRealCubicDepthLedgerPacket rootGap/gapCore fields.

Target theorem:

theorem gapCore_thetaResidue_eq
    (p : RamifiedPairedThetaRootJetPacket) :
    SevenRealCubicInt.thetaResidue
      p.signedDepth.balanced.axisDrop.depthLedger.gapCore =
        -2 *
          (p.signedDepth.balanced.axisDrop.depthLedger.exactPower.upToUnit
            .normPacket.innerSndRoot : ZMod 7)

Use:

7 = eisensteinAxis^3 * thetaSevenUnit

and compute the theta residue of thetaSevenUnit explicitly.
Account separately for the theta-constant, theta-linear, and
theta-square differences. Do not infer the result only from exact
depth; prove the leading residue.

2. Strengthen SevenUnitGridAddress.

Replace or complement the unrestricted ZMod fields with unit-valued
binary and ternary sectors.

Introduce types equivalent to:

SevenBinarySector =
  {u : (ZMod 7)ˣ // u^2 = 1}

SevenTernarySector =
  {u : (ZMod 7)ˣ // u^3 = 1}

Construct the explicit equivalence

(ZMod 7)ˣ ≃ SevenBinarySector × SevenTernarySector

given by s -> (s^3,s^2), with inverse (r,c) -> r/c.

Prove for the paired roots:

- the left and right binary sectors are negatives;
- the left and right ternary sectors are equal;
- both reconstruct the corresponding signed slope.

3. Audit row provenance.

Trace the current packet chain from
AwaySevenBaseTerminalUnitSectorPacket through
PrimitiveRamifiedSummitPacket,
RamifiedQuadraticInnerRootPacket,
RamifiedRealCubicExactPowerPacket,
and RamifiedPairedThetaRootJetPacket.

Determine whether the original surviving row Y/Z is still recoverable
from stored data.

Remember that Row-Sum has already been eliminated before the common
ramified summit. Therefore the actual source lineage has only Y or Z.

If provenance is retained, prove a theorem relating the surviving row
sign to fusionSlope^3.

If provenance is erased, add the smallest possible provenance packet
before commonization. Do not duplicate the mathematical summit packet.

Do not claim

fusionSlope^3 = awaySevenBaseRowSignUnit row

until an explicit equality of the relevant normalized units is proved.

4. Build the signed unit shadow of RamifiedSignedRootRoutingPacket.

First prove:

routing.c31 = 1
routing.c32 = 1
routing.c33 = 1.

Then prove all six active cells are not divisible by seven.

The existing routing uses Int.natAbs and therefore loses sign.
Add an explicit orientation/sign companion before comparing cells with
the signed fusion slope.

Define the two independent K_{2,3} cycle ratios of the active unit board,
for example cross-ratios based on:

(c11*c22)/(c12*c21)
(c12*c23)/(c13*c22).

Investigate whether the current FLT7 packet forces these two invariants
to be explicit functions of fusionSlope.

Do not identify a particular routing cell merely because both structures
have six sectors.

5. Branch decision.

If the cycle ratios are fully determined by fusionSlope, package a
direct routing reconstruction theorem and begin FUSION-003A.

If an independent cycle parameter remains, stop the direct route and
build the cyclotomic torsor normalization:

relativeIndex(k) = k / fusionSlope.

Do not arbitrarily declare k = fusionSlope to be the distinguished
Kummer factor. First prove which relative index has the required
divisibility or seventh-power property.

6. Optional finite Hensel reconnaissance.

For the normalized triangular equations in U,V, formalize the modulo-seven
Jacobian and prove that its determinant is A^12 and is nonzero.

This is reconnaissance toward uniqueness of higher seven-adic jet lifts.
Do not introduce a full p-adic analytic framework yet.

7. Documentation.

Update the stale historical tail of STATUS.md. Mark it as a superseded
checkpoint or rewrite it so it no longer says FUSION-001 Outcome A or
lists completed obligations as future work.

Keep PR #73 Draft.

Do not claim:

- a selected routing cell without an explicit bridge;
- reconstructed primitive Fermat data;
- a strict well-founded decrease;
- an inhabited descent provider;
- FLT7.
```

---

## 最終推論

いま得られた $\tau$ は、単なる residue label ではありません。

```text
τ
├─ integer margin      gapRoot / a³
├─ right root jet      ( τ, -3τ²)
├─ left root jet       (-τ, -3τ²)
├─ binary sector       τ³
└─ ternary sector      τ²
```

まで一つに束ねています。

そして次の決定点は、

> $\tau$ が routing board の二つの cycle 自由度まで支配するか

です。

支配するなら、直接 integer chart reconstruction。

支配しないなら、その余剰自由度こそ full cyclotomic carrier へ持ち上げるべき情報です。

どちらへ転んでも、FUSION-002 は無駄になりません。

むしろ今回初めて、FUSION-003A と FUSION-003B の分岐条件そのものが、Lean で検査可能な有限 invariant の問題になりました。
