# FLT7-FUSION-002-ABC result and next

## 総合判定

今回の実装は、FUSION-002 の敵を完全に変えました。

以前の敵は、

```text
巨大な homogeneous degree-7 方程式
seventhSourcePlaneEquation A B C = 0
```

でした。

現在の敵は、

```text
G = B·GB + 7C²·GC
H = C·HC + B²·HB
```

という **三角型 ramified lifting** です。

しかも先頭係数は、

$$
GB\equiv A^6,\qquad HC\equiv A^6,\qquad HB\equiv3A^5\pmod7
$$

であり、$7\nmid A$ ならすべて $7$-unit です。

したがって、もう次数 7 零点集合の一般分類は必要ありません。

> 七乗写像は $\theta$-jet 上で、再び一段ずつ解ける三角写像になっています。

依存関係の修正も正しいです。`GB` の $C$ 依存と `HC` の $B,C$ 依存を落とすと、実在する交差項を消してしまいます。Lean が固定した現在の形が本体です。

---

## 1. exact $(3,6)$ は valuation 理論なしで閉じる

actual source root を、

$$
x=A+B\theta+C\theta^2
$$

とします。

左右を $\varepsilon=-1,+1$ で統一すると、source equation から、

$$
G(A,B,C)=\varepsilon,7^3m^7
$$

$$
H(A,B,C)=0
$$

です。

さらに source の定数項は modulo $7$ で $a$ なので、

$$
A\equiv a\pmod7
$$

です。既存 packet には $7\nmid a$ があるため、

$$
7\nmid A
$$

です。

### 三角 depth-step

次の一段補題を作れば、証明全体が自己相似になります。

$k<3$ とし、

$$
7^k\mid B
$$

$$
7^{2k}\mid C
$$

を仮定します。

そこで、

$$
B=7^kb,\qquad C=7^{2k}c
$$

と置きます。

$G$ は、

$$
G=7^k\left(b,GB+7^{1+3k}c^2GC\right)
$$

となります。

一方、

$$
G=\varepsilon,7^3m^7
$$

です。

$k<3$ なので、$7^k$ を消去した後の右辺には、まだ $7$ が残っています。第二項にも少なくとも $7$ が残っています。

したがって modulo $7$ で、

$$
b,GB\equiv0
$$

です。

$GB$ は unit なので、

$$
7\mid b
$$

すなわち、

$$
7^{k+1}\mid B
$$

です。

次に、

$$
C,HC=-B^2HB
$$

です。

$HC$ は unit であり、右辺には $7^{2(k+1)}$ が含まれるため、

$$
7^{2(k+1)}\mid C
$$

です。

従って一段の操作は、

$$
(k,2k)\longmapsto(k+1,2k+2)
$$

です。

これを $k=0,1,2$ と三回繰り返せば、

$$
\boxed{7^3\mid B}
$$

$$
\boxed{7^6\mid C}
$$

です。

これは `padicValNat` を導入せず、既存の `dvd`、`IsCoprime`、ZMod reduction だけで閉じます。

推奨補題は、

```lean
theorem triangularJet_depth_step
    {A B C M ε : ℤ}
    (k : ℕ)
    (hk : k < 3)
    (hA : ¬(7 : ℤ) ∣ A)
    (hGB : ¬(7 : ℤ) ∣ seventhThetaLinearBFactor A B C)
    (hHC : ¬(7 : ℤ) ∣ seventhThetaSquareCFactor A B C)
    (hG :
      seventhThetaLinearQuotient A B C =
        ε * 7 ^ 3 * M ^ 7)
    (hH :
      seventhThetaSquareQuotient A B C = 0)
    (hB : (7 : ℤ) ^ k ∣ B)
    (hC : (7 : ℤ) ^ (2 * k) ∣ C) :
    (7 : ℤ) ^ (k + 1) ∣ B ∧
      (7 : ℤ) ^ (2 * (k + 1)) ∣ C
```

です。

`hGB`、`hHC` は毎回引数に持たせず、$A$ unit と residue theorem から内部生成してもよいです。

---

## 2. depth は下限ではなく exact になる

三段 lifting 後、

$$
B=7^3u
$$

$$
C=7^6v
$$

と置きます。

$G$ を $7^3$ で割ると、

$$
u,GB+7^{10}v^2GC=\varepsilon m^7
$$

です。

modulo $7$ では、

$$
uA^6\equiv\varepsilon m^7
$$

です。

$A,m$ は units なので、

$$
A^6\equiv1,\qquad m^7\equiv m
$$

です。従って、

$$
\boxed{u\equiv\varepsilon m\pmod7}
$$

です。

よって、

$$
7\nmid u
$$

です。

次に $H$ を $7^6$ で割ると、

$$
v,HC+u^2HB=0
$$

です。

modulo $7$ で、

$$
vA^6+3u^2A^5=0
$$

すなわち、

$$
\boxed{Av+3u^2\equiv0\pmod7}
$$

です。

$A,u$ は units なので、

$$
7\nmid v
$$

です。

したがって、

$$
\boxed{v_7(B)=3,\qquad v_7(C)=6}
$$

が exact に閉じます。

---

## 3. 左右 root は一つの slope から生成される

左右 root について、

$$
A_L\equiv A_R\equiv a\pmod7
$$

です。

また、

$$
u_L\equiv-m\pmod7
$$

$$
u_R\equiv m\pmod7
$$

です。

そして、

$$
Av+3u^2\equiv0
$$

より、

$$
v\equiv-3A^{-1}u^2
$$

です。

符号は平方で消えるため、

$$
\boxed{v_L\equiv v_R\equiv-3a^{-1}m^2\pmod7}
$$

です。

つまり左右 root は、

```text
left:
  A ≡ a
  u ≡ -m
  v ≡ -3 a⁻¹ m²

right:
  A ≡ a
  u ≡  m
  v ≡ -3 a⁻¹ m²
```

です。

第三座標は残りますが、自由変数ではありません。

> 線形 jet の符号だけが左右を分け、二次 jet は両者に共通する補正核です。

---

## 4. Outcome A は消え、Outcome C も自由ではない

exact packet が完成すると、

$$
C=7^6v
$$

かつ、

$$
7\nmid v
$$

なので、

$$
C\ne0
$$

です。

したがって、

$$
\boxed{\neg\operatorname{IsSourcePlane}(X_L)}
$$

$$
\boxed{\neg\operatorname{IsSourcePlane}(X_R)}
$$

です。

Outcome A は不可能です。

しかし、これは unrestricted Outcome C でもありません。

root は必ず、

$$
X=A+7^3u\theta+7^6v\theta^2
$$

かつ、

$$
Av+3u^2\equiv0
$$

という一本の quadratic jet graph 上にあります。

従って分類名は、次の方が正確です。

```text
Outcome A:
  source-plane root
  impossible

Outcome B′:
  controlled finite theta-jet sector
  actual result

Outcome C:
  unrestricted three-coordinate root
  excluded as a local model
```

---

## 5. 本当の FUSION invariant は一個の slope です

次の量を置きます。

$$
\tau=\frac{m}{a}\in\mathbf F_7^\times
$$

root を $A$ で projective normalization すると、

$$
\frac{u_R}{A_R}=\tau
$$

$$
\frac{u_L}{A_L}=-\tau
$$

です。

また、

$$
\frac{v}{A}=-3\left(\frac{u}{A}\right)^2
$$

なので、

$$
\frac{v_L}{A_L}=\frac{v_R}{A_R}=-3\tau^2
$$

です。

したがって左右 root の projective jet は、

$$
\boxed{J_R=(\tau,-3\tau^2)}
$$

$$
\boxed{J_L=(-\tau,-3\tau^2)}
$$

です。

この $\tau$ は整数 packet からも見えています。

現在 Lean は、

$$
d\equiv a^2m\pmod7
$$

を固定しました。

従って、

$$
\boxed{\tau=\frac{m}{a}=\frac{d}{a^3}\pmod7}
$$

です。

つまり同じ $\tau$ が、

```text
integer gapRoot
real-cubic root jet
paired left/right orientation
```

の三世界に同時に現れます。

これを正式に、

```lean
def fusionSlope
    (p : RamifiedSignedRootDepthPacket) : ZMod 7 :=
  (p.gapRoot : ZMod 7) /
    ((innerFst p : ZMod 7) ^ 3)
```

として固定する価値があります。

---

## 6. $2\times3$ routing の正体が見えました

$\mathbf F_7^\times$ は位数 $6$ の巡回群です。

任意の unit $s$ に対して、

$$
s^3\in{1,-1}
$$

です。

これは二つの row sector です。

一方、

$$
s^2\in{1,2,4}
$$

です。

これは三つの column sector です。

具体的には、

```text
s       1  2  3  4  5  6
s³      +  +  -  +  -  -
s²      1  4  2  2  4  1
```

です。

六つの unit が、重複なく完全な $2\times3$ grid を埋めます。

さらに、

$$
s=\frac{s^3}{s^2}
$$

なので、row と column の組は元の $s$ を一意に復元します。

これは偶然とは考えにくいです。

現在の signed routing は、

```text
2 nontrivial rows × 3 columns
```

です。

`CoprimeTripleRouting` の各 cell は row と column の gcd address として canonical であることが既に証明されています。

一方、paired jet では、

```text
right slope  =  τ
left slope   = -τ
```

です。

negation は、

$$
(-\tau)^3=-\tau^3
$$

によって row を反転しますが、

$$
(-\tau)^2=\tau^2
$$

によって column を保存します。

したがって左右 root は、

> 同一 column の上下二つの active cells

に入ります。

これは exact $(3,6)$ packet の後に構築すべき、本命の有限 address です。

推奨定義：

```lean
structure SevenUnitGridAddress where
  rowSign : ZMod 7
  columnClass : ZMod 7
  rowSign_eq : rowSign = slope ^ 3
  columnClass_eq : columnClass = slope ^ 2
```

実装上は、`rowSign` を custom two-element type、`columnClass` を custom three-element type にしてもよいでしょう。

---

## 7. これは完全円分体の六因子とも同じ grid です

原始七乗根を $\zeta$、$\lambda=1-\zeta$ とします。

非自明な六つの線形因子は、

$$
\beta_k=X_R-\zeta^kX_L,\qquad k=1,\dots,6
$$

です。

これらは $\mathbf F_7^\times$ の六元で添字付けされています。

従って $k$ 自身にも、

$$
(k^3,k^2)
$$

という $2\times3$ address があります。

つまり、

```text
signed integer 2×3 routing
theta-jet six-sector
six cyclotomic linear factors
```

は、すべて同じ

$$
\mathbf F_7^\times\cong C_2\times C_3
$$

を見ている可能性が高いです。

これは FUSION-003A と FUSION-003B が別ルートではなく、

> 同じ六 sector の integer realization と cyclotomic realization

である可能性を示します。

---

## 8. `quotientRoot ≡ 1` の本当の意味

ここは重要な補正です。

既存 terminal route では、normalized unit が $+1$ なら row `Y` です。

しかし、

$$
E\equiv1\pmod7
$$

だけから直ちに row `Y` を選ぶべきではありません。

この $+1$ は、signed seventh quotient に対して普遍的に現れます。

完全円分体で考えると、

$$
\frac{\beta_k}{\lambda}\equiv ka\pmod\lambda
$$

が予測されます。

従って、

$$
\frac{\Phi_7(X_R,X_L)}{\lambda^6}
\equiv(1\cdot2\cdot3\cdot4\cdot5\cdot6)a^6
\equiv-1
$$

です。

一方、

$$
\frac7{\lambda^6}
=\prod_{k=1}^{6}\frac{1-\zeta^k}{\lambda}
\equiv1\cdot2\cdot3\cdot4\cdot5\cdot6
\equiv-1
$$

です。

したがって、

$$
\frac{\Phi_7(X_R,X_L)}7\equiv\frac{-1}{-1}\equiv1
$$

です。

つまり `quotientRoot ≡ 1` は、

> Wilson product による cyclotomic normalization

と読むべきです。

これは row 固有の情報ではない可能性があります。

row-sensitive な候補は、むしろ、

$$
\tau^3\in{1,-1}
$$

です。

`awaySevenBaseRowSignUnit` と比較すべき対象は `quotientRoot` ではなく、**fusion slope の cube component** です。

---

## 9. exact jet 後に root gap はさらに鋭くなる

paired packet から、

$$
B_R-B_L=7^3(u_R-u_L)
$$

です。

かつ、

$$
u_R-u_L\equiv2m\not\equiv0\pmod7
$$

です。

従って linear gap は exact depth $3$ です。

一方、

$$
v_R\equiv v_L\pmod7
$$

なので、

$$
C_R-C_L
$$

には $7^7$ が入ります。

次に theta-constant power を展開すると、予測される形は、

```lean
thetaConstInt
    ((ofThetaCoordinates A (7^3*u) (7^6*v)) ^ 7)
  = A ^ 7 + 7 ^ 11 * correction
```

です。

左右 source の theta-constant 差は、

$$
(a+4n)-(a-3n)=7n=7^5m^7
$$

なので、これと integer seventh-quotient argument を合わせれば、

$$
A_R-A_L=7^4s
$$

かつ、

$$
s\equiv m\pmod7
$$

が得られるはずです。

すると root gap は、

$$
X_R-X_L=7^4s+7^3w\theta+7^7t\theta^2
$$

で、

$$
w\equiv2m\pmod7
$$

です。

$7=\theta^3U$、$U\equiv-1\pmod\theta$ を使うと、$\theta$-depth $10$ の先頭項は linear jet だけです。

従って既存 ledger の normalized `gapCore` について、

$$
\boxed{\mathrm{thetaConstModSeven}(\operatorname{gapCore})\equiv-2m}
$$

が予測されます。

これは単なる `gapCore_not_axis_dvd` より一段強い theorem です。

---

## 10. 次の packet 設計

まず root 一個の packet：

```lean
structure RamifiedThetaRootJetPacket : Type where
  root : SevenRealCubicInt
  sideSign : ℤ

  thetaConst : ℤ
  thetaLinearCore : ℤ
  thetaSquareCore : ℤ

  root_eq :
    root =
      SevenRealCubicInt.ofThetaCoordinates
        thetaConst
        (7 ^ 3 * thetaLinearCore)
        (7 ^ 6 * thetaSquareCore)

  thetaConst_not_seven_dvd :
    ¬(7 : ℤ) ∣ thetaConst

  thetaLinearCore_not_seven_dvd :
    ¬(7 : ℤ) ∣ thetaLinearCore

  thetaSquareCore_not_seven_dvd :
    ¬(7 : ℤ) ∣ thetaSquareCore

  thetaConst_modSeven :
    (thetaConst : ZMod 7) = innerFst

  thetaLinearCore_modSeven :
    (thetaLinearCore : ZMod 7) =
      sideSign * innerSndRoot

  quadraticJet_modSeven :
    ((thetaConst * thetaSquareCore +
      3 * thetaLinearCore ^ 2 : ℤ) : ZMod 7) = 0
```

その後、左右を束ねます。

```lean
structure RamifiedPairedThetaRootJetPacket : Type where
  signedDepth : RamifiedSignedRootDepthPacket
  left : RamifiedThetaRootJetPacket
  right : RamifiedThetaRootJetPacket

  left_side : left.sideSign = -1
  right_side : right.sideSign = 1

  left_root_eq : left.root = exactPower.leftRoot
  right_root_eq : right.root = exactPower.rightRoot
```

ここから corollary として、

```lean
left_not_sourcePlane
right_not_sourcePlane
linearCores_opposite_modSeven
squareCores_equal_modSeven
```

を出します。

---

## 次の Codex 指示

```text
Continue FLT7-FUSION from commit
b110bfbca31a37883415229e4d9b540ca42b6465
on branch wip/FLT7-fusion-260729.

Goal:
complete the exact paired theta-jet packet for FUSION-002.
Do not begin the full cyclotomic carrier yet.

1. Add a generic division-free triangular lifting theorem.

Inputs should include:

- 7 ∤ A;
- 7 ∤ M;
- G(A,B,C) = sign * 7^3 * M^7;
- H(A,B,C) = 0;
- sign = 1 or sign = -1.

Use the existing identities

G = B * GB(A,B,C) + 7 * C^2 * GC(A,C)
H = C * HC(A,B,C) + B^2 * HB(A,B)

and the proved modulo-seven residues.

Prefer a reusable one-step theorem:

triangularJet_depth_step

which advances

7^k ∣ B
7^(2*k) ∣ C

to

7^(k+1) ∣ B
7^(2*(k+1)) ∣ C

for k < 3.

Iterate it at k = 0, 1, 2.

Do not introduce a general p-adic valuation layer unless the
division-free proof genuinely fails.

2. Prove the exact normalized output.

Construct U and V with

B = 7^3 * U
C = 7^6 * V

and prove

7 ∤ U
7 ∤ V
U = sign * M              in ZMod 7
A * V + 3 * U^2 = 0       in ZMod 7.

3. Connect the theorem to the actual exact-power packet.

Add theta-coordinate lemmas for leftSource and rightSource:

left source:
  thetaConst  = a - 3*n
  thetaLinear = -n
  thetaSquare = 0

right source:
  thetaConst  = a + 4*n
  thetaLinear = n
  thetaSquare = 0.

Use n = 7^4 * m^7.

Prove that the theta constant of each exact algebraic root is
congruent to a modulo seven and is therefore a seven-unit.

4. Add:

RamifiedThetaRootJetPacket
RamifiedPairedThetaRootJetPacket

The paired packet must record:

left U  = -m             in ZMod 7
right U =  m             in ZMod 7
left V  = right V        in ZMod 7
V = -3 * a⁻¹ * m^2       in ZMod 7.

5. Derive the formal FUSION-002 outcome.

Prove:

- neither exact root lies in IsSourcePlane;
- both roots have exact theta-linear integer depth 3;
- both roots have exact theta-square integer depth 6;
- the roots lie in a controlled finite projective theta-jet sector.

Do not describe the result as unrestricted Outcome C.
Record it as a controlled finite theta-jet outcome.

6. Add a lightweight fusion-slope layer.

Define the modulo-seven slope

tau = m / a.

Also prove its integer-shadow expression

tau = gapRoot / a^3.

For the paired roots prove:

right normalized linear jet = tau
left normalized linear jet  = -tau
normalized quadratic jet    = -3 * tau^2.

7. Reconnaissance only after the packet is complete.

Investigate the canonical six-sector address

row component    = tau^3 ∈ {1, -1}
column component = tau^2 ∈ {1, 2, 4}.

The pair (tau^3, tau^2) determines tau and gives a natural
2-by-3 address on ZMod 7 units.

Compare this address with:

- the active two-by-three cells of RamifiedSignedRootRoutingPacket;
- awaySevenBaseRowSignUnit;
- the six nontrivial cyclotomic indices k = 1,...,6.

Do not claim an identification until the existing fixed routing margins
and the new unit address have been connected by explicit equalities.

8. Optional immediate epilogue after the paired packet.

Prove a theta-constant seventh-power expansion at jet depth:

thetaConstInt
  ((ofThetaCoordinates A (7^3*U) (7^6*V))^7)
  = A^7 + 7^11 * correction.

Use the left/right source constants to derive

A_right - A_left = 7^4 * scalarGapCore
scalarGapCore = m mod 7.

Then derive a coordinate normal form for the algebraic root gap and
test the predicted residue

thetaConstModSeven gapCore = -2*m.

Keep the PR Draft.
Do not claim a reconstructed Fermat chart, strict descent, a descent
provider, or FLT7.
```

---

## 最終結論

今回の実装で、FUSION-002 は「巨大零点曲線」ではなくなりました。

正確には、

```text
three triangular lifting steps
        ↓
exact B-depth 3
exact C-depth 6
        ↓
one projective slope τ
        ↓
left/right opposite rows
common quadratic column
```

です。

さらに $\tau$ の、

$$
(\tau^3,\tau^2)
$$

は完全な $2\times3$ unit address を作ります。

これは、

```text
signed integer routing
real-cubic theta jets
degree-six cyclotomic factors
```

の三者を同じ有限グリッド上へ載せる候補です。

ここが本気の FUSION 魔核です。
