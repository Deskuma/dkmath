# FLT7-FUSION-001-B

## FLT7-FUSION-002：次数 7 零点曲線の正面突破は不要です

### 判定

`FUSION-001B` は完全に閉じました。

今回 Lean が固定したものは、単なる

```text
algebraic depth 10
integer depth 4
```

の併記ではありません。

```text
theta-depth 10 の algebraic perturbation
        ↓ coordinate norm first variation
明示的な depth-four coefficient
        ↓ coefficient_eq_gapRoot
signed integer gapRoot
```

という **同一係数による融合** です。

さらに、

```text
IsCoprime gapRoot quotientRoot
canonical 2 × 3 routing
```

まで完成しています。これは本来の意味での `FUSION-001` 完了です。

そして `FUSION-002` は、現在の巨大な

```text
seventhSourcePlaneEquation a b c = 0
```

を全整数上で直接分類する必要はありません。

$\theta$ 基底へ戻すと、この次数 7 曲線は局所的に三角化できます。

---

## 1. $\alpha$ 基底から $\theta$ 基底へ戻す

現在の実三次整数は、

$$
x=x_0+x_1\alpha+x_2\alpha^2
$$

です。

ここで、

$$
\theta=\alpha-3
$$

なので、

$$
\alpha=\theta+3,\qquad \alpha^2=\theta^2+6\theta+9
$$

です。

したがって、$x$ を

$$
x=A+B\theta+C\theta^2
$$

と書くと、

$$
A=x_0+3x_1+9x_2
$$

$$
B=x_1+6x_2
$$

$$
C=x_2
$$

です。

これは既存の

```lean
thetaConstModSeven
thetaLinearModSeven
thetaSquareModSeven
```

の整数版そのものです。

また $\theta$ は、

$$
\theta^3+7\theta^2+14\theta+7=0
$$

すなわち、

$$
\theta^3=-7(\theta+1)^2
$$

を満たします。$\theta+1$ は unit なので、

$$
7\sim\theta^3
$$

です。

---

## 2. source-plane equation の本当の局所形

$x=A+B\theta+C\theta^2$ とします。

$x^7$ の $\theta$ 座標を展開すると、ある整数係数多項式 $P,G,H$ によって、

$$
x^7=P(A,B,C)+7G(A,B,C)\theta+7H(A,B,C)\theta^2
$$

と書けます。

現在実装された `seventhSourcePlaneEquation` は、本質的にはこの $H$ です。

$$
x^7\in\operatorname{SourcePlane}\iff H(A,B,C)=0
$$

です。

ところが $G,H$ は、巨大な次数 7 多項式のまま扱う必要がありません。整理すると、次の形へ分かれます。

$$
G=B,G_B+7C^2G_C
$$

$$
H=C,H_C+B^2H_B
$$

ここで modulo $7$ では、

$$
G_B\equiv A^6\pmod 7
$$

$$
H_C\equiv A^6\pmod 7
$$

$$
H_B\equiv3A^5\pmod 7
$$

$$
G_C\equiv-3A^5\pmod 7
$$

です。

特に $7\nmid A$ なら、$G_B,H_C,H_B$ はすべて $7$-units になります。

これが次数 7 零点曲線の魔核です。

---

## 3. exact-power packet が与える入力

現在の exact-power packet には、

$$
X_L^7=\operatorname{leftSource}(a,n)
$$

$$
X_R^7=\operatorname{rightSource}(a,n)
$$

があります。

また、

$$
n=7^4m^7
$$

かつ、

$$
7\nmid m
$$

です。

$\theta$ 基底では source は、

$$
\operatorname{leftSource}(a,n)=(a-3n)-n\theta
$$

$$
\operatorname{rightSource}(a,n)=(a+4n)+n\theta
$$

です。

したがって、左右それぞれについて、

$$
X_\varepsilon^7=S_\varepsilon+\varepsilon,7^4m^7\theta
$$

となります。ここで $\varepsilon=-1$ が左、$\varepsilon=1$ が右です。

$\theta^2$ 成分は完全にゼロです。

さらに root は $\theta$-unit なので、

$$
7\nmid A
$$

です。左 root が $\theta$ で割れないことは既に証明され、root gap が $\theta$ で割れるため右 root も同じ非零 residue を持ちます。

---

## 4. 第二・第三座標の exact depth が強制される

$\theta$ 線形成分の比較から、

$$
7G(A,B,C)=\varepsilon,7^4m^7
$$

です。

よって、

$$
G(A,B,C)=\varepsilon,7^3m^7
$$

です。

一方、source-plane 条件から、

$$
H(A,B,C)=0
$$

です。

まず modulo $7$ を取ります。

$$
G\equiv A^6B\pmod7
$$

であり、右辺は $7$ で割れるので、

$$
7\mid B
$$

です。

次に、

$$
H\equiv A^6C+3A^5B^2\pmod7
$$

です。

既に $7\mid B$ なので、

$$
A^6C\equiv0\pmod7
$$

です。

$7\nmid A$ より、

$$
7\mid C
$$

です。

ここまでは第一段の residue です。

---

### $H=0$ が第三座標を第二座標の平方へ固定する

因子分解、

$$
H=C,H_C+B^2H_B
$$

を使います。

$H_C,H_B$ は $7$-units なので、

$$
C,H_C=-B^2H_B
$$

から、

$$
v_7(C)=2v_7(B)
$$

が得られます。

つまり第三座標は独立ではありません。

第二座標 $B$ が決まれば、第三座標 $C$ はその平方深度へ自動的に送られます。

---

### $G$ が第二座標の exact depth を決める

もう一方の式は、

$$
G=B,G_B+7C^2G_C
$$

です。

$s=v_7(B)$ と置くと、

$$
v_7(C)=2s
$$

なので、二項の深度は、

$$
v_7(BG_B)=s
$$

$$
v_7(7C^2G_C)=1+4s
$$

です。

$s\ge1$ なので、

$$
s<1+4s
$$

です。

従って cancellation は起きず、

$$
v_7(G)=s
$$

です。

一方、

$$
G=\varepsilon,7^3m^7
$$

かつ $7\nmid m$ なので、

$$
v_7(G)=3
$$

です。

ゆえに、

$$
\boxed{v_7(B)=3}
$$

そして、

$$
\boxed{v_7(C)=6}
$$

です。

---

## 5. Outcome A は不可能です

したがって root は必ず、

$$
B=7^3u
$$

$$
C=7^6v
$$

と書け、

$$
7\nmid u,\qquad7\nmid v
$$

です。

特に、

$$
C\ne0
$$

です。

`IsSourcePlane x` は $C=0$ なので、

$$
\boxed{X_L\notin\operatorname{SourcePlane}}
$$

$$
\boxed{X_R\notin\operatorname{SourcePlane}}
$$

です。

つまり FUSION-002 の Outcome A は、単に「まだ証明されていない」のではありません。

> 現在の exact-power packet では Outcome A は成立しません。

root は必ず真正な三座標元です。

したがって、文字どおりの A/B/C 分類ならば、raw coordinate 上は Outcome C が選ばれます。

ただし、この三座標性は自由な三座標性ではありません。

---

## 6. root は scalar から exact $\theta$-depth 10 だけ離れている

root は、

$$
X=A+7^3u\theta+7^6v\theta^2
$$

です。

$7^3\theta$ は、

$$
7^3\theta\sim\theta^{10}
$$

です。

また、

$$
7^6\theta^2\sim\theta^{20}
$$

です。

したがって、

$$
X-A=7^3\theta\left(u+7^3v\theta\right)
$$

です。

括弧内は $\theta$-unit なので、

$$
\boxed{v_\theta(X-A)=10}
$$

です。

これは非常に重要です。

root は source plane 上にはいませんが、

> 整数 scalar 軸から exact $\theta$-depth $10$ の位置にある。

という、極めて細い ramified jet 上にあります。

```text
scalar A
   +
theta-depth 10 linear jet
   +
theta-depth 20 quadratic correction
```

です。

従って FUSION-002 は「三座標 root の全分類」ではなく、

```text
exact theta-depth-10 scalar jets
```

の分類へ縮小できます。

---

## 7. 左右 root の sector は符号まで決まる

$B=7^3u$、$C=7^6v$ を $G,H$ に代入します。

$\theta$ 線形成分の式を $7^3$ で割って modulo $7$ を取ると、

$$
A^6u\equiv\varepsilon m^7\pmod7
$$

です。

$A$ は $7$-unit なので、

$$
A^6\equiv1\pmod7
$$

です。

また、

$$
m^7\equiv m\pmod7
$$

です。

従って、

$$
\boxed{u\equiv\varepsilon m\pmod7}
$$

です。

左右については、

$$
u_L\equiv-m\pmod7
$$

$$
u_R\equiv m\pmod7
$$

です。

したがって、

$$
u_R-u_L\equiv2m\not\equiv0\pmod7
$$

です。

これが root gap の exact $\theta$-depth $10$ の局所的な正体です。

左右の root は、同じ scalar sector から、

```text
left  jet direction = -m
right jet direction = +m
```

へ分岐しています。

---

## 8. 第三座標は左右で同じ二次補正を持つ

$H=0$ を $7^6$ で割って modulo $7$ を取ると、

$$
A^6v+3A^5u^2\equiv0\pmod7
$$

です。

$A$ は unit なので、

$$
\boxed{Av+3u^2\equiv0\pmod7}
$$

すなわち、

$$
\boxed{v\equiv-3A^{-1}u^2\pmod7}
$$

です。

左右では $u$ の符号だけが反転しますが、$u^2$ は同じです。

また source の scalar residue は左右とも $a$ なので、

$$
A_L\equiv A_R\equiv a\pmod7
$$

です。

したがって、

$$
v_L\equiv v_R\equiv-3a^{-1}m^2\pmod7
$$

です。

つまり、局所図は次の形です。

```text
left root:
  scalar residue       a
  linear jet          -m
  quadratic correction -3 a⁻¹ m²

right root:
  scalar residue       a
  linear jet          +m
  quadratic correction -3 a⁻¹ m²
```

左右差を生むのは線形 jet の符号だけです。

第三座標は、その線形 jet を source plane へ七乗で戻すための共通補正です。

これはまさに「魔核生成術式」の二次補正層です。

---

## 9. scalar 座標差も exact depth 4 になる

$x^7$ の scalar $\theta$ 座標は、$B=7^3u$、$C=7^6v$ のもとで、

$$
P(A,B,C)\equiv A^7\pmod{7^{10}}
$$

です。

左右 source の scalar 座標差は、

$$
(a+4n)-(a-3n)=7n=7^5m^7
$$

です。

よって、

$$
A_R^7-A_L^7\equiv7^5m^7\pmod{7^{10}}
$$

です。

$A_L,A_R$ は同じ非零 residue を持つので、整数側の seventh-power difference と同様に、

$$
v_7(A_R-A_L)=4
$$

です。

従って、

$$
A_R-A_L=7^4s
$$

と書け、

$$
s\equiv m\pmod7
$$

となります。

root gap の $\theta$ 基底表示は概念的に、

```text
scalar difference       7^4 s
linear difference        7^3 (uR-uL)
quadratic difference     7^6 (vR-vL)
```

です。

このうち $\theta$-depth $10$ の主成分は、線形差 $u_R-u_L\equiv2m$ です。

---

## 10. integer gapRoot の residue が決まる

$\theta$ 基底で Norm は、

$$
N(A+B\theta+C\theta^2)=A^3-7A^2B+21A^2C+14AB^2-77ABC+98AC^2-7B^3+49B^2C-98BC^2+49C^3
$$

です。

$B=7^3u$、$C=7^6v$ の場合、depth $4$ までで残るのは、

$$
N(X)\equiv A^3-7^4A^2u\pmod{7^7}
$$

です。

左右差を $7^4$ で割ると、

$$
d\equiv a^2\left(3s-(u_R-u_L)\right)\pmod7
$$

です。

既に、

$$
s\equiv m\pmod7
$$

$$
u_R-u_L\equiv2m\pmod7
$$

なので、

$$
\boxed{d\equiv a^2m\pmod7}
$$

です。

これは `coefficient_eq_gapRoot` の modulo $7$ 先頭項です。

つまり `normFirstVariationCoefficient` は、巨大な座標式に見えますが、局所先頭項は極めて単純です。

```text
gapRoot leading unit = a² × m
```

です。

---

## 11. quotientRoot は必ず $+1$ sector です

これはさらに簡単に現在の signed quotient 恒等式から出ます。

$$
\Phi_7(r,l)-7l^6=(r-l)F(r,l)
$$

であり、

$$
r-l=7^4d
$$

です。

また、

$$
\Phi_7(r,l)=7E
$$

です。

従って modulo $7$ で、

$$
E\equiv l^6\pmod7
$$

です。

$7\nmid l$ なので、

$$
l^6\equiv1\pmod7
$$

です。

ゆえに、

$$
\boxed{E\equiv1\pmod7}
$$

です。

さらに、

$$
dE=a(a+n)m^7
$$

へ代入すれば、

$$
d\equiv a^2m\pmod7
$$

が整数 routing だけからも再確認できます。

したがって新しい $2\times3$ routing の左辺 unit sector は、

```text
gapRoot unit      = a² m
quotientRoot unit = 1
```

まで固定されます。

この $E\equiv1$ は、既存 terminal route の positive unit sector と非常によく似ています。

既存 API では normalized unit が $1$ になるのは row `Y` のみです。

ただし、現段階では、

```text
quotientRoot E
=
AwaySevenBaseUnitEquationPacket.normalized_rootLinearUnit
```

という bridge はまだありません。

従って、まだ「row Y が確定した」とは言いません。

しかし次の最重要探索対象は明確です。

```text
E ≡ 1
        ↓ identification bridge
normalized terminal unit = 1
        ↓
row = Y
```

この bridge が通れば、FUSION-003A の直接 chart reconstruction が一気に近づきます。

---

## 12. FUSION-002 の判定を更新する

元の分類は、

```text
A. root 自身が source plane
B. finite unit-translated planes
C. genuine three-coordinate root
```

でした。

今回の推論で、

```text
A. impossible
```

です。

そして、

```text
C. true
```

です。

ただし C は「自由な一般三座標」ではありません。

```text
A unit scalar
+
exact theta-depth 10 linear jet
+
forced theta-depth 20 quadratic correction
```

という有限 residue sector に閉じ込められています。

従って実際の分類は、

```text
A. source plane
   impossible

B'. finite theta-jet sectors
   strongly predicted

C. unrestricted three-coordinate root
   false as a local description
```

と読み替えるべきです。

第三座標は残りますが、自由度はありません。

$$
v\equiv-3A^{-1}u^2\pmod7
$$

という放物線状の jet graph に拘束されています。

---

## 13. 次の Lean 実装順序

### FUSION-002A — integral $\theta$ coordinates

```lean
def thetaConstInt (x : SevenRealCubicInt) : ℤ :=
  x.fst + 3 * x.snd + 9 * x.thd

def thetaLinearInt (x : SevenRealCubicInt) : ℤ :=
  x.snd + 6 * x.thd

def thetaSquareInt (x : SevenRealCubicInt) : ℤ :=
  x.thd
```

```lean
theorem theta_coordinate_decomposition
    (x : SevenRealCubicInt) :
    x =
      (thetaConstInt x : SevenRealCubicInt) +
        thetaLinearInt x * eisensteinAxis +
        thetaSquareInt x * eisensteinAxis ^ 2
```

---

### FUSION-002B — divided seventh-power coordinates

```lean
def seventhThetaLinearQuotient (A B C : ℤ) : ℤ := ...
def seventhThetaSquareQuotient (A B C : ℤ) : ℤ := ...
```

```lean
theorem thetaLinear_pow_seven
    (x : SevenRealCubicInt) :
    thetaLinearInt (x ^ 7) =
      7 * seventhThetaLinearQuotient
        (thetaConstInt x)
        (thetaLinearInt x)
        (thetaSquareInt x)
```

```lean
theorem thetaSquare_pow_seven
    (x : SevenRealCubicInt) :
    thetaSquareInt (x ^ 7) =
      7 * seventhThetaSquareQuotient
        (thetaConstInt x)
        (thetaLinearInt x)
        (thetaSquareInt x)
```

---

### FUSION-002C — triangular factor identities

```lean
theorem seventhThetaLinearQuotient_factor :
    G A B C =
      B * GB A B C + 7 * C ^ 2 * GC A B C
```

```lean
theorem seventhThetaSquareQuotient_factor :
    H A B C =
      C * HC A B C + B ^ 2 * HB A B
```

そして、

```lean
GB A B C ≡ A^6 [ZMOD 7]
HC A B C ≡ A^6 [ZMOD 7]
HB A B   ≡ 3*A^5 [ZMOD 7]
```

を固定します。

巨大 polynomial 全体の分類は不要です。

必要なのはこの三つの unit residue だけです。

---

### FUSION-002D — exact root jet packet

推奨 packet は、

```lean
structure RamifiedSeventhRootJetPacket : Type where
  root : SevenRealCubicInt

  thetaConst : ℤ
  thetaLinearCore : ℤ
  thetaSquareCore : ℤ

  thetaConst_eq :
    thetaConstInt root = thetaConst

  thetaLinear_eq :
    thetaLinearInt root = 7 ^ 3 * thetaLinearCore

  thetaSquare_eq :
    thetaSquareInt root = 7 ^ 6 * thetaSquareCore

  thetaConst_not_seven_dvd :
    ¬(7 : ℤ) ∣ thetaConst

  thetaLinearCore_not_seven_dvd :
    ¬(7 : ℤ) ∣ thetaLinearCore

  thetaSquareCore_not_seven_dvd :
    ¬(7 : ℤ) ∣ thetaSquareCore

  quadraticJetEquation :
    ((thetaConst * thetaSquareCore +
      3 * thetaLinearCore ^ 2 : ℤ) : ZMod 7) = 0
```

です。

左右を束ねる packet には、

```lean
leftLinearCore_modSeven :
  left.thetaLinearCore = -m

rightLinearCore_modSeven :
  right.thetaLinearCore = m
```

を `ZMod 7` 等式として持たせます。

---

### FUSION-002E — integer unit-sector fusion

先に安価な theorem を置けます。

```lean
theorem quotientRoot_modSeven_eq_one
    (p : RamifiedSignedRootDepthPacket) :
    (p.quotientRoot : ZMod 7) = 1
```

```lean
theorem gapRoot_modSeven_eq
    (p : RamifiedSignedRootDepthPacket) :
    (p.gapRoot : ZMod 7) =
      (innerFst : ZMod 7) ^ 2 *
        (innerSndRoot : ZMod 7)
```

その後、

```text
quotientRoot = +1 sector
        +
canonical 2 × 3 routing
        +
existing terminal normalized-unit API
```

の identification を試します。

ここが通れば `FUSION-003A`。

通らなければ、jet packet をそのまま完全円分体へ持ち上げて `FUSION-003B` です。

---

## 14. 完全円分体へ進む場合も情報は大幅に増えた

$\theta\sim\lambda^2$ なので、

$$
v_\theta(X-A)=10
$$

は、

$$
v_\lambda(X-A)=20
$$

になります。

従って、

$$
X_R-\zeta X_L=(X_R-X_L)+(1-\zeta)X_L
$$

では、

```text
X_R - X_L     lambda-depth 20
(1-zeta) X_L  lambda-depth 1
```

です。

ゆえに、

$$
v_\lambda(X_R-\zeta X_L)=1
$$

です。

これは以前の予測どおりですが、今度は各 root 自身が scalar modulo $\lambda^{20}$ であることまで分かります。

したがって linear Kummer factor の residue は、ほぼ scalar $a$ によって固定されます。

```text
beta / lambda mod lambda
```

の unit class が曖昧な一般元ではなく、source scalar residue から来ることになります。

full cyclotomic route に進む場合も、unit-class 戦は以前予測したより軽くなる可能性があります。

---

## 最終結論

`FUSION-001B` の完成によって、depth $10\to4$ は完全に同一係数へ融合しました。

そして `FUSION-002` の次手は、

```text
primitive integral zero-locus of a degree-seven plane curve
```

の全分類ではありません。

正しい敵は、

```text
theta-linear exact depth 3
theta-square exact depth 6
quadratic jet residue
```

です。

最も強い新規予測は、次の五本です。

$$
\boxed{v_7(B)=3}
$$

$$
\boxed{v_7(C)=6}
$$

$$
\boxed{u_L\equiv-m,\qquad u_R\equiv m\pmod7}
$$

$$
\boxed{v_L\equiv v_R\equiv-3a^{-1}m^2\pmod7}
$$

$$
\boxed{E\equiv1,\qquad d\equiv a^2m\pmod7}
$$

これにより Outcome A は消えます。

しかし Outcome C は無制御な三座標世界ではなく、

> exact $\theta$-depth $10$ の左右対称 jet と、その depth $20$ の二次補正

へ圧縮されます。

次の一手は `seventhSourcePlaneEquation` の巨大式を殴ることではありません。

```text
theta jet exact-depth packet
        ↓
E = +1 unit-sector bridge
        ↓
direct row/chart reconstruction test
```

です。

ここで row reconstruction が成功すれば `FUSION-003A`。

失敗しても、その jet packet はそのまま $\lambda$-depth $1$ の linear Kummer packet を作るため、`FUSION-003B` へ無駄なく接続します。

魔核はもう、次数 7 多項式の内部から取り出せています。
