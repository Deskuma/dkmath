# FLT7-FUSION-003D-REAL-PAIR-CARRIER result review and next

## 賢狼の総合判定

## FUSION-003D は完成です

今回の実装により、

```text
signed integer roots
  → three real conjugate-pair carriers
  → exact theta-depth-one cores
  → ternary pair selection by tau²
  → left/right quadratic theta jets
```

が一つの Lean 経路として閉じました。

三つの carrier $P_i$ の積が `signedSeventhQuotient` になり、各 carrier が $P_i=\theta C_i$ と正規化され、各 core の residue が pair phase の負号として確定しています。さらに exact $\theta$-depth $1$ も証明済みです。

また、

$$
-(\theta+1)^2C_0C_1C_2=\operatorname{quotientRoot}
$$

という厳密な積再構成から、`quotientRoot ≡ 1 mod 7` の第二証明まで到達しています。

選択された index は $\tau^2$ による ternary pair であり、selected core の residue と左右 quadratic jet は、

$$
\mathrm{thetaResidue}(C_{\tau})=-\tau^2
$$

$$
\frac{V_L}{A_L}=\frac{V_R}{A_R}=3,\mathrm{thetaResidue}(C_{\tau})=-3\tau^2
$$

として直接融合しました。binary orientation を使わず、unordered pair ${\tau,-\tau}$ だけを選ぶ構造も正確です。

---

## 1. 現在の coprimality の壁は、実際には消せます

レポートでは残る補題を、

```text
IsCoprime (r*l) gapRoot
```

としています。

これは新しい深い定理を必要とせず、既存 packet の Bézout 等式だけで証明できます。

以下、

$$
r=\operatorname{signedRightRoot},\qquad l=\operatorname{signedLeftRoot},\qquad d=\operatorname{gapRoot}
$$

と置きます。

既存 packet には、

$$
\operatorname{IsCoprime}(l,r)
$$

$$
r-l=7^4d
$$

があります。

`IsCoprime l r` の Bézout witness を、

$$
ul+vr=1
$$

とします。

$r-7^4d=l$ を代入すると、

$$
(u+v)r-u7^4d=1
$$

なので、

$$
\operatorname{IsCoprime}(r,d)
$$

です。

同様に $r=l+7^4d$ を代入すれば、

$$
(u+v)l+v7^4d=1
$$

なので、

$$
\operatorname{IsCoprime}(l,d)
$$

です。

したがって、

$$
\boxed{\operatorname{IsCoprime}(rl,d)}
$$

が得られます。

この証明には $7\nmid r,l,d$ さえ不要です。`signedRoots_isCoprime` と `signedGap_eq` だけで閉じます。

Lean の theorem 目標はそのまま、

```lean
theorem signedRootsProduct_isCoprime_gapRoot
    (p : RamifiedSignedRootDepthPacket) :
    IsCoprime
      (p.signedRightRoot * p.signedLeftRoot)
      p.gapRoot
```

です。

---

## 2. 整数素因子を三次整数環へ戻す補題も不要です

さらに重要な点です。

レポートでは、

> 整数の共通素因子を三次整数環へ輸送する補題

が必要とされていますが、prime-divisor transport 自体を使わずに pairwise coprimality を証明できます。

次を置きます。

$$
R=rl
$$

$$
H=\theta^{23},\operatorname{thetaSevenUnit}^8,d^2
$$

$$
C_i=H-u_iR
$$

`realPairCore` はまさにこの形です。

### $R$ と $d$ の coprimality

先ほどの整数定理を、

```lean
Int.castRingHom SevenRealCubicInt
```

で map すれば、

$$
\operatorname{IsCoprime}\bigl((R:\mathcal O),(d:\mathcal O)\bigr)
$$

が得られます。

### $R$ と $\theta$ の coprimality

今回 Lean は、

$$
R\equiv1\pmod7
$$

を証明しています。

そこで整数 $k$ を、

$$
R-1=7k
$$

として取ります。

既存の ramified relation、

$$
7=\theta^3\operatorname{thetaSevenUnit}
$$

を代入すると、

$$
R-\theta\left(\theta^2\operatorname{thetaSevenUnit}k\right)=1
$$

です。

これはそのまま $R$ と $\theta$ の Bézout identity です。

よって、

$$
\operatorname{IsCoprime}(R,\theta)
$$

です。

### $R$ と高次項 $H$

$R$ は $\theta$ と $d$ に coprime であり、`thetaSevenUnit` は unit です。

したがって、

$$
\operatorname{IsCoprime}(R,H)
$$

となります。

### $R$ と各 core

$C_i=H-u_iR$ なので、Bézout identity の通常の加減変換により、

$$
\operatorname{IsCoprime}(R,C_i)
$$

です。

### core 同士

core の差は、

$$
C_i-C_j=-(u_i-u_j)R
$$

です。

今回、三つの $u_i-u_j$ の norm が $-1,-1,1$ であり、全て global unit であることが既に証明されました。

したがって $C_i-C_j$ は $R$ の unit multiple です。

$R\perp C_i$ であるため、

$$
\boxed{\operatorname{IsCoprime}(C_i,C_j)}
$$

が従います。

つまり coprimality の証明経路は、

```text
integer Bezout
  → map to SevenRealCubicInt
  → R ⟂ theta
  → R ⟂ H
  → R ⟂ Cᵢ
  → Cᵢ - Cⱼ = unit * R
  → Cᵢ ⟂ Cⱼ
```

です。

**三次整数環の prime を整数 prime へ戻す必要はありません。**

---

## 3. 次に固定すべきは Galois naturality

pairwise coprimality の次に、すぐ seventh-power extraction へ進んではなりません。

先に三つの core の Galois 関係を固定すべきです。

carrier は定義から、

$$
P_1=\sigma(P_0),\qquad P_2=\sigma^2(P_0)
$$

となるはずです。

整数 $r,l$ は Galois rotation で固定され、`cyclicAlpha` だけが三つの共役を巡るためです。

一方、

$$
P_0=\theta C_0
$$

であり、

$$
\sigma(\theta)=\theta u_1
$$

$$
\sigma^2(\theta)=\theta u_2
$$

です。

したがって $\theta\neq0$ を消去すれば、

$$
\boxed{C_1=u_1\sigma(C_0)}
$$

$$
\boxed{C_2=u_2\sigma^2(C_0)}
$$

が得られます。

これは三つの core が単に同じ residue family なのではなく、

> **unit-twisted Galois conjugates**

であることを示します。

推奨 theorem：

```lean
theorem rotate_realPairCarrier_zero :
    rotateEquiv (p.realPairCarrier 0) =
      p.realPairCarrier 1

theorem rotate_realPairCarrier_one :
    rotateEquiv (p.realPairCarrier 1) =
      p.realPairCarrier 2

theorem realPairCore_one_eq_unit_mul_rotate :
    p.realPairCore 1 =
      pairAxisUnit 1 * rotateEquiv (p.realPairCore 0)

theorem realPairCore_two_eq_unit_mul_rotate_sq :
    p.realPairCore 2 =
      pairAxisUnit 2 *
        rotateEquiv (rotateEquiv (p.realPairCore 0))
```

---

## 4. 真の決定門は core の norm

既存 DkMath には、三次整数環の norm が三つの cyclic conjugate の積である定理があります。

よって、

$$
\operatorname{Norm}(P_0)=P_0P_1P_2
$$

です。

今回、

$$
P_0P_1P_2=7,\operatorname{quotientRoot}
$$

が証明されました。

また、

$$
P_0=\theta C_0
$$

であり、

$$
\operatorname{Norm}(\theta)=-7
$$

です。

したがって、

$$
-7,\operatorname{Norm}(C_0)=7,\operatorname{quotientRoot}
$$

となり、

$$
\boxed{\operatorname{Norm}(C_0)=-\operatorname{quotientRoot}}
$$

です。

$C_1,C_2$ は norm $1$ の unit を掛けた conjugate なので、

$$
\boxed{\operatorname{Norm}(C_i)=-\operatorname{quotientRoot}}
$$

が全 $i$ で成立すると予測されます。

これは極めて重要です。

---

## 5. pairwise coprime だけでは seventh power は出ません

現在の積は、

$$
-(\theta+1)^2C_0C_1C_2=\operatorname{quotientRoot}
$$

です。

右辺はまだ seventh power と証明されていません。

したがって、

```text
C₀, C₁, C₂ pairwise coprime
```

だけでは、

```text
Cᵢ = unit * seventhPower
```

は導けません。

実際、norm identity により、仮に、

$$
C_i=\varepsilon\gamma^7
$$

ならば、

$$
-\operatorname{quotientRoot}
=\operatorname{Norm}(\varepsilon)\operatorname{Norm}(\gamma)^7
$$

です。

したがって少なくとも、

$$
\boxed{|\operatorname{quotientRoot}|\text{ が七乗}}
$$

でなければなりません。

つまり norm は extraction の必要条件を完全に可視化します。

推奨するガード theorem は、

```lean
theorem quotientRoot_signedSeventhPower_of_core_associated_pow
    (p : RamifiedSignedRootDepthPacket)
    (i : Fin 3)
    (h :
      ∃ u : SevenRealCubicIntˣ,
        ∃ x : SevenRealCubicInt,
          p.realPairCore i = u * x ^ 7) :
    ∃ z : ℤ,
      p.quotientRoot = z ^ 7 ∨
      p.quotientRoot = -(z ^ 7)
```

です。

この theorem が通れば、「core extraction を主張するには何が必要か」が Lean 上で明文化されます。

---

## 6. `quotientRoot` の七乗性は routing の第2行問題

signed routing は、

```text
row 1 = |gapRoot|
row 2 = |quotientRoot|
row 3 = 1

column 1 = |a|
column 2 = |a+n|
column 3 = |m^7|
```

という canonical $2\times3$ board です。

さらに三つの column margins は互いに coprime で、normalized equation から board が inhabited になっています。

第2行を、

$$
|\operatorname{quotientRoot}|=c_{21}c_{22}c_{23}
$$

と読みます。

第3列は $|m^7|$ です。

したがって column-$3$ の coprime split により、$c_{13}$ と $c_{23}$ はそれぞれ七乗へ抽出できるはずです。

よって `quotientRoot` が七乗になるかどうかの本体は、

$$
\boxed{c_{21}c_{22}}
$$

です。

すなわち、次の二つの cell が魔核です。

```text
c21 : quotientRoot 側に入った a-column の成分
c22 : quotientRoot 側に入った (a+n)-column の成分
```

次の判定は、

```text
c21 = 1 and c22 = 1
```

または少なくとも、

```text
c21 and c22 are seventh powers
```

を既存 terminal provenance / row classification から証明できるかです。

これが閉じれば、

$$
|\operatorname{quotientRoot}|=z^7
$$

が得られ、pairwise coprime core の積から `exists_associated_pow_of_mul_eq_pow` を正当に適用できます。

閉じなければ、selected core は単独では seventh power ではなく、

> routing cell の scalar load を補正した **loaded pair core**

が必要です。

---

## 次フェーズの正式名称

```text
FUSION-003E — Real Pair Coprimality and Norm Gate
```

が適切です。

内容は二段です。

```text
003E-1:
  pair cores pairwise coprime

003E-2:
  Norm(Cᵢ) = -quotientRoot
  and decide whether quotientRoot is a signed seventh power
```

---

## Codex 指示

```text
Continue FLT7-FUSION from head

88748f05c1afdbafee50092a2791aadc8313108a

on branch

wip/FLT7-fusion-260729

FUSION-003D is complete.

The next phase is:

FUSION-003E — real-pair coprimality and norm gate.

1. Prove the integer coprimality directly by Bezout substitution.

For p : RamifiedSignedRootDepthPacket, prove:

IsCoprime
  (p.signedRightRoot * p.signedLeftRoot)
  p.gapRoot.

Use only:

p.signedRoots_isCoprime
p.signedGap_eq.

If u*l + v*r = 1 and r-l = 7^4*d, derive:

(u+v)*r - u*7^4*d = 1
(u+v)*l + v*7^4*d = 1.

Combine the two Bezout identities to obtain
IsCoprime (r*l) d.

Do not use prime factorization or seven-primitivity here.

2. Map this coprimality into SevenRealCubicInt.

Let:

R = (r*l : SevenRealCubicInt)
D = (d : SevenRealCubicInt)
H = theta^23 * thetaSevenUnit^8 * D^2.

Prove IsCoprime R D using IsCoprime.map.

3. Prove IsCoprime R theta by an explicit Bezout identity.

Use the existing theorem:

signedRoots_product_modSeven_eq_one

to obtain an integer k with:

r*l - 1 = 7*k.

Then rewrite:

7 = theta^3 * thetaSevenUnit

and prove:

R - theta * (theta^2 * thetaSevenUnit * k) = 1.

4. Prove:

IsCoprime R H

using coprimality with theta and D, and the unit property of
thetaSevenUnit.

5. Prove for every i:

IsCoprime R (p.realPairCore i).

Use:

realPairCore i = H - pairAxisUnit i * R.

This should be a Bezout-preserving affine transformation, not a
prime-divisor argument.

6. Prove the generic unit-difference theorem:

pairAxisUnit_sub_isUnit
    {i j : Fin 3} (hij : i ≠ j) :
    IsUnit (pairAxisUnit i - pairAxisUnit j).

Use fin_cases and the three existing explicit unit theorems.

Then prove:

realPairCore_sub
    p i j :
    p.realPairCore i - p.realPairCore j =
      -(pairAxisUnit i - pairAxisUnit j) * R.

Conclude:

Pairwise (fun i j =>
  IsCoprime (p.realPairCore i) (p.realPairCore j)).

Do not introduce a scalar-prime transport from the cubic order back to
the integers unless the Bezout route genuinely fails.

7. Add the Galois naturality layer.

Prove:

rotateEquiv (p.realPairCarrier 0) = p.realPairCarrier 1
rotateEquiv (p.realPairCarrier 1) = p.realPairCarrier 2
rotateEquiv (p.realPairCarrier 2) = p.realPairCarrier 0.

Then cancel theta in the normalized carrier identities and prove:

p.realPairCore 1 =
  pairAxisUnit 1 * rotateEquiv (p.realPairCore 0)

p.realPairCore 2 =
  pairAxisUnit 2 *
    rotateEquiv (rotateEquiv (p.realPairCore 0)).

8. Prove the exact norm gate.

Using:

mul_rotateEquiv_mul_rotateEquiv_sq_eq_norm
realPairCarrier_product_eq_signedSeventhQuotient
signedQuotient_eq
realPairCarrier_eq_eisensteinAxis_mul_core
norm eisensteinAxis = -7

prove for every i:

norm (p.realPairCore i) = -p.quotientRoot.

9. Do not infer seventh-power association from pairwise coprimality alone.

First expose the necessary condition:

if realPairCore i is a unit times a seventh power,
then quotientRoot is a signed seventh power.

10. Audit the coherent signed routing.

The routing rows and columns are:

row2 = |quotientRoot|
col3 = |m^7|.

Prove the col3 cells are seventh powers using the coprime factor split.

Then isolate the exact remaining obstruction:

the row2 cells in col1 and col2.

Branch:

A. If terminal provenance forces those cells to be one or seventh powers,
   prove quotientRoot is a signed seventh power and apply the PID/GCD
   associated-power extraction to the pair cores.

B. Otherwise define a routing-loaded real-pair core whose norm has the
   missing scalar cell load removed.

Keep PR #73 Draft.

Do not claim:

- that pairwise coprimality alone gives seventh powers;
- an oriented cyclotomic factor;
- a primitive reconstructed Fermat chart;
- strict descent;
- a descent provider;
- FLT7.
```

## 最終結論

今回の停止点は二段に分かれます。

第一の壁、

$$
\operatorname{IsCoprime}(rl,d)
$$

と pair-core coprimality は、**既存 packet の Bézout 代数だけで突破可能**です。

しかし、その先の本当の魔核は、

$$
\boxed{\operatorname{Norm}(C_i)=-\operatorname{quotientRoot}}
$$

です。

したがって次の問いは、

> core が coprime か？

ではなく、

> `quotientRoot` の第2 routing row は七乗 load だけで構成されているか？

です。

ここが Yes なら、real-pair Kummer extraction が開きます。

No なら、routing cell を吸収した loaded pair core が次の正しい術式です。
