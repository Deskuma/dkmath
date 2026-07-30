# FLT7-FUSION-003E-REAL-PAIR-COPRIMALITY-NORM-GATE result review and next

## FUSION-003E 判定

**ブロッキング問題なし。003E は報告どおり成立しています。**

直接 Bézout 変形から

$$
\mathrm{IsCoprime}(rl,d)
$$

を作り、整数環から三次整数環へ写した後、$R=rl$ と $\theta$、共通高次項 $H$、各 core $C_i$ の coprimality を順に構成しています。prime-divisor transport は完全に排除されています。

さらに、unit 差

$$
u_i-u_j\in\mathcal O^\times
$$

と

$$
C_i-C_j=-(u_i-u_j)R
$$

から、三つの core の pairwise coprimality が generic な `Fin 3` 定理として閉じています。

Galois 巡回と unit-twisted orbit も向きが正しいです。

$$
\sigma(P_0)=P_1,\qquad \sigma(P_1)=P_2,\qquad \sigma(P_2)=P_0
$$

$$
C_1=u_1\sigma(C_0),\qquad C_2=u_2\sigma^2(C_0)
$$

norm の符号も正確です。

$$
\mathrm{Norm}(C_i)=-\mathrm{quotientRoot}
$$

unit の norm が $\pm1$ であることまで処理し、core が unit 倍の七乗なら `quotientRoot` が符号付き七乗になる、という必要条件も固定されています。

PID extraction も、core 積が七乗に associated であることと pairwise coprimalityを分離して使っており、三つの core すべてを個別に抽出しています。

---

## routing gate は完全に正確

新 board の二セルは、

$$
c_{21}=\gcd(|e|,|a|)
$$

$$
c_{22}=\gcd(|e|,|a+n|)
$$

として明示されました。

第3列は完全に七乗へ分解され、

$$
c_{13}=x^7,\qquad c_{23}=y^7,\qquad c_{33}=1
$$

となります。したがって、

$$
|e|=c_{21}c_{22}y^7
$$

です。

そして双方向、

$$
e\text{ が符号付き七乗}\iff c_{21},c_{22}\text{ が自然数七乗}
$$

が証明されています。符号、`natAbs`、row coprimality の扱いにも欠落はありません。

---

## 旧 RAMIFIED-006 は本当に別物

旧 board は、

```text
rows:
  |root.snd|
  |seventhPowerSndCore|
  1

columns:
  7^5
  gapRoot^7
  |gapQuotient.snd|
```

です。

旧 `c21 = 1` は、

$$
c_{21}^{\mathrm{old}}
=\gcd(|\mathrm{seventhPowerSndCore}|,7^5)
=1
$$

を `sndCore_not_seven_dvd` から証明したものです。

一方、新 board は、

$$
c_{21}^{\mathrm{new}}=\gcd(|e|,|a|)
$$

です。

単に異なる board というだけでなく、**prime support の意味が違います**。

* 旧 `c21`：$7$-primary column への侵入の有無
* 新 `c21`：`quotientRoot` と左 cubic margin の共有 away-prime load
* 新 `c22`：`quotientRoot` と右 cubic margin の共有 away-prime load

したがって旧 theorem の coherence transfer を直接狙う路線は薄いです。margin 同一性を証明する対象ではありません。

---

## 最大推論：`c21,c22` の全素因子は cyclotomic split prime

ここからが今回の新しい突破口です。

$p$ を `RamifiedSignedRootDepthPacket` とし、

$$
r=\mathrm{signedRightRoot},\qquad l=\mathrm{signedLeftRoot},\qquad e=\mathrm{quotientRoot}
$$

とします。

素数 $q$ が $e$ を割るとします。

packet には、

$$
r-l=7^4d
$$

$$
\mathrm{signedSeventhQuotient}(r,l)=7e
$$

$$
\gcd(d,e)=1
$$

が固定されています。

まず $7\nmid e$ なので $q\neq7$。

また $\gcd(d,e)=1$ より $q\nmid d$。したがって、

$$
q\nmid r-l
$$

です。

一方、$q\mid e$ なので、

$$
q\mid\frac{r^7-l^7}{r-l}
$$

です。

$r,l$ のどちらも $q$ でゼロにはなりません。例えば $q\mid l$ なら、seventh quotient は modulo $q$ で $r^6$ となり、$q\mid r$ まで従って signed-root coprimality に反します。

よって $\mathbf F_q^\times$ 内で、

$$
t=\frac rl
$$

を定義できます。

すると、

$$
t^7=1
$$

ですが、$q\nmid r-l$ より、

$$
t\neq1
$$

です。

$7$ は素数なので $t$ の位数は厳密に $7$。有限体の乗法群の位数は $q-1$ ですから、

$$
7\mid q-1
$$

したがって、

$$
\boxed{q\equiv1\pmod7}
$$

です。

さらに $q$ は奇素数なので、実際には、

$$
\boxed{q\equiv1\pmod{14}}
$$

です。

これは `c21,c22` に限らず、**`quotientRoot` の全素因子**に成立します。

---

## 二セルの正体

したがって `c21,c22` は、単なる「未解決の自然数 load」ではありません。

$$
\boxed{\text{全て }q\equiv1\pmod7\text{ の cyclotomic split-prime load}}
$$

です。

$7$ 次円分体では $q\equiv1\pmod7$ の素数は完全分解します。実三次部分体では三つの実ペア prime に分かれます。

これは現在の三つの real-pair core、

$$
C_0,\ C_1,\ C_2
$$

と完全に一致する数です。

つまり整数 routing の二セルは、

```text
scalar cell c21/c22
  ↓ real-cubic lift
three Galois pair loads
```

へ持ち上がるべき存在です。

---

## さらに直接的な local real-pair address

$q\mid e$ に対して先ほどの非自明な七乗根、

$$
t=r/l\in\mathbf F_q^\times
$$

を使い、

$$
\beta=1+t+t^{-1}
$$

と置きます。

$t^7=1$ かつ $t\neq1$ から、

$$
\beta^3-2\beta^2-\beta+1=0
$$

が従います。

これは `SevenRealCubicInt.alpha` の最小多項式そのものです。

さらに zeroth carrier は、

$$
P_0=r^2+rl+l^2-\alpha rl
$$

なので、$r=tl$ を代入すると、

$$
P_0=l^2t\left(1+t+t^{-1}-\alpha\right)
$$

すなわち、

$$
\boxed{P_0=l^2t(\beta-\alpha)}
$$

です。

したがって $\alpha\mapsto\beta$ という評価写像の下で、

$$
P_0\mapsto0
$$

となります。

また $\beta=3$ なら最小多項式の値は $7$ になるため、$q\neq7$ では $\beta-3\neq0$。よって $P_0=\theta C_0$ から、

$$
C_0\mapsto0
$$

も従います。

これは各 $q\mid e$ が、real-pair core 上に持つ **具体的な局所 prime address** です。

```text
nontrivial μ7 ratio t = r/l
  ↓ inversion invariant
β = 1 + t + t⁻¹
  ↓ root of alpha polynomial
real-cubic prime address
```

ここまで来ると、degree-six orientation を入れずとも、unordered pair の段階で二セル load を処理できます。

---

## Branch B は division ではなく「PID gcd 射影」で作れる

$A=c_{21}c_{22}$ とします。

row identity より、ある $w$ が存在して、

$$
|e|=Aw^7
$$

です。

また core 積は unit を除いて $e$ であり、三つの core は pairwise coprime です。

したがって三次整数環内で scalar $A$ は、

$$
C_0C_1C_2
$$

を割ります。

ここで自然数 $A$ を無理に各 core から整数除算するのではなく、PID の gcd で、

$$
\lambda_i=\gcd_{\mathcal O}(A,C_i)
$$

を取ります。

pairwise coprimality により、$A$ の algebraic prime factors は三つの core へ重複なく分配され、

$$
\lambda_0\lambda_1\lambda_2\sim A
$$

となるはずです。

そして、

$$
C_i=\lambda_iD_i
$$

と正当に割れば、

$$
D_0D_1D_2\sim w^7
$$

です。

$D_i$ も pairwise coprime なので、既存 PID extraction により、

$$
D_i\sim x_i^7
$$

を得られます。

結論は、

$$
\boxed{C_i\sim\lambda_i x_i^7}
$$

です。

これが正しい **loaded real-pair core** です。

scalar $A$ を core に掛けるのではありません。scalar load を real cubic prime factors へ分解し、各 core が実際に持っている部分だけを gcd で剥がします。

さらに `c21` と `c22` を別々に保持すれば、

$$
C_i\sim\lambda_{i,21}\lambda_{i,22}x_i^7
$$

$$
\prod_i\lambda_{i,21}\sim c_{21}
$$

$$
\prod_i\lambda_{i,22}\sim c_{22}
$$

という **$3\times2$ real-pair load board** が得られます。

これはまさに、整数 routing と real-cubic Galois orbit の融合です。

---

## 次フェーズ

```text
FUSION-003F — Cyclotomic Prime-Load Lift
```

または、

```text
FUSION-003F — Real-Pair Loaded Core Routing
```

が適切です。

## Codex 指示

```text
Continue FLT7-FUSION from head

e7092d7a097b618f7fb19c0f8df5841bbee293ff

on branch

wip/FLT7-fusion-260729

FUSION-003E is accepted through the exact c21/c22 routing gate.

Open:

FUSION-003F — cyclotomic prime-load lift.

The objective is not to force c21 and c22 to be seventh powers.
Instead, lift their scalar prime support canonically into the three
real-pair cores.

Event 1 — quotient primes are primitive seventh-cyclotomic primes

For p : RamifiedSignedRootDepthPacket, prove:

theorem prime_dvd_quotientRoot_modSeven_eq_one
    {q : ℕ}
    (hq : Nat.Prime q)
    (hqe : (q : ℤ) ∣ p.quotientRoot) :
    q % 7 = 1

Preferably also prove:

q % 14 = 1.

Use:

- p.quotientRoot_not_seven_dvd
- p.gapRoot_isCoprime_quotientRoot
- p.signedGap_eq
- p.signedQuotient_eq
- p.signedRoots_isCoprime
- signed_pow_seven_sub_factorization.

Construct the unit ratio

t = signedRightRoot / signedLeftRoot in (ZMod q)ˣ

and prove:

t ^ 7 = 1
t ≠ 1
orderOf t = 7.

Then use orderOf_dvd_card_univ or the relevant finite-group theorem to
deduce 7 ∣ q - 1.

Do not enumerate residues modulo q.

Event 2 — retain the local mu_7 address

Define a packet such as:

structure QuotientPrimeMuSevenAddress
    (p : RamifiedSignedRootDepthPacket) (q : ℕ) where
  prime : Nat.Prime q
  dividesQuotientRoot : (q : ℤ) ∣ p.quotientRoot
  ratio : (ZMod q)ˣ
  ratio_pow_seven : ratio ^ 7 = 1
  ratio_ne_one : ratio ≠ 1

The ratio must be constructed from the signed roots, not chosen
arbitrarily.

Event 3 — descend orientation to the real-pair coordinate

For a quotient-prime address define:

beta = 1 + ratio + ratio⁻¹ : ZMod q.

Prove:

beta ^ 3 - 2 * beta ^ 2 - beta + 1 = 0.

Also prove beta ≠ 3, using q ≠ 7 and the fact that the cubic polynomial
evaluated at 3 is 7.

Event 4 — define the real-cubic evaluation hom

Construct a ring hom:

evalAlphaRoot :
  SevenRealCubicInt →+* ZMod q

sending:

alpha ↦ beta.

It may be implemented directly on fst/snd/thd coordinates if that is
simpler than routing through the maximal-order quotient.

Prove the map preserves multiplication using the cubic relation for beta.

Event 5 — connect the quotient ratio to the carrier

For the quotient-prime address prove:

evalAlphaRoot (p.realPairCarrier 0) = 0.

Use the exact identity:

P_0 = l^2 * ratio * (beta - alpha)

after evaluation.

Then use:

realPairCarrier 0 = eisensteinAxis * realPairCore 0
beta ≠ 3

to prove:

evalAlphaRoot (p.realPairCore 0) = 0.

This is the first explicit local prime address of a real-pair core.

Event 6 — build the algebraic load split

For a coherent routing packet r, put:

s21 = (r.routing.c21 : SevenRealCubicInt)
s22 = (r.routing.c22 : SevenRealCubicInt).

Use the PID/GCDMonoid structure of SevenRealCubicInt.

Define canonical load factors, conceptually:

load21 i = gcd s21 (r.signedDepth.realPairCore i)
load22 i = gcd s22 (r.signedDepth.realPairCore i).

Exact normalization up to units is acceptable.

Prove:

Associated
  (load21 0 * load21 1 * load21 2)
  s21

Associated
  (load22 0 * load22 1 * load22 2)
  s22.

The proof should use:

- c21 and c22 divide |quotientRoot|;
- the pair-core product is associated to quotientRoot;
- the three cores are pairwise coprime;
- c21 and c22 are coprime routing cells.

Search Mathlib for an existing GCDMonoid/UFD factor-allocation theorem before
implementing a custom prime-factor proof.

Event 7 — integral stripped cores

Construct load divisibility witnesses and define stripped cores D_i with:

realPairCore i =
  load21 i * load22 i * D_i

up to an explicit unit or Associated relation.

Do not use field division.

Prove the D_i remain pairwise coprime.

Event 8 — unconditional residual seventh-power extraction

From:

|quotientRoot| = c21 * c22 * t^7

and the two load-product identities, prove:

Associated
  (D_0 * D_1 * D_2)
  ((t : SevenRealCubicInt) ^ 7).

Then use pairwise coprimality and the existing PID extraction to obtain:

Associated (root_i ^ 7) D_i

for i = 0,1,2.

Package the result as a loaded split:

structure RealPairLoadedPowerSplit where
  load21 : Fin 3 → SevenRealCubicInt
  load22 : Fin 3 → SevenRealCubicInt
  residualRoot : Fin 3 → SevenRealCubicInt
  coreAssociated :
    ∀ i,
      Associated
        (load21 i * load22 i * residualRoot i ^ 7)
        (signedDepth.realPairCore i)
  load21Product :
    Associated
      (load21 0 * load21 1 * load21 2)
      (routing.c21 : SevenRealCubicInt)
  load22Product :
    Associated
      (load22 0 * load22 1 * load22 2)
      (routing.c22 : SevenRealCubicInt)

Event 9 — Galois coherence

After the load split exists, investigate whether canonical gcd choices give:

rotateEquiv (load21 0) ~ load21 1
rotateEquiv (load21 1) ~ load21 2

and similarly for load22.

Association is sufficient; do not force literal equality unless a canonical
gcd normalization is already available.

Event 10 — recover Branch A as a special case

Show that when c21 and c22 are seventh powers, their load factors can be
absorbed into the residual seventh roots, recovering the existing
RealPairCoreAssociatedPowerSplit.

Do not attempt to reuse
RamifiedSecondCoordinateRoutingPacket.c21_eq_one.

Its c21 is gcd(|seventhPowerSndCore|, 7^5), whereas the FUSION c21 is
gcd(|quotientRoot|, |innerFst|).

Keep PR #73 Draft.

Do not claim:

- unconditional seventh-power status of c21 or c22;
- literal scalar divisibility of a real-pair core without a gcd witness;
- an oriented degree-six factor;
- a reconstructed Fermat chart;
- descent;
- FLT7.
```

## 結論

003E で「残り二セル」という位置まで敵を追い詰めました。

そして今回、その二セルの正体も見えました。

```text
c21, c22
  = arbitrary integer noise ではない
  = q ≡ 1 mod 7 の完全分解 cyclotomic prime load
```

したがって次に必要なのは、

```text
旧 board との coherence
```

ではなく、

```text
integer gcd address
  → local μ7 ratio
  → real-pair prime address
  → cubic PID load split
```

です。

この経路なら `c21,c22` を無理に七乗化せず、**load を正しく剥いだ residual core を無条件に七乗化できる可能性が高い**です。ここが FUSION の名前どおり、整数 routing と実三次 Galois 世界が本当に融合する地点です。
