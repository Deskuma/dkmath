# GN–Cyclotomic–Eisenstein Bridge 調査・実装設計

- Date: 2026-07-28
- Status: Not implemented / research and implementation roadmap
- Target branch: `develop`
- Suggested implementation module: `DkMath.NumberTheory.GNCyclotomicBridge`
- cid: `6a689e21-b308-83ee-a894-0e40d37adb06`

## 1. 結論

DkMath の `GN` と素数次円分多項式は、単に係数の形が似ているのではない。

`GN` は冪差商

$$
\frac{x^n-y^n}{x-y}
$$

を斉次多項式として保持し、さらに Gap 座標

$$
x=g+y
$$

へ移したものである。

特に指数が素数 $p$ のとき、冪差商は単独の円分因子となるため、

$$
\operatorname{GN}_p(g,y)
=
\operatorname{HCycl}_p(g+y,y)
$$

であり、$y=1$ に正規化すると、

$$
\operatorname{GN}_p(g,1)
=
\Phi_p(g+1)
$$

となる。

多項式としては、まさに mathlib の

```lean
(cyclotomic p ℤ).comp (X + 1)
```

である。

したがって、mathlib の既存定理

```lean
cyclotomic_comp_X_add_one_isEisensteinAt
```

は、DkMath の言葉では

> 素数次 GN の単位断面 `GN p X 1` は $p$-Eisenstein である

という定理に読み替えられる。

さらに、この Eisenstein 定理の mathlib 実装内部では、実際に

```lean
rw [cyclotomic_prime, geom_sum_X_comp_X_add_one_eq_sum, ...]
```

という書き換えが使われている。

すなわち mathlib 内部には既に、

```text
prime cyclotomic
  → geometric sum
  → X ↦ X + 1
  → binomial / GN coefficients
  → Eisenstein
```

という経路が存在する。

DkMath で不足しているのは、この既存経路へ `GN` の名前と Gap 座標を接続する薄い Bridge 層である。

---

## 2. 現在の DkMath `GN5`

既存ファイル：

```text
lean/dk_math/DkMath/FLT/Five/GN5.lean
```

現在の定義は、

```lean
def GN5 (g y : ℕ) : ℕ :=
  g ^ 4
    + 5 * g ^ 3 * y
    + 10 * g ^ 2 * y ^ 2
    + 10 * g * y ^ 3
    + 5 * y ^ 4
```

である。

同ファイルでは既に、

```lean
theorem GN5_eq_homogeneous_cyclotomic
```

により、

$$
\operatorname{GN}_5(g,y)
=
(g+y)^4+(g+y)^3y+(g+y)^2y^2+(g+y)y^3+y^4
$$

が固定されている。

さらに、

```lean
theorem add_pow_five_sub_eq_mul_GN5
```

により、

$$
(g+y)^5-y^5
=
g\operatorname{GN}_5(g,y)
$$

も実装済みである。

つまり `GN5` は既に、説明・定義・定理のすべてにおいて

> homogeneous fifth cyclotomic factor in gap coordinates

として実装されている。

今回の一般化は `GN5` の意味を変更するものではなく、その正体を一般の指数 $n$、特に素数指数 $p$ へ持ち上げるものである。

---

## 3. 一般 GN の二つの表示

### 3.1 冪差商・斉次等比和表示

交換半環または交換環上で、斉次等比和を

$$
\operatorname{HGeom}_n(x,y)
=
\sum_{i=0}^{n-1}x^i y^{n-1-i}
$$

とする。

mathlib では、この和は `geom_sum₂` 系の補題で扱われている。

冪差との関係は、

$$
(x-y)\operatorname{HGeom}_n(x,y)
=
x^n-y^n
$$

である。

Gap 座標 $x=g+y$ を代入すると、

$$
\operatorname{GN}_n(g,y)
:=
\operatorname{HGeom}_n(g+y,y)
$$

となり、

$$
g\operatorname{GN}_n(g,y)
=
(g+y)^n-y^n
$$

を得る。

### 3.2 二項係数表示

二項展開により、同じ GN は

$$
\operatorname{GN}_n(g,y)
=
\sum_{i=0}^{n-1}
\binom{n}{i+1}
 g^i y^{n-1-i}
$$

と表せる。

$n=5$ では、

$$
\operatorname{GN}_5(g,y)
=
g^4+5g^3y+10g^2y^2+10gy^3+5y^4
$$

となり、現在の `GN5` と一致する。

実装上は、現在の `GN5` と直接一致する二項係数表示を一般 `GN` の canonical definition とし、斉次等比和表示を Bridge theorem にする案が自然である。

候補定義：

```lean
def GN
    {R : Type*} [CommSemiring R]
    (n : ℕ) (g y : R) : R :=
  ∑ i ∈ Finset.range n,
    (n.choose (i + 1) : R) * g ^ i * y ^ (n - 1 - i)
```

注意：実装時には積の結合順序、`Nat.cast`、`Finset.sum` の正規形を mathlib の既存補題に合わせて調整する。

---

## 4. 素数指数で円分多項式になる理由

一般の $n$ について、

$$
\frac{X^n-1}{X-1}
$$

は通常、一個の円分多項式ではない。

正確には、

$$
\frac{X^n-1}{X-1}
=
\prod_{\substack{d\mid n\\d>1}}\Phi_d(X)
$$

である。

したがって、一般 `GN n` は「全非自明円分因子をまとめた斉次冪差商」である。

一方、$p$ が素数なら約数は $1,p$ だけなので、

$$
\frac{X^p-1}{X-1}
=
\Phi_p(X)
=
1+X+\cdots+X^{p-1}
$$

となる。

よって素数指数の場合に限り、

$$
\operatorname{GN}_p(g,y)
$$

は単独の $p$ 次円分多項式の斉次 Gap 座標化となる。

この区別は重要である。

```text
GN n       = 一般冪差商・複数円分因子の積
GN p       = 単独の prime cyclotomic factor（p prime）
GN p _ 1   = Φₚ(X + 1) の評価
```

---

## 5. `X ↦ X + 1` と GN の完全一致

素数 $p$ について、

$$
\Phi_p(X)
=
\sum_{i=0}^{p-1}X^i
$$

である。

これを $X+1$ へ移すと、

$$
\Phi_p(X+1)
=
\sum_{i=0}^{p-1}(X+1)^i
$$

となる。

mathlib には、次の既存補題がある。

```lean
Polynomial.geom_sum_X_comp_X_add_one_eq_sum
```

その内容は概ね、

$$
\left(\sum_{i=0}^{n-1}X^i\right)\circ(X+1)
=
\sum_{i=0}^{n-1}\binom{n}{i+1}X^i
$$

である。

したがって素数 $p$ では、

$$
\Phi_p(X+1)
=
\sum_{i=0}^{p-1}\binom{p}{i+1}X^i
$$

となる。

右辺は、まさに $y=1$ とした GN である。

$$
\operatorname{GN}_p(X,1)
=
\Phi_p(X+1)
$$

ここが、DkMath の GN と

```lean
cyclotomic_comp_X_add_one_isEisensteinAt
```

を接続する最短経路である。

---

## 6. mathlib で確認された既存補題

### 6.1 円分多項式と平行移動

ファイル：

```text
Mathlib/RingTheory/Polynomial/Eisenstein/IsIntegral.lean
```

既存定理：

```lean
theorem cyclotomic_comp_X_add_one_isEisensteinAt [Fact p.Prime] :
    ((cyclotomic p ℤ).comp (X + 1)).IsEisensteinAt
      (Submodule.span ℤ {(p : ℤ)})
```

この証明内部では、

```lean
cyclotomic_prime
geom_sum_X_comp_X_add_one_eq_sum
Nat.Prime.dvd_choose_self
```

が直接使われている。

これは、

1. prime cyclotomic を等比和へ展開する
2. `X + 1` を合成する
3. 二項係数表示へ変換する
4. 中間二項係数が $p$ で割れることを使う
5. 定数項が $p^2$ では割れないことを示す

という GN 的な証明そのものである。

また同ファイルには、素数冪円分多項式版

```lean
theorem cyclotomic_prime_pow_comp_X_add_one_isEisensteinAt
```

も存在する。

これは将来の `GNPrimePower` または反復 Gap 構造へ繋がる可能性がある。

### 6.2 平行移動した等比和の二項係数展開

ファイル：

```text
Mathlib/RingTheory/Polynomial/Basic.lean
```

既存定理：

```lean
theorem geom_sum_X_comp_X_add_one_eq_sum (n : ℕ) :
    (∑ i ∈ range n, (X : R[X]) ^ i).comp (X + 1) =
      (Finset.range n).sum fun i : ℕ =>
        (n.choose (i + 1) : R[X]) * X ^ i
```

これは GN の単位断面の係数公式を、そのまま多項式恒等式として与える。

### 6.3 冪差と valuation excess

ファイル：

```text
Mathlib/NumberTheory/Multiplicity.lean
```

確認された主要定理：

```lean
dvd_geom_sum₂_iff_of_dvd_sub
not_dvd_geom_sum₂
emultiplicity_geom_sum₂_eq_one
emultiplicity_pow_prime_sub_pow_prime
Int.emultiplicity_pow_sub_pow
Int.emultiplicity_pow_add_pow
```

特に、適切な素性・奇素数性・$p\mid x-y$・$p\nmid x$ の条件下で、

```lean
emultiplicity_geom_sum₂_eq_one
```

は

$$
v_p\!\left(\operatorname{HGeom}_p(x,y)\right)
=
1
$$

を与える。

さらに、

```lean
emultiplicity_pow_prime_sub_pow_prime
```

は

$$
v_p(x^p-y^p)
=
v_p(x-y)+1
$$

を与える。

これは DkMath で観測・実装してきた

> exceptional prime $p$ の GN valuation excess はちょうど $1$

という構造と一致する。

したがって GN 一般化は、円分多項式と Eisenstein だけでなく、mathlib の LTE / multiplicity 系へも直接接続できる。

---

## 7. 冪の和・交代和は符号反転した同一 GN

奇数 $p$ について、

$$
(-y)^p
=
-y^p
$$

なので、

$$
\frac{x^p+y^p}{x+y}
=
\frac{x^p-(-y)^p}{x-(-y)}
$$

となる。

したがって冪の和の商は、新しい構造ではなく、冪差 GN の第2座標を反転したものである。

Gap を

$$
s=x+y
$$

と置けば $x=s-y=s+(-y)$ なので、

$$
x^p+y^p
=
s\operatorname{GN}_p(s,-y)
$$

となる。

よって FLT の交代和因子は、

$$
\operatorname{GN}_p(s,-y)
$$

で統一できる。

円分多項式としては、奇素数 $p$ について、

$$
\Phi_{2p}(X)
=
\Phi_p(-X)
$$

であり、

$$
\frac{x^p+y^p}{x+y}
$$

は $\Phi_{2p}$ の斉次化に対応する。

したがって符号の差は、

```text
y ↦ -y
```

または

```text
Φₚ ↔ Φ₂ₚ
```

という反転射影として整理できる。

---

## 8. 実装すべき一般定義

推奨モジュール：

```text
lean/dk_math/DkMath/NumberTheory/GNCyclotomicBridge.lean
```

推奨 namespace：

```lean
namespace DkMath.NumberTheory
```

### 8.1 一般 GN

```lean
def GN
    {R : Type*} [CommSemiring R]
    (n : ℕ) (g y : R) : R :=
  ∑ i ∈ Finset.range n,
    (n.choose (i + 1) : R) * g ^ i * y ^ (n - 1 - i)
```

### 8.2 単位断面 GN 多項式

```lean
def GNPolynomial (n : ℕ) : ℤ[X] :=
  ∑ i ∈ Finset.range n,
    Polynomial.C (n.choose (i + 1) : ℤ) * Polynomial.X ^ i
```

別案として、最初から

```lean
def PrimeGNPolynomial (p : ℕ) : ℤ[X] :=
  (Polynomial.cyclotomic p ℤ).comp (Polynomial.X + 1)
```

と定義し、係数表示を定理にすることも可能である。

しかし DkMath の GN を主語にするなら、二項係数表示を定義にして円分多項式との一致を Bridge とする方が、既存 `GN5` との連続性が高い。

---

## 9. 実装すべき補題

以下の型は実装候補であり、正確な namespace、暗黙引数、積の正規形はビルド時に調整する。

### Event 1 — GN と斉次等比和

```lean
theorem GN_eq_geom_sum₂
    {R : Type*} [CommSemiring R]
    (n : ℕ) (g y : R) :
    GN n g y =
      ∑ i ∈ Finset.range n,
        (g + y) ^ i * y ^ (n - 1 - i)
```

役割：二項係数座標と冪差商座標を一致させる中心 Bridge。

### Event 2 — 冪差分解

減算を避ける半環版：

```lean
theorem add_pow_eq_add_mul_GN
    {R : Type*} [CommSemiring R]
    (n : ℕ) (g y : R) :
    (g + y) ^ n = y ^ n + g * GN n g y
```

交換環版：

```lean
theorem add_pow_sub_pow_eq_mul_GN
    {R : Type*} [CommRing R]
    (n : ℕ) (g y : R) :
    (g + y) ^ n - y ^ n = g * GN n g y
```

役割：現在の `add_pow_five_sub_eq_mul_GN5` の一般化。

### Event 3 — GN 多項式の評価

```lean
theorem eval_GNPolynomial
    (n : ℕ) (g : ℤ) :
    Polynomial.eval g (GNPolynomial n) = GN n g 1
```

可能なら係数環を一般化した `eval₂` 版も用意する。

### Event 4 — shifted geometric sum

```lean
theorem GNPolynomial_eq_geom_sum_comp_X_add_one
    (n : ℕ) :
    GNPolynomial n =
      (∑ i ∈ Finset.range n, (Polynomial.X : ℤ[X]) ^ i).comp
        (Polynomial.X + 1)
```

主な利用候補：

```lean
Polynomial.geom_sum_X_comp_X_add_one_eq_sum
```

### Event 5 — prime cyclotomic identification

```lean
theorem GNPolynomial_eq_cyclotomic_comp_X_add_one
    (p : ℕ) [Fact p.Prime] :
    GNPolynomial p =
      (Polynomial.cyclotomic p ℤ).comp (Polynomial.X + 1)
```

主な利用候補：

```lean
Polynomial.cyclotomic_prime
Polynomial.geom_sum_X_comp_X_add_one_eq_sum
```

これが今回の最重要 Bridge である。

### Event 6 — GN の Eisenstein 性

```lean
theorem GNPolynomial_isEisensteinAt
    (p : ℕ) [Fact p.Prime] :
    (GNPolynomial p).IsEisensteinAt
      (Submodule.span ℤ {(p : ℤ)})
```

想定証明：

```lean
rw [GNPolynomial_eq_cyclotomic_comp_X_add_one]
exact cyclotomic_comp_X_add_one_isEisensteinAt p
```

実際の namespace と implicit argument はコンパイルで確定する。

### Event 7 — 係数公式

```lean
theorem coeff_GNPolynomial
    (n i : ℕ) :
    (GNPolynomial n).coeff i =
      if i < n then (n.choose (i + 1) : ℤ) else 0
```

または `i < n` を仮定した簡潔版を先に置く。

役割：Eisenstein 条件・mod $p$ 簡約・端点係数の直接利用。

### Event 8 — prime coefficient divisibility

```lean
theorem prime_dvd_coeff_GNPolynomial_of_lt_natDegree
    (p i : ℕ) [Fact p.Prime]
    (hi : i < p - 1) :
    (p : ℤ) ∣ (GNPolynomial p).coeff i
```

ただし定数項は $p$ をちょうど一個持つ。

```lean
theorem coeff_zero_GNPolynomial_prime
    (p : ℕ) [Fact p.Prime] :
    (GNPolynomial p).coeff 0 = p
```

```lean
theorem prime_sq_not_dvd_coeff_zero_GNPolynomial
    (p : ℕ) [Fact p.Prime] :
    ¬(p : ℤ) ^ 2 ∣ (GNPolynomial p).coeff 0
```

これらは Eisenstein 定理から必要に応じて抽出するか、二項係数から直接証明する。

### Event 9 — modulo $p$ の GN 核

素数 $p$ では中間二項係数がすべて $p$ で消えるため、

$$
\operatorname{GN}_p(g,y)
\equiv
g^{p-1}\pmod p
$$

となる。

候補：

```lean
theorem GN_prime_modEq_g_pow
    (p g y : ℕ)
    (hp : p.Prime) :
    GN p g y ≡ g ^ (p - 1) [MOD p]
```

または `ZMod p` 上の等式：

```lean
theorem GN_prime_zmod
    (p : ℕ) [Fact p.Prime]
    (g y : ZMod p) :
    GN p g y = g ^ (p - 1)
```

これは既存の

```lean
GN5_eq_g_pow_four_add_five_mul
```

を一般化する。

### Event 10 — modulo Gap の端点核

$g$ を法にすると、定数項だけが残るため、

$$
\operatorname{GN}_p(g,y)
\equiv
py^{p-1}\pmod g
$$

となる。

候補：

```lean
theorem GN_prime_modEq_prime_mul_y_pow
    (p g y : ℕ) :
    GN p g y ≡ p * y ^ (p - 1) [MOD g]
```

これは既存の

```lean
GN5_eq_gap_mul_add_five_mul_y_pow_four
```

を一般化する。

### Event 11 — GN valuation excess = 1

`GN_eq_geom_sum₂` を経由し、mathlib の

```lean
emultiplicity_geom_sum₂_eq_one
```

へ接続する。

候補概念形：

```lean
theorem emultiplicity_GN_prime_eq_one
    {R : Type*} [CommRing R] [IsDomain R]
    {p : ℕ} {g y : R}
    (hp : Prime (p : R))
    (hpodd : Odd p)
    (hpg : (p : R) ∣ g)
    (hpy : ¬(p : R) ∣ y) :
    emultiplicity (p : R) (GN p g y) = 1
```

実装時には mathlib 定理の変数 $x=g+y$、$y=y$ へ合わせ、

```text
p ∣ (g + y) - y
```

を `p ∣ g` から供給する。

また `p ∤ (g+y)` と `p ∤ y` の相互変換に `p ∣ g` を用いる。

### Event 12 — LTE Bridge

```lean
theorem emultiplicity_add_pow_sub_pow_eq
```

として、

$$
v_p\!\left((g+y)^p-y^p\right)
=
v_p(g)+1
$$

を GN 分解経由で得る。

ただし mathlib には既に

```lean
emultiplicity_pow_prime_sub_pow_prime
Int.emultiplicity_pow_sub_pow
```

があるため、DkMath 側では再証明よりも「GN factor の valuation が $1$」という中間 Bridge を主成果とする方がよい。

### Event 13 — 冪和・交代和 GN

交換環上で、

```lean
def GNPlus
    {R : Type*} [CommRing R]
    (p : ℕ) (s y : R) : R :=
  GN p s (-y)
```

または定義を増やさず、定理だけを置く。

```lean
theorem sub_add_pow_add_pow_eq_mul_GN_neg
    {R : Type*} [CommRing R]
    (p : ℕ) (hpodd : Odd p) (s y : R) :
    (s - y) ^ p + y ^ p = s * GN p s (-y)
```

これは FLT の

$$
\frac{x^p+y^p}{x+y}
$$

を一般 GN へ統合する Bridge となる。

### Event 14 — `GN5` compatibility

```lean
theorem GN_five_eq_GN5 (g y : ℕ) :
    GN 5 g y = DkMath.FLT.Five.GN5 g y
```

または向きを逆にして、

```lean
theorem GN5_eq_GN (g y : ℕ) :
    DkMath.FLT.Five.GN5 g y = GN 5 g y
```

を置く。

既存 API を壊さず、`GN5` の各定理を一般 GN の特殊化として徐々に置換可能にする。

---

## 10. 推奨実装順序

### Phase A — algebraic core

1. `GN` 定義
2. `GN_eq_geom_sum₂`
3. `add_pow_eq_add_mul_GN`
4. `add_pow_sub_pow_eq_mul_GN`
5. $n=3,5,7$ の smoke test

この段階では円分多項式・Eisenstein・valuation を入れない。

### Phase B — polynomial bridge

1. `GNPolynomial`
2. `eval_GNPolynomial`
3. `GNPolynomial_eq_geom_sum_comp_X_add_one`
4. `GNPolynomial_eq_cyclotomic_comp_X_add_one`
5. `GNPolynomial_isEisensteinAt`

ここで `cyclotomic_comp_X_add_one_isEisensteinAt` への接続が完成する。

### Phase C — congruence and coefficients

1. `coeff_GNPolynomial`
2. `GN_prime_modEq_g_pow`
3. `GN_prime_modEq_prime_mul_y_pow`
4. `GN5` の既存二分解との compatibility

### Phase D — valuation bridge

1. `emultiplicity_GN_prime_eq_one`
2. LTE 系既存補題との接続
3. Nat / Int / general integral domain のどの層を DkMath API とするか決定

### Phase E — FLT sign bridge

1. `GN p s (-y)` による冪和分解
2. $\Phi_p$ と $\Phi_{2p}$ の符号反転対応
3. FLT3・FLT5・FLT7 の既存因子層へ接続

---

## 11. 推奨 import 候補

最小構成は実装時に監査するが、候補は次の通り。

```lean
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.NumberTheory.Multiplicity
import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic
import Mathlib.RingTheory.Polynomial.Eisenstein.IsIntegral
```

`Eisenstein.IsIntegral` は比較的重い可能性があるため、代数 Core と Eisenstein Bridge を別ファイルに分離する案もある。

```text
DkMath.NumberTheory.GN.Basic
DkMath.NumberTheory.GN.CyclotomicBridge
DkMath.NumberTheory.GN.EisensteinBridge
DkMath.NumberTheory.GN.ValuationBridge
```

ただし最初の実験実装では、一つの小規模モジュール

```text
DkMath.NumberTheory.GNCyclotomicBridge
```

にまとめ、依存と API が固まった後に分割する方が安全である。

---

## 12. 検証用の具体例

### $p=3$

$$
\operatorname{GN}_3(g,y)
=
g^2+3gy+3y^2
$$

単位断面：

$$
\operatorname{GN}_3(g,1)
=
g^2+3g+3
=
\Phi_3(g+1)
$$

これは $3$-Eisenstein。

### $p=5$

$$
\operatorname{GN}_5(g,y)
=
g^4+5g^3y+10g^2y^2+10gy^3+5y^4
$$

単位断面：

$$
\operatorname{GN}_5(g,1)
=
g^4+5g^3+10g^2+10g+5
=
\Phi_5(g+1)
$$

これは $5$-Eisenstein。

### $p=7$

$$
\operatorname{GN}_7(g,y)
=
g^6+7g^5y+21g^4y^2+35g^3y^3
 +35g^2y^4+21gy^5+7y^6
$$

単位断面：

$$
\operatorname{GN}_7(g,1)
=
g^6+7g^5+21g^4+35g^3+35g^2+21g+7
=
\Phi_7(g+1)
$$

これは $7$-Eisenstein。

FLT の冪和座標では $y\mapsto-y$ とするため、

$$
\operatorname{GN}_7(s,-y)
=
s^6-7s^5y+21s^4y^2-35s^3y^3
 +35s^2y^4-21sy^5+7y^6
$$

となり、観測された交代和型の $7$-Eisenstein 端点多項式を得る。

---

## 13. 設計上の重要判断

### 13.1 GN を FLT 専用に置かない

GN は冪差・円分・二項係数・Eisenstein・valuation を結ぶ一般構造である。

したがって、実装本体は

```text
DkMath.NumberTheory
```

側へ置き、FLT3・FLT5・FLT7 は特殊化 Bridge とするのが望ましい。

### 13.2 `GN p g y` と `GNPolynomial p` を分ける

`GN p g y` は二変数の斉次 Gap 座標であり、`GNPolynomial p` は $y=1$ の単位断面である。

Eisenstein 性は主に `GNPolynomial p` に対して述べられる。

一方、FLT や valuation で必要なのは二変数の `GN p g y` である。

この二層を混同しない。

### 13.3 Eisenstein は入口であり、valuation が実戦層

`GNPolynomial_isEisensteinAt` は既約性と局所分岐を示す強い入口である。

しかし DkMath の FLT 実装で直接必要となる可能性が高いのは、

$$
v_p(\operatorname{GN}_p)=1
$$

という exact valuation excess である。

したがって実装完了条件は Eisenstein Bridge のみではなく、`emultiplicity_geom_sum₂_eq_one` まで繋ぐこととする。

---

## 14. 最終的な統一図

```text
                         cyclotomic_prime
                                │
                                ▼
Φₚ(X) = 1 + X + ··· + X^(p-1) = prime geometric sum
                                │
                          comp (X + 1)
                                ▼
              geom_sum_X_comp_X_add_one_eq_sum
                                │
                                ▼
Φₚ(X + 1) = Σ choose(p,i+1) X^i = GNPolynomial p
                                │
                 ┌──────────────┴──────────────┐
                 ▼                             ▼
cyclotomic_comp_X_add_one_          evaluation / homogenization
isEisensteinAt                                  │
                 │                              ▼
                 │                     GN p g y
                 │                              │
                 │                    GN_eq_geom_sum₂
                 │                              │
                 │                 ┌────────────┴────────────┐
                 ▼                 ▼                         ▼
          p-Eisenstein      power-difference factor   valuation excess = 1
                                      │                         │
                                      ▼                         ▼
                              (g+y)^p-y^p              LTE / FLT exceptional p
```

冪和型 FLT では、右下の `GN p g y` に対して

```text
y ↦ -y
```

を適用するだけである。

---

## 15. 研究記録としての確定事項

1. `GN5` は既に fifth homogeneous cyclotomic factor の Gap 座標として実装されている。
2. 一般 `GN n` は冪差商の斉次 Gap 座標化である。
3. `n=p` が素数のとき、`GN p` は単独の prime cyclotomic factor になる。
4. `GN p X 1` は `(cyclotomic p ℤ).comp (X + 1)` と同一である。
5. mathlib の `cyclotomic_comp_X_add_one_isEisensteinAt` は、その証明内部で shifted geometric sum の二項係数展開を使用している。
6. mathlib には GN valuation excess $1$ に相当する `emultiplicity_geom_sum₂_eq_one` が既にある。
7. 冪の和・交代和は、奇数指数で `y ↦ -y` とした同一 GN である。
8. DkMath に必要なのは、既存 mathlib 定理群を GN API へ翻訳する Bridge 層である。

以上より、次の実装目標を固定する。

> `GN` を独立した特殊多項式として拡張するのではなく、
> homogeneous geometric sum、prime cyclotomic、shifted Eisenstein、
> multiplicity / LTE を一つの API で往来できる共通座標として実装する。
