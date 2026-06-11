# GN Anchor Phase 実験設計書

## 1. 目的

本実験の目的は、GN kernel に現れる素因子を、単なる可除性ではなく **素数の種** として観測できるかを Lean 上で検証することである。

現在の主対象は原始素因子である。
Zsigmondy theorem へ直接進む前に、まず次の三点を Lean で分離する。

```text
boundary factor
GN kernel factor
exceptional / anchored prime component
```

基本形は次である。

$$
(x+u)^d-u^d=x\cdot GN_d(x,u)
$$

ここで \(x\) は境界因子、\(GN_d(x,u)\) は境界を剥がした後に残る観測核である。

$$
\mathrm{GN}_d(x,u):=\sum_{k=0}^{d-1}\binom{d}{k+1}x^{d-1-k}\,u^{k}
$$

本実験では、素因子 \(q\) が差冪全体に現れるとき、それが境界側ではなく GN 側に移る条件を調べる。

成功すれば、これは後に primitive prime divisor / Zsigmondy bridge へ昇華する。

## 2. 背景

Petal / S0 では、三次元の場合に次の関係が現れる。

$$
c^3-b^3=(c-b)S0(c,b)
$$

かつ

$$
S0(c,b)=GN_3(c-b,b)
$$

したがって S0 は独立した特殊式ではなく、三次 GN kernel の Petal 可視面である。

既存実装では、\(3\) に関して例外が出る。

典型的には、

```text
q ∣ S0(c,b)
```

から

```text
q ∤ c-b
```

を得たいが、\(q=3\) では偽になる場合がある。

本実験では、この \(3\) を単に排除するのではなく、

```text
3-primary / anchored component
```

として先に分離し、その reduced world で \(q\ne3\) の GN support を観測する。

## 3. 基本方針

### 3.1. 新しい数学用語を作りすぎない

通常の primorial や素数概念は変更しない。

代わりに、観測射影を導入する。

例として、\(r\) より小さい素因子を潰した reduced support を考える。

```lean
def HasNoPrimeBelow (r n : ℕ) : Prop :=
  ∀ p, p.Prime → p < r → ¬ p ∣ n
```

これは「\(r\) から始まる世界」を標準数学用語を壊さずに表現するための predicate である。

### 3.2. 例外 prime は排除ではなく分離する

\(q\ne3\) は、単なる例外回避ではなく、

```text
3-primary component を先に分離した reduced statement
```

として扱う。

この読みを Lean では次のような名前で固定する。

```lean
def ReducedAwayFrom (r n : ℕ) : Prop :=
  HasNoPrimeBelow r n
```

また、S0 専用には次のような predicate を置く候補がある。

```lean
def S0ReducedAwayFromThree (c b : ℕ) : Prop :=
  ¬ 3 ∣ c - b
```

### 3.3. 先に GN 可除性を固める

Zsigmondy は強い存在定理である。
先に GN 側で「どこに素因子がいるか」を確定する。

最初の実験命題は次の形を狙う。

```lean
theorem prime_dvd_GN_of_dvd_diff_not_dvd_boundary
    {d x u q : ℕ}
    (hq : q.Prime)
    (hdiv : q ∣ (x + u)^d - u^d)
    (hx : ¬ q ∣ x) :
    q ∣ GN d x u
```

既存定理がある場合は新証明せず、Petal / GN-facing alias として再公開する。

## 4. 実験対象

## 4.1. Phase A. S0 / GN 三次面の再固定

目的は、S0 が GN 三次面であることを読みやすい名前で再公開することである。

候補定理:

```lean
theorem S0_nat_eq_cubicGNFace
    {c b : ℕ} (hbc : b < c) :
    S0_nat c b = GN 3 (c - b) b
```

```lean
theorem cubicDiff_eq_boundary_mul_S0
    {c b : ℕ} :
    c^3 - b^3 = (c - b) * S0_nat c b
```

注意:

* `Nat` 減算のため、必要なら `b ≤ c` や `b < c` を付ける。
* 既存 `GN_three_sub_eq_S0_nat` / `S0_nat_eq_GN_three_sub` を使えるなら wrapper に留める。

## 4.2. Phase B. 三例外の構造分離

目的は、\(3\) が S0 と境界にまたがることを明示することである。

候補定理:

```lean
theorem three_dvd_S0_nat_of_three_dvd_sub
    {c b : ℕ} :
    3 ∣ c - b → 3 ∣ S0_nat c b
```

または、既存の向きに合わせて、

```lean
theorem three_not_dvd_S0_nat_of_not_dvd_sub
    {c b : ℕ} (hbc : b < c) :
    ¬ 3 ∣ c - b → ¬ 3 ∣ S0_nat c b
```

この段階では「\(3\) を除外した」のではなく、

```text
3-primary component が boundary と kernel の接触成分である
```

という解釈を theorem 名と doc comment に残す。

## 4.3. Phase C. (r)-anchor reduced support

目的は、\(3,5,7,11,\dots\) から始まる世界を、射影・同型的な観測面として Lean に置くことである。

最小定義:

```lean
def HasNoPrimeBelow (r n : ℕ) : Prop :=
  ∀ p, p.Prime → p < r → ¬ p ∣ n

def HasAnchorPrime (r n : ℕ) : Prop :=
  r.Prime ∧ r ∣ n ∧ HasNoPrimeBelow r n
```

意味:

```text
HasAnchorPrime r n
```

は、\(n\) の最小 prime support が \(r\) であることを表す。

候補補題:

```lean
theorem hasAnchorPrime_no_smaller_prime
    {r n p : ℕ}
    (h : HasAnchorPrime r n)
    (hp : p.Prime)
    (hpr : p < r) :
    ¬ p ∣ n
```

```lean
theorem hasAnchorPrime_anchor_dvd
    {r n : ℕ}
    (h : HasAnchorPrime r n) :
    r ∣ n
```

この段階では concrete な `nthPrime` や standard primorial へは接続しない。
まず support predicate として通す。

## 4.4. Phase D. GN primitive candidate

目的は、GN 側に現れる素因子を primitive candidate として包装することである。

候補定義:

```lean
def GNPrimitiveCandidate (d x u q : ℕ) : Prop :=
  q.Prime ∧ q ∣ GN d x u ∧ ¬ q ∣ x ∧ ¬ q ∣ u
```

より弱い候補:

```lean
def GNBoundaryFreePrime (d x u q : ℕ) : Prop :=
  q.Prime ∧ q ∣ GN d x u ∧ ¬ q ∣ x
```

実験ではまず弱い方を優先する。

候補補題:

```lean
theorem GNBoundaryFreePrime.of_dvd_diff_not_dvd_boundary
    {d x u q : ℕ}
    (hq : q.Prime)
    (hdiv : q ∣ (x + u)^d - u^d)
    (hx : ¬ q ∣ x) :
    GNBoundaryFreePrime d x u q
```

この補題が通れば、

```text
差冪に現れ、境界にはいない素因子は GN 側にいる
```

が Lean 上で固定される。

## 4.5. Phase E. Anchor と GN の合流

目的は、\(r\)-anchor world と GN support を結び、\(r\) から始まる reduced world における GN 素因子観測を作ることである。

候補定義:

```lean
def AnchoredGNPrimeSupport (r d x u q : ℕ) : Prop :=
  HasAnchorPrime r q ∧ GNBoundaryFreePrime d x u q
```

ただし、\(q\) 自体が素数なら `HasAnchorPrime r q` は \(q=r\) を強く示す方向に寄るため、実際には support carrier を別に置く方がよい可能性がある。

代替案:

```lean
def AnchoredGNCarrier (r d x u n : ℕ) : Prop :=
  HasAnchorPrime r n ∧ n ∣ GN d x u
```

まずはこちらを実験する。

## 5. ファイル構成案

実験段階では `not_implements` か `Research` 側に置く。

候補:

```text
docs/not_implements/GN_AnchorPhase_ExperimentalDesign.md
lean/dk_math/DkMath/Petal/Experimental/AnchorPhase.lean
lean/dk_math/DkMath/Petal/Experimental/GNPrimitiveCandidate.lean
```

または、Lean 実験だけなら:

```text
lean/dk_math/DkMath/Research/Petal/AnchorPhase.lean
```

本線昇格時:

```text
DkMath.Petal.Anchor
DkMath.Petal.GNPrimitive
DkMath.Petal.ReducedSupport
```

## 6. import 方針

初期実験:

```lean
import Mathlib
import DkMath.Petal.GNBridge
import DkMath.Petal.GcdBridge
```

`GcdBridge` が未完成なら:

```lean
import DkMath.Petal.GNBridge
import DkMath.NumberTheory.Gcd.GN
```

必要に応じて:

```lean
import DkMath.NumberTheory.WeightedBinomial
import DkMath.NumberTheory.PascalPrimeDial
```

ただし、最初の実験では import を増やしすぎない。

## 7. 成功条件

本実験の成功条件は次である。

1. `S0` を `GN 3` の Petal face として再利用しやすい名前で参照できる。
2. \(3\) 例外を `q ≠ 3` の単純排除ではなく、`3-primary` 分離として theorem 名に反映できる。
3. \(r\)-anchor reduced support を `HasNoPrimeBelow` / `HasAnchorPrime` として表現できる。
4. 差冪に現れ境界にいない素因子が GN 側へ移ることを theorem 化できる。
5. `GNPrimitiveCandidate` または `GNBoundaryFreePrime` が Zsigmondy bridge の入力語彙として使える。

## 8. 失敗条件

次のいずれかが発生した場合は、定理化を急がず実験を止める。

1. `HasAnchorPrime` が強すぎて、一般 \(r\)-world を表現できない。
2. \(3\)-primary 分離が S0 専用すぎて一般 GN に持ち上がらない。
3. `Nat` 減算条件が重くなり、定理文が downstream で使いにくい。
4. 既存 GN / gcd theorem の wrapper で済む範囲を超え、新規 gcd 理論が必要になる。
5. Zsigmondy へ渡す前に anchor predicate が本線 import を汚染する。

## 9. 昇格条件

次が満たされたら、実験ファイルから本線へ昇格する。

```text
lake build DkMath.Petal.Experimental.AnchorPhase
```

が通り、かつ次の最小 API が no-sorry で成立すること。

```lean
HasNoPrimeBelow
HasAnchorPrime
GNBoundaryFreePrime
S0_nat_eq_cubicGNFace
three_not_dvd_S0_nat_of_not_dvd_sub
GNBoundaryFreePrime.of_dvd_diff_not_dvd_boundary
```

昇格先は次のいずれかとする。

```text
DkMath.Petal.ReducedSupport
DkMath.Petal.GNPrimitive
DkMath.Petal.Anchor
```

## 10. 将来展望

この実験が成功した場合、次の定理群へ進む。

```text
r-start reduced primorial support
GN support birth by d-phase
primitive factor emergence in GN kernel
Zsigmondy bridge input normalization
```

最終的には、

```text
素数の種
  -> d 位相で観測
  -> GN kernel に現れる
  -> 境界因子から分離
  -> 原始素因子として Zsigmondy へ渡る
```

という流れを Lean 上で固定する。
