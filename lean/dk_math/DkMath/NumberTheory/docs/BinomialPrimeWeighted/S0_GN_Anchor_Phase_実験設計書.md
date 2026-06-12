# GN Anchor Phase 実験設計書

## 0. Current status

Status: **PARTIALLY COMPLETED / REDUCED-SUPPORT PHASE REMAINS**

This note was originally written as an experiment plan.  Since then, several
parts have already moved from experiment to mainline Petal bridge theorems.

Status tags used below:

```text
[DONE]        Implemented as no-sorry Lean theorem in the current mainline.
[PARTIAL]     Core bridge exists, but the planned vocabulary is not complete.
[ACTIVE]      Still the next meaningful experiment target.
[DEFERRED]    Useful later, but not needed for the next checkpoint.
[OBSOLETE]    The original experiment item was replaced by a stronger bridge.
```

Current implementation anchors:

```text
DkMath.Petal.GNBridge
DkMath.Petal.GcdBridge
DkMath.Petal.PadicBridge
DkMath.Petal.PrimitiveBridge
```

Main completed bridge chain:

```text
S0_nat
  = GN 3 (c - b) b
  -> gcd control with boundary gap
  -> p-adic valuation transfer
  -> primitive-prime / PrimitiveOnS0 bridge
```

Remaining experiment target:

```text
ReducedSupport / Anchor vocabulary
  -> HasNoPrimeBelow
  -> HasAnchorPrime
  -> anchored GN support carrier
```

## 1. 目的

本実験の目的は、GN kernel に現れる素因子を、単なる可除性ではなく **素数の種** として観測できるかを Lean 上で検証することである。

Current status: **[PARTIAL]**

The direct S0/GN, gcd, p-adic, and primitive-prime bridges are now implemented.
The remaining purpose is narrower: decide whether an explicit reduced-support
or anchor-prime vocabulary is useful before Zsigmondy-facing normalization.

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

This part is now mostly covered by:

```lean
DkMath.Petal.primitiveOnS0_of_prime_dvd_cube_sub_not_dvd_sub
DkMath.Petal.primitive_prime_dvd_S0_nat
DkMath.Petal.primitive_prime_padicValNat_cube_sub_eq_S0_nat
```

## 2. 背景

Petal / S0 では、三次元の場合に次の関係が現れる。

Current status: **[DONE]**

$$
c^3-b^3=(c-b)S0(c,b)
$$

かつ

$$
S0(c,b)=GN_3(c-b,b)
$$

したがって S0 は独立した特殊式ではなく、三次 GN kernel の Petal 可視面である。

This is now documented separately:

```text
docs/explanation/S0_cubic_petal_kernel.md
```

and implemented as:

```lean
DkMath.Petal.S0_nat_eq_GN_three_sub
```

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

The concrete degree-three boundary contact is now captured by:

```lean
DkMath.Petal.gcd_sub_S0_nat_eq_gcd_sub_three
DkMath.Petal.gcd_sub_S0_nat_dvd_three
DkMath.Petal.coprime_sub_S0_nat_of_coprime_of_not_dvd_three
```

The more general reduced-world vocabulary is still **[ACTIVE]**.

## 3. 基本方針

### 3.1. 新しい数学用語を作りすぎない

Current status: **[ACTIVE]**

通常の primorial や素数概念は変更しない。

代わりに、観測射影を導入する。

例として、\(r\) より小さい素因子を潰した reduced support を考える。

```lean
def HasNoPrimeBelow (r n : ℕ) : Prop :=
  ∀ p, p.Prime → p < r → ¬ p ∣ n
```

これは「\(r\) から始まる世界」を標準数学用語を壊さずに表現するための predicate である。

This remains the main open design point.  No mainline `HasNoPrimeBelow` or
`HasAnchorPrime` predicate has been introduced yet.

### 3.2. 例外 prime は排除ではなく分離する

Current status: **[PARTIAL]**

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

For S0 itself, explicit predicate wrappers have not yet been added.  However,
the working theorem surface already expresses the separation:

```lean
three_not_dvd_S0_nat_of_not_dvd_sub
gcd_sub_S0_nat_eq_gcd_sub_three
coprime_sub_S0_nat_of_coprime_of_not_dvd_three
```

So `S0ReducedAwayFromThree` is optional.  It should only be added if downstream
statements become clearer with a named predicate.

### 3.3. 先に GN 可除性を固める

Current status: **[DONE] / [OBSOLETE AS EXPERIMENT]**

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

This is now covered through existing Cosmic/Petal/GN bridge theorems and the
Petal primitive bridge:

```lean
DkMath.FLT.prime_dvd_S0_via_cosmic_bridge
DkMath.Petal.primitiveOnS0_of_prime_dvd_cube_sub_not_dvd_sub
```

The exact generic `GNBoundaryFreePrime` wrapper has not been introduced, but
the main divisibility movement needed for the cubic S0 path is available.

## 4. 実験対象

## 4.1. Phase A. S0 / GN 三次面の再固定

Status: **[DONE]**

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

Implemented:

```lean
DkMath.FLT.GN_three_sub_eq_S0_nat
DkMath.Petal.S0_nat_eq_GN_three_sub
```

Related existing cubic factorization:

```lean
DkMath.FLT.cube_sub_eq_mul_sub_S0
```

## 4.2. Phase B. 三例外の構造分離

Status: **[DONE FOR S0] / [ACTIVE FOR GENERAL REDUCED SUPPORT]**

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

Implemented S0-facing bridge names:

```lean
DkMath.Petal.three_not_dvd_S0_nat_of_not_dvd_sub
DkMath.Petal.gcd_sub_S0_nat_eq_gcd_sub_three
DkMath.Petal.gcd_sub_S0_nat_dvd_three
DkMath.Petal.coprime_sub_S0_nat_of_coprime_of_not_dvd_three
```

The stronger gcd formula makes the original one-way experiment less important:

```text
gcd(c - b, S0(c,b)) = gcd(c - b, 3)
```

This is the desired "3-primary contact" observation for the cubic Petal face.

## 4.3. Phase C. (r)-anchor reduced support

Status: **[ACTIVE]**

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

This is now the main remaining experiment.  The recommended next file is:

```text
lean/dk_math/DkMath/Petal/ReducedSupport.lean
```

Minimal first API:

```lean
def HasNoPrimeBelow (r n : ℕ) : Prop :=
  ∀ p, p.Prime → p < r → ¬ p ∣ n

def HasAnchorPrime (r n : ℕ) : Prop :=
  r.Prime ∧ r ∣ n ∧ HasNoPrimeBelow r n

def HasPositiveAnchorPrime (r n : ℕ) : Prop :=
  0 < n ∧ HasAnchorPrime r n

theorem hasAnchorPrime_prime
theorem hasAnchorPrime_anchor_dvd
theorem hasAnchorPrime_no_smaller_prime
theorem hasAnchorPrime_anchor_le_of_prime_dvd
theorem hasPositiveAnchorPrime_pos
theorem hasPositiveAnchorPrime_prime
theorem hasPositiveAnchorPrime_anchor_dvd
theorem hasPositiveAnchorPrime_no_smaller_prime
theorem hasPositiveAnchorPrime_anchor_le_of_prime_dvd
```

Keep this layer independent of S0 at first.

Design decision:

```text
HasAnchorPrime           = wide raw carrier predicate
HasPositiveAnchorPrime   = strict support predicate for nonzero carriers
```

This is the B-plan for the `0` carrier issue.  The wide predicate keeps the
entrance broad, while the positive predicate is used when strict prime-support
semantics are required.

## 4.4. Phase D. GN primitive candidate

Status: **[PARTIAL]**

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

The cubic S0 primitive path is already implemented:

```lean
DkMath.Petal.primitive_prime_dvd_S0_nat
DkMath.Petal.primitive_prime_padicValNat_cube_sub_eq_S0_nat
DkMath.Petal.primitiveOnS0_of_prime_dvd_cube_sub_not_dvd_sub
DkMath.Petal.exists_primitiveOnS0_of_not_three_dvd_sub
```

What remains is optional vocabulary design:

```lean
GNBoundaryFreePrime
GNPrimitiveCandidate
```

Recommendation: defer these until `ReducedSupport` shows a concrete need.

## 4.5. Phase E. Anchor と GN の合流

Status: **[ACTIVE AFTER PHASE C]**

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

Updated recommendation:

Do not attach `HasAnchorPrime r q` directly to a prime `q` unless the intended
claim is `q = r`.  For support observation, prefer a carrier number:

```lean
def AnchoredCarrier (r n : ℕ) : Prop :=
  HasAnchorPrime r n

def AnchoredGNCarrier (r d x u n : ℕ) : Prop :=
  AnchoredCarrier r n ∧ n ∣ GN d x u
```

Only specialize to prime witnesses after the carrier API is tested.

## 5. ファイル構成案

Status: **[UPDATED]**

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

Current recommendation:

```text
DkMath.Petal.ReducedSupport     [next]
DkMath.Petal.Anchor             [after ReducedSupport proves useful]
DkMath.Petal.GNPrimitive        [defer until a concrete theorem needs it]
```

The already completed bridge files are:

```text
DkMath.Petal.GNBridge
DkMath.Petal.GcdBridge
DkMath.Petal.PadicBridge
DkMath.Petal.PrimitiveBridge
```

## 6. import 方針

Status: **[UPDATED]**

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

For the current remaining reduced-support experiment, start with a very small
import surface:

```lean
import DkMath.Petal.Basic
```

Only import `DkMath.Petal.GNBridge` or `DkMath.Petal.PrimitiveBridge` when the
first GN-facing theorem is added.

## 7. 成功条件

Status: **[UPDATED]**

本実験の成功条件は次である。

1. `S0` を `GN 3` の Petal face として再利用しやすい名前で参照できる。
2. \(3\) 例外を `q ≠ 3` の単純排除ではなく、`3-primary` 分離として theorem 名に反映できる。
3. \(r\)-anchor reduced support を `HasNoPrimeBelow` / `HasAnchorPrime` として表現できる。
4. 差冪に現れ境界にいない素因子が GN 側へ移ることを theorem 化できる。
5. `GNPrimitiveCandidate` または `GNBoundaryFreePrime` が Zsigmondy bridge の入力語彙として使える。

Current status of the original success conditions:

```text
1. S0 as GN 3 Petal face                  [DONE]
2. 3-primary S0 boundary contact          [DONE FOR S0]
3. r-anchor reduced support predicates    [ACTIVE]
4. boundary-free prime moves to GN/S0      [DONE FOR CUBIC S0]
5. GNPrimitiveCandidate vocabulary         [DEFERRED]
```

Revised success condition for the remaining experiment:

```text
ReducedSupport minimal API builds no-sorry.
It does not force unwanted imports into DkMath.Petal.
It can express "no smaller prime support" without committing to nthPrime or primorial.
It can later compose with S0/GN bridge theorems without changing their statements.
```

## 8. 失敗条件

Status: **[STILL VALID]**

次のいずれかが発生した場合は、定理化を急がず実験を止める。

1. `HasAnchorPrime` が強すぎて、一般 \(r\)-world を表現できない。
2. \(3\)-primary 分離が S0 専用すぎて一般 GN に持ち上がらない。
3. `Nat` 減算条件が重くなり、定理文が downstream で使いにくい。
4. 既存 GN / gcd theorem の wrapper で済む範囲を超え、新規 gcd 理論が必要になる。
5. Zsigmondy へ渡す前に anchor predicate が本線 import を汚染する。

    Additional current failure condition:

6. `HasAnchorPrime r n` is mostly used with `n = q` for a prime witness and
   collapses to `q = r`, making the predicate too narrow for support carriers.

## 9. 昇格条件

Status: **[UPDATED]**

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

The old list mixes already-completed bridge targets with still-open vocabulary.
The updated minimal build target should be:

```text
lake build DkMath.Petal.ReducedSupport
```

with no-sorry API:

```lean
HasNoPrimeBelow
HasAnchorPrime
hasAnchorPrime_prime
hasAnchorPrime_anchor_dvd
hasAnchorPrime_no_smaller_prime
```

Optional second checkpoint:

```lean
AnchoredCarrier
AnchoredGNCarrier
anchoredGNCarrier_anchor
anchoredGNCarrier_dvd_GN
```

昇格先は次のいずれかとする。

```text
DkMath.Petal.ReducedSupport
DkMath.Petal.GNPrimitive
DkMath.Petal.Anchor
```

Current preferred promotion order:

```text
1. DkMath.Petal.ReducedSupport
2. DkMath.Petal.Anchor
3. DkMath.Petal.GNPrimitive, only if needed
```

## 10. 将来展望

Status: **[UNCHANGED]**

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
