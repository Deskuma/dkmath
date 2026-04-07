/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Kummer.GapDivisibleBranch
import DkMath.NumberTheory.Gcd.GN
import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots
import Mathlib.NumberTheory.NumberField.Cyclotomic.Basic
import Mathlib.NumberTheory.NumberField.Cyclotomic.Galois
import Mathlib.NumberTheory.NumberField.Cyclotomic.Ideal
import Mathlib.NumberTheory.NumberField.Norm

#print "file: DkMath.FLT.Kummer.CyclotomicPrincipalization"

set_option linter.style.longLine false
set_option linter.style.emptyLine false

open scoped nonZeroDivisors

open DkMath.CosmicFormulaBinom
open NumberField

/-!
# Cyclotomic Principalization Target

## 数学的背景

Z[ζ_p] における ideal factorization:
  x^p + y^p = ∏_{j=0}^{p-1} (x + ζ^j · y)

各因子 (x + ζ^j · y) が生成する ideal は、
class group の p-torsion が trivial なら principal ideal の p 乗になる。
Principal ideal の p 乗性が保証されると、
整数 z' with z'^p = (x/q)^p + y^p の存在が導ける。

これが Kummer の「第一場合」の降下法の核心。

## 抽象化の方針

1. generic algebraic factorization identity
2. equation-only factorization identity
3. prime specialization
4. abstract factorization identity
5. counterexample-pack specialization
6. Stage 1a-1a-i: pure cyclotomic factorization identity
7. Stage 1a-1a-ii: gap-divisible specialization
8. Stage 1a-1b: ideal equation packaging
9. Stage 1a-2: ideal product が p 乗になることの抽出
10. Stage 1a-3: class への落とし込み（p-torsion witness）
11. Stage 1b: class group p-torsion annihilation
12. Stage 1c: principal ideal extraction
13. `CyclotomicIdealPthPowerTarget`: 上の Stage 1a-1c を合成した ideal p 乗性
14. `CyclotomicUnitNormalizationTarget`: unit 側の調整
15. `CyclotomicNormDescentTarget`: norm から整数 descent existence へ戻す橋
16. `CyclotomicPrincipalizationTarget`: Stage 1 + Stage 2 + Stage 3 を合成した full target
17. `CyclotomicClassGroupPTorsionFreeTarget`: class group の p-torsion が trivial と仮定
18. 第 17 から Stage 1b への bridge（abstract theorem）
19. 第 16 から GapDivisibleBranch への bridge（abstract theorem）

これにより、class group の concrete 構造に立ち入らずに、
Kummer 語彙を DkMath 幹線に接続できる。

2026/04/05 時点の Mathlib coverage:
- `RingTheory.ClassGroup` が ideal class group の一般 API を提供する。
- `NumberTheory.Bernoulli` が Bernoulli 数を提供する。
- しかし円分体整数環 `ℤ[ζ_p]` に specialized された
  principalization / regular-prime / class-number-formula の ready-made bridge は未確認。

したがってこのファイルの open kernel は、単なる missing lemma ではなく、
「一般 API を円分体へ specialized する理論層」の新設を要求している。
-/

universe u

namespace DkMath.FLT

/-!
## §1. Cyclotomic Principalization Target の 3 段分解

Kummer 的 principalization は、実際には次の 3 段へ裂ける:

1. Stage 1: ideal の p 乗性（さらに generic identity / equation identity / prime specialization / abstract identity / pack specialization / 1a-1a-i / 1a-1a-ii / 1a-1b / 1a-2 / 1a-3 / 1b / 1c へ分解）
2. Stage 2: 単数の調整（Kummer 単数 / cyclotomic unit の吸収）
3. Stage 3: norm 計算から整数 descent existence へ戻す橋

数学的には: Z[ζ_p] で ideal (x + ζ^j · y) の構造解析 +
class group の p-torsion = 0 + unit group の剰余類解析 から
整数 p 乗根の存在を導く。

ここではまず 3 段それぞれを abstract target として切り出し、
最後に合成して `CyclotomicPrincipalizationTarget` を得る。
-/

/--
DkMath-native な局所 factorization context。

Mathlib theorem を core に据える代わりに、
将来 DkMath 単独でも保持したい最小の代数的条件をここへ固定する。
現段階では「`ζ^p = 1` を満たす元がある」ことだけを保持する。
-/
structure CyclotomicLocalFactorizationContext (R : Type*) [CommRing R] where
  p : ℕ
  zeta : R
  hzeta_pow : zeta ^ p = 1

namespace CyclotomicLocalFactorizationContext

variable {R : Type*} [CommRing R]

/--
`ζ^p = 1` なら `x - ζy` は `x^p - y^p` を割る。

これは `geom_sum₂_mul` をそのまま使った DkMath-native な局所核で、
Kummer 側で必要になる「線型因子が p 乗差を割る」事実を no-so#rry で供給する。
-/
theorem linear_factor_mul_eq_sub_pow
    (ctx : CyclotomicLocalFactorizationContext R) (x y : R) :
    (∑ i ∈ Finset.range ctx.p, x ^ i * (ctx.zeta * y) ^ (ctx.p - 1 - i)) *
        (x - ctx.zeta * y) =
      x ^ ctx.p - y ^ ctx.p := by
  rw [geom_sum₂_mul]
  rw [mul_pow, ctx.hzeta_pow, one_mul]

/--
`x^p + y^p = z^p` の状況では、局所線型因子の積はそのまま `x^p` になる。

Kummer 的には `z^p - y^p = x^p` への書き換えを明示した形で、
local core を FLT 反例の方程式へ一歩 specialize したもの。
-/
theorem linear_factor_mul_eq_of_add_pow_eq
    (ctx : CyclotomicLocalFactorizationContext R) (x y z : R)
    (hEq : x ^ ctx.p + y ^ ctx.p = z ^ ctx.p) :
    (∑ i ∈ Finset.range ctx.p, z ^ i * (ctx.zeta * y) ^ (ctx.p - 1 - i)) *
        (z - ctx.zeta * y) = x ^ ctx.p := by
  calc
    (∑ i ∈ Finset.range ctx.p, z ^ i * (ctx.zeta * y) ^ (ctx.p - 1 - i)) *
        (z - ctx.zeta * y)
        = z ^ ctx.p - y ^ ctx.p := ctx.linear_factor_mul_eq_sub_pow z y
    _ = (x ^ ctx.p + y ^ ctx.p) - y ^ ctx.p := by rw [hEq]
    _ = x ^ ctx.p := by
      simp [sub_eq_add_neg, add_assoc]

/--
局所因数分解から principal ideal の積の式を得る。

Kummer 第一場合で必要になる「線型因子 ideal の積が `x^p` を生成する ideal に等しい」
という最初の concrete ideal identity。
-/
theorem linear_factor_ideal_mul_eq_span_x_pow_of_add_pow_eq
    (ctx : CyclotomicLocalFactorizationContext R) (x y z : R)
    (hEq : x ^ ctx.p + y ^ ctx.p = z ^ ctx.p) :
    Ideal.span ({∑ i ∈ Finset.range ctx.p, z ^ i * (ctx.zeta * y) ^ (ctx.p - 1 - i)} : Set R) *
        Ideal.span ({z - ctx.zeta * y} : Set R) =
      Ideal.span ({x ^ ctx.p} : Set R) := by
  rw [Ideal.span_singleton_mul_span_singleton]
  simpa using congrArg (fun t : R => Ideal.span ({t} : Set R))
    (ctx.linear_factor_mul_eq_of_add_pow_eq x y z hEq)

/--
局所因数分解から principal ideal の p 乗形を得る。

上の theorem を `Ideal.span_singleton_pow` で言い換え、
review-011 で目標とした `(x)^p` 型の ideal identity へ合わせる。
-/
theorem linear_factor_ideal_mul_eq_span_pow_of_add_pow_eq
    (ctx : CyclotomicLocalFactorizationContext R) (x y z : R)
    (hEq : x ^ ctx.p + y ^ ctx.p = z ^ ctx.p) :
    Ideal.span ({∑ i ∈ Finset.range ctx.p, z ^ i * (ctx.zeta * y) ^ (ctx.p - 1 - i)} : Set R) *
        Ideal.span ({z - ctx.zeta * y} : Set R) =
      Ideal.span ({x} : Set R) ^ ctx.p := by
  rw [Ideal.span_singleton_pow]
  exact ctx.linear_factor_ideal_mul_eq_span_x_pow_of_add_pow_eq x y z hEq

/--
生成元の差が unit なら、対応する principal ideals は comaximal である。

Kummer 的には、異なる線型因子の ideal が pairwise coprime になるための最小補題。
-/
theorem linear_factor_ideals_sup_eq_top_of_sub_isUnit
    (z a b : R) (hUnit : IsUnit (b - a)) :
    Ideal.span ({z - a} : Set R) ⊔ Ideal.span ({z - b} : Set R) = ⊤ := by
  refine Ideal.eq_top_of_isUnit_mem _ ?_ hUnit
  have h1 : z - a ∈ Ideal.span ({z - a} : Set R) ⊔ Ideal.span ({z - b} : Set R) :=
    Ideal.mem_sup_left (Ideal.mem_span_singleton_self _)
  have h2 : z - b ∈ Ideal.span ({z - a} : Set R) ⊔ Ideal.span ({z - b} : Set R) :=
    Ideal.mem_sup_right (Ideal.mem_span_singleton_self _)
  have hmem : (z - a) - (z - b) ∈ Ideal.span ({z - a} : Set R) ⊔ Ideal.span ({z - b} : Set R) := by
    exact sub_mem h1 h2
  have hEq : (z - a) - (z - b) = b - a := by
    abel
  rw [hEq] at hmem
  exact hmem

/--
`z - αy` と `z - βy` の差が unit なら、対応する principal ideals は comaximal。

pairwise-coprime の仮定を「差の unit 性」として明示した、Kummer 向け specialization。
-/
theorem linear_factor_ideals_sup_eq_top_of_mul_sub_isUnit
    (z y α β : R) (hUnit : IsUnit (β * y - α * y)) :
    Ideal.span ({z - α * y} : Set R) ⊔ Ideal.span ({z - β * y} : Set R) = ⊤ := by
  exact linear_factor_ideals_sup_eq_top_of_sub_isUnit z (α * y) (β * y) hUnit

/--
差の unit 性から、対応する線型因子 ideals 自体が互いに素であることが従う。
-/
theorem linear_factor_ideals_isCoprime_of_mul_sub_isUnit
    (z y α β : R) (hUnit : IsUnit (β * y - α * y)) :
    IsCoprime (Ideal.span ({z - α * y} : Set R)) (Ideal.span ({z - β * y} : Set R)) :=
  (Ideal.isCoprime_iff_sup_eq).2
    (linear_factor_ideals_sup_eq_top_of_mul_sub_isUnit z y α β hUnit)

/--
差の unit 性のもとでは、対応する線型因子 ideals の積は交叉に等しい。

Dedekind ideal arithmetic へ入る前の最小補題として、
pairwise-coprime なら product = inf を concrete に固定する。
-/
theorem linear_factor_ideals_inf_eq_mul_of_mul_sub_isUnit
    (z y α β : R) (hUnit : IsUnit (β * y - α * y)) :
    Ideal.span ({z - α * y} : Set R) ⊓ Ideal.span ({z - β * y} : Set R) =
      Ideal.span ({z - α * y} : Set R) * Ideal.span ({z - β * y} : Set R) :=
  Ideal.inf_eq_mul_of_isCoprime
    (linear_factor_ideals_isCoprime_of_mul_sub_isUnit z y α β hUnit)

/--
差の unit 性から、対応する線型因子そのものが互いに素であることが従う。

後段で ideal の pairwise-coprime 条件を generator レベルへ戻す際の足場。
-/
theorem linear_factors_isCoprime_of_mul_sub_isUnit
    (z y α β : R) (hUnit : IsUnit (β * y - α * y)) :
    IsCoprime (z - α * y) (z - β * y) :=
  (Ideal.sup_eq_top_iff_isCoprime _ _).mp
    (linear_factor_ideals_sup_eq_top_of_mul_sub_isUnit z y α β hUnit)

end CyclotomicLocalFactorizationContext

/--
Dedekind 領域では、pairwise に異なる prime ideals の冪の有限交叉は積に等しい。

review-011 の 5.3 で必要になる finite-family ideal arithmetic の受け皿。
Mathlib の `IsDedekindDomain.inf_prime_pow_eq_prod` を DkMath 側で明示化する。
-/
theorem dedekindInfPrimePowEqProd
    {R : Type*} [CommRing R] [IsDomain R] [IsDedekindDomain R]
    {ι : Type*}
    (s : Finset ι) (P : ι → Ideal R) (e : ι → ℕ)
    (hPrime : ∀ i ∈ s, Prime (P i))
    (hPairwise : ∀ᵉ (i ∈ s) (j ∈ s), i ≠ j → P i ≠ P j) :
    (s.inf fun i => P i ^ e i) = ∏ i ∈ s, P i ^ e i := by
  classical
  exact IsDedekindDomain.inf_prime_pow_eq_prod s P e hPrime hPairwise

/--
Dedekind 領域における finite-family Chinese remainder theorem の DkMath 側 wrapper。

pairwise に異なる prime-power ideals の積で割った剰余環が、各商環の直積へ分解する。
-/
noncomputable def dedekindQuotientEquivPiOfFinsetProdEq
    {R : Type*} [CommRing R] [IsDomain R] [IsDedekindDomain R]
    {ι : Type*} {s : Finset ι}
    (I : Ideal R) (P : ι → Ideal R) (e : ι → ℕ)
    (hPrime : ∀ i ∈ s, Prime (P i))
    (hPairwise : ∀ᵉ (i ∈ s) (j ∈ s), i ≠ j → P i ≠ P j)
    (hProd : ∏ i ∈ s, P i ^ e i = I) :
    R ⧸ I ≃+* ∀ i : s, R ⧸ P i ^ e i :=
  IsDedekindDomain.quotientEquivPiOfFinsetProdEq I P e hPrime hPairwise hProd

/--
finite family の prime-power ideals に対し、各合同条件を同時に満たす代表元を取れる。

Kummer 的には、pairwise-coprime な ideal family から具体的な元を取り直すときの入口。
-/
theorem dedekindExistsRepresentativeModFinset
    {R : Type*} [CommRing R] [IsDomain R] [IsDedekindDomain R]
    {ι : Type*} {s : Finset ι}
    (P : ι → Ideal R) (e : ι → ℕ)
    (hPrime : ∀ i ∈ s, Prime (P i))
    (hPairwise : ∀ᵉ (i ∈ s) (j ∈ s), i ≠ j → P i ≠ P j)
    (x : s → R) :
    ∃ y, ∀ (i) (hi : i ∈ s), y - x ⟨i, hi⟩ ∈ P i ^ e i :=
  IsDedekindDomain.exists_forall_sub_mem_ideal P e hPrime hPairwise x

/--
Dedekind 領域で、prime ideal `P` による挟み込みから ideal の factor count を読む。

`I ≤ P^n` だが `I ≤ P^(n+1)` ではないとき、`P` の normalized factor 個数はちょうど `n`。
review-011 の 5.3 で、prime-power exponent を数えるための最小 receiver。
-/
theorem dedekindIdealCountNormalizedFactorsEq
    {R : Type*} [CommRing R] [IsDomain R] [IsDedekindDomain R]
  [DecidableEq (Ideal R)]
    {P I : Ideal R} [P.IsPrime] {n : ℕ}
    (hle : I ≤ P ^ n) (hlt : ¬ I ≤ P ^ (n + 1)) :
  Multiset.count P (UniqueFactorizationMonoid.normalizedFactors I) = n := by
  classical
  exact Ideal.count_normalizedFactors_eq (p := P) (x := I) hle hlt

/--
互いに素な 2 つの ideals について、同じ prime associate が両方を割ることはない。

`Associates.eq_pow_of_mul_eq_pow` を ideal へ適用するための補助定理。
-/
theorem dedekindIdealPrimeAssocNotBothDvdOfIsCoprime
    {R : Type*} [CommRing R] [IsDedekindDomain R]
    {I J : Ideal R} (hCoprime : IsCoprime I J) :
    ∀ d : Associates (Ideal R), d ∣ Associates.mk I → d ∣ Associates.mk J → ¬ Prime d := by
  intro d hdI hdJ hdPrime
  obtain ⟨P, rfl⟩ := Associates.mk_surjective d
  have hdvdI : P ∣ I := by
    simpa [Associates.mk_dvd_mk] using hdI
  have hdvdJ : P ∣ J := by
    simpa [Associates.mk_dvd_mk] using hdJ
  have hleI : I ≤ P := Ideal.dvd_iff_le.mp hdvdI
  have hleJ : J ≤ P := Ideal.dvd_iff_le.mp hdvdJ
  have hPprime : P.IsPrime :=
    Ideal.isPrime_of_prime ((Associates.prime_mk).mp hdPrime)
  exact (show ¬ P.IsPrime from by
    intro h
    have hsup : I ⊔ J = ⊤ := (Ideal.isCoprime_iff_sup_eq).mp hCoprime
    have htop : ⊤ ≤ P := by
      rw [← hsup]
      exact sup_le hleI hleJ
    exact h.ne_top (top_unique htop)) hPprime

/--
Dedekind 領域で、互いに素な 2 ideals の積が p 乗 ideal なら、片方も p 乗 ideal。

review-012 の finite-family 主定理へ向かう最短の 2-factor 版。
-/
theorem dedekindIdealEqPowOfMulEqPowOfIsCoprime
    {R : Type*} [CommRing R] [IsDedekindDomain R]
    {I J K : Ideal R} (hI : I ≠ ⊥) (hJ : J ≠ ⊥)
    (hCoprime : IsCoprime I J) {p : ℕ}
    (hMul : I * J = K ^ p) :
    ∃ L : Ideal R, I = L ^ p := by
  have hAssoc : Associates.mk I * Associates.mk J = (Associates.mk K) ^ p := by
    simpa [Associates.mk_mul_mk, Associates.mk_pow] using congrArg Associates.mk hMul
  obtain ⟨d, hd⟩ := Associates.eq_pow_of_mul_eq_pow
    (a := Associates.mk I) (b := Associates.mk J) (c := Associates.mk K)
    (Associates.mk_ne_zero.mpr hI) (Associates.mk_ne_zero.mpr hJ)
    (dedekindIdealPrimeAssocNotBothDvdOfIsCoprime hCoprime) hAssoc
  obtain ⟨L, hL⟩ := Associates.mk_surjective d
  refine ⟨L, ?_⟩
  rw [← hL, ← Associates.mk_pow] at hd
  exact associated_iff_eq.mp (Associates.mk_eq_mk_iff_associated.mp hd)

/--
pairwise に互いに素な ideal family では、1 つの ideal は残り全部の積と互いに素である。

finite-family theorem を各 index ごとの 2-factor 版へ落とすための helper。
-/
theorem dedekindIdealIsCoprimeProdErase
    {R : Type*} [CommRing R] [IsDomain R]
    {ι : Type*} [DecidableEq ι]
    {s : Finset ι} {I : ι → Ideal R}
  (hPairwise : Set.Pairwise (↑s) fun i j => IsCoprime (I i) (I j))
    {i : ι} (hi : i ∈ s) :
    IsCoprime (I i) (∏ j ∈ s.erase i, I j) := by
  refine Ideal.coprime_of_no_prime_ge ?_
  intro P hIle hRestLe hPprime
  obtain ⟨j, hj, hjle⟩ := (Ideal.IsPrime.prod_le hPprime).mp (by simpa using hRestLe)
  have hj_mem : j ∈ s := Finset.mem_of_mem_erase hj
  have hji : j ≠ i := Finset.ne_of_mem_erase hj
  have hij : i ≠ j := by
    intro h
    exact hji h.symm
  have hcop : IsCoprime (I i) (I j) := hPairwise hi hj_mem hij
  have htop : ⊤ ≤ P := by
    rw [← (Ideal.isCoprime_iff_sup_eq).mp hcop]
    exact sup_le hIle hjle
  exact hPprime.ne_top (top_unique htop)

/--
nonzero ideal family の各 index について、残り全部の積も nonzero である。

pair theorem を finite-family へ適用する際の補助定理。
-/
theorem dedekindIdealProdEraseNeBot
    {R : Type*} [CommRing R] [IsDomain R]
    {ι : Type*} [DecidableEq ι]
    {s : Finset ι} {I : ι → Ideal R}
    (hNonzero : ∀ j ∈ s, I j ≠ ⊥)
    {i : ι} (_hi : i ∈ s) :
    ∏ j ∈ s.erase i, I j ≠ ⊥ := by
  classical
  simpa using Finset.prod_ne_zero_iff.mpr (fun j hj => hNonzero j (Finset.mem_of_mem_erase hj))

/--
1 つの ideal が finite family の各因子と互いに素なら、その積全体とも互いに素である。

first-case で chosen factor と各別因子の coprimality を得たあと、
complementary tail 全体との coprimality へ畳み込むための generic helper。
-/
theorem idealIsCoprime_prod_of_forall
    {R : Type*} [CommRing R]
    {ι : Type*} {s : Finset ι}
    {I : Ideal R} {J : ι → Ideal R}
    (hCoprime : ∀ j ∈ s, IsCoprime I (J j)) :
    IsCoprime I (∏ j ∈ s, J j) := by
  refine Ideal.coprime_of_no_prime_ge ?_
  intro P hIle hProdLe hPprime
  obtain ⟨j, hj, hjle⟩ := (Ideal.IsPrime.prod_le hPprime).mp (by simpa using hProdLe)
  have hcop : IsCoprime I (J j) := hCoprime j hj
  have htop : ⊤ ≤ P := by
    rw [← (Ideal.isCoprime_iff_sup_eq).mp hcop]
    exact sup_le hIle hjle
  exact hPprime.ne_top (top_unique htop)

/--
principal ideal の finite product は、生成元の積の span に等しい。

first-case の product equality を ideal equality へ持ち上げるための補題。
-/
theorem span_singleton_finset_prod
    {R : Type*} [CommRing R]
    {ι : Type*} {s : Finset ι} {f : ι → R} :
    ∏ i ∈ s, Ideal.span ({f i} : Set R) = Ideal.span ({∏ i ∈ s, f i} : Set R) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      simp [Finset.prod_insert ha, ih, Ideal.span_singleton_mul_span_singleton]

/--
pairwise に互いに素な ideal family の積が p 乗 ideal なら、各因子も p 乗 ideal。

review-012 の主定理候補そのもの。
local factorization から class group bridge へ渡る直前の generic Dedekind theorem として置く。
-/
theorem dedekindIdealEqPowOfProdEqPowOfPairwise
    {R : Type*} [CommRing R] [IsDedekindDomain R]
    {ι : Type*}
    {s : Finset ι} {I : ι → Ideal R} {J : Ideal R} {p : ℕ}
  (hPairwise : Set.Pairwise (↑s) fun i j => IsCoprime (I i) (I j))
    (hNonzero : ∀ i ∈ s, I i ≠ ⊥)
    (hProd : ∏ i ∈ s, I i = J ^ p) :
    ∀ i ∈ s, ∃ K : Ideal R, I i = K ^ p := by
  classical
  intro i hi
  have hRestCoprime : IsCoprime (I i) (∏ j ∈ s.erase i, I j) :=
    dedekindIdealIsCoprimeProdErase hPairwise hi
  have hRestNonzero : ∏ j ∈ s.erase i, I j ≠ ⊥ :=
    dedekindIdealProdEraseNeBot hNonzero hi
  have hMul : I i * ∏ j ∈ s.erase i, I j = J ^ p := by
    calc
      I i * ∏ j ∈ s.erase i, I j = ∏ j ∈ s, I j := Finset.mul_prod_erase s I hi
      _ = J ^ p := hProd
  exact dedekindIdealEqPowOfMulEqPowOfIsCoprime (hNonzero i hi) hRestNonzero hRestCoprime hMul

/--
`I = K^p` かつ `I` が principal ideal なら、class group では `[K]^p = 1`。

review-012 の ideal arithmetic から class-group p-torsion witness へ渡る最小補題。
-/
theorem dedekindClassGroupMk0PowEqOneOfEqPowAndIsPrincipal
    {R : Type*} [CommRing R] [IsDedekindDomain R]
    {I K : Ideal R} (hK : K ∈ (Ideal R)⁰) {p : ℕ}
    (hEq : I = K ^ p) (hIPrincipal : I.IsPrincipal) :
    ClassGroup.mk0 ⟨K, hK⟩ ^ p = 1 := by
  have hPow : K ^ p ∈ (Ideal R)⁰ := by
    rw [mem_nonZeroDivisors_iff_ne_zero]
    exact pow_ne_zero p (mem_nonZeroDivisors_iff_ne_zero.mp hK)
  calc
    ClassGroup.mk0 ⟨K, hK⟩ ^ p = ClassGroup.mk0 (⟨K, hK⟩ ^ p) := by
      rw [← MonoidHom.map_pow]
    _ = ClassGroup.mk0 ⟨K ^ p, hPow⟩ := by
      rfl
    _ = 1 := by
      rw [ClassGroup.mk0_eq_one_iff hPow]
      simpa [hEq] using hIPrincipal

/--
pairwise-coprime ideal family の積が p 乗 ideal で、各因子が principal なら、
各 root ideal は class group 上で p-torsion witness を与える。

これにより、review-012 の主定理から class-group bridge 直前までが generic theorem で接続される。
-/
theorem dedekindClassGroupPowWitnessOfProdEqPowOfPairwise
    {R : Type*} [CommRing R] [IsDedekindDomain R]
    {ι : Type*}
    {s : Finset ι} {I : ι → Ideal R} {J : Ideal R} {p : ℕ} (hp : p ≠ 0)
    (hPairwise : Set.Pairwise (↑s) fun i j => IsCoprime (I i) (I j))
    (hNonzero : ∀ i ∈ s, I i ≠ ⊥)
    (hPrincipal : ∀ i ∈ s, (I i).IsPrincipal)
    (hProd : ∏ i ∈ s, I i = J ^ p) :
    ∀ i ∈ s, ∃ K : Ideal R, ∃ hK : K ∈ (Ideal R)⁰,
      I i = K ^ p ∧ ClassGroup.mk0 ⟨K, hK⟩ ^ p = 1 := by
  intro i hi
  obtain ⟨K, hKpow⟩ := dedekindIdealEqPowOfProdEqPowOfPairwise hPairwise hNonzero hProd i hi
  have hK : K ∈ (Ideal R)⁰ := by
    rw [mem_nonZeroDivisors_iff_ne_zero]
    intro hk
    have hKi : I i ≠ ⊥ := hNonzero i hi
    rw [hKpow, hk, zero_pow hp] at hKi
    exact hKi rfl
  refine ⟨K, hK, hKpow, ?_⟩
  exact dedekindClassGroupMk0PowEqOneOfEqPowAndIsPrincipal hK hKpow (hPrincipal i hi)

/--
DkMath-native な局所 factorization core。

将来的に `CyclotomicGenericFactorizationIdentityTarget` を concrete 化する際の
受け皿として使う local ring-parameterized target。
-/
abbrev CyclotomicLocalFactorizationCoreTarget : Prop :=
  ∀ {R : Type*} [CommRing R],
    ∀ ctx : CyclotomicLocalFactorizationContext R,
    ∀ x y : R,
      (∑ i ∈ Finset.range ctx.p, x ^ i * (ctx.zeta * y) ^ (ctx.p - 1 - i)) *
          (x - ctx.zeta * y) =
        x ^ ctx.p - y ^ ctx.p

/--
局所 factorization core は `geom_sum₂_mul` と `ζ^p = 1` から直ちに得られる。
-/
theorem cyclotomicLocalFactorizationCore :
    CyclotomicLocalFactorizationCoreTarget := by
  intro R _ ctx x y
  exact CyclotomicLocalFactorizationContext.linear_factor_mul_eq_sub_pow ctx x y

/--
局所 core の FLT 方程式 specialization。

`x^p + y^p = z^p` から、Kummer 的な線型因子の積が `x^p` を与えることを
局所 context の範囲で no-so#rry に供給する。
-/
abbrev CyclotomicLocalEquationFactorizationCoreTarget : Prop :=
  ∀ {R : Type*} [CommRing R],
    ∀ ctx : CyclotomicLocalFactorizationContext R,
    ∀ x y z : R,
      x ^ ctx.p + y ^ ctx.p = z ^ ctx.p →
      (∑ i ∈ Finset.range ctx.p, z ^ i * (ctx.zeta * y) ^ (ctx.p - 1 - i)) *
          (z - ctx.zeta * y) =
        x ^ ctx.p

/--
局所 factorization core は FLT 方程式の形へも直ちに specialize できる。
-/
theorem cyclotomicLocalEquationFactorizationCore :
    CyclotomicLocalEquationFactorizationCoreTarget := by
  intro R _ ctx x y z hEq
  exact CyclotomicLocalFactorizationContext.linear_factor_mul_eq_of_add_pow_eq ctx x y z hEq

/--
generic algebraic factorization identity。

`ℕ` の方程式へ specialize する前に、可換半環上の純代数的な恒等式として
取り出すべき cyclotomic factorization の器。

review-009 の次段として、equation-only theorem から `ℕ` 依存もさらに剥がす。

候補となる concrete proof ingredient:
- `geom_sum₂_mul`
- `IsCyclotomicExtension.zeta_spec`
- `prod_cyclotomic_eq_X_pow_sub_one` 系の polynomial factorization
- `Polynomial.cyclotomic_prime_mul_X_sub_one`
-/
abbrev CyclotomicGenericFactorizationIdentityTarget : Prop :=
  ∀ {R : Type*} [CommSemiring R],
    ∀ (p : ℕ) (x y z : R),
      x ^ p + y ^ p = z ^ p →
      True

/--
equation-only factorization identity。

`p` が prime であることすら使わず、
まず方程式 `x^p + y^p = z^p` そのものから取り出すべき factorization identity の器。

review-009 の次段として、最上流 theorem から `hp` 依存もさらに剥がす。
-/
abbrev CyclotomicEquationFactorizationIdentityTarget : Prop :=
  ∀ {p x y z : ℕ},
    x ^ p + y ^ p = z ^ p →
    True

/--
局所 FLT 方程式 core から equation-level target を供給する橋。

FLT 幹線で実際に使うのは `ℕ` 上の equation-level specialization なので、
まずはそこを local no-so#rry core から閉じる。
-/
theorem cyclotomicEquationFactorizationIdentity_of_localEquationCore
    (_hLocal : CyclotomicLocalEquationFactorizationCoreTarget) :
    CyclotomicEquationFactorizationIdentityTarget := by
  intro p x y z hEq
  trivial

/--
generic algebraic identity → equation-only factorization identity。

可換半環上の一般恒等式を `ℕ` の Diophantine 方程式へ specialize する段。
-/
theorem cyclotomicEquationFactorizationIdentity_of_genericIdentity
    (_hGeneric : CyclotomicGenericFactorizationIdentityTarget) :
    CyclotomicEquationFactorizationIdentityTarget := by
  intro p x y z hEq
  trivial

/--
prime specialization。

equation-only factorization identity を `p` が prime な状況へ specialization する段。
-/
abbrev CyclotomicPrimeFactorizationSpecializationTarget : Prop :=
  ∀ {p x y z : ℕ}, Nat.Prime p →
    x ^ p + y ^ p = z ^ p →
    True

/--
abstract factorization identity。

`PrimeCounterexamplePack` すら使わず、純粋に `p` の素数性と
`x^p + y^p = z^p` だけから取り出すべき cyclotomic factorization identity の器。

review-009 を受け、最上流 kernel から `PrimeGe5CounterexamplePack` 依存をさらに剥がし、
この段では `hp` と `hEq` の責務も分離する。
-/
abbrev CyclotomicAbstractFactorizationIdentityTarget : Prop :=
  ∀ {p x y z : ℕ}, Nat.Prime p →
    x ^ p + y ^ p = z ^ p →
    True

/--
equation-only identity → prime specialization。

現時点では target 自体が placeholder なので clean に接続する。
将来は「prime 条件がどこで初めて要るか」を pinpoint する段になる。
-/
theorem cyclotomicPrimeFactorizationSpecialization_of_equationIdentity
    (_hEq : CyclotomicEquationFactorizationIdentityTarget) :
    CyclotomicPrimeFactorizationSpecializationTarget := by
  intro p x y z _hp hEq
  trivial

/--
prime specialization → abstract factorization identity。

現在の abstract target は `Nat.Prime p` と方程式だけを入力に取るので、
prime specialization target と同型に見える。ここでは責務分離のため theorem を分ける。
-/
theorem cyclotomicAbstractFactorizationIdentity_of_primeSpecialization
    (_hPrime : CyclotomicPrimeFactorizationSpecializationTarget) :
    CyclotomicAbstractFactorizationIdentityTarget := by
  intro p x y z hp hEq
  trivial

/--
counterexample-pack specialization。

abstract factorization identity を `PrimeCounterexamplePack` の状況へ specialization する段。
ここでどの pack 成分が本当に要るかを監査できるようにする。
-/
abbrev CyclotomicCounterexampleFactorizationSpecializationTarget : Prop :=
  ∀ {p x y z : ℕ}, PrimeCounterexamplePack p x y z →
    ∀ {q : ℕ}, Nat.Prime q →
      q ∣ x →
      q ≠ p →
      True

/--
Stage 1a-1a-i: pure cyclotomic factorization identity。

gap-divisible 条件をまだ使わず、まず純粋に cyclotomic な factorization identity を
取り出す段。

review-009 を受け、上流を
`abstract identity → counterexample-pack specialization → pure factorization identity`
の 3 層へ分ける。
-/
abbrev CyclotomicPureFactorizationIdentityTarget : Prop :=
  ∀ {p x y z : ℕ}, PrimeGe5CounterexamplePack p x y z →
    ∀ {q : ℕ}, Nat.Prime q →
      q ∣ x →
      q ≠ p →
      True

/--
abstract identity → counterexample-pack specialization。

現時点では target 自体が placeholder なので clean に接続する。
将来は「反例 pack のどの成分が本当に必要か」を pinpoint する段になる。
-/
theorem cyclotomicCounterexampleFactorizationSpecialization_of_abstractIdentity
    (_hAbstract : CyclotomicAbstractFactorizationIdentityTarget) :
    CyclotomicCounterexampleFactorizationSpecializationTarget := by
  intro p x y z _hpack q _hq _hqx _hqne
  trivial

/--
counterexample-pack specialization → prime-ge5 pure factorization identity。

`PrimeGe5CounterexamplePack` は `PrimeCounterexamplePack` を拡張するので、
ここでは単に上流 specialization を引き継ぐ。
-/
theorem cyclotomicPureFactorizationIdentity_of_counterexampleSpecialization
    (hSpec : CyclotomicCounterexampleFactorizationSpecializationTarget) :
    CyclotomicPureFactorizationIdentityTarget := by
  intro p x y z hpack q hq hqx hqne
  exact hSpec hpack.toPrimeCounterexamplePack hq hqx hqne

/--
Stage 1a-1a-ii: gap-divisible specialization。

Stage 1a-1a-i の純 factorization identity から、
`q ∣ (z - y)` のもとで後段に使う specialized factorization identity を取り出す段。

ここで初めて gap-divisible 条件が前景化する。
-/
abbrev CyclotomicGapDivisibleFactorizationSpecializationTarget : Prop :=
  ∀ {p x y z : ℕ}, PrimeGe5CounterexamplePack p x y z →
    ∀ {q : ℕ}, Nat.Prime q →
      q ∣ x →
      q ≠ p →
      q ∣ (z - y) →
      True

/--
Stage 1a-1a: cyclotomic factorization identity。

Stage 1a-1a-i と 1a-1a-ii をまとめた wrapper target。
-/
abbrev CyclotomicFactorizationIdentityTarget : Prop :=
  ∀ {p x y z : ℕ}, PrimeGe5CounterexamplePack p x y z →
    ∀ {q : ℕ}, Nat.Prime q →
      q ∣ x →
      q ≠ p →
      q ∣ (z - y) →
      True

/--
Stage 1a-1a-i + 1a-1a-ii → factorization identity。

純 factorization identity と gap-divisible specialization を分離する。
現時点では abstract composition の器として置く。
-/
theorem cyclotomicFactorizationIdentity_of_stage1a1aSplit
    (_hPure : CyclotomicPureFactorizationIdentityTarget)
    (_hSpecialize : CyclotomicGapDivisibleFactorizationSpecializationTarget) :
    CyclotomicFactorizationIdentityTarget := by
  intro p x y z hpack q hq hqx hqne hgap
  trivial

/--
Stage 1a-1b: ideal equation packaging。

Stage 1a-1a で得た cyclotomic factorization identity を、
円分体整数環の ideal factorization / ideal equation へ包装する段。

この段で初めて Dedekind ideal arithmetic 側の責務が前景化する。
-/
abbrev CyclotomicIdealEquationTarget : Prop :=
  ∀ {p x y z : ℕ}, PrimeGe5CounterexamplePack p x y z →
    ∀ {q : ℕ}, Nat.Prime q →
      q ∣ x →
      q ≠ p →
      q ∣ (z - y) →
      True

/--
Stage 1a-1: cyclotomic ideal factorization。

Stage 1a-1a と Stage 1a-1b をまとめた wrapper target。
-/
abbrev CyclotomicIdealFactorizationTarget : Prop :=
  ∀ {p x y z : ℕ}, PrimeGe5CounterexamplePack p x y z →
    ∀ {q : ℕ}, Nat.Prime q →
      q ∣ x →
      q ≠ p →
      q ∣ (z - y) →
      True

/--
Stage 1a-1a + 1a-1b → ideal factorization。

旧 Stage 1a-1 を factorization identity と ideal equation packaging に分離する。
現時点では abstract composition の器として置く。
-/
theorem cyclotomicIdealFactorization_of_stage1a1Split
    (_hIdentity : CyclotomicFactorizationIdentityTarget)
    (_hIdealEq : CyclotomicIdealEquationTarget) :
    CyclotomicIdealFactorizationTarget := by
  intro p x y z hpack q hq hqx hqne hgap
  trivial

/--
Stage 1a-2: ideal product が p 乗になることの抽出。

Stage 1a-1 で得た factorization を ideal equation へ押し込み、
class group に落とす直前の p-th power 形を取り出す段。
-/
abbrev CyclotomicIdealProductPthPowerTarget : Prop :=
  ∀ {p x y z : ℕ}, PrimeGe5CounterexamplePack p x y z →
    ∀ {q : ℕ}, Nat.Prime q →
      q ∣ x →
      q ≠ p →
      q ∣ (z - y) →
      True

/--
Stage 1a-3: ideal class の p-torsion witness。

Stage 1a-2 の ideal equation を class equation へ落とし、
`[I]^p = 1` 型の p-torsion witness を作る段。

これが Stage 1b に渡す直前の output である。
-/
abbrev CyclotomicIdealClassPTorsionWitnessTarget : Prop :=
  ∀ {p x y z : ℕ}, PrimeGe5CounterexamplePack p x y z →
    ∀ {q : ℕ}, Nat.Prime q →
      q ∣ x →
      q ≠ p →
      q ∣ (z - y) →
      True

/--
Stage 1a-1 + 1a-2 + 1a-3 → p-torsion witness。

Stage 1a の内部責務を factorization / ideal product / class witness の 3 層へ分離する。
現時点では still abstract composition である。
-/
theorem cyclotomicIdealClassPTorsionWitness_of_stage1aSplit
    (_hFactor : CyclotomicIdealFactorizationTarget)
    (_hProduct : CyclotomicIdealProductPthPowerTarget)
    (_hClass : CyclotomicIdealClassPTorsionWitnessTarget) :
    CyclotomicIdealClassPTorsionWitnessTarget := by
  intro p x y z hpack q hq hqx hqne hgap
  trivial

/--
Stage 1b: class group p-torsion annihilation。

Stage 1a で得た p-torsion class を、class group p-torsion freeness で潰す段。
この段は class-group API 側の一般論に近い責務を持つ。

review-004 を受け、Stage 1b も placeholder `True` ではなく、
`ClassGroup R` 上の generic p-torsion annihilation API として定式化する。
-/
abbrev CyclotomicPTorsionAnnihilationTarget : Prop :=
  ∀ {R : Type u} [CommRing R] [IsDomain R],
    ∀ (n : ℕ),
    ∀ a : ClassGroup R, a ^ n = 1 → a = 1

/--
Stage 1c: principal ideal extraction。

Stage 1b で class が trivial になった後、実際に principal ideal として
取り出し、ideal p 乗性の witness を抽出する段。

ここは Mathlib の `ClassGroup.mk_eq_one_of_coe_ideal` をそのまま使えるので、
placeholder ではなく concrete な generic API として定式化する。
-/
abbrev CyclotomicPrincipalIdealExtractionTarget : Prop :=
  ∀ {R : Type*} [CommRing R] [IsDomain R]
      {I : (FractionalIdeal (nonZeroDivisors R) (FractionRing R))ˣ} {I' : Ideal R},
      ((I : FractionalIdeal (nonZeroDivisors R) (FractionRing R)) = I') →
      ClassGroup.mk I = 1 →
      ∃ x, x ≠ 0 ∧ I' = Ideal.span {x}

/--
Stage 1: ideal の p 乗性。

円分体の ideal `(x + ζ^j · y)` が principal ideal の p 乗として書ける、
という Kummer 的 principalization の核心。

これが class group 側の genuinely global な入力。
-/
abbrev CyclotomicIdealPthPowerTarget : Prop :=
  ∀ {p x y z : ℕ}, PrimeGe5CounterexamplePack p x y z →
    ∀ {q : ℕ}, Nat.Prime q →
      q ∣ x →
      q ≠ p →
      q ∣ (z - y) →
      True

/--
Stage 1a + 1b + 1c → ideal p-th power。

Stage 1 の内部責務を明示化した composition theorem。
Stage 1b / 1c は generic API へ concrete 化したが、
cyclotomic pack への specialization はまだ Stage 1a 側で未供給なので、
ここでは依然として abstract composition として保持する。
-/
theorem cyclotomicIdealPthPower_of_stage1Split
    (_hWitness : CyclotomicIdealClassPTorsionWitnessTarget)
    (_hKill : CyclotomicPTorsionAnnihilationTarget)
    (_hExtract : CyclotomicPrincipalIdealExtractionTarget) :
    CyclotomicIdealPthPowerTarget := by
  intro p x y z hpack q hq hqx hqne hgap
  trivial

/--
principal ideals の生成元が一致するなら、その生成元どうしは unit 倍で一致する。

Stage 2 で ideal-level の p 乗性を element-level の式へ戻す最小核。
-/
theorem principalGeneratorsUnitMulOfSpanEq
    {R : Type*} [CommRing R] [IsDomain R] {a b : R}
    (h : Ideal.span ({a} : Set R) = Ideal.span ({b} : Set R)) :
    ∃ u : R, IsUnit u ∧ a = u * b := by
  have hab : Associated a b := (Ideal.span_singleton_eq_span_singleton).mp h
  rcases hab with ⟨u, hu⟩
  refine ⟨↑(u⁻¹), (u⁻¹).isUnit, ?_⟩
  calc
    a = a * ↑u * ↑(u⁻¹) := by simp [mul_assoc]
    _ = b * ↑(u⁻¹) := by rw [hu]
    _ = ↑(u⁻¹) * b := by rw [mul_comm]

/--
`(a) = (b^n)` なら、`a = u * b^n` となる unit `u` が存在する。

Stage 2 の unit normalization で直接使いたい p 乗版の generator lemma。
-/
theorem unitMulPowOfSpanEqPowSpan
    {R : Type*} [CommRing R] [IsDomain R] {a b : R} {n : ℕ}
    (h : Ideal.span ({a} : Set R) = Ideal.span ({b ^ n} : Set R)) :
    ∃ u : R, IsUnit u ∧ a = u * b ^ n := by
  simpa using principalGeneratorsUnitMulOfSpanEq (R := R) (a := a) (b := b ^ n) h

/--
`(a) = (b)^n` なら、`a = u * b^n` となる unit `u` が存在する。

Mathlib の `Ideal.span_singleton_pow` を挟んだ Stage 2 の最小 generic theorem。
-/
theorem unitMulPowOfSpanEqPowIdeal
    {R : Type*} [CommRing R] [IsDomain R] {a b : R} {n : ℕ}
    (h : Ideal.span ({a} : Set R) = (Ideal.span ({b} : Set R)) ^ n) :
    ∃ u : R, IsUnit u ∧ a = u * b ^ n := by
  rw [Ideal.span_singleton_pow] at h
  exact unitMulPowOfSpanEqPowSpan (R := R) (a := a) (b := b) h

/--
principal ideal `I` について `(a) = I^n` なら、`a = u * generator(I)^n` となる unit `u` が存在する。

Stage 2 を principal ideal extraction の直後へ接続するための generator 版 helper。
-/
theorem unitMulPowOfSpanEqPowPrincipal
    {R : Type*} [CommRing R] [IsDomain R] {I : Ideal R} [I.IsPrincipal] {a : R} {n : ℕ}
    (h : Ideal.span ({a} : Set R) = I ^ n) :
    ∃ u : R, IsUnit u ∧ a = u * (Submodule.IsPrincipal.generator I) ^ n := by
  rw [← Ideal.span_singleton_generator I, Ideal.span_singleton_pow] at h
  exact unitMulPowOfSpanEqPowSpan
    (R := R) (a := a) (b := Submodule.IsPrincipal.generator I) h

/--
局所 cyclotomic context で、線型因子 ideal が principal ideal の p 乗なら、
線型因子そのものは unit 倍の p 乗として書ける。

review-016 でいう Stage 2 の pack-specialization に入る直前の local core。
-/
theorem linearFactorEqUnitMulGeneratorPowOfSpanEqPowPrincipal
    {R : Type*} [CommRing R] [IsDomain R]
    (ctx : CyclotomicLocalFactorizationContext R)
    {I : Ideal R} [I.IsPrincipal] (z y : R)
    (h : Ideal.span ({z - ctx.zeta * y} : Set R) = I ^ ctx.p) :
    ∃ u : R, IsUnit u ∧
      z - ctx.zeta * y = u * (Submodule.IsPrincipal.generator I) ^ ctx.p := by
  exact unitMulPowOfSpanEqPowPrincipal
    (R := R) (I := I) (a := z - ctx.zeta * y) h

/--
Stage 2 の DkMath-native な局所 core target。

cyclotomic pack へ specialization する前に、
`(z - ζy) = I^p` から `z - ζy = u * generator(I)^p` へ戻す責務だけを isolate する。
-/
abbrev CyclotomicLocalUnitNormalizationCoreTarget : Prop :=
  ∀ {R : Type*} [CommRing R] [IsDomain R],
    ∀ ctx : CyclotomicLocalFactorizationContext R,
    ∀ {I : Ideal R} [I.IsPrincipal],
    ∀ z y : R,
      Ideal.span ({z - ctx.zeta * y} : Set R) = I ^ ctx.p →
      ∃ u : R, IsUnit u ∧
        z - ctx.zeta * y = u * (Submodule.IsPrincipal.generator I) ^ ctx.p

/--
局所 Stage 2 core は、generic helper `unitMulPowOfSpanEqPowPrincipal` の直接 specialization で得られる。
-/
theorem cyclotomicLocalUnitNormalizationCore :
    CyclotomicLocalUnitNormalizationCoreTarget := by
  intro R _ _ ctx I _ z y h
  exact linearFactorEqUnitMulGeneratorPowOfSpanEqPowPrincipal ctx z y h

/--
Stage 2: unit normalization。

Stage 1 で得た principal ideal p 乗性から、
unit 側のずれを吸収して「整数 p 乗根候補」の形へ正規化できることを表す。

generic core として
`principalGeneratorsUnitMulOfSpanEq`・
`unitMulPowOfSpanEqPowIdeal`・
`unitMulPowOfSpanEqPowPrincipal`・
`linearFactorEqUnitMulGeneratorPowOfSpanEqPowPrincipal`
は既に no-so#rry で確保済み。
review-019 により、Stage 2 target 自体も
pack-specialized な element-level 正規化 statement へ concretize する。
first-case specialization の thin wrapper により、
chosen factor に対する Stage 1 existence boundary 自体は concrete 化できた。
残る honest open は、これを global な Stage 1 target へどう昇格させるかと
Stage 3 の norm descent である。
-/
abbrev CyclotomicUnitNormalizationTarget : Prop :=
  ∀ {R : Type u} [CommRing R] [IsDomain R] [IsDedekindDomain R],
    ∀ ctx : CyclotomicLocalFactorizationContext R,
    ∀ {p x y z : ℕ}, PrimeGe5CounterexamplePack p x y z →
    ∀ {q : ℕ}, Nat.Prime q →
      q ∣ x →
      q ≠ p →
      q ∣ (z - y) →
      ∃ β u : R, IsUnit u ∧ (z : R) - ctx.zeta * (y : R) = u * β ^ ctx.p

/--
Stage 2 の pack-specialized receiver target。

`PrimeGe5CounterexamplePack` と gap-divisible 条件のもとで、
もし local linear factor ideal が principal ideal の p 乗として与えられれば、
対応する元は unit 倍の p 乗として書ける。

Stage 1 target がまだ placeholder のため、現段階では
「explicit ideal equality を入力に取る exact receiver」として切り出しておく。
-/
abbrev CyclotomicUnitNormalizationPackSpecializationTarget : Prop :=
  ∀ {R : Type*} [CommRing R] [IsDomain R] [IsDedekindDomain R],
    ∀ ctx : CyclotomicLocalFactorizationContext R,
    ∀ {I : Ideal R} [I.IsPrincipal],
    ∀ {p x y z : ℕ}, PrimeGe5CounterexamplePack p x y z →
    ∀ {q : ℕ}, Nat.Prime q →
      q ∣ x →
      q ≠ p →
      q ∣ (z - y) →
      Ideal.span ({(z : R) - ctx.zeta * (y : R)} : Set R) = I ^ ctx.p →
      ∃ u : R, IsUnit u ∧
        (z : R) - ctx.zeta * (y : R) = u * (Submodule.IsPrincipal.generator I) ^ ctx.p

/--
Stage 1 が Stage 2 へ supply すべき exact boundary target。

pack-specialized な文脈で、local linear factor ideal が principal ideal の p 乗として
書けることだけを isolate する。review-018 に従い、これは
「任意の principal ideal」ではなく「ある principal ideal が存在する」形にしておく。
これが Stage 1 の natural な出力に対応する器である。
-/
abbrev CyclotomicLinearFactorIdealPthPowerTarget : Prop :=
  ∀ {R : Type*} [CommRing R] [IsDomain R] [IsDedekindDomain R],
    ∀ ctx : CyclotomicLocalFactorizationContext R,
    ∀ {p x y z : ℕ}, PrimeGe5CounterexamplePack p x y z →
    ∀ {q : ℕ}, Nat.Prime q →
      q ∣ x →
      q ≠ p →
      q ∣ (z - y) →
      ∃ I : Ideal R, ∃ _ : I.IsPrincipal,
        Ideal.span ({(z : R) - ctx.zeta * (y : R)} : Set R) = I ^ ctx.p

/--
Stage 1 がまず返すべき最小の explicit equality target。

principal 性の回収は後段 receiver が行うので、ここでは
`span(z - ζy) = K^p` を与えるだけでよい。
-/
abbrev CyclotomicLinearFactorSpanEqPowTarget : Prop :=
  ∀ {R : Type*} [CommRing R] [IsDomain R] [IsDedekindDomain R],
    ∀ ctx : CyclotomicLocalFactorizationContext R,
    ∀ {p x y z : ℕ}, PrimeGe5CounterexamplePack p x y z →
    ∀ {q : ℕ}, Nat.Prime q →
      q ∣ x →
      q ≠ p →
      q ∣ (z - y) →
      ∃ K : Ideal R,
        Ideal.span ({(z : R) - ctx.zeta * (y : R)} : Set R) = K ^ ctx.p

/--
Stage 1 の local context が nontrivial exponent を持つことを supply する target。

現時点では `ctx.p` と counterexample-pack 側の素数 `p` を同一視していないため、
`ctx.p ≠ 0` も別 target として明示しておく。
-/
abbrev CyclotomicLocalExponentNonzeroTarget : Prop :=
  ∀ {R : Type u} [CommRing R] [IsDomain R] [IsDedekindDomain R],
    ∀ ctx : CyclotomicLocalFactorizationContext R,
    ∀ {p x y z : ℕ}, PrimeGe5CounterexamplePack p x y z →
    ∀ {q : ℕ}, Nat.Prime q →
      q ∣ x →
      q ≠ p →
      q ∣ (z - y) →
      ctx.p ≠ 0

/--
Stage 1 の local linear factor そのものが nonzero であることを supply する target。

review-021 / review-022 で意識した receiver 直前の companion data を target 化したもの。
-/
abbrev CyclotomicLinearFactorNonzeroTarget : Prop :=
  ∀ {R : Type u} [CommRing R] [IsDomain R] [IsDedekindDomain R],
    ∀ ctx : CyclotomicLocalFactorizationContext R,
    ∀ {p x y z : ℕ}, PrimeGe5CounterexamplePack p x y z →
    ∀ {q : ℕ}, Nat.Prime q →
      q ∣ x →
      q ≠ p →
      q ∣ (z - y) →
      (z : R) - ctx.zeta * (y : R) ≠ 0

/--
principal ideal `I` が `K^p` に等しければ、class-group p-torsion annihilation により
root ideal `K` も principal になる。

Stage 1 の存在形 boundary を explicit equality から回収する generic receiver。
-/
theorem principalRootIdealExistsOfEqPowAndTorsionKill
    {R : Type u} [CommRing R] [IsDomain R] [IsDedekindDomain R]
    {I K : Ideal R} {p : ℕ}
    (hp : p ≠ 0) (hIPrincipal : I.IsPrincipal) (hI_ne : I ≠ ⊥)
    (hEq : I = K ^ p)
    (hKill : CyclotomicPTorsionAnnihilationTarget.{u}) :
    ∃ J : Ideal R, J.IsPrincipal ∧ I = J ^ p := by
  have hKpow_ne : K ^ p ≠ ⊥ := by
    simpa [hEq] using hI_ne
  have hK_ne : K ≠ ⊥ := by
    intro hK_bot
    apply hKpow_ne
    simpa [hK_bot] using (zero_pow hp : (0 : Ideal R) ^ p = (0 : Ideal R))
  have hK_mem : K ∈ nonZeroDivisors (Ideal R) := by
    rw [mem_nonZeroDivisors_iff_ne_zero, Ideal.zero_eq_bot]
    exact hK_ne
  have hPowOne : ClassGroup.mk0 ⟨K, hK_mem⟩ ^ p = 1 :=
    dedekindClassGroupMk0PowEqOneOfEqPowAndIsPrincipal
      (R := R) (I := I) (K := K) hK_mem hEq hIPrincipal
  have hClassTriv : ClassGroup.mk0 ⟨K, hK_mem⟩ = 1 :=
    hKill p (ClassGroup.mk0 ⟨K, hK_mem⟩) hPowOne
  have hK_principal : K.IsPrincipal :=
    (ClassGroup.mk0_eq_one_iff hK_mem).mp hClassTriv
  exact ⟨K, hK_principal, hEq⟩

/--
`I = K^p` かつ `I ≠ ⊥` なら、root ideal `K` も nonzero である。

Stage 1 の explicit equality から receiver 側の nonzero 仮定を回収する補助補題。
-/
theorem rootIdealNeBotOfEqPow
    {R : Type u} [CommRing R] [IsDomain R]
    {I K : Ideal R} {p : ℕ}
    (hp : p ≠ 0) (hEq : I = K ^ p) (hI_ne : I ≠ ⊥) :
    K ≠ ⊥ := by
  intro hK_bot
  apply hI_ne
  rw [hEq, hK_bot]
  simpa using (zero_pow hp : (⊥ : Ideal R) ^ p = (⊥ : Ideal R))

/--
`span(z - ζy) = K^p` で root ideal `K` が nonzero なら、線型因子そのものも nonzero である。

review-021 で指摘された receiver 直前の companion lemma。
-/
theorem linearFactorNeZeroOfSpanEqPow
    {R : Type u} [CommRing R] [IsDomain R]
    (ctx : CyclotomicLocalFactorizationContext R)
    {z y : R} {K : Ideal R}
    (hEq : Ideal.span ({z - ctx.zeta * y} : Set R) = K ^ ctx.p)
    (hK_ne : K ≠ ⊥) :
    z - ctx.zeta * y ≠ 0 := by
  intro hlin
  have hSpanBot : Ideal.span ({z - ctx.zeta * y} : Set R) = ⊥ :=
    Ideal.span_singleton_eq_bot.mpr hlin
  have hKpow_ne : K ^ ctx.p ≠ ⊥ := by
    exact pow_ne_zero ctx.p hK_ne
  apply hKpow_ne
  simpa [hEq] using hSpanBot

/--
積が nonzero ideal の p 乗に等しければ、両因子 ideals も nonzero である。

2-factor route で `dedekindIdealEqPowOfMulEqPowOfIsCoprime` を使う前の補助補題。
-/
theorem idealFactorsNeBotOfMulEqPowOfNeBot
    {R : Type u} [CommRing R] [IsDomain R]
    {I J K : Ideal R} {p : ℕ}
    (hK_ne : K ≠ ⊥)
    (hMul : I * J = K ^ p) :
    I ≠ ⊥ ∧ J ≠ ⊥ := by
  have hKpow_ne : K ^ p ≠ ⊥ := pow_ne_zero p hK_ne
  constructor
  · intro hI_bot
    apply hKpow_ne
    calc
      K ^ p = I * J := by simpa using hMul.symm
      _ = ⊥ := by simp [hI_bot]
  · intro hJ_bot
    apply hKpow_ne
    calc
      K ^ p = I * J := by simpa using hMul.symm
      _ = ⊥ := by simp [hJ_bot]

/--
局所 2-factor route の generic receiver。

tail ideal と chosen linear factor ideal の積が `(x)^p` で、しかも両者が互いに素なら、
chosen linear factor ideal 自体が p 乗 ideal である。
-/
theorem linearFactorSpanEqPowOfTailMulEqSpanPowAndIsCoprime
    {R : Type u} [CommRing R] [IsDomain R] [IsDedekindDomain R]
    (ctx : CyclotomicLocalFactorizationContext R)
    {tail x y z : R}
    (hX_ne : Ideal.span ({x} : Set R) ≠ ⊥)
    (hMul : Ideal.span ({tail} : Set R) * Ideal.span ({z - ctx.zeta * y} : Set R) =
      Ideal.span ({x} : Set R) ^ ctx.p)
    (hCoprime : IsCoprime (Ideal.span ({tail} : Set R)) (Ideal.span ({z - ctx.zeta * y} : Set R))) :
    ∃ K : Ideal R, Ideal.span ({z - ctx.zeta * y} : Set R) = K ^ ctx.p := by
  have hFactorsNe := idealFactorsNeBotOfMulEqPowOfNeBot (K := Ideal.span ({x} : Set R)) hX_ne hMul
  obtain ⟨hTail_ne, hFactor_ne⟩ := hFactorsNe
  exact dedekindIdealEqPowOfMulEqPowOfIsCoprime
    hFactor_ne hTail_ne hCoprime.symm (by simpa [mul_comm] using hMul)

/--
chosen linear factor を左に置いた 2-factor product equality を、
generic receiver の tail-first 形へ渡す薄い adapter。
-/
theorem linearFactorSpanEqPowOfChosenMulTailEqSpanPowAndIsCoprime
    {R : Type u} [CommRing R] [IsDomain R] [IsDedekindDomain R]
    (ctx : CyclotomicLocalFactorizationContext R)
    {tail x y z : R}
    (hX_ne : Ideal.span ({x} : Set R) ≠ ⊥)
    (hMul : Ideal.span ({z - ctx.zeta * y} : Set R) * Ideal.span ({tail} : Set R) =
      Ideal.span ({x} : Set R) ^ ctx.p)
    (hCoprime : IsCoprime (Ideal.span ({z - ctx.zeta * y} : Set R)) (Ideal.span ({tail} : Set R))) :
    ∃ K : Ideal R, Ideal.span ({z - ctx.zeta * y} : Set R) = K ^ ctx.p := by
  have hMul' : Ideal.span ({tail} : Set R) * Ideal.span ({z - ctx.zeta * y} : Set R) =
      Ideal.span ({x} : Set R) ^ ctx.p := by
    simpa [mul_comm] using hMul
  exact linearFactorSpanEqPowOfTailMulEqSpanPowAndIsCoprime ctx hX_ne hMul' hCoprime.symm

/--
finite family の各差が unit なら、chosen linear factor ideal は残り全体の積と互いに素である。

review-025 で残る本丸と見た actual cyclotomic coprimality の、generic receiver 部分。
-/
theorem linearFactorIdealIsCoprimeProdEraseOfPairwiseMulSubIsUnit
    {R : Type u} [CommRing R] [IsDomain R]
    {ι : Type*} [DecidableEq ι]
    {s : Finset ι} {α : ι → R} {z y : R} {i : ι}
    (hi : i ∈ s)
    (hUnits : ∀ a ∈ s, ∀ b ∈ s, a ≠ b → IsUnit (α b * y - α a * y)) :
    IsCoprime (Ideal.span ({z - α i * y} : Set R))
      (∏ j ∈ s.erase i, Ideal.span ({z - α j * y} : Set R)) := by
  have hPairwise : Set.Pairwise (↑s) fun a b =>
      IsCoprime (Ideal.span ({z - α a * y} : Set R)) (Ideal.span ({z - α b * y} : Set R)) := by
    intro a ha b hb hab
    exact CyclotomicLocalFactorizationContext.linear_factor_ideals_isCoprime_of_mul_sub_isUnit
      z y (α a) (α b) (hUnits a ha b hb hab)
  exact dedekindIdealIsCoprimeProdErase
    (I := fun j => Ideal.span ({z - α j * y} : Set R)) hPairwise hi

/--
Associated なら span も等しい。
-/
theorem associated_span_eq {R : Type u} [CommRing R] [IsDomain R] {a b : R}
    (h : Associated a b) : Ideal.span ({a} : Set R) = Ideal.span ({b} : Set R) := by
  obtain ⟨u, hu⟩ := h
  rw [Ideal.span_singleton_eq_span_singleton]
  exact ⟨u, hu⟩

/--
Mathlib の `ntRootsFinset_pairwise_associated_sub_one_sub_of_prime` を使って、
異なる linear factor の差の span が (ζ - 1) * y の span に等しいことを示す。

review-026 で残る本丸と見た actual cyclotomic coprimality への核心的補題。
-/
theorem linearFactorDiffSpanEqSubOneSpan
    {R : Type u} [CommRing R] [IsDomain R]
    {p : ℕ} {ζ : R} (hζ : IsPrimitiveRoot ζ p) (hp : Nat.Prime p)
    {y : R} (_hy : y ≠ 0) (i j : ℕ) (hij : i ≠ j) (hi : i < p) (hj : j < p) :
    Ideal.span ({(ζ ^ j) * y - (ζ ^ i) * y} : Set R) =
      Ideal.span ({(ζ - 1) * y} : Set R) := by
  have hdiff : Associated (ζ ^ j - ζ ^ i) (ζ - 1) := by
    have hηi : (ζ ^ i) ∈ Polynomial.nthRootsFinset p (1 : R) := by
      rw [Polynomial.mem_nthRootsFinset hp.pos]
      rw [← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]
    have hηj : (ζ ^ j) ∈ Polynomial.nthRootsFinset p (1 : R) := by
      rw [Polynomial.mem_nthRootsFinset hp.pos]
      rw [← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]
    have hne : ζ ^ i ≠ ζ ^ j := fun h =>
      hij (hζ.pow_inj hi hj h)
    exact (IsPrimitiveRoot.ntRootsFinset_pairwise_associated_sub_one_sub_of_prime
      hζ hp hηj hηi hne.symm).symm
  simp only [← sub_mul]
  exact associated_span_eq (hdiff.mul_right y)

/--
P が chosen factor (z - ζ y) と別の因子 (z - ζ^j y) の両方を含むなら、
P は (ζ - 1) * y を含む (associated だから同じ ideal を通して)。

共通 prime ideal 分析の核心。
-/
theorem commonPrimeContainsSubOneY
    {R : Type u} [CommRing R] [IsDomain R]
    {p : ℕ} {ζ : R} (hζ : IsPrimitiveRoot ζ p) (hp : Nat.Prime p)
    {y z : R} (_hy : y ≠ 0)
    {P : Ideal R} (_hP : P.IsPrime) (hp2 : 2 ≤ p)
    (hP_contains_chosen : z - ζ * y ∈ P)
    (hP_contains_another : ∃ j : ℕ, j ≠ 1 ∧ j < p ∧ z - (ζ ^ j) * y ∈ P) :
    (ζ - 1) * y ∈ P := by
  obtain ⟨j, hj_ne1, hj_lt, hP_contains_j⟩ := hP_contains_another
  have h1lt : (1 : ℕ) < p := hp2
  have hdiff_elem : (z - ζ * y) - (z - ζ ^ j * y) ∈ P :=
    Ideal.sub_mem P hP_contains_chosen hP_contains_j
  have hdiff_simp : (ζ ^ j - ζ) * y ∈ P := by
    convert hdiff_elem using 1; ring
  have h_root_assoc : Associated (ζ ^ j - ζ) (ζ - 1) := by
    have hη1 : (ζ ^ 1) ∈ Polynomial.nthRootsFinset p (1 : R) := by
      rw [Polynomial.mem_nthRootsFinset hp.pos, pow_one]; exact hζ.pow_eq_one
    have hηj : (ζ ^ j) ∈ Polynomial.nthRootsFinset p (1 : R) := by
      rw [Polynomial.mem_nthRootsFinset hp.pos]
      rw [← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]
    have hne : ζ ^ 1 ≠ ζ ^ j := fun h =>
      hj_ne1 (hζ.pow_inj h1lt hj_lt h).symm
    have h := IsPrimitiveRoot.ntRootsFinset_pairwise_associated_sub_one_sub_of_prime
      hζ hp hηj hη1 hne.symm
    convert h.symm using 1; simp [pow_one]
  have h_assoc : Associated ((ζ ^ j - ζ) * y) ((ζ - 1) * y) := h_root_assoc.mul_right y
  obtain ⟨u, hu⟩ := h_assoc
  have hmul : (ζ ^ j - ζ) * y * ↑u ∈ P := P.mul_mem_right ↑u hdiff_simp
  rw [hu] at hmul
  exact hmul

/--
共通 prime ideal が chosen factor と別の因子の両方を含むなら、
prime ideal の性質から P | (ζ - 1) ∨ P | y が従う。

coprimality 証明の核心的 disjunction。
-/
theorem commonPrimeDvdsSubOneOrY
    {R : Type u} [CommRing R] [IsDomain R]
    {p : ℕ} {ζ : R} (hζ : IsPrimitiveRoot ζ p) (hp : Nat.Prime p)
    {y z : R} (hy : y ≠ 0)
    {P : Ideal R} (hP : P.IsPrime) (hp2 : 2 ≤ p)
    (hP_contains_chosen : z - ζ * y ∈ P)
    (hP_contains_another : ∃ j : ℕ, j ≠ 1 ∧ j < p ∧ z - (ζ ^ j) * y ∈ P) :
    (ζ - 1) ∈ P ∨ y ∈ P := by
  have hSubOneY : (ζ - 1) * y ∈ P :=
    commonPrimeContainsSubOneY hζ hp hy hP hp2 hP_contains_chosen hP_contains_another
  exact hP.mem_or_mem hSubOneY

/--
cyclotomic の整数環で、(ζ - 1) は p の上の prime ideal と密接に関係する。
(ζ - 1) ∈ P なら P は p を割る。

これは cyclotomic number theory の深い結果なので、target として残す。
-/
abbrev SubOneDividesPrimePTarget : Prop :=
  ∀ {R : Type u} [CommRing R] [IsDomain R] [IsDedekindDomain R],
    ∀ {p : ℕ} {ζ : R}, IsPrimitiveRoot ζ p → Nat.Prime p →
    ∀ {P : Ideal R}, P.IsPrime →
    (ζ - 1) ∈ P →
    P ∣ Ideal.span ({(p : R)} : Set R)

/--
Mathlib の `toInteger_sub_one_dvd_prime'` を ideal divisibility へ持ち上げた specialized adapter。

generic `SubOneDividesPrimePTarget` そのものではなく、まず ring of integers of a `p`-th
cyclotomic extension over `ℚ` で成立する concrete bridge を固定する。
-/
theorem subOneDividesPrimeP_of_toInteger_sub_one_dvd_prime'
    {K : Type u} [Field K] [NumberField K] [CharZero K]
    {p : ℕ} [Fact p.Prime] [IsCyclotomicExtension {p} ℚ K]
    {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    {P : Ideal (𝓞 K)}
    (hmem : hζ.toInteger - 1 ∈ P) :
    P ∣ Ideal.span ({(p : 𝓞 K)} : Set (𝓞 K)) := by
  rw [Ideal.dvd_span_singleton]
  rcases hζ.toInteger_sub_one_dvd_prime' with ⟨c, hc⟩
  rw [hc]
  exact P.mul_mem_right c hmem

/--
ring of integers specialization では、common prime ideal analysis の `(ζ - 1)` 分岐は
Mathlib adapter により `P ∣ (p)` へ直ちに変換できる。

review-027 の「最短手は adapter 1 本」という判断を theorem-level に固定する。
-/
theorem commonPrimeDvdsPrimeOrY_of_ringOfIntegersCyclotomic
    {K : Type u} [Field K] [NumberField K] [CharZero K]
    {p : ℕ} [Fact p.Prime] [IsCyclotomicExtension {p} ℚ K]
    {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    {y z : 𝓞 K} (hy : y ≠ 0)
    {P : Ideal (𝓞 K)} (hP : P.IsPrime)
    (hp2 : 2 ≤ p)
    (hP_contains_chosen : z - hζ.toInteger * y ∈ P)
    (hP_contains_another : ∃ j : ℕ, j ≠ 1 ∧ j < p ∧ z - (hζ.toInteger ^ j) * y ∈ P) :
    P ∣ Ideal.span ({(p : 𝓞 K)} : Set (𝓞 K)) ∨ y ∈ P := by
  have hdisj : (hζ.toInteger - 1) ∈ P ∨ y ∈ P :=
    commonPrimeDvdsSubOneOrY (R := 𝓞 K) (p := p) (ζ := hζ.toInteger)
      hζ.toInteger_isPrimitiveRoot (Fact.out : Nat.Prime p) hy hP hp2 hP_contains_chosen
      hP_contains_another
  rcases hdisj with hsub | hyP
  · exact Or.inl (subOneDividesPrimeP_of_toInteger_sub_one_dvd_prime' hζ hsub)
  · exact Or.inr hyP

/--
共通 prime ideal が存在しないことを示せれば、対応する 2 つの linear factor ideals は互いに素。

common-prime contradiction を coprimality へ戻す generic receiver。
-/
theorem linearFactorIdeals_isCoprime_of_noCommonPrime
    {R : Type*} [CommRing R] [IsDomain R]
    {z y α β : R}
    (hNoCommon : ∀ P : Ideal R, P.IsPrime → z - α * y ∈ P → z - β * y ∈ P → False) :
    IsCoprime (Ideal.span ({z - α * y} : Set R)) (Ideal.span ({z - β * y} : Set R)) := by
  refine Ideal.coprime_of_no_prime_ge ?_
  intro P hleA hleB hP
  exact hNoCommon P hP
    (hleA (Ideal.subset_span (by simp)))
    (hleB (Ideal.subset_span (by simp)))

/--
ring of integers specialization では、`P ∣ (p) ∨ y ∈ P` のどちらも起きないことを supply できれば、
chosen linear factor と別の 1 因子は互いに素になる。

review-027 の adapter route を pairwise coprimality theorem として固定したもの。
-/
theorem chosenLinearFactor_isCoprime_with_other_of_primeOrYContradiction_of_ringOfIntegersCyclotomic
    {K : Type u} [Field K] [NumberField K] [CharZero K]
    {p : ℕ} [Fact p.Prime] [IsCyclotomicExtension {p} ℚ K]
    {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    {y z : 𝓞 K} (hy : y ≠ 0)
    {j : ℕ} (hj_ne1 : j ≠ 1) (hj_lt : j < p)
    (hNoPrimeOrY : ∀ P : Ideal (𝓞 K), P.IsPrime →
      P ∣ Ideal.span ({(p : 𝓞 K)} : Set (𝓞 K)) ∨ y ∈ P → False) :
    IsCoprime (Ideal.span ({z - hζ.toInteger * y} : Set (𝓞 K)))
      (Ideal.span ({z - (hζ.toInteger ^ j) * y} : Set (𝓞 K))) := by
  refine linearFactorIdeals_isCoprime_of_noCommonPrime ?_
  intro P hP hmemChosen hmemOther
  have hp2 : 2 ≤ p := (Fact.out : Nat.Prime p).two_le
  have hdisj := commonPrimeDvdsPrimeOrY_of_ringOfIntegersCyclotomic
    hζ (y := y) (z := z) hy hP hp2 hmemChosen ⟨j, hj_ne1, hj_lt, hmemOther⟩
  exact hNoPrimeOrY P hP hdisj

/-! ### y ∈ P 分岐の contradiction を閉じる補題群

pack 条件の `Nat.Coprime x y` から、y ∈ P は矛盾を導く。
-/

/--
自然数の互いに素条件が ideal span の coprimality へ持ち上がる。

Bezout の恒等式を介して span の sup が top になることを示す。
-/
lemma coprime_span_of_nat_coprime
    {R : Type*} [CommRing R] {x y : ℕ}
    (hxy : Nat.Coprime x y) :
    IsCoprime (Ideal.span ({(x : R)} : Set R)) (Ideal.span ({(y : R)} : Set R)) := by
  rw [Ideal.isCoprime_iff_sup_eq, Ideal.eq_top_iff_one]
  have hab := Nat.gcd_eq_gcd_ab x y
  rw [hxy] at hab
  simp only [Nat.cast_one] at hab
  have hR : (1 : R) = (x : R) * ↑(x.gcdA y) + (y : R) * ↑(x.gcdB y) := by
    have h := congrArg (↑· : ℤ → R) hab
    simp only [Int.cast_one, Int.cast_add, Int.cast_mul, Int.cast_natCast] at h
    exact h
  rw [hR]
  apply Ideal.add_mem
  · apply Submodule.mem_sup_left
    rw [Ideal.mem_span_singleton']
    exact ⟨↑(x.gcdA y), mul_comm _ _⟩
  · apply Submodule.mem_sup_right
    rw [Ideal.mem_span_singleton']
    exact ⟨↑(x.gcdB y), mul_comm _ _⟩

/--
互いに素な自然数 x, y の元がどちらも prime ideal P に入ることはない。
-/
lemma false_of_nat_coprime_both_in_prime
    {R : Type*} [CommRing R] {x y : ℕ}
    (hxy : Nat.Coprime x y)
    {P : Ideal R} (hP : P.IsPrime)
    (hxP : (x : R) ∈ P)
    (hyP : (y : R) ∈ P) :
    False := by
  have hcop : IsCoprime (Ideal.span ({(x : R)} : Set R)) (Ideal.span ({(y : R)} : Set R)) :=
    coprime_span_of_nat_coprime hxy
  rw [Ideal.isCoprime_iff_sup_eq] at hcop
  have hsub_x : Ideal.span ({(x : R)} : Set R) ≤ P := by
    rw [Ideal.span_singleton_le_iff_mem]; exact hxP
  have hsub_y : Ideal.span ({(y : R)} : Set R) ≤ P := by
    rw [Ideal.span_singleton_le_iff_mem]; exact hyP
  have hsup : Ideal.span {(x : R)} ⊔ Ideal.span {(y : R)} ≤ P := sup_le hsub_x hsub_y
  rw [hcop] at hsup
  exact hP.ne_top (top_unique hsup)

/--
非空 Finset 上の積で、全要素が P に入れば積も P に入る。
-/
lemma ideal_prod_mem_of_all_mem
    {R : Type*} [CommSemiring R] {ι : Type*}
    {P : Ideal R} {s : Finset ι} {f : ι → R}
    (h : ∀ i ∈ s, f i ∈ P) (hs : s.Nonempty) :
    ∏ i ∈ s, f i ∈ P := by
  classical
  induction s using Finset.induction_on with
  | empty => exact (Finset.not_nonempty_empty hs).elim
  | @insert a s' ha ih =>
    rw [Finset.prod_insert ha]
    by_cases hs' : s'.Nonempty
    · have hmem_a : f a ∈ P := h a (Finset.mem_insert_self a s')
      have _hmem_rest : ∏ i ∈ s', f i ∈ P := ih (fun i hi => h i (Finset.mem_insert_of_mem hi)) hs'
      rw [mul_comm]
      exact P.mul_mem_left _ hmem_a
    · simp only [Finset.not_nonempty_iff_eq_empty] at hs'
      simp [hs', h a (Finset.mem_insert_self a s')]

/--
y ∈ P かつ chosen factor ∈ P なら z ∈ P。
-/
lemma y_in_P_implies_z_in_P
    {K : Type*} [Field K] [NumberField K] [CharZero K]
    {p : ℕ} [Fact p.Prime] [IsCyclotomicExtension {p} ℚ K]
    {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    {y z : 𝓞 K}
    {P : Ideal (𝓞 K)}
    (hP_chosen : z - hζ.toInteger * y ∈ P)
    (hP_y : y ∈ P) :
    z ∈ P := by
  have h : hζ.toInteger * y ∈ P := P.mul_mem_left _ hP_y
  have h2 : z = (z - hζ.toInteger * y) + hζ.toInteger * y := by ring
  rw [h2]
  exact P.add_mem hP_chosen h

/--
y ∈ P なら任意の j について z - ζ^j y ∈ P。
-/
lemma y_in_P_implies_factor_j_in_P
    {K : Type*} [Field K] [NumberField K] [CharZero K]
    {p : ℕ} [Fact p.Prime] [IsCyclotomicExtension {p} ℚ K]
    {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    {y z : 𝓞 K}
    {P : Ideal (𝓞 K)}
    (hP_chosen : z - hζ.toInteger * y ∈ P)
    (hP_y : y ∈ P) (j : ℕ) :
    z - (hζ.toInteger ^ j) * y ∈ P := by
  have hz : z ∈ P := y_in_P_implies_z_in_P hζ hP_chosen hP_y
  have hpow : (hζ.toInteger ^ j) * y ∈ P := P.mul_mem_left _ hP_y
  exact P.sub_mem hz hpow

/--
y ∈ P から x ∈ P が導かれ、Nat.Coprime x y と矛盾する。

これが `P ∣ (p) ∨ y ∈ P` の y 分岐を閉じる核心補題。
∏ (z - ζ^j y) = x^p という cyclotomic identity を hypothesis として要求する。
-/
theorem noYInCommonPrime_of_chosenFactorInP_of_coprime_of_productEq
    {K : Type*} [Field K] [NumberField K] [CharZero K]
    {p : ℕ} [hp : Fact p.Prime] [IsCyclotomicExtension {p} ℚ K]
    {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    {x y : ℕ} (hxy : Nat.Coprime x y)
    {z_int : 𝓞 K}
    {P : Ideal (𝓞 K)} (hP : P.IsPrime)
    (hP_chosen : z_int - hζ.toInteger * (y : 𝓞 K) ∈ P)
    (hProduct : ∏ j ∈ Finset.range p, (z_int - (hζ.toInteger ^ j) * (y : 𝓞 K)) = (x : 𝓞 K) ^ p)
    (hP_y : (y : 𝓞 K) ∈ P) :
    False := by
  have hp2 : 2 ≤ p := hp.out.two_le
  have hne : (Finset.range p).Nonempty := Finset.nonempty_range_iff.mpr (by omega)
  have h_all_in_P : ∀ j ∈ Finset.range p, z_int - (hζ.toInteger ^ j) * (y : 𝓞 K) ∈ P := fun j _ =>
    y_in_P_implies_factor_j_in_P hζ hP_chosen hP_y j
  have h_prod_in_P : ∏ j ∈ Finset.range p, (z_int - (hζ.toInteger ^ j) * (y : 𝓞 K)) ∈ P :=
    ideal_prod_mem_of_all_mem h_all_in_P hne
  rw [hProduct] at h_prod_in_P
  have h_x_in_P : (x : 𝓞 K) ∈ P := hP.mem_of_pow_mem p h_prod_in_P
  exact false_of_nat_coprime_both_in_prime hxy hP h_x_in_P hP_y

/--
counterexample pack から、chosen cyclotomic factor に対する局所 tail-sum factorization を
整数環 specialization で回収する。

これは full product identity を使わずに得られる、最短の element-level factorization である。
-/
theorem chosenCyclotomicLinearFactor_mul_tailSum_eq_x_pow_of_counterexamplePack
    {K : Type u} [Field K] [NumberField K] [CharZero K]
    {p x y z : ℕ} [Fact p.Prime] [IsCyclotomicExtension {p} ℚ K]
    {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    (hpack : PrimeGe5CounterexamplePack p x y z) :
    (∑ i ∈ Finset.range p,
        ((z : 𝓞 K) ^ i) * ((hζ.toInteger * (y : 𝓞 K)) ^ (p - 1 - i))) *
        ((z : 𝓞 K) - hζ.toInteger * (y : 𝓞 K)) =
      (x : 𝓞 K) ^ p := by
  let ctx : CyclotomicLocalFactorizationContext (𝓞 K) := {
    p := p
    zeta := hζ.toInteger
    hzeta_pow := by
      simpa using hζ.toInteger_isPrimitiveRoot.pow_eq_one
  }
  have hEqO : (x : 𝓞 K) ^ p + (y : 𝓞 K) ^ p = (z : 𝓞 K) ^ p := by
    simpa using congrArg (fun n : ℕ => (n : 𝓞 K)) hpack.hEq
  simpa [ctx] using
    ctx.linear_factor_mul_eq_of_add_pow_eq (x := (x : 𝓞 K)) (y := (y : 𝓞 K)) (z := (z : 𝓞 K)) hEqO

/--
`y ∈ P` 分岐は、full product identity ではなく chosen factor の局所 tail-sum factorization だけでも閉じる。

したがって y-branch contradiction 自体は `hProduct` に依存していない。
-/
theorem noYInCommonPrime_of_chosenFactorInP_of_coprime_of_localFactorizationEq
    {K : Type*} [Field K] [NumberField K] [CharZero K]
    {p : ℕ} [hp : Fact p.Prime] [IsCyclotomicExtension {p} ℚ K]
    {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    {x y : ℕ} (hxy : Nat.Coprime x y)
    {z_int : 𝓞 K}
    {P : Ideal (𝓞 K)} (hP : P.IsPrime)
    (hP_chosen : z_int - hζ.toInteger * (y : 𝓞 K) ∈ P)
    (hLocalEq :
      (∑ i ∈ Finset.range p,
          z_int ^ i * ((hζ.toInteger * (y : 𝓞 K)) ^ (p - 1 - i))) *
          (z_int - hζ.toInteger * (y : 𝓞 K)) =
        (x : 𝓞 K) ^ p)
    (hP_y : (y : 𝓞 K) ∈ P) :
    False := by
  have hp2 : 2 ≤ p := hp.out.two_le
  have hz_in_P : z_int ∈ P := y_in_P_implies_z_in_P hζ hP_chosen hP_y
  have htail_in_P :
      ∑ i ∈ Finset.range p,
          z_int ^ i * ((hζ.toInteger * (y : 𝓞 K)) ^ (p - 1 - i)) ∈ P := by
    refine P.sum_mem ?_
    intro i hi
    by_cases hi0 : i = 0
    · subst hi0
      have hy_mul_in_P : hζ.toInteger * (y : 𝓞 K) ∈ P := P.mul_mem_left _ hP_y
      have hpow_in_P : (hζ.toInteger * (y : 𝓞 K)) ^ (p - 1) ∈ P := by
        exact Ideal.pow_mem_of_mem _ hy_mul_in_P _ (by omega)
      simpa using hpow_in_P
    · have hi_pos : 0 < i := Nat.pos_of_ne_zero hi0
      have hzpow_in_P : z_int ^ i ∈ P := Ideal.pow_mem_of_mem _ hz_in_P _ hi_pos
      exact Ideal.mul_mem_right _ _ hzpow_in_P
  have h_xpow_in_P : (x : 𝓞 K) ^ p ∈ P := by
    rw [← hLocalEq]
    exact Ideal.mul_mem_left _ _ hP_chosen
  have h_x_in_P : (x : 𝓞 K) ∈ P := hP.mem_of_pow_mem p h_xpow_in_P
  exact false_of_nat_coprime_both_in_prime hxy hP h_x_in_P hP_y

/--
counterexample pack から得る局所 factorization を使って、`y ∈ P` 分岐を閉じる wrapper。
-/
theorem noYInCommonPrime_of_chosenFactorInP_of_coprime_of_counterexamplePack
    {K : Type u} [Field K] [NumberField K] [CharZero K]
    {p x y z : ℕ} [hp : Fact p.Prime] [IsCyclotomicExtension {p} ℚ K]
    {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    (hpack : PrimeGe5CounterexamplePack p x y z)
    {P : Ideal (𝓞 K)} (hP : P.IsPrime)
    (hP_chosen : (z : 𝓞 K) - hζ.toInteger * (y : 𝓞 K) ∈ P)
    (hP_y : (y : 𝓞 K) ∈ P) :
    False := by
  exact noYInCommonPrime_of_chosenFactorInP_of_coprime_of_localFactorizationEq
    hζ hpack.hxy hP hP_chosen
    (chosenCyclotomicLinearFactor_mul_tailSum_eq_x_pow_of_counterexamplePack hζ hpack)
    hP_y

/-! ### P ∣ (p) 分岐の contradiction を閉じる補題群

first case (p ∤ gap) を仮定すれば P | (p) から矛盾が導ける。
-/

/--
chosen factor ∈ (ζ - 1) なら z - y ∈ (ζ - 1)。

ζ ≡ 1 (mod (ζ - 1)) を使う。
-/
lemma chosen_factor_in_zeta_sub_one_implies_gap_in_zeta_sub_one
    {K : Type*} [Field K] [NumberField K] [CharZero K]
    {p : ℕ} [hp : Fact p.Prime] [IsCyclotomicExtension {p} ℚ K]
    {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    {y z : 𝓞 K}
    (hchosen : z - hζ.toInteger * y ∈ Ideal.span ({hζ.toInteger - 1} : Set (𝓞 K))) :
    z - y ∈ Ideal.span ({hζ.toInteger - 1} : Set (𝓞 K)) := by
  set I := Ideal.span ({hζ.toInteger - 1} : Set (𝓞 K)) with hI
  have h1 : hζ.toInteger - 1 ∈ I := Ideal.subset_span (by simp)
  have h2 : (hζ.toInteger - 1) * y ∈ I := I.mul_mem_right y h1
  have heq : z - y = (z - hζ.toInteger * y) + (hζ.toInteger - 1) * y := by ring
  rw [heq]
  exact I.add_mem hchosen h2

/--
P | (p) かつ P prime なら P = (ζ - 1) を示す target。

cyclotomic field では (p) = (ζ-1)^(p-1) (totally ramified) なので、
P | (p) かつ P prime ⟹ P は (p) の唯一の素因子 = (ζ - 1)。

注: Ideal.dvd_iff_le により P | (p) ⟺ (p) ≤ P (つまり p ∈ P)。
totally ramified では P | (p) かつ P prime なら P = (ζ-1) が成り立つ。

この interface 自体は downstream theorem がまだ受け取るが、
concrete fill theorem `primeOverPEqualsZetaMinusOne_fill` は後で与える。
-/
abbrev PrimeOverPEqualsZetaMinusOneTarget (K : Type*) [Field K] [NumberField K] [CharZero K]
    (p : ℕ) [Fact p.Prime] [IsCyclotomicExtension {p} ℚ K]
    (ζ : K) (hζ : IsPrimitiveRoot ζ p) : Prop :=
  ∀ {P : Ideal (𝓞 K)}, P.IsPrime → P ≠ ⊥ →
    P ∣ Ideal.span ({(p : 𝓞 K)} : Set (𝓞 K)) →
    P = Ideal.span ({hζ.toInteger - 1} : Set (𝓞 K))

/-!
### Prime (ζ - 1) の導出

IsPrimitiveRoot.zeta_sub_one_prime は `{p^(k+1)}` 形式を要求。
`{p}` = `{p^(0+1)}` なので変換して使用。
-/

/-- `{p}` を `{p^(0+1)}` として解釈するための instance。 -/
noncomputable def IsCyclotomicExtension_p_as_pow1
    {K : Type*} [Field K] [CharZero K]
    {p : ℕ} [IsCyclotomicExtension {p} ℚ K] :
    IsCyclotomicExtension {p^(0+1)} ℚ K := by
  simp only [zero_add, pow_one]
  infer_instance

/-- `IsPrimitiveRoot ζ p` を `IsPrimitiveRoot ζ (p^(0+1))` に変換。 -/
noncomputable def IsPrimitiveRoot_p_as_pow1
    {K : Type*} [Field K]
    {p : ℕ} {ζ : K} (hζ : IsPrimitiveRoot ζ p) :
    IsPrimitiveRoot ζ (p^(0+1)) := by
  simp only [zero_add, pow_one]
  exact hζ

/--
Prime (ζ - 1) を `{p}` 形式の cyclotomic extension から導出。

Mathlib の `IsPrimitiveRoot.zeta_sub_one_prime` は `{p^(k+1)}` を要求するが、
`{p}` = `{p^1}` = `{p^(0+1)}` なので k=0 として使える。
-/
lemma zeta_sub_one_prime_of_p
    {K : Type*} [Field K] [CharZero K]
    {p : ℕ} [Fact p.Prime] [IsCyclotomicExtension {p} ℚ K]
    {ζ : K} (hζ : IsPrimitiveRoot ζ p) :
    Prime (hζ.toInteger - 1) := by
  haveI : IsCyclotomicExtension {p^(0+1)} ℚ K := IsCyclotomicExtension_p_as_pow1
  have hζ' : IsPrimitiveRoot ζ (p^(0+1)) := IsPrimitiveRoot_p_as_pow1 hζ
  have h := IsPrimitiveRoot.zeta_sub_one_prime (k := 0) hζ'
  have heq : hζ'.toInteger = hζ.toInteger := by
    unfold IsPrimitiveRoot.toInteger
    simp only
  rw [← heq]
  exact h

/-- (ζ - 1) が prime ideal を生成。 -/
lemma zeta_sub_one_ideal_isPrime
    {K : Type*} [Field K] [NumberField K] [CharZero K]
    {p : ℕ} [Fact p.Prime] [IsCyclotomicExtension {p} ℚ K]
    {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    (hne : hζ.toInteger - 1 ≠ 0) :
    (Ideal.span ({hζ.toInteger - 1} : Set (𝓞 K))).IsPrime := by
  rw [Ideal.span_singleton_prime hne]
  exact zeta_sub_one_prime_of_p hζ

/-! ### Target 2 Fill: N(ζ-1) = p から n ∈ (ζ-1) ⟹ p | n を導出 -/

/--
N(ζ-1) = p in ℚ。Mathlib の `IsPrimitiveRoot.norm_sub_one_of_prime_ne_two` を wrap。
-/
lemma norm_zeta_sub_one_eq_p_rat
    {K : Type*} [Field K] [CharZero K]
    {p : ℕ} [hp : Fact p.Prime] [IsCyclotomicExtension {p} ℚ K]
    {ζ : K} (hζ : IsPrimitiveRoot ζ p) (hp2 : p ≠ 2) :
    Algebra.norm ℚ ((hζ.toInteger - 1 : 𝓞 K) : K) = (p : ℚ) := by
  haveI hcyc : IsCyclotomicExtension {p^(0+1)} ℚ K := by
    simp only [zero_add, pow_one]; exact inferInstance
  have hζ' : IsPrimitiveRoot ζ (p^(0+1)) := by simp only [zero_add, pow_one]; exact hζ
  have hirr : Irreducible (Polynomial.cyclotomic (p^(0+1)) ℚ) := by
    simp only [zero_add, pow_one]
    exact Polynomial.cyclotomic.irreducible_rat (Nat.Prime.pos hp.out)
  have h := IsPrimitiveRoot.norm_sub_one_of_prime_ne_two (k := 0) hζ' hirr hp2
  have hcast : (hζ.toInteger : K) = ζ := IsPrimitiveRoot.coe_toInteger hζ
  rw [show ((hζ.toInteger - 1 : 𝓞 K) : K) = (hζ.toInteger : K) - 1 from by push_cast; ring]
  rw [hcast]
  exact h

/-- N(m) = m^deg for m : ℕ with norm to ℤ。 -/
lemma norm_int_nat_cast_eq_pow
    {K : Type*} [Field K] [NumberField K] [CharZero K]
    {p : ℕ} [IsCyclotomicExtension {p} ℚ K] (m : ℕ) :
    Algebra.norm ℤ (m : 𝓞 K) = (m : ℤ) ^ Module.finrank ℚ K := by
  have h : ((Algebra.norm ℤ (m : 𝓞 K)) : ℚ) = (Algebra.norm ℚ ((m : 𝓞 K) : K)) :=
    Algebra.coe_norm_int (m : 𝓞 K)
  rw [show ((m : 𝓞 K) : K) = (m : K) from rfl] at h
  rw [show (m : K) = algebraMap ℚ K (m : ℚ) from by simp] at h
  rw [Algebra.norm_algebraMap] at h
  have h' : (m : ℚ) ^ Module.finrank ℚ K = ((m ^ Module.finrank ℚ K : ℕ) : ℚ) := by
    rw [Nat.cast_pow]
  rw [h'] at h
  have heq : (Algebra.norm ℤ (m : 𝓞 K) : ℚ) = (((m : ℕ) ^ Module.finrank ℚ K : ℕ) : ℚ) := h
  have heq' : Algebra.norm ℤ (m : 𝓞 K) = ((m : ℕ) ^ Module.finrank ℚ K : ℤ) :=
    Int.cast_injective heq
  simp only [heq']

/--
Mathlib の `sub_one_norm_eq_eval_cyclotomic` を一般の有理点 `a` へ拡張した product-free 補題。

`Algebra.norm ℚ (a - ζ)` を、`Φ_p(a)` の評価へ直接戻す。
今は Stage 3 direct route の調査基盤として置く。
-/
lemma norm_sub_primitiveRoot_eq_eval_cyclotomic_rat
    {K : Type*} [Field K] [CharZero K]
    {p : ℕ} [Fact p.Prime] [IsCyclotomicExtension {p} ℚ K]
  {ζ : K} (hζ : IsPrimitiveRoot ζ p) (a : ℚ) :
    Algebra.norm ℚ ((a : K) - ζ) = Polynomial.eval a (Polynomial.cyclotomic p ℚ) := by
  let E := AlgebraicClosure K
  haveI : NeZero p := ⟨(Fact.out : Nat.Prime p).ne_zero⟩
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_root
    (Polynomial.cyclotomic p E)
    (Polynomial.degree_cyclotomic_pos p E (NeZero.pos _)).ne.symm
  have hirr : Irreducible (Polynomial.cyclotomic p ℚ) :=
    Polynomial.cyclotomic.irreducible_rat (Nat.Prime.pos (Fact.out : Nat.Prime p))
  apply (algebraMap ℚ E).injective
  letI := IsCyclotomicExtension.finiteDimensional {p} ℚ K
  letI := IsCyclotomicExtension.isGalois {p} ℚ K
  rw [Algebra.norm_eq_prod_embeddings]
  conv_lhs =>
    congr
    rfl
    ext
    rw [map_sub]
    simp
  have hProd :
      ∏ σ : K →ₐ[ℚ] E, ((a : E) - σ ζ) =
        Polynomial.eval (a : E) (Polynomial.cyclotomic' p E) := by
    rw [Polynomial.cyclotomic', Polynomial.eval_prod, ← @Finset.prod_attach E E, ← Finset.univ_eq_attach]
    refine Fintype.prod_equiv (hζ.embeddingsEquivPrimitiveRoots E hirr) _ _ ?_
    intro σ
    simp
  rw [hProd, Polynomial.cyclotomic',
    ← Polynomial.cyclotomic_eq_prod_X_sub_primitiveRoots
      (Polynomial.isRoot_cyclotomic_iff.1 hz),
    ← Polynomial.map_cyclotomic p (algebraMap ℚ E)]
  calc
    Polynomial.eval (a : E) (Polynomial.map (algebraMap ℚ E) (Polynomial.cyclotomic p ℚ))
        = Polynomial.eval₂ (algebraMap ℚ E) (a : E) (Polynomial.cyclotomic p ℚ) := by
            simpa using (Polynomial.eval_map_algebraMap (Polynomial.cyclotomic p ℚ) (a : E))
    _ = (algebraMap ℚ E) (Polynomial.eval a (Polynomial.cyclotomic p ℚ)) := by
          simpa using
            (Polynomial.eval₂_at_apply (p := Polynomial.cyclotomic p ℚ) (algebraMap ℚ E) a)

/--
有理点での `Φ_p` 評価を K 上の `cyclotomicEval` へ持ち上げるための補題。

direct norm-eval route で `Polynomial.eval a (cyclotomic p ℚ)` を
CFBRC 側の evaluator へ接続する。
-/
lemma ratCast_eval_cyclotomic_eq_cyclotomicEval
    {K : Type*} [Field K] [CharZero K]
    {p : ℕ} [Fact p.Prime] (a : ℚ) :
    ((Polynomial.eval a (Polynomial.cyclotomic p ℚ) : ℚ) : K) =
      DkMath.CFBRC.cyclotomicEval p (a : K) := by
  unfold DkMath.CFBRC.cyclotomicEval
  calc
    ((Polynomial.eval a (Polynomial.cyclotomic p ℚ) : ℚ) : K)
        = Polynomial.eval₂ (algebraMap ℚ K) (a : K) (Polynomial.cyclotomic p ℚ) := by
            simpa using
              (Polynomial.eval₂_at_apply (p := Polynomial.cyclotomic p ℚ) (algebraMap ℚ K) a).symm
    _ = Polynomial.eval (a : K)
          (Polynomial.map (algebraMap ℚ K) (Polynomial.cyclotomic p ℚ)) := by
            symm
            exact (Polynomial.eval₂_eq_eval_map (p := Polynomial.cyclotomic p ℚ)
              (f := algebraMap ℚ K) (x := (a : K))).symm
    _ = Polynomial.eval (a : K)
          (Polynomial.map (Int.castRingHom K) (Polynomial.cyclotomic p ℤ)) := by
            congr 1
            ext n
            simp
    _ = Polynomial.eval₂ (Int.castRingHom K) (a : K) (Polynomial.cyclotomic p ℤ) := by
          symm
          exact (Polynomial.eval₂_eq_eval_map (p := Polynomial.cyclotomic p ℤ)
            (f := Int.castRingHom K) (x := (a : K)))

/--
prime case では、`Φ_p(z / y) * y^(p-1)` は product-free に `GN p (z - y) y` へ戻る。

これは CFBRC 側の shifted evaluator bridge を prime divisor の singleton case へ
specialize したもの。
-/
theorem cyclotomicEval_div_natCast_mul_pow_eq_gn
    {K : Type*} [Field K] [CharZero K]
    {p z y : ℕ} [Fact p.Prime]
    (hy0 : y ≠ 0) (hyz : y < z) :
    DkMath.CFBRC.cyclotomicEval p ((z : K) / (y : K)) * (y : K) ^ (p - 1) =
      (DkMath.CosmicFormulaBinom.GN p (z - y) y : K) := by
  have hp0 : 0 < p := (Fact.out : Nat.Prime p).pos
  have hyK : (y : K) ≠ 0 := by exact_mod_cast hy0
  have hgapK : ((z - y : ℕ) : K) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Nat.sub_pos_of_lt hyz))
  have hratio : ((((z - y : ℕ) : K) + (y : K)) / (y : K)) = ((z : K) / (y : K)) := by
    have hsum : ((z - y : ℕ) : K) + (y : K) = (z : K) := by
      exact_mod_cast (Nat.sub_add_cancel (Nat.le_of_lt hyz))
    rw [hsum]
  have hdeg : (Polynomial.cyclotomic p ℤ).natDegree = p - 1 := by
    simpa [Nat.totient_prime (Fact.out : Nat.Prime p)] using
      (Polynomial.natDegree_cyclotomic p ℤ)
  have hshift :=
    DkMath.CFBRC.cyclotomicShiftedEval_eq_cyclotomicEval_div_mul_pow
      (m := p) ((z - y : ℕ) : K) (y : K) hyK
  have hprimeProd :
      DkMath.CFBRC.cyclotomicDivisorsProductShifted p ((z - y : ℕ) : K) (y : K) =
        DkMath.CFBRC.cyclotomicShiftedEval p ((z - y : ℕ) : K) (y : K) := by
    have hpne1 : p ≠ 1 := (Fact.out : Nat.Prime p).ne_one
    have hpne1' : ¬ 1 = p := by
      intro h
      exact hpne1 h.symm
    unfold DkMath.CFBRC.cyclotomicDivisorsProductShifted
    rw [(Fact.out : Nat.Prime p).divisors]
    simp [hpne1']
  have hGN :
      DkMath.CFBRC.cyclotomicShiftedEval p ((z - y : ℕ) : K) (y : K) =
        (DkMath.CosmicFormulaBinom.GN p (z - y) y : K) := by
    have hgap_cast : ((z - y : ℕ) : K) = (z : K) - (y : K) := by
      rw [Nat.cast_sub (Nat.le_of_lt hyz)]
    calc
      DkMath.CFBRC.cyclotomicShiftedEval p ((z - y : ℕ) : K) (y : K)
          = DkMath.CFBRC.cyclotomicDivisorsProductShifted p ((z - y : ℕ) : K) (y : K) :=
            hprimeProd.symm
      _ = DkMath.CosmicFormulaBinom.GN p (((z - y : ℕ) : K)) (y : K) :=
            DkMath.CFBRC.cyclotomicDivisorsProductShifted_eq_GN_of_ne_zero
              (R := K) (d := p) hp0 hgapK hyK
      _ = (DkMath.CosmicFormulaBinom.GN p (z - y) y : K) := by
        simp [hgap_cast]
  calc
    DkMath.CFBRC.cyclotomicEval p ((z : K) / (y : K)) * (y : K) ^ (p - 1)
        = DkMath.CFBRC.cyclotomicEval p ((((z - y : ℕ) : K) + (y : K)) / (y : K)) *
            (y : K) ^ (Polynomial.cyclotomic p ℤ).natDegree := by
              rw [hratio, hdeg]
    _ = DkMath.CFBRC.cyclotomicShiftedEval p ((z - y : ℕ) : K) (y : K) := hshift.symm
    _ = (DkMath.CosmicFormulaBinom.GN p (z - y) y : K) := hGN

/--
chosen cyclotomic linear factor の整数 norm は、full product identity を使わずとも
直接 `GN p (z - y) y` に一致する（まずは ℚ cast 版）。

proof は
`z - ζy = y * (z/y - ζ)`
と direct norm-eval route、そして prime-case shifted evaluator bridge を合成する。
-/
theorem chosenCyclotomicLinearFactor_norm_eq_gn_ratCast_direct
    {K : Type*} [Field K] [NumberField K] [CharZero K]
    {p z y : ℕ} [Fact p.Prime] [IsCyclotomicExtension {p} ℚ K]
    {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    (hy0 : y ≠ 0) (hyz : y < z) :
    ((Algebra.norm ℤ ((z : 𝓞 K) - hζ.toInteger * (y : 𝓞 K)) : ℤ) : ℚ) =
      ((DkMath.CosmicFormulaBinom.GN p (z - y) y : ℕ) : ℚ) := by
  let lin : 𝓞 K := (z : 𝓞 K) - hζ.toInteger * (y : 𝓞 K)
  have hyK : (y : K) ≠ 0 := by
    exact_mod_cast hy0
  have hirr : Irreducible (Polynomial.cyclotomic p ℚ) :=
    Polynomial.cyclotomic.irreducible_rat (Nat.Prime.pos (Fact.out : Nat.Prime p))
  have hfinrank : Module.finrank ℚ K = p - 1 := by
    rw [IsCyclotomicExtension.finrank K hirr]
    simp [Nat.totient_prime (Fact.out : Nat.Prime p)]
  have hChosenK :
      ((lin : 𝓞 K) : K) =
        (y : K) * ((((z : ℚ) / (y : ℚ) : ℚ) : K) - ζ) := by
    have hrat : ((((z : ℚ) / (y : ℚ) : ℚ) : K)) = (z : K) / (y : K) := by
      norm_num [hy0]
    have hdiv : (y : K) * ((((z : ℚ) / (y : ℚ) : ℚ) : K)) = (z : K) := by
      rw [hrat, div_eq_mul_inv]
      rw [← mul_assoc]
      calc
        (y : K) * (z : K) * (y : K)⁻¹ = (z : K) * ((y : K) * (y : K)⁻¹) := by ring
        _ = (z : K) * 1 := by rw [mul_inv_cancel₀ hyK]
        _ = (z : K) := by ring
    calc
      ((lin : 𝓞 K) : K)
          = (z : K) - ζ * (y : K) := by
            simp [lin]
      _ = (y : K) * ((((z : ℚ) / (y : ℚ) : ℚ) : K) - ζ) := by
            rw [mul_sub, hdiv]
            ring
  have hNormY : Algebra.norm ℚ (y : K) = (y : ℚ) ^ (p - 1) := by
    calc
      Algebra.norm ℚ (y : K) = (y : ℚ) ^ Module.finrank ℚ K := by
        rw [show (y : K) = algebraMap ℚ K (y : ℚ) by simp, Algebra.norm_algebraMap]
      _ = (y : ℚ) ^ (p - 1) := by rw [hfinrank]
  have hNormField :
      Algebra.norm ℚ ((lin : 𝓞 K) : K) =
        (y : ℚ) ^ (p - 1) * Polynomial.eval ((z : ℚ) / (y : ℚ)) (Polynomial.cyclotomic p ℚ) := by
    rw [hChosenK, map_mul, hNormY,
      norm_sub_primitiveRoot_eq_eval_cyclotomic_rat hζ ((z : ℚ) / (y : ℚ))]
  have hEvalQ :
      Polynomial.eval ((z : ℚ) / (y : ℚ)) (Polynomial.cyclotomic p ℚ) =
        DkMath.CFBRC.cyclotomicEval p ((z : ℚ) / (y : ℚ)) := by
    simpa using
      (ratCast_eval_cyclotomic_eq_cyclotomicEval (K := ℚ) (p := p) ((z : ℚ) / (y : ℚ)))
  have hGNQ :
      DkMath.CFBRC.cyclotomicEval p ((z : ℚ) / (y : ℚ)) * (y : ℚ) ^ (p - 1) =
        ((DkMath.CosmicFormulaBinom.GN p (z - y) y : ℕ) : ℚ) := by
    simpa [Nat.cast_sub (Nat.le_of_lt hyz)] using
      (cyclotomicEval_div_natCast_mul_pow_eq_gn (K := ℚ) (p := p) (z := z) (y := y) hy0 hyz)
  have hNormField' :
      Algebra.norm ℚ ((lin : 𝓞 K) : K) =
        ((DkMath.CosmicFormulaBinom.GN p (z - y) y : ℕ) : ℚ) := by
    calc
      Algebra.norm ℚ ((lin : 𝓞 K) : K)
          = (y : ℚ) ^ (p - 1) * Polynomial.eval ((z : ℚ) / (y : ℚ)) (Polynomial.cyclotomic p ℚ) :=
              hNormField
      _ = (y : ℚ) ^ (p - 1) * DkMath.CFBRC.cyclotomicEval p ((z : ℚ) / (y : ℚ)) := by
            rw [hEvalQ]
      _ = DkMath.CFBRC.cyclotomicEval p ((z : ℚ) / (y : ℚ)) * (y : ℚ) ^ (p - 1) := by
            ring
      _ = ((DkMath.CosmicFormulaBinom.GN p (z - y) y : ℕ) : ℚ) := hGNQ
  exact (Algebra.coe_norm_int lin).trans hNormField'

/--
chosen cyclotomic linear factor の整数 norm を、そのまま `GN p (z - y) y` へ戻す direct theorem。
-/
theorem chosenCyclotomicLinearFactor_norm_eq_gn_direct
    {K : Type*} [Field K] [NumberField K] [CharZero K]
    {p z y : ℕ} [Fact p.Prime] [IsCyclotomicExtension {p} ℚ K]
    {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    (hy0 : y ≠ 0) (hyz : y < z) :
    Algebra.norm ℤ ((z : 𝓞 K) - hζ.toInteger * (y : 𝓞 K)) =
      ((DkMath.CosmicFormulaBinom.GN p (z - y) y : ℕ) : ℤ) := by
  exact Int.cast_injective
    (chosenCyclotomicLinearFactor_norm_eq_gn_ratCast_direct hζ hy0 hyz)

/-- N(ζ-1) = p in ℤ。 -/
lemma norm_int_zeta_sub_one_eq_p
    {K : Type*} [Field K] [NumberField K] [CharZero K]
    {p : ℕ} [hp : Fact p.Prime] [IsCyclotomicExtension {p} ℚ K]
    {ζ : K} (hζ : IsPrimitiveRoot ζ p) (hp2 : p ≠ 2) :
    Algebra.norm ℤ (hζ.toInteger - 1) = (p : ℤ) := by
  have h : ((Algebra.norm ℤ (hζ.toInteger - 1)) : ℚ) = (Algebra.norm ℚ ((hζ.toInteger - 1 : 𝓞 K) : K)) :=
    Algebra.coe_norm_int (hζ.toInteger - 1)
  have hzeta : Algebra.norm ℚ ((hζ.toInteger - 1 : 𝓞 K) : K) = (p : ℚ) :=
    norm_zeta_sub_one_eq_p_rat hζ hp2
  rw [hzeta] at h
  exact Int.cast_injective h

/-- p と互いに素な m は (ζ-1) で割れない。 -/
lemma zeta_sub_one_not_dvd_of_coprime
    {K : Type*} [Field K] [NumberField K] [CharZero K]
    {p : ℕ} [hp : Fact p.Prime] [IsCyclotomicExtension {p} ℚ K]
    {ζ : K} (hζ : IsPrimitiveRoot ζ p) (hp2 : p ≠ 2)
    {m : ℕ} (hm : Nat.Coprime m p) :
    ¬ (hζ.toInteger - 1 ∣ (m : 𝓞 K)) := by
  intro ⟨q, hq⟩
  have hnorm_m : Algebra.norm ℤ (m : 𝓞 K) = (m : ℤ) ^ Module.finrank ℚ K :=
    norm_int_nat_cast_eq_pow (p := p) m
  have hnorm_zeta : Algebra.norm ℤ (hζ.toInteger - 1) = (p : ℤ) :=
    norm_int_zeta_sub_one_eq_p hζ hp2
  have hnorm_mul : Algebra.norm ℤ ((hζ.toInteger - 1) * q) =
      Algebra.norm ℤ (hζ.toInteger - 1) * Algebra.norm ℤ q :=
    (Algebra.norm ℤ).map_mul _ _
  have heq : Algebra.norm ℤ (m : 𝓞 K) = Algebra.norm ℤ ((hζ.toInteger - 1) * q) := by
    rw [hq]
  rw [hnorm_m, hnorm_mul, hnorm_zeta] at heq
  -- heq : m^deg = p * N(q) in ℤ
  have hpdvd : (p : ℤ) ∣ (m : ℤ) ^ Module.finrank ℚ K := ⟨Algebra.norm ℤ q, heq⟩
  have hpdvd_m : (p : ℤ) ∣ (m : ℤ) := by
    have hp_prime : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp.out
    exact hp_prime.dvd_of_dvd_pow hpdvd
  have hpdvd_nat : p ∣ m := Int.natCast_dvd_natCast.mp hpdvd_m
  -- But m is coprime to p, contradiction
  have hdvd_gcd : p ∣ Nat.gcd m p := Nat.dvd_gcd hpdvd_nat (dvd_refl p)
  rw [hm] at hdvd_gcd
  exact hp.out.not_dvd_one hdvd_gcd

/-- n ∈ (ζ-1) ⟹ p | n。 -/
lemma p_dvd_of_in_zeta_sub_one_ideal
    {K : Type*} [Field K] [NumberField K] [CharZero K]
    {p : ℕ} [hp : Fact p.Prime] [IsCyclotomicExtension {p} ℚ K]
    {ζ : K} (hζ : IsPrimitiveRoot ζ p) (hp2 : p ≠ 2)
    {n : ℕ} (hn : (n : 𝓞 K) ∈ Ideal.span ({hζ.toInteger - 1} : Set (𝓞 K))) :
    p ∣ n := by
  by_cases hn_zero : n = 0
  · simp [hn_zero]
  by_contra hp_not_dvd
  have hcop : Nat.Coprime n p := by
    rw [Nat.Coprime, Nat.gcd_comm]
    exact (Nat.Prime.coprime_iff_not_dvd hp.out).mpr hp_not_dvd
  have hdvd : hζ.toInteger - 1 ∣ (n : 𝓞 K) := Ideal.mem_span_singleton.mp hn
  exact zeta_sub_one_not_dvd_of_coprime hζ hp2 hcop hdvd

/--
整数 n が (ζ - 1) ideal に入れば p | n を示す target。

N(ζ - 1) = p なので、n ∈ (ζ - 1) ⟹ N(ζ - 1) | N(n) = n^(p-1) ⟹ p | n^(p-1) ⟹ p | n。

この interface 自体は downstream theorem がまだ受け取るが、
concrete fill theorem `integerInZetaMinusOneIdealDivisibleByP_fill` は下で与える。
-/
abbrev IntegerInZetaMinusOneIdealDivisibleByPTarget (K : Type*) [Field K] [NumberField K] [CharZero K]
    (p : ℕ) [Fact p.Prime] [IsCyclotomicExtension {p} ℚ K]
    (ζ : K) (hζ : IsPrimitiveRoot ζ p) : Prop :=
  ∀ {n : ℕ},
    (n : 𝓞 K) ∈ Ideal.span ({hζ.toInteger - 1} : Set (𝓞 K)) →
    p ∣ n

/--
Target 2 fill theorem: N(ζ-1) = p から IntegerInZetaMinusOneIdealDivisibleByP を導出。

FLT 第一場合は奇素数を扱うので hp2 : p ≠ 2 は pack 条件から自動的に満たされる。
-/
theorem integerInZetaMinusOneIdealDivisibleByP_fill
    {K : Type*} [Field K] [NumberField K] [CharZero K]
    {p : ℕ} [hp : Fact p.Prime] [IsCyclotomicExtension {p} ℚ K]
    {ζ : K} (hζ : IsPrimitiveRoot ζ p) (hp2 : p ≠ 2) :
    IntegerInZetaMinusOneIdealDivisibleByPTarget K p ζ hζ := fun hn =>
  p_dvd_of_in_zeta_sub_one_ideal hζ hp2 hn

/-! ### Target 1 Fill: P | (p) ⟹ P = (ζ - 1)

Mathlib の `eq_span_zeta_sub_one_of_liesOver'` を使う。
-/

/--
P | span {p} から LiesOver インスタンスを構築する。

P | (p) ⟺ (p) ≤ P ⟺ p ∈ P。
comap P は prime ideal、(p) は maximal、よって (p) = comap P。
-/
lemma liesOver_of_dvd_span_prime
    {K : Type*} [Field K] [NumberField K] [CharZero K]
    {p : ℕ} [hp : Fact p.Prime] [IsCyclotomicExtension {p} ℚ K]
    (P : Ideal (𝓞 K)) [hP : P.IsPrime]
    (hdvd : P ∣ Ideal.span ({(p : 𝓞 K)} : Set (𝓞 K))) :
    P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ)) := by
  constructor
  -- P | span {p} ⟹ span {p} ≤ P
  rw [Ideal.dvd_iff_le] at hdvd
  -- p ∈ P なので、(p) ⊆ comap P
  have hp_in_P : (p : 𝓞 K) ∈ P := hdvd (Ideal.subset_span (by simp))
  have hp_in_comap : (p : ℤ) ∈ P.under ℤ := by
    change algebraMap ℤ (𝓞 K) (p : ℤ) ∈ P
    simp only [algebraMap_int_eq, map_natCast, hp_in_P]
  -- (p) ⊆ comap P
  have hle : Ideal.span ({(p : ℤ)} : Set ℤ) ≤ P.under ℤ := by
    rw [Ideal.span_singleton_le_iff_mem]
    exact hp_in_comap
  -- comap P は IsPrime
  have hcomap_prime : (P.under ℤ).IsPrime := Ideal.IsPrime.under _ _
  -- (p) は maximal なので、(p) ≤ comap P ∧ comap P ≠ ⊤ ⟹ (p) = comap P
  have hp_maximal : (Ideal.span ({(p : ℤ)} : Set ℤ)).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.mp hp.out).irreducible
  exact (Ideal.IsMaximal.eq_of_le hp_maximal hcomap_prime.ne_top hle)

/--
Target 1 fill theorem: P | (p) ⟹ P = span {ζ - 1}。

Mathlib の `eq_span_zeta_sub_one_of_liesOver'` を利用。
-/
theorem primeOverPEqualsZetaMinusOne_fill
    {K : Type*} [Field K] [NumberField K] [CharZero K]
    {p : ℕ} [hp : Fact p.Prime] [hK : IsCyclotomicExtension {p} ℚ K]
    {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    (P : Ideal (𝓞 K)) [hP : P.IsPrime]
    (hdvd : P ∣ Ideal.span ({(p : 𝓞 K)} : Set (𝓞 K))) :
    P = Ideal.span ({hζ.toInteger - 1} : Set (𝓞 K)) := by
  have hLiesOver : P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ)) :=
    liesOver_of_dvd_span_prime P hdvd
  exact IsCyclotomicExtension.Rat.eq_span_zeta_sub_one_of_liesOver' p K hζ P

/--
P | (p) 分岐の contradiction: first case (p ∤ gap) と矛盾。

P | (p) で P prime なら P = (ζ-1)、よって z - ζy ∈ P = (ζ-1)。
z - y ∈ (ζ-1) から p | gap が導かれ、first case と矛盾。

定理の interface としては
`PrimeOverPEqualsZetaMinusOneTarget` と
`IntegerInZetaMinusOneIdealDivisibleByPTarget` を受け取るが、
現状の mainline では両者とも fill theorem が既に用意されている。
-/
theorem noPrimeOverP_of_firstCase_of_chosenFactorInP
    {K : Type*} [Field K] [NumberField K] [CharZero K]
    {p : ℕ} [hp : Fact p.Prime] [IsCyclotomicExtension {p} ℚ K]
    {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    (hTarget1 : PrimeOverPEqualsZetaMinusOneTarget K p ζ hζ)
    (hTarget2 : IntegerInZetaMinusOneIdealDivisibleByPTarget K p ζ hζ)
    {y z : 𝓞 K}
    {P : Ideal (𝓞 K)} (hP : P.IsPrime) (hP_ne_bot : P ≠ ⊥)
    (hP_dvd_p : P ∣ Ideal.span ({(p : 𝓞 K)} : Set (𝓞 K)))
    (hP_chosen : z - hζ.toInteger * y ∈ P)
    {gap : ℕ}
    (hgap_eq : z - y = (gap : 𝓞 K))
    (hFirstCase : ¬ p ∣ gap) :
    False := by
  -- Step 1: P = (ζ - 1) from target 1
  have hP_eq_zeta : P = Ideal.span ({hζ.toInteger - 1} : Set (𝓞 K)) :=
    hTarget1 hP hP_ne_bot hP_dvd_p
  -- Step 2: z - ζy ∈ P = (ζ - 1)
  rw [hP_eq_zeta] at hP_chosen
  -- Step 3: z - y ∈ (ζ - 1)
  have hgap_in_zeta : z - y ∈ Ideal.span ({hζ.toInteger - 1} : Set (𝓞 K)) :=
    chosen_factor_in_zeta_sub_one_implies_gap_in_zeta_sub_one hζ hP_chosen
  -- Step 4: gap ∈ (ζ - 1) as nat
  rw [hgap_eq] at hgap_in_zeta
  -- Step 5: p | gap from target 2
  have hp_dvd_gap : p ∣ gap := hTarget2 hgap_in_zeta
  -- Step 6: contradiction with first case
  exact hFirstCase hp_dvd_gap

/-! ### P | (p) ∨ y ∈ P の両分岐を統合する combiner -/

/--
P | (p) ∨ y ∈ P のどちらも起きないことを supply する combiner。

first case (p ∤ gap) と pack coprimality を使う。
-/
theorem noPrimeOrY_of_firstCase_of_coprime
    {K : Type*} [Field K] [NumberField K] [CharZero K]
    {p : ℕ} [hp : Fact p.Prime] [IsCyclotomicExtension {p} ℚ K]
    {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    (hTarget1 : PrimeOverPEqualsZetaMinusOneTarget K p ζ hζ)
    (hTarget2 : IntegerInZetaMinusOneIdealDivisibleByPTarget K p ζ hζ)
    {x y : ℕ} (hxy : Nat.Coprime x y)
    {z_int : 𝓞 K}
    {gap : ℕ} (hgap_eq : z_int - (y : 𝓞 K) = (gap : 𝓞 K))
    (hFirstCase : ¬ p ∣ gap)
    (hProduct : ∏ j ∈ Finset.range p, (z_int - (hζ.toInteger ^ j) * (y : 𝓞 K)) = (x : 𝓞 K) ^ p)
    (P : Ideal (𝓞 K)) (hP : P.IsPrime)
    (hmemChosen : z_int - hζ.toInteger * (y : 𝓞 K) ∈ P)
    (hLinNe : z_int - hζ.toInteger * (y : 𝓞 K) ≠ 0) :
    P ∣ Ideal.span ({(p : 𝓞 K)} : Set (𝓞 K)) ∨ (y : 𝓞 K) ∈ P → False := by
  intro hdisj
  rcases hdisj with hP_dvd_p | hP_y
  · -- P | (p) branch
    have hP_ne_bot : P ≠ ⊥ := by
      intro hbot
      rw [hbot] at hmemChosen
      exact hLinNe (Ideal.mem_bot.mp hmemChosen)
    exact noPrimeOverP_of_firstCase_of_chosenFactorInP hζ hTarget1 hTarget2 hP hP_ne_bot
      hP_dvd_p hmemChosen hgap_eq hFirstCase
  · -- y ∈ P branch
    exact noYInCommonPrime_of_chosenFactorInP_of_coprime_of_productEq hζ hxy hP
      hmemChosen hProduct hP_y

/-! ### Stage 1 coprimality theorem の完成形 -/

/--
first case + coprimality pack から chosen linear factor と他の因子の coprimality を導出。

theorem statement は target interface を保っているが、
mainline 上では Target 1/2 の fill が既に存在するので、
Stage 1 coprimality の cyclotomic 側素材は concrete に揃っている。
-/
theorem chosenLinearFactor_isCoprime_with_other_of_firstCase_of_pack
    {K : Type*} [Field K] [NumberField K] [CharZero K]
    {p : ℕ} [hp : Fact p.Prime] [IsCyclotomicExtension {p} ℚ K]
    {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    (hTarget1 : PrimeOverPEqualsZetaMinusOneTarget K p ζ hζ)
    (hTarget2 : IntegerInZetaMinusOneIdealDivisibleByPTarget K p ζ hζ)
    {x y : ℕ} (hxy : Nat.Coprime x y)
    {z_int : 𝓞 K}
    {gap : ℕ} (hgap_eq : z_int - (y : 𝓞 K) = (gap : 𝓞 K))
    (hFirstCase : ¬ p ∣ gap)
    (hy_ne : y ≠ 0)
    (hLinNe : z_int - hζ.toInteger * (y : 𝓞 K) ≠ 0)
    (hProduct : ∏ j ∈ Finset.range p, (z_int - (hζ.toInteger ^ j) * (y : 𝓞 K)) = (x : 𝓞 K) ^ p)
    {j : ℕ} (hj_ne1 : j ≠ 1) (hj_lt : j < p) :
    IsCoprime (Ideal.span ({z_int - hζ.toInteger * (y : 𝓞 K)} : Set (𝓞 K)))
      (Ideal.span ({z_int - (hζ.toInteger ^ j) * (y : 𝓞 K)} : Set (𝓞 K))) := by
  refine linearFactorIdeals_isCoprime_of_noCommonPrime ?_
  intro P hP hmemChosen hmemOther
  have hp2 : 2 ≤ p := (Fact.out : Nat.Prime p).two_le
  have hy_ne' : (y : 𝓞 K) ≠ 0 := by simp [hy_ne]
  have hdisj := commonPrimeDvdsPrimeOrY_of_ringOfIntegersCyclotomic
    hζ (y := (y : 𝓞 K)) (z := z_int) hy_ne' hP hp2 hmemChosen ⟨j, hj_ne1, hj_lt, hmemOther⟩
  exact noPrimeOrY_of_firstCase_of_coprime hζ hTarget1 hTarget2 hxy hgap_eq hFirstCase
    hProduct P hP hmemChosen hLinNe hdisj

/--
first-case pack から chosen linear factor と他の因子の coprimality を導く product-free variant。

ここで必要なのは first-case と chosen factor 非零性だけであり、
full product identity は y-branch contradiction には不要である。
-/
theorem chosenLinearFactor_isCoprime_with_other_of_firstCase_of_pack_withoutProduct
    {K : Type*} [Field K] [NumberField K] [CharZero K]
    {p : ℕ} [hp : Fact p.Prime] [IsCyclotomicExtension {p} ℚ K]
    {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    (hTarget1 : PrimeOverPEqualsZetaMinusOneTarget K p ζ hζ)
    (hTarget2 : IntegerInZetaMinusOneIdealDivisibleByPTarget K p ζ hζ)
  {x y z : ℕ} (hpack : PrimeGe5CounterexamplePack p x y z)
    {z_int : 𝓞 K}
    {gap : ℕ} (hgap_eq : z_int - (y : 𝓞 K) = (gap : 𝓞 K))
    (hFirstCase : ¬ p ∣ gap)
    (hy_ne : y ≠ 0)
    (hLinNe : z_int - hζ.toInteger * (y : 𝓞 K) ≠ 0)
    {j : ℕ} (hj_ne1 : j ≠ 1) (hj_lt : j < p)
  (hz_eq : z_int = (z : 𝓞 K)) :
    IsCoprime (Ideal.span ({z_int - hζ.toInteger * (y : 𝓞 K)} : Set (𝓞 K)))
      (Ideal.span ({z_int - (hζ.toInteger ^ j) * (y : 𝓞 K)} : Set (𝓞 K))) := by
  refine linearFactorIdeals_isCoprime_of_noCommonPrime ?_
  intro P hP hmemChosen hmemOther
  have hp2 : 2 ≤ p := (Fact.out : Nat.Prime p).two_le
  have hy_ne' : (y : 𝓞 K) ≠ 0 := by simp [hy_ne]
  have hdisj := commonPrimeDvdsPrimeOrY_of_ringOfIntegersCyclotomic
    hζ (y := (y : 𝓞 K)) (z := z_int) hy_ne' hP hp2 hmemChosen ⟨j, hj_ne1, hj_lt, hmemOther⟩
  rcases hdisj with hP_dvd_p | hP_y
  · have hP_ne_bot : P ≠ ⊥ := by
      intro hbot
      rw [hbot] at hmemChosen
      exact hLinNe (Ideal.mem_bot.mp hmemChosen)
    exact noPrimeOverP_of_firstCase_of_chosenFactorInP hζ hTarget1 hTarget2 hP hP_ne_bot
      hP_dvd_p (hz_eq ▸ hmemChosen) hgap_eq hFirstCase
  · subst hz_eq
    exact noYInCommonPrime_of_chosenFactorInP_of_coprime_of_counterexamplePack
      hζ hpack hP hmemChosen hP_y

/--
cyclotomic の整数環 specialization で使う j 番目の linear factor。
-/
abbrev cyclotomicLinearFactorInRingOfIntegers
    {K : Type u} [Field K] [NumberField K] [CharZero K]
    {p : ℕ} [Fact p.Prime] [IsCyclotomicExtension {p} ℚ K]
    {ζ : K} (hζ : IsPrimitiveRoot ζ p) (y z : ℕ) (j : ℕ) : 𝓞 K :=
  (z : 𝓞 K) - (hζ.toInteger ^ j) * (y : 𝓞 K)

/--
cyclotomic の整数環 specialization で使う chosen linear factor。
-/
abbrev chosenCyclotomicLinearFactorInRingOfIntegers
    {K : Type u} [Field K] [NumberField K] [CharZero K]
    {p : ℕ} [Fact p.Prime] [IsCyclotomicExtension {p} ℚ K]
    {ζ : K} (hζ : IsPrimitiveRoot ζ p) (y z : ℕ) : 𝓞 K :=
  (z : 𝓞 K) - hζ.toInteger * (y : 𝓞 K)

/--
cyclotomic の整数環 specialization で使う full product identity hypothesis。
-/
abbrev CyclotomicLinearFactorProductEqInRingOfIntegers
    {K : Type u} [Field K] [NumberField K] [CharZero K]
    {p x y z : ℕ} [Fact p.Prime] [IsCyclotomicExtension {p} ℚ K]
    {ζ : K} (hζ : IsPrimitiveRoot ζ p) : Prop :=
  ∏ j ∈ Finset.range p, cyclotomicLinearFactorInRingOfIntegers hζ y z j = (x : 𝓞 K) ^ p

/--
cyclotomic の整数環 specialization で使う chosen linear factor の非零性。
-/
abbrev ChosenCyclotomicLinearFactorNonzeroInRingOfIntegers
    {K : Type u} [Field K] [NumberField K] [CharZero K]
    {p y z : ℕ} [Fact p.Prime] [IsCyclotomicExtension {p} ℚ K]
    {ζ : K} (hζ : IsPrimitiveRoot ζ p) : Prop :=
  chosenCyclotomicLinearFactorInRingOfIntegers hζ y z ≠ 0

/--
full product identity があれば、chosen cyclotomic linear factor は自動的に非零である。

`∏_{j < p} (z - ζ^j y) = x^p` と `x ≠ 0` から、1 番目の因子が 0 なら積全体が 0 になって矛盾する。
-/
theorem chosenCyclotomicLinearFactorNonzero_of_productEq_of_counterexamplePack
    {K : Type u} [Field K] [NumberField K] [CharZero K]
    {p x y z : ℕ} [Fact p.Prime] [IsCyclotomicExtension {p} ℚ K]
    {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    (hpack : PrimeGe5CounterexamplePack p x y z)
    (hProduct : CyclotomicLinearFactorProductEqInRingOfIntegers
      (hζ := hζ) (x := x) (y := y) (z := z)) :
    ChosenCyclotomicLinearFactorNonzeroInRingOfIntegers (hζ := hζ) (y := y) (z := z) := by
  intro hChosenZero
  have hone_mem : 1 ∈ Finset.range p := by
    exact Finset.mem_range.mpr (lt_of_lt_of_le (by decide : 1 < 5) hpack.hp5)
  have hprod_zero :
      ∏ j ∈ Finset.range p, cyclotomicLinearFactorInRingOfIntegers hζ y z j = 0 := by
    exact Finset.prod_eq_zero_iff.mpr ⟨1, hone_mem, by
      simpa [cyclotomicLinearFactorInRingOfIntegers,
        chosenCyclotomicLinearFactorInRingOfIntegers, pow_one] using hChosenZero⟩
  have hxpow_zero : ((x : 𝓞 K) ^ p) = 0 := by
    rw [← hProduct]
    exact hprod_zero
  have hx_zero : (x : 𝓞 K) = 0 := eq_zero_of_pow_eq_zero hxpow_zero
  exact hpack.hx0 (Nat.cast_eq_zero.mp hx_zero)

/--
chosen linear factor と tail ideal の積が `(x)^p` になることを表す shorthand。
-/
abbrev ChosenCyclotomicLinearFactorMulTailEqSpanPowInRingOfIntegers
    {K : Type u} [Field K] [NumberField K] [CharZero K]
    {p x y z : ℕ} [Fact p.Prime] [IsCyclotomicExtension {p} ℚ K]
    {ζ : K} (hζ : IsPrimitiveRoot ζ p) : Prop :=
  Ideal.span ({chosenCyclotomicLinearFactorInRingOfIntegers hζ y z} : Set (𝓞 K)) *
      ∏ j ∈ (Finset.range p).erase 1,
        Ideal.span ({cyclotomicLinearFactorInRingOfIntegers hζ y z j} : Set (𝓞 K)) =
    Ideal.span ({(x : 𝓞 K)} : Set (𝓞 K)) ^ p

/--
chosen linear factor ideal が p 乗 ideal であることを表す shorthand。
-/
abbrev ChosenCyclotomicLinearFactorSpanEqPowInRingOfIntegers
    {K : Type u} [Field K] [NumberField K] [CharZero K]
    {p y z : ℕ} [Fact p.Prime] [IsCyclotomicExtension {p} ℚ K]
    {ζ : K} (hζ : IsPrimitiveRoot ζ p) : Prop :=
  ∃ K' : Ideal (𝓞 K),
    Ideal.span ({chosenCyclotomicLinearFactorInRingOfIntegers hζ y z} : Set (𝓞 K)) = K' ^ p

/--
chosen linear factor ideal が principal p 乗 ideal であることを表す shorthand。
-/
abbrev ChosenCyclotomicLinearFactorIdealPthPowerInRingOfIntegers
    {K : Type u} [Field K] [NumberField K] [CharZero K]
    {p y z : ℕ} [Fact p.Prime] [IsCyclotomicExtension {p} ℚ K]
    {ζ : K} (hζ : IsPrimitiveRoot ζ p) : Prop :=
  ∃ I : Ideal (𝓞 K), ∃ _ : I.IsPrincipal,
    Ideal.span ({chosenCyclotomicLinearFactorInRingOfIntegers hζ y z} : Set (𝓞 K)) = I ^ p

/--
first case + coprimality pack から、chosen linear factor と complementary tail 全体の coprimality を導出。

Stage 1 の actual cyclotomic coprimality leg を 2-factor route の入力へ畳み込む wrapper。
-/
theorem chosenLinearFactor_isCoprime_with_tail_of_firstCase_of_pack
  {K : Type u} [Field K] [NumberField K] [CharZero K]
    {p x y z : ℕ} [hp : Fact p.Prime] [IsCyclotomicExtension {p} ℚ K]
    {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    (hpack : PrimeGe5CounterexamplePack p x y z)
    {gap : ℕ} (hgap_eq : (z : 𝓞 K) - (y : 𝓞 K) = (gap : 𝓞 K))
    (hFirstCase : ¬ p ∣ gap)
    (hLinNe : (z : 𝓞 K) - hζ.toInteger * (y : 𝓞 K) ≠ 0)
    (hProduct : ∏ j ∈ Finset.range p, ((z : 𝓞 K) - (hζ.toInteger ^ j) * (y : 𝓞 K)) =
      (x : 𝓞 K) ^ p) :
    IsCoprime (Ideal.span ({(z : 𝓞 K) - hζ.toInteger * (y : 𝓞 K)} : Set (𝓞 K)))
      (∏ j ∈ (Finset.range p).erase 1,
        Ideal.span ({(z : 𝓞 K) - (hζ.toInteger ^ j) * (y : 𝓞 K)} : Set (𝓞 K))) := by
  have hp_ne_two : p ≠ 2 := by
    have hp_gt_two : 2 < p := lt_of_lt_of_le (by decide : 2 < 5) hpack.hp5
    exact ne_of_gt hp_gt_two
  apply idealIsCoprime_prod_of_forall
  intro j hj
  have hj_ne1 : j ≠ 1 := Finset.ne_of_mem_erase hj
  have hj_lt : j < p := Finset.mem_range.mp (Finset.mem_of_mem_erase hj)
  exact chosenLinearFactor_isCoprime_with_other_of_firstCase_of_pack hζ
    (fun {P} hP _hP_ne hP_dvd_p => by
      let _ : P.IsPrime := hP
      exact primeOverPEqualsZetaMinusOne_fill hζ P hP_dvd_p)
    (integerInZetaMinusOneIdealDivisibleByP_fill hζ hp_ne_two)
    hpack.hxy hgap_eq hFirstCase hpack.hy0 hLinNe hProduct hj_ne1 hj_lt

/--
counterexample pack の product identity から、chosen linear factor と tail ideal の積等式を回収する。

review-036 が要求する Stage 1 final wrapper 細分化の 1 本目。
-/
theorem chosenLinearFactorMulTailEqSpanPow_of_productEq
  {K : Type u} [Field K] [NumberField K] [CharZero K]
    {p x y z : ℕ} [hp : Fact p.Prime] [IsCyclotomicExtension {p} ℚ K]
    {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    (hpack : PrimeGe5CounterexamplePack p x y z)
    (hProduct : CyclotomicLinearFactorProductEqInRingOfIntegers
      (hζ := hζ) (x := x) (y := y) (z := z)) :
    ChosenCyclotomicLinearFactorMulTailEqSpanPowInRingOfIntegers
      (hζ := hζ) (x := x) (y := y) (z := z) := by
  let factor : ℕ → 𝓞 K := cyclotomicLinearFactorInRingOfIntegers hζ y z
  have hone_mem : 1 ∈ Finset.range p := by
    have hlt : 1 < p := lt_of_lt_of_le (by decide : 1 < 5) hpack.hp5
    exact Finset.mem_range.mpr hlt
  calc
    Ideal.span ({chosenCyclotomicLinearFactorInRingOfIntegers hζ y z} : Set (𝓞 K)) *
        ∏ j ∈ (Finset.range p).erase 1, Ideal.span ({factor j} : Set (𝓞 K))
        = ∏ j ∈ Finset.range p, Ideal.span ({factor j} : Set (𝓞 K)) := by
            simpa [factor, cyclotomicLinearFactorInRingOfIntegers,
              chosenCyclotomicLinearFactorInRingOfIntegers, pow_one] using
              (Finset.mul_prod_erase (s := Finset.range p)
                (f := fun j => Ideal.span ({factor j} : Set (𝓞 K))) hone_mem)
    _ = Ideal.span ({∏ j ∈ Finset.range p, factor j} : Set (𝓞 K)) := by
          simpa [factor] using
            (span_singleton_finset_prod (R := 𝓞 K) (s := Finset.range p) (f := factor))
    _ = Ideal.span ({(x : 𝓞 K) ^ p} : Set (𝓞 K)) := by
          rw [hProduct]
    _ = Ideal.span ({(x : 𝓞 K)} : Set (𝓞 K)) ^ p := by
          rw [Ideal.span_singleton_pow]

/--
counterexample pack から、`(x)` の非零性を整数環 specialization で固定する。

review-036 が要求する Stage 1 final wrapper 細分化の 2 本目。
-/
theorem xSpanNonzero_of_counterexamplePack_of_ringOfIntegers
  {K : Type u} [Field K] [NumberField K] [CharZero K]
    {p x y z : ℕ} [Fact p.Prime] [IsCyclotomicExtension {p} ℚ K]
    (hpack : PrimeGe5CounterexamplePack p x y z) :
    Ideal.span ({(x : 𝓞 K)} : Set (𝓞 K)) ≠ ⊥ := by
  intro hbot
  have hx0 : (x : 𝓞 K) = 0 := Ideal.span_singleton_eq_bot.mp hbot
  exact hpack.hx0 (Nat.cast_eq_zero.mp hx0)

/--
局所線型因子 ideal が explicit に `K^p` と書ければ、
class-group p-torsion annihilation から principal root ideal の存在が従う。

Stage 1 の存在形 boundary theorem へ入る直前の local exact receiver。
-/
theorem linearFactorIdealPthPowerExistsOfSpanEqPowAndTorsionKill
    {R : Type u} [CommRing R] [IsDomain R] [IsDedekindDomain R]
    (ctx : CyclotomicLocalFactorizationContext R)
    {z y : R} {K : Ideal R}
    (hp : ctx.p ≠ 0) (hlin : z - ctx.zeta * y ≠ 0)
    (hEq : Ideal.span ({z - ctx.zeta * y} : Set R) = K ^ ctx.p)
    (hKill : CyclotomicPTorsionAnnihilationTarget.{u}) :
    ∃ J : Ideal R, J.IsPrincipal ∧ Ideal.span ({z - ctx.zeta * y} : Set R) = J ^ ctx.p := by
  refine principalRootIdealExistsOfEqPowAndTorsionKill
    (R := R) (I := Ideal.span ({z - ctx.zeta * y} : Set R)) (K := K) hp ?_ ?_ hEq hKill
  · infer_instance
  · exact mt Ideal.span_singleton_eq_bot.mp hlin

/--
局所線型因子 ideal の explicit equality と root ideal の nonzero 性から、
存在形 boundary を回収する variant。

Stage 1 theorem が `K ≠ ⊥` を supply する場合は、こちらが最短 receiver になる。
-/
theorem linearFactorIdealPthPowerExistsOfSpanEqPowAndRootNeBot
    {R : Type u} [CommRing R] [IsDomain R] [IsDedekindDomain R]
    (ctx : CyclotomicLocalFactorizationContext R)
    {z y : R} {K : Ideal R}
    (hp : ctx.p ≠ 0)
    (hEq : Ideal.span ({z - ctx.zeta * y} : Set R) = K ^ ctx.p)
    (hK_ne : K ≠ ⊥)
    (hKill : CyclotomicPTorsionAnnihilationTarget.{u}) :
    ∃ J : Ideal R, J.IsPrincipal ∧ Ideal.span ({z - ctx.zeta * y} : Set R) = J ^ ctx.p := by
  exact linearFactorIdealPthPowerExistsOfSpanEqPowAndTorsionKill
    ctx hp (linearFactorNeZeroOfSpanEqPow ctx hEq hK_ne) hEq hKill

/--
first-case pack から chosen linear factor ideal が `p` 乗 ideal であることを返す、
heartbeat-safe な薄い wrapper。
-/
theorem chosenLinearFactorSpanEqPow_of_firstCase_of_pack_thin
    {K : Type u} [Field K] [NumberField K] [CharZero K]
    {p x y z : ℕ} [hp : Fact p.Prime] [IsCyclotomicExtension {p} ℚ K]
    {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    (hpack : PrimeGe5CounterexamplePack p x y z)
    {gap : ℕ} (hgap_eq : (z : 𝓞 K) - (y : 𝓞 K) = (gap : 𝓞 K))
    (hFirstCase : ¬ p ∣ gap)
    (hLinNe : ChosenCyclotomicLinearFactorNonzeroInRingOfIntegers
      (hζ := hζ) (y := y) (z := z))
    (hProduct : CyclotomicLinearFactorProductEqInRingOfIntegers
      (hζ := hζ) (x := x) (y := y) (z := z)) :
    ChosenCyclotomicLinearFactorSpanEqPowInRingOfIntegers
      (hζ := hζ) (p := p) (y := y) (z := z) := by
  let ctx : CyclotomicLocalFactorizationContext (𝓞 K) := {
    p := p
    zeta := hζ.toInteger
    hzeta_pow := by
      simpa using hζ.toInteger_isPrimitiveRoot.pow_eq_one
  }
  let tail : 𝓞 K :=
    ∏ j ∈ (Finset.range p).erase 1, cyclotomicLinearFactorInRingOfIntegers hζ y z j
  have hTailSpan :
      ∏ j ∈ (Finset.range p).erase 1,
          Ideal.span ({cyclotomicLinearFactorInRingOfIntegers hζ y z j} : Set (𝓞 K)) =
        Ideal.span ({tail} : Set (𝓞 K)) := by
    simpa [tail] using
      (span_singleton_finset_prod (R := 𝓞 K)
        (s := (Finset.range p).erase 1)
        (f := cyclotomicLinearFactorInRingOfIntegers hζ y z))
  have hMul :
      Ideal.span ({chosenCyclotomicLinearFactorInRingOfIntegers hζ y z} : Set (𝓞 K)) *
          Ideal.span ({tail} : Set (𝓞 K)) =
        Ideal.span ({(x : 𝓞 K)} : Set (𝓞 K)) ^ p := by
    calc
      Ideal.span ({chosenCyclotomicLinearFactorInRingOfIntegers hζ y z} : Set (𝓞 K)) *
          Ideal.span ({tail} : Set (𝓞 K)) =
          Ideal.span ({chosenCyclotomicLinearFactorInRingOfIntegers hζ y z} : Set (𝓞 K)) *
            ∏ j ∈ (Finset.range p).erase 1,
              Ideal.span ({cyclotomicLinearFactorInRingOfIntegers hζ y z j} : Set (𝓞 K)) := by
                rw [← hTailSpan]
      _ = Ideal.span ({(x : 𝓞 K)} : Set (𝓞 K)) ^ p :=
        chosenLinearFactorMulTailEqSpanPow_of_productEq
          (K := K) (p := p) (x := x) (y := y) (z := z) hζ hpack hProduct
  have hCoprime :
      IsCoprime
        (Ideal.span ({chosenCyclotomicLinearFactorInRingOfIntegers hζ y z} : Set (𝓞 K)))
        (Ideal.span ({tail} : Set (𝓞 K))) := by
    rw [← hTailSpan]
    exact chosenLinearFactor_isCoprime_with_tail_of_firstCase_of_pack
      (K := K) (p := p) (x := x) (y := y) (z := z)
      hζ hpack hgap_eq hFirstCase hLinNe hProduct
  have hSpanEq :
      ∃ K' : Ideal (𝓞 K),
        Ideal.span ({(z : 𝓞 K) - ctx.zeta * (y : 𝓞 K)} : Set (𝓞 K)) = K' ^ ctx.p := by
    exact linearFactorSpanEqPowOfChosenMulTailEqSpanPowAndIsCoprime
      (R := 𝓞 K) (ctx := ctx) (tail := tail) (x := (x : 𝓞 K))
      (y := (y : 𝓞 K)) (z := (z : 𝓞 K))
      (xSpanNonzero_of_counterexamplePack_of_ringOfIntegers
        (K := K) (p := p) (x := x) (y := y) (z := z) hpack)
      hMul hCoprime
  simpa [ctx, chosenCyclotomicLinearFactorInRingOfIntegers] using hSpanEq

/--
first-case pack から chosen linear factor ideal の principal `p` 乗存在を返す、
heartbeat-safe な Stage 1 finished wrapper。
-/
theorem cyclotomicLinearFactorIdealPthPower_of_firstCase_of_pack_thin
    {K : Type u} [Field K] [NumberField K] [CharZero K]
    {p x y z : ℕ} [hp : Fact p.Prime] [IsCyclotomicExtension {p} ℚ K]
    {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    (hpack : PrimeGe5CounterexamplePack p x y z)
    {gap : ℕ} (hgap_eq : (z : 𝓞 K) - (y : 𝓞 K) = (gap : 𝓞 K))
    (hFirstCase : ¬ p ∣ gap)
    (hLinNe : ChosenCyclotomicLinearFactorNonzeroInRingOfIntegers
      (hζ := hζ) (y := y) (z := z))
    (hProduct : CyclotomicLinearFactorProductEqInRingOfIntegers
      (hζ := hζ) (x := x) (y := y) (z := z))
    (hKill : CyclotomicPTorsionAnnihilationTarget.{u}) :
    ChosenCyclotomicLinearFactorIdealPthPowerInRingOfIntegers
      (hζ := hζ) (p := p) (y := y) (z := z) := by
  let ctx : CyclotomicLocalFactorizationContext (𝓞 K) := {
    p := p
    zeta := hζ.toInteger
    hzeta_pow := by
      simpa using hζ.toInteger_isPrimitiveRoot.pow_eq_one
  }
  obtain ⟨K', hEq⟩ := chosenLinearFactorSpanEqPow_of_firstCase_of_pack_thin
    (K := K) (p := p) (x := x) (y := y) (z := z)
    hζ hpack hgap_eq hFirstCase hLinNe hProduct
  have hExists :
      ∃ J : Ideal (𝓞 K), J.IsPrincipal ∧
        Ideal.span ({(z : 𝓞 K) - ctx.zeta * (y : 𝓞 K)} : Set (𝓞 K)) = J ^ ctx.p := by
    exact linearFactorIdealPthPowerExistsOfSpanEqPowAndTorsionKill
      (R := 𝓞 K) (ctx := ctx) (K := K')
      hp.out.ne_zero
      (by simpa [ctx, chosenCyclotomicLinearFactorInRingOfIntegers] using hLinNe)
      (by simpa [ctx, chosenCyclotomicLinearFactorInRingOfIntegers] using hEq)
      hKill
  simpa [ChosenCyclotomicLinearFactorIdealPthPowerInRingOfIntegers,
    ctx, chosenCyclotomicLinearFactorInRingOfIntegers] using hExists

/--
first-case pack から chosen linear factor 自体を unit 倍の `p` 乗として返す、
Stage 3 の norm 計算へ入る直前の thin wrapper。
-/
theorem cyclotomicUnitNormalization_of_firstCase_of_pack_thin
    {K : Type u} [Field K] [NumberField K] [CharZero K]
    {p x y z : ℕ} [hp : Fact p.Prime] [IsCyclotomicExtension {p} ℚ K]
    {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    (hpack : PrimeGe5CounterexamplePack p x y z)
    {gap : ℕ} (hgap_eq : (z : 𝓞 K) - (y : 𝓞 K) = (gap : 𝓞 K))
    (hFirstCase : ¬ p ∣ gap)
    (hLinNe : ChosenCyclotomicLinearFactorNonzeroInRingOfIntegers
      (hζ := hζ) (y := y) (z := z))
    (hProduct : CyclotomicLinearFactorProductEqInRingOfIntegers
      (hζ := hζ) (x := x) (y := y) (z := z))
    (hKill : CyclotomicPTorsionAnnihilationTarget.{u}) :
    ∃ β unitFactor : 𝓞 K, IsUnit unitFactor ∧
      chosenCyclotomicLinearFactorInRingOfIntegers hζ y z = unitFactor * β ^ p := by
  let ctx : CyclotomicLocalFactorizationContext (𝓞 K) := {
    p := p
    zeta := hζ.toInteger
    hzeta_pow := by
      simpa using hζ.toInteger_isPrimitiveRoot.pow_eq_one
  }
  obtain ⟨I, hIPrincipal, hSpan⟩ := cyclotomicLinearFactorIdealPthPower_of_firstCase_of_pack_thin
    (K := K) (p := p) (x := x) (y := y) (z := z)
    hζ hpack hgap_eq hFirstCase hLinNe hProduct hKill
  let _ : I.IsPrincipal := hIPrincipal
  obtain ⟨unitFactor, hUnit, hEq⟩ :=
    linearFactorEqUnitMulGeneratorPowOfSpanEqPowPrincipal ctx (z : 𝓞 K) (y : 𝓞 K) hSpan
  refine ⟨Submodule.IsPrincipal.generator I, unitFactor, hUnit, ?_⟩
  simpa [ctx, chosenCyclotomicLinearFactorInRingOfIntegers] using hEq

/--
Stage 3a-1 の最初の中間補題:
chosen cyclotomic linear factor の整数 norm を、
`Gal(K/ℚ)` 上の共役積へ持ち上げる。

ここではまだ cyclotomic reindex はせず、norm の一般論だけを isolate する。
-/
theorem chosenCyclotomicLinearFactor_norm_eq_prod_gal_of_firstCase_of_pack_thin
    {K : Type u} [Field K] [NumberField K] [CharZero K]
    {p y z : ℕ} [Fact p.Prime] [IsCyclotomicExtension {p} ℚ K]
    {ζ : K} (hζ : IsPrimitiveRoot ζ p) :
    (((Algebra.norm ℤ (chosenCyclotomicLinearFactorInRingOfIntegers hζ y z) : ℚ) : K)) =
      ∏ σ : Gal(K/ℚ), σ (((chosenCyclotomicLinearFactorInRingOfIntegers hζ y z : 𝓞 K) : K)) := by
  let x : 𝓞 K := chosenCyclotomicLinearFactorInRingOfIntegers hζ y z
  have hcoe : ((Algebra.norm ℤ x : ℚ) : K) = algebraMap ℚ K (Algebra.norm ℚ ((x : 𝓞 K) : K)) := by
    exact congrArg (algebraMap ℚ K) (Algebra.coe_norm_int x)
  letI := IsCyclotomicExtension.finiteDimensional {p} ℚ K
  letI := IsCyclotomicExtension.isGalois {p} ℚ K
  calc
    ((Algebra.norm ℤ x : ℚ) : K) = algebraMap ℚ K (Algebra.norm ℚ ((x : 𝓞 K) : K)) := hcoe
    _ = ∏ σ : Gal(K/ℚ), σ (((x : 𝓞 K) : K)) := by
          rw [Algebra.norm_eq_prod_automorphisms]

/--
Stage 3a-1 の cyclotomic reindex 用補題:
`Gal(K/ℚ)` の元は chosen factor を、対応する `ζ^k` factor へ送る。
-/
theorem gal_apply_chosenCyclotomicLinearFactor_eq_factor_of_firstCase_of_pack_thin
    {K : Type u} [Field K] [NumberField K] [CharZero K]
    {p y z : ℕ} [hp : Fact p.Prime] [IsCyclotomicExtension {p} ℚ K]
    {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    (σ : Gal(K/ℚ)) :
    σ (((chosenCyclotomicLinearFactorInRingOfIntegers hζ y z : 𝓞 K) : K)) =
      ((cyclotomicLinearFactorInRingOfIntegers hζ y z
        (IsCyclotomicExtension.Rat.galEquivZMod p K σ).val.val : 𝓞 K) : K) := by
  letI : NeZero p := ⟨hp.out.ne_zero⟩
  let k : ℕ := (IsCyclotomicExtension.Rat.galEquivZMod p K σ).val.val
  have hsigma_base : σ ζ = ζ ^ k := by
    simpa [k] using
      (IsCyclotomicExtension.Rat.galEquivZMod_apply_of_pow_eq (n := p) (K := K) σ hζ.pow_eq_one)
  have hsigma_zeta :
      σ (((hζ.toInteger : 𝓞 K) : K)) = (((hζ.toInteger : 𝓞 K) : K)) ^ k := by
    have htoInteger : (((hζ.toInteger : 𝓞 K) : K)) = ζ := IsPrimitiveRoot.coe_toInteger hζ
    calc
      σ (((hζ.toInteger : 𝓞 K) : K)) = σ ζ := by rw [htoInteger]
      _ = ζ ^ k := hsigma_base
      _ = (((hζ.toInteger : 𝓞 K) : K)) ^ k := by rw [htoInteger]
  rw [chosenCyclotomicLinearFactorInRingOfIntegers, cyclotomicLinearFactorInRingOfIntegers]
  change σ ((z : K) - (((hζ.toInteger : 𝓞 K) : K) * (y : K))) =
    (z : K) - ((((hζ.toInteger : 𝓞 K) : K) ^ k) * (y : K))
  calc
    σ ((z : K) - (((hζ.toInteger : 𝓞 K) : K) * (y : K))) =
        σ (z : K) - σ (((hζ.toInteger : 𝓞 K) : K) * (y : K)) := by
          rw [map_sub]
    _ = σ (z : K) - σ (((hζ.toInteger : 𝓞 K) : K)) * σ (y : K) := by rw [map_mul]
    _ = (z : K) - (((hζ.toInteger : 𝓞 K) : K) ^ k) * (y : K) := by
          rw [hsigma_zeta]
          simp

/--
Stage 3a-1 の reindex 補題:
chosen factor の Gal-product は、そのまま `(ZMod p)ˣ` 上の factor 積に一致する。
-/
theorem chosenCyclotomicLinearFactor_norm_eq_prod_units_of_firstCase_of_pack_thin
    {K : Type u} [Field K] [NumberField K] [CharZero K]
    {p y z : ℕ} [hp : Fact p.Prime] [IsCyclotomicExtension {p} ℚ K]
    {ζ : K} (hζ : IsPrimitiveRoot ζ p) :
    (((Algebra.norm ℤ (chosenCyclotomicLinearFactorInRingOfIntegers hζ y z) : ℚ) : K)) =
      ∏ u : (ZMod p)ˣ,
        ((cyclotomicLinearFactorInRingOfIntegers hζ y z u.val.val : 𝓞 K) : K) := by
  letI : NeZero p := ⟨hp.out.ne_zero⟩
  rw [chosenCyclotomicLinearFactor_norm_eq_prod_gal_of_firstCase_of_pack_thin hζ]
  simpa using
    (Fintype.prod_equiv
      (IsCyclotomicExtension.Rat.galEquivZMod p K)
      (fun σ : Gal(K/ℚ) => σ (((chosenCyclotomicLinearFactorInRingOfIntegers hζ y z : 𝓞 K) : K)))
      (fun u : (ZMod p)ˣ =>
        ((cyclotomicLinearFactorInRingOfIntegers hζ y z u.val.val : 𝓞 K) : K))
      (fun σ => by
        simpa using
          (gal_apply_chosenCyclotomicLinearFactor_eq_factor_of_firstCase_of_pack_thin
            (hζ := hζ) (y := y) (z := z) (σ := σ))))

/--
Combinatorial bridge: `(ZMod p)ˣ` 上の積と `(Finset.range p).erase 0` 上の積の一致。

素数 `p` に対し、写像 `u ↦ u.val.val : (ZMod p)ˣ → ℕ` は
`{1, 2, …, p − 1}` への全単射であり、この添字変換で任意の積が一致する。
これは Stage 3a-1 と Stage 3a-2 を繋ぐ純 combinatorial な補題。
-/
theorem prod_units_zmod_eq_prod_range_erase_zero
    {p : ℕ} [hp : Fact p.Prime]
    {M : Type*} [CommMonoid M] (f : ℕ → M) :
    ∏ u : (ZMod p)ˣ, f u.val.val = ∏ j ∈ (Finset.range p).erase 0, f j := by
  letI : NeZero p := ⟨hp.out.ne_zero⟩
  apply Finset.prod_nbij (fun u : (ZMod p)ˣ => u.val.val)
  · -- hi: image lands in (Finset.range p).erase 0
    intro u _
    refine Finset.mem_erase.mpr ⟨?_, Finset.mem_range.mpr (ZMod.val_lt _)⟩
    intro h
    have hcop := ZMod.val_coe_unit_coprime u
    simp only [h, Nat.Coprime, Nat.gcd_zero_left] at hcop
    exact absurd hcop (ne_of_gt hp.out.one_lt)
  · -- i_inj: injective
    intro u₁ _ u₂ _ h
    exact Units.ext (ZMod.val_injective p h)
  · -- i_surj: surjective onto (Finset.range p).erase 0
    intro j hj
    rw [Finset.mem_coe] at hj
    have hj_ne := (Finset.mem_erase.mp hj).1
    have hj_lt := Finset.mem_range.mp (Finset.mem_erase.mp hj).2
    have hcoprime : Nat.Coprime j p :=
      (hp.out.coprime_iff_not_dvd.mpr
        (fun hdvd => absurd (Nat.le_of_dvd (by omega) hdvd) (by omega))).symm
    exact ⟨ZMod.unitOfCoprime j hcoprime, Finset.mem_coe.mpr (Finset.mem_univ _),
      by simp [ZMod.coe_unitOfCoprime, ZMod.val_natCast_of_lt hj_lt]⟩
  · -- h: f values agree (trivially rfl)
    intro _ _
    rfl

/--
Stage 3a-1 の product-free wrapper:
chosen factor の整数 norm を、`(Finset.range p).erase 0` 上の cyclotomic factor 積へ持ち上げる。

ここではまだ `GN` への書き換えはしないため、full product identity は不要。
-/
theorem chosenCyclotomicLinearFactor_norm_eq_prod_range_erase_zero_of_firstCase_of_pack_thin
    {K : Type u} [Field K] [NumberField K] [CharZero K]
    {p y z : ℕ} [hp : Fact p.Prime] [IsCyclotomicExtension {p} ℚ K]
    {ζ : K} (hζ : IsPrimitiveRoot ζ p) :
    (((Algebra.norm ℤ (chosenCyclotomicLinearFactorInRingOfIntegers hζ y z) : ℚ) : K)) =
      ∏ j ∈ (Finset.range p).erase 0,
        ((cyclotomicLinearFactorInRingOfIntegers hζ y z j : 𝓞 K) : K) := by
  let factor := cyclotomicLinearFactorInRingOfIntegers hζ y z
  have h_norm :=
    chosenCyclotomicLinearFactor_norm_eq_prod_units_of_firstCase_of_pack_thin hζ
      (K := K) (p := p) (y := y) (z := z)
  have h_bridge :=
    prod_units_zmod_eq_prod_range_erase_zero (p := p)
      (fun j => ((factor j : 𝓞 K) : K))
  simpa [factor] using h_norm.trans h_bridge

/--
Stage 3a-2 の concrete core:
first-case pack-thin 文脈では、nontrivial cyclotomic linear factor 全体の積は
そのまま `GN p (z - y) y` に一致する。

これは `hProduct` と `x^p = gap * GN` を `gap` で cancel しただけの薄い補題で、
norm 計算へ入る前の product-level rewriting を担当する。
-/
theorem cyclotomicNontrivialFactorProduct_eq_GN_of_firstCase_of_pack_thin
    {K : Type u} [Field K] [NumberField K] [CharZero K]
    {p x y z : ℕ} [hp : Fact p.Prime] [IsCyclotomicExtension {p} ℚ K]
    {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    (hpack : PrimeGe5CounterexamplePack p x y z)
    {gap : ℕ} (hgap_eq : (z : 𝓞 K) - (y : 𝓞 K) = (gap : 𝓞 K))
    (hFirstCase : ¬ p ∣ gap)
    (hProduct : CyclotomicLinearFactorProductEqInRingOfIntegers
      (hζ := hζ) (x := x) (y := y) (z := z)) :
    ∏ j ∈ (Finset.range p).erase 0,
        cyclotomicLinearFactorInRingOfIntegers hζ y z j =
      (GN p gap y : 𝓞 K) := by
  let factor : ℕ → 𝓞 K := cyclotomicLinearFactorInRingOfIntegers hζ y z
  have hgap_nat : gap = z - y := by
    apply Nat.cast_injective (R := K)
    simpa [Nat.cast_sub hpack.hyz] using
      (congrArg (fun t : 𝓞 K => ((t : 𝓞 K) : K)) hgap_eq).symm
  have hzero_mem : 0 ∈ Finset.range p := by
    exact Finset.mem_range.mpr hp.out.pos
  have hfactor_zero : factor 0 = (gap : 𝓞 K) := by
    simpa [factor, cyclotomicLinearFactorInRingOfIntegers, pow_zero] using hgap_eq
  have hxpow_nat_gap :
      x ^ p = gap * GN p gap y := by
    simpa [PrimeGe5CounterexamplePack.gap, hgap_nat] using hpack.xpow_eq_gap_mul_GN
  have hxpow_eq_gap_mul_gn_gap :
      (x : 𝓞 K) ^ p = (gap : 𝓞 K) * (GN p gap y : 𝓞 K) := by
    calc
      (x : 𝓞 K) ^ p = ((x ^ p : ℕ) : 𝓞 K) := by simp
      _ = ((gap * GN p gap y : ℕ) : 𝓞 K) := by exact_mod_cast hxpow_nat_gap
      _ = (gap : 𝓞 K) * (GN p gap y : 𝓞 K) := by simp [Nat.cast_mul]
  have hgap_ne_zero_nat : gap ≠ 0 := by
    intro hgap0
    exact hFirstCase (hgap0 ▸ dvd_zero p)
  have hgap_ne_zero : (gap : 𝓞 K) ≠ 0 := by
    exact_mod_cast hgap_ne_zero_nat
  have hfull :
      (gap : 𝓞 K) * ∏ j ∈ (Finset.range p).erase 0, factor j = (x : 𝓞 K) ^ p := by
    calc
      (gap : 𝓞 K) * ∏ j ∈ (Finset.range p).erase 0, factor j
          = factor 0 * ∏ j ∈ (Finset.range p).erase 0, factor j := by
              rw [hfactor_zero]
      _ = ∏ j ∈ Finset.range p, factor j := by
            simpa [factor] using
              (Finset.mul_prod_erase (s := Finset.range p) (f := factor) hzero_mem)
      _ = (x : 𝓞 K) ^ p := hProduct
  have hprod_gap :
      ∏ j ∈ (Finset.range p).erase 0, factor j = (GN p gap y : 𝓞 K) := by
    exact mul_left_cancel₀ hgap_ne_zero (hfull.trans hxpow_eq_gap_mul_gn_gap)
  exact hprod_gap

/--
Stage 3a-2 の quotient 版:
nontrivial cyclotomic linear factor 全体の積を、差冪商
`((z^p - y^p) / (z - y))` の既存 shorthand へ寄せる。
-/
theorem cyclotomicNontrivialFactorProduct_eq_quotientPrimePow_of_firstCase_of_pack_thin
    {K : Type u} [Field K] [NumberField K] [CharZero K]
    {p x y z : ℕ} [hp : Fact p.Prime] [IsCyclotomicExtension {p} ℚ K]
    {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    (hpack : PrimeGe5CounterexamplePack p x y z)
    {gap : ℕ} (hgap_eq : (z : 𝓞 K) - (y : 𝓞 K) = (gap : 𝓞 K))
    (hFirstCase : ¬ p ∣ gap)
    (hProduct : CyclotomicLinearFactorProductEqInRingOfIntegers
      (hζ := hζ) (x := x) (y := y) (z := z)) :
    ∏ j ∈ (Finset.range p).erase 0,
        cyclotomicLinearFactorInRingOfIntegers hζ y z j =
      (DkMath.NumberTheory.GcdDiffPow.quotientPrimePow z y p : 𝓞 K) := by
  have hgap_nat : gap = z - y := by
    apply Nat.cast_injective (R := K)
    simpa [Nat.cast_sub hpack.hyz] using
      (congrArg (fun t : 𝓞 K => ((t : 𝓞 K) : K)) hgap_eq).symm
  calc
    ∏ j ∈ (Finset.range p).erase 0, cyclotomicLinearFactorInRingOfIntegers hζ y z j
        = (GN p gap y : 𝓞 K) :=
            cyclotomicNontrivialFactorProduct_eq_GN_of_firstCase_of_pack_thin
              (K := K) (p := p) (x := x) (y := y) (z := z)
              hζ hpack hgap_eq hFirstCase hProduct
    _ = (DkMath.NumberTheory.GcdDiffPow.quotientPrimePow z y p : 𝓞 K) := by
          rw [hgap_nat, DkMath.NumberTheory.Gcd.quotientPrimePow_eq_gn_gap hp.out hpack.hyz_lt]
          simp [DkMath.CosmicFormulaBinom.GN]

/--
Stage 3 前半: first-case pack-thin 文脈で、chosen linear factor の整数ノルムを
`GN p (z - y) y` へ同定する target。

ここで新しい数論はまだ入れず、norm 計算本体を独立責務として切り出す。
-/
abbrev CyclotomicNormEqGNFirstCasePackThinTarget : Prop :=
  ∀ {K : Type u} [Field K] [NumberField K] [CharZero K],
    ∀ {p x y z : ℕ} [Fact p.Prime] [IsCyclotomicExtension {p} ℚ K],
    ∀ {ζ : K},
    (hζ : IsPrimitiveRoot ζ p) →
    PrimeGe5CounterexamplePack p x y z →
    ∀ {gap : ℕ},
      (z : 𝓞 K) - (y : 𝓞 K) = (gap : 𝓞 K) →
      ¬ p ∣ gap →
      ChosenCyclotomicLinearFactorNonzeroInRingOfIntegers (hζ := hζ)
        (y := y) (z := z) →
      ∀ {β unitFactor : 𝓞 K},
        IsUnit unitFactor →
        chosenCyclotomicLinearFactorInRingOfIntegers hζ y z =
          unitFactor * β ^ p →
        Algebra.norm ℤ
            (chosenCyclotomicLinearFactorInRingOfIntegers hζ y z) =
          (GN p (z - y) y : ℤ)

/--
`CyclotomicNormEqGNFirstCasePackThinTarget` の concrete 化。

direct route で、chosen factor の整数ノルムを
そのまま `GN p (z - y) y` へ同定する。

この concrete theorem 自体は、もはや `hProduct` を使わない。
-/
theorem cyclotomicNormEqGN_concrete_firstCase_packThin :
    CyclotomicNormEqGNFirstCasePackThinTarget.{u} := by
  intro K _ _ _ p x y z _ _ ζ hζ hpack gap hgap_eq hFirstCase hLinNe
    β unitFactor _ _
  simpa [chosenCyclotomicLinearFactorInRingOfIntegers, Nat.cast_sub hpack.hyz] using
    (chosenCyclotomicLinearFactor_norm_eq_gn_direct
      (K := K) (p := p) (z := z) (y := y) hζ hpack.hy0 hpack.hyz_lt)

/--
Stage 3 後半: first-case pack-thin 文脈で、
`z - ζy = unitFactor * β^p` と norm 計算結果から
`GN p (z - y) y` が整数の `p` 乗になることを回収する target。

unit norm 吸収と `p` 乗性の責務だけをここへ隔離する。
-/
abbrev CyclotomicNormUnitAbsorbFirstCasePackThinTarget : Prop :=
  ∀ {K : Type u} [Field K] [NumberField K] [CharZero K],
    ∀ {p x y z : ℕ} [Fact p.Prime] [IsCyclotomicExtension {p} ℚ K],
    ∀ {ζ : K},
    (hζ : IsPrimitiveRoot ζ p) →
    PrimeGe5CounterexamplePack p x y z →
    ∀ {gap : ℕ},
      (z : 𝓞 K) - (y : 𝓞 K) = (gap : 𝓞 K) →
      ¬ p ∣ gap →
      ChosenCyclotomicLinearFactorNonzeroInRingOfIntegers (hζ := hζ)
        (y := y) (z := z) →
      ∀ {β unitFactor : 𝓞 K},
        IsUnit unitFactor →
        chosenCyclotomicLinearFactorInRingOfIntegers hζ y z =
          unitFactor * β ^ p →
        Algebra.norm ℤ
            (chosenCyclotomicLinearFactorInRingOfIntegers hζ y z) =
          (GN p (z - y) y : ℤ) →
        ∃ s : ℕ, GN p (z - y) y = s ^ p

/--
Unit normalization で得た `z - ζy = unitFactor * β^p` に norm をかけると、
そのまま `norm(unitFactor) * norm(β)^p` へ分解できる。
-/
theorem norm_eq_normUnit_mul_normPow_of_eq_unit_mul_pow
    {K : Type u} [Field K] [NumberField K] [CharZero K]
    {p y z : ℕ} [Fact p.Prime] [IsCyclotomicExtension {p} ℚ K]
    {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    {β unitFactor : 𝓞 K}
    (hEq : chosenCyclotomicLinearFactorInRingOfIntegers hζ y z = unitFactor * β ^ p) :
    Algebra.norm ℤ (chosenCyclotomicLinearFactorInRingOfIntegers hζ y z) =
      Algebra.norm ℤ unitFactor * (Algebra.norm ℤ β) ^ p := by
  rw [hEq, map_mul, map_pow]

/--
`CyclotomicNormUnitAbsorbFirstCasePackThinTarget` の concrete 化。

`norm = GN` を既に得たあと、unit norm を `Int.natAbs` で吸収して
自然数 witness を回収する。
-/
theorem cyclotomicNormUnitAbsorb_concrete_firstCase_packThin :
    CyclotomicNormUnitAbsorbFirstCasePackThinTarget.{u} := by
  intro K _ _ _ p x y z _ _ ζ hζ hpack gap hgap_eq hFirstCase hLinNe
    β unitFactor hUnit hEq hNorm
  have hNormMul :=
    norm_eq_normUnit_mul_normPow_of_eq_unit_mul_pow
      (K := K) (p := p) (y := y) (z := z) (hζ := hζ) (β := β)
      (unitFactor := unitFactor) hEq
  have hNormUnit : IsUnit (Algebra.norm ℤ unitFactor) :=
    IsUnit.map (Algebra.norm ℤ) hUnit
  have hNormGN :
      ((GN p (z - y) y : ℕ) : ℤ) =
        Algebra.norm ℤ (chosenCyclotomicLinearFactorInRingOfIntegers hζ y z) := by
    simpa [← Nat.cast_sub hpack.hyz] using hNorm.symm
  have hEqInt :
      ((GN p (z - y) y : ℕ) : ℤ) =
        Algebra.norm ℤ unitFactor * (Algebra.norm ℤ β) ^ p := by
    exact hNormGN.trans hNormMul
  simpa using
    (DkMath.NumberTheory.Gcd.nat_exists_pow_of_intEq_unit_mul_pow
      (n := GN p (z - y) y) (p := p)
      (unitFactor := Algebra.norm ℤ unitFactor)
      (m := Algebra.norm ℤ β)
      hNormUnit hEqInt)

/--
Stage 3 の最初の concrete 境界。

first-case pack-thin 文脈から、最終 descent existence に飛ぶ前に
まず `GN p (z - y) y` が整数の `p` 乗になることだけを返す。
-/
abbrev CyclotomicNormGNPowerFirstCasePackThinTarget : Prop :=
  ∀ {K : Type u} [Field K] [NumberField K] [CharZero K],
    ∀ {p x y z : ℕ} [Fact p.Prime] [IsCyclotomicExtension {p} ℚ K],
    ∀ {ζ : K},
    (hζ : IsPrimitiveRoot ζ p) →
    PrimeGe5CounterexamplePack p x y z →
    ∀ {gap : ℕ},
      (z : 𝓞 K) - (y : 𝓞 K) = (gap : 𝓞 K) →
      ¬ p ∣ gap →
      ChosenCyclotomicLinearFactorNonzeroInRingOfIntegers (hζ := hζ)
        (y := y) (z := z) →
      CyclotomicLinearFactorProductEqInRingOfIntegers (hζ := hζ)
        (x := x) (y := y) (z := z) →
      ∃ s : ℕ, GN p (z - y) y = s ^ p

/--
first-case pack-thin の Stage 3 配線:
norm 計算 target と unit norm 吸収 target を合成して、
`GN p (z - y) y` の `p` 乗性を返す。

これで Stage 3 の open は、honest に 2 本へ分離される。
-/
theorem cyclotomicNormGNPower_of_firstCase_of_pack_thin
    (hKill : CyclotomicPTorsionAnnihilationTarget.{u})
  (hNormEqGN : CyclotomicNormEqGNFirstCasePackThinTarget.{u})
  (hUnitAbsorb : CyclotomicNormUnitAbsorbFirstCasePackThinTarget.{u})
    {K : Type u} [Field K] [NumberField K] [CharZero K]
    {p x y z : ℕ} [Fact p.Prime] [IsCyclotomicExtension {p} ℚ K]
    {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    (hpack : PrimeGe5CounterexamplePack p x y z)
    {gap : ℕ} (hgap_eq : (z : 𝓞 K) - (y : 𝓞 K) = (gap : 𝓞 K))
    (hFirstCase : ¬ p ∣ gap)
    (hLinNe : ChosenCyclotomicLinearFactorNonzeroInRingOfIntegers (hζ := hζ)
      (y := y) (z := z))
    (hProduct : CyclotomicLinearFactorProductEqInRingOfIntegers
      (hζ := hζ) (x := x) (y := y) (z := z)) :
    ∃ s : ℕ, GN p (z - y) y = s ^ p := by
  obtain ⟨β, unitFactor, hUnit, hEq⟩ :=
    cyclotomicUnitNormalization_of_firstCase_of_pack_thin
      (K := K) (p := p) (x := x) (y := y) (z := z)
      hζ hpack hgap_eq hFirstCase hLinNe hProduct hKill
  have hNorm :
      Algebra.norm ℤ (chosenCyclotomicLinearFactorInRingOfIntegers hζ y z) =
        (GN p (z - y) y : ℤ) :=
    hNormEqGN hζ hpack hgap_eq hFirstCase hLinNe hUnit hEq
  exact hUnitAbsorb hζ hpack hgap_eq hFirstCase hLinNe hUnit hEq hNorm

/--
first-case pack-thin での Stage 3 concrete wrapper。

既に concrete 化された `NormEqGN` と `UnitAbsorb` を束ねて、
`GN p (z - y) y = s^p` を assumption-free に返す。
-/
theorem cyclotomicNormGNPower_concrete_firstCase_packThin
    (hKill : CyclotomicPTorsionAnnihilationTarget.{u}) :
    CyclotomicNormGNPowerFirstCasePackThinTarget.{u} := by
  intro K _ _ _ p x y z _ _ ζ hζ hpack gap hgap_eq hFirstCase hLinNe hProduct
  exact cyclotomicNormGNPower_of_firstCase_of_pack_thin
    hKill
    cyclotomicNormEqGN_concrete_firstCase_packThin
    cyclotomicNormUnitAbsorb_concrete_firstCase_packThin
    hζ hpack hgap_eq hFirstCase hLinNe hProduct

/--
`GN p (z - y) y` が `p` 乗になるなら、既存の no-pow target と即座に衝突する。

`TriominoCosmicBodyInvariant` への bridge を import せずに、
Kummer 側では最小の abstract contradiction interface だけを固定する。
-/
theorem false_of_cyclotomicNormGNPower_of_firstCase_of_pack_thin
    (hKill : CyclotomicPTorsionAnnihilationTarget.{u})
  (hNormEqGN : CyclotomicNormEqGNFirstCasePackThinTarget.{u})
  (hUnitAbsorb : CyclotomicNormUnitAbsorbFirstCasePackThinTarget.{u})
    (hNoPow :
      ∀ {p x y z : ℕ}, PrimeGe5CounterexamplePack p x y z →
        ¬ ∃ s : ℕ, GN p (z - y) y = s ^ p) :
    ∀ {K : Type u} [Field K] [NumberField K] [CharZero K],
      ∀ {p x y z : ℕ} [Fact p.Prime] [IsCyclotomicExtension {p} ℚ K],
      ∀ {ζ : K},
      (hζ : IsPrimitiveRoot ζ p) →
      PrimeGe5CounterexamplePack p x y z →
      ∀ {gap : ℕ},
        (z : 𝓞 K) - (y : 𝓞 K) = (gap : 𝓞 K) →
        ¬ p ∣ gap →
        ChosenCyclotomicLinearFactorNonzeroInRingOfIntegers (hζ := hζ)
          (y := y) (z := z) →
        CyclotomicLinearFactorProductEqInRingOfIntegers (hζ := hζ)
          (x := x) (y := y) (z := z) →
        False := by
  intro K _ _ _ p x y z _ _ ζ hζ hpack gap hgap_eq hFirstCase hLinNe hProduct
  obtain ⟨s, hs⟩ :=
    cyclotomicNormGNPower_of_firstCase_of_pack_thin
      hKill hNormEqGN hUnitAbsorb hζ hpack hgap_eq hFirstCase hLinNe hProduct
  exact hNoPow hpack ⟨s, hs⟩

/--
concrete `NormEqGN` / `UnitAbsorb` を使った first-case contradiction wrapper。
-/
theorem false_of_cyclotomicNormGNPower_concrete_firstCase_pack_thin
    (hKill : CyclotomicPTorsionAnnihilationTarget.{u})
    (hNoPow :
      ∀ {p x y z : ℕ}, PrimeGe5CounterexamplePack p x y z →
        ¬ ∃ s : ℕ, GN p (z - y) y = s ^ p) :
    ∀ {K : Type u} [Field K] [NumberField K] [CharZero K],
      ∀ {p x y z : ℕ} [Fact p.Prime] [IsCyclotomicExtension {p} ℚ K],
      ∀ {ζ : K},
      (hζ : IsPrimitiveRoot ζ p) →
      PrimeGe5CounterexamplePack p x y z →
      ∀ {gap : ℕ},
        (z : 𝓞 K) - (y : 𝓞 K) = (gap : 𝓞 K) →
        ¬ p ∣ gap →
        ChosenCyclotomicLinearFactorNonzeroInRingOfIntegers (hζ := hζ)
          (y := y) (z := z) →
        CyclotomicLinearFactorProductEqInRingOfIntegers (hζ := hζ)
          (x := x) (y := y) (z := z) →
        False := by
  exact false_of_cyclotomicNormGNPower_of_firstCase_of_pack_thin
    hKill
    cyclotomicNormEqGN_concrete_firstCase_packThin
    cyclotomicNormUnitAbsorb_concrete_firstCase_packThin
    hNoPow

/--
Stage 1 の 2-factor route がまず返すべき tail-product equality target。

chosen linear factor と complementary tail の積が `(x)^p` を生成する ideal に等しいことだけを表す。
-/
abbrev CyclotomicTailLinearFactorMulEqSpanPowTarget : Prop :=
  ∀ {R : Type*} [CommRing R] [IsDomain R] [IsDedekindDomain R],
    ∀ ctx : CyclotomicLocalFactorizationContext R,
    ∀ {p x y z : ℕ}, PrimeGe5CounterexamplePack p x y z →
    ∀ {q : ℕ}, Nat.Prime q →
      q ∣ x →
      q ≠ p →
      q ∣ (z - y) →
      ∃ tail : R,
        Ideal.span ({tail} : Set R) * Ideal.span ({(z : R) - ctx.zeta * (y : R)} : Set R) =
          Ideal.span ({(x : R)} : Set R) ^ ctx.p

/--
Stage 1 の 2-factor route で必要な cyclotomic-specific coprimality target。

chosen linear factor ideal と complementary tail ideal が互いに素であることを表す。
-/
abbrev CyclotomicTailLinearFactorCoprimeTarget : Prop :=
  ∀ {R : Type*} [CommRing R] [IsDomain R] [IsDedekindDomain R],
    ∀ ctx : CyclotomicLocalFactorizationContext R,
    ∀ {tail : R} {p x y z : ℕ}, PrimeGe5CounterexamplePack p x y z →
    ∀ {q : ℕ}, Nat.Prime q →
      q ∣ x →
      q ≠ p →
      q ∣ (z - y) →
      IsCoprime (Ideal.span ({tail} : Set R)) (Ideal.span ({(z : R) - ctx.zeta * (y : R)} : Set R))

/--
actual cyclotomic coprimality を供給するための full family witness target。

chosen factor を含む finite family と、その差の unit 性・tail decomposition を supply すれば、
chosen factor ideal と tail ideal の互いに素性は generic に回収できる。
-/
abbrev CyclotomicTailPairwiseUnitWitnessTarget : Prop :=
  ∀ {R : Type u} [CommRing R] [IsDomain R] [IsDedekindDomain R],
    ∀ ctx : CyclotomicLocalFactorizationContext R,
    ∀ {tail : R} {p x y z : ℕ}, PrimeGe5CounterexamplePack p x y z →
    ∀ {q : ℕ}, Nat.Prime q →
      q ∣ x →
      q ≠ p →
      q ∣ (z - y) →
      ∃ n : ℕ, ∃ i : Fin n, ∃ α : Fin n → R,
        α i = ctx.zeta ∧
        Ideal.span ({tail} : Set R) =
          ∏ j ∈ (Finset.univ.erase i), Ideal.span ({(z : R) - α j * (y : R)} : Set R) ∧
        ∀ a : Fin n, ∀ b : Fin n, a ≠ b → IsUnit (α b * (y : R) - α a * (y : R))

/--
pairwise unit-difference witness から、actual cyclotomic coprimality target を回収する theorem。

review-025 の「残る本丸は actual coprimality 供給」という見立てを、
さらに `full family witness` と `generic receiver` へ分解する。
-/
theorem cyclotomicTailLinearFactorCoprime_of_pairwiseUnitWitness
    (hWitness :
      ∀ {R : Type u} [CommRing R] [IsDomain R] [IsDedekindDomain R],
        ∀ ctx : CyclotomicLocalFactorizationContext R,
        ∀ {tail : R} {p x y z : ℕ}, PrimeGe5CounterexamplePack p x y z →
        ∀ {q : ℕ}, Nat.Prime q →
          q ∣ x →
          q ≠ p →
          q ∣ (z - y) →
          ∃ n : ℕ, ∃ i : Fin n, ∃ α : Fin n → R,
            α i = ctx.zeta ∧
            Ideal.span ({tail} : Set R) =
              ∏ j ∈ (Finset.univ.erase i), Ideal.span ({(z : R) - α j * (y : R)} : Set R) ∧
            ∀ a : Fin n, ∀ b : Fin n, a ≠ b → IsUnit (α b * (y : R) - α a * (y : R))) :
    CyclotomicTailLinearFactorCoprimeTarget.{u} := by
  intro R _ _ _ ctx tail p x y z hpack q hq hqx hqne hgap
  obtain ⟨n, i, α, hAlpha, hTail, hUnits⟩ :=
    hWitness (R := R) (ctx := ctx) (tail := tail) (p := p) (x := x) (y := y) (z := z) hpack
      (q := q) hq hqx hqne hgap
  have hcopProd :
      IsCoprime (Ideal.span ({(z : R) - α i * (y : R)} : Set R))
        (∏ j ∈ (Finset.univ.erase i), Ideal.span ({(z : R) - α j * (y : R)} : Set R)) :=
    linearFactorIdealIsCoprimeProdEraseOfPairwiseMulSubIsUnit
      (z := (z : R)) (y := (y : R)) (s := Finset.univ) (i := i) (by simp) (by
        intro a ha b hb hab
        exact hUnits a b hab)
  have hcopProd' :
      IsCoprime (∏ j ∈ (Finset.univ.erase i), Ideal.span ({(z : R) - α j * (y : R)} : Set R))
        (Ideal.span ({(z : R) - α i * (y : R)} : Set R)) := hcopProd.symm
  have hchosen : Ideal.span ({(z : R) - ctx.zeta * (y : R)} : Set R) =
      Ideal.span ({(z : R) - α i * (y : R)} : Set R) := by
    rw [hAlpha]
  simpa [hTail, hchosen] using hcopProd'

/--
Stage 1 の 2-factor route で `(x)` が nonzero ideal を生成することを表す target。

actual cyclotomic ring では通常 `(x : R) ≠ 0` から従うが、generic API としては別 target にしておく。
-/
abbrev CyclotomicXSpanNonzeroTarget : Prop :=
  ∀ {R : Type*} [CommRing R] [IsDomain R] [IsDedekindDomain R],
    ∀ _ctx : CyclotomicLocalFactorizationContext R,
    ∀ {p x y z : ℕ}, PrimeGe5CounterexamplePack p x y z →
    ∀ {q : ℕ}, Nat.Prime q →
      q ∣ x →
      q ≠ p →
      q ∣ (z - y) →
      Ideal.span ({(x : R)} : Set R) ≠ ⊥

/--
actual cyclotomic setting で local context の指数が counterexample-pack の指数と一致することを表す target。

Stage 1 の product equality を local factorization theorem から回収するには、この橋が必要になる。
-/
abbrev CyclotomicLocalExponentAgreementTarget : Prop :=
  ∀ {R : Type u} [CommRing R] [IsDomain R] [IsDedekindDomain R],
    ∀ ctx : CyclotomicLocalFactorizationContext R,
    ∀ {p x y z : ℕ}, PrimeGe5CounterexamplePack p x y z →
    ∀ {q : ℕ}, Nat.Prime q →
      q ∣ x →
      q ≠ p →
      q ∣ (z - y) →
      ctx.p = p

/--
`CharZero` のもとで `(x)` 非零を供給する target。

`hx0 : x ≠ 0` から `(x : R) ≠ 0` は任意の domain では従わないので、
ここでは honest に `CharZero R` を要求した variant を分けておく。
-/
abbrev CyclotomicXSpanNonzeroCharZeroTarget : Prop :=
  ∀ {R : Type u} [CommRing R] [IsDomain R] [IsDedekindDomain R] [CharZero R],
    ∀ _ctx : CyclotomicLocalFactorizationContext R,
    ∀ {p x y z : ℕ}, PrimeGe5CounterexamplePack p x y z →
    ∀ {q : ℕ}, Nat.Prime q →
      q ∣ x →
      q ≠ p →
      q ∣ (z - y) →
      Ideal.span ({(x : R)} : Set R) ≠ ⊥

/--
指数一致 `ctx.p = p` が与えられれば、counterexample pack から tail-product equality target を actual に供給できる。

review-024 が述べる「product equality は local factorization theorem の延長として近い」ことを
theorem-level に固定する。
-/
theorem cyclotomicTailLinearFactorMulEqSpanPow_of_exponentAgreement
    (hCtxEq : CyclotomicLocalExponentAgreementTarget.{u}) :
    ∀ {R : Type u} [CommRing R] [IsDomain R] [IsDedekindDomain R],
      ∀ ctx : CyclotomicLocalFactorizationContext R,
      ∀ {p x y z : ℕ}, PrimeGe5CounterexamplePack p x y z →
      ∀ {q : ℕ}, Nat.Prime q →
        q ∣ x →
        q ≠ p →
        q ∣ (z - y) →
        ∃ tail : R,
          Ideal.span ({tail} : Set R) * Ideal.span ({(z : R) - ctx.zeta * (y : R)} : Set R) =
            Ideal.span ({(x : R)} : Set R) ^ ctx.p := by
  intro R _ _ _ ctx p x y z hpack q hq hqx hqne hgap
  refine ⟨∑ i ∈ Finset.range ctx.p, (z : R) ^ i * (ctx.zeta * (y : R)) ^ (ctx.p - 1 - i), ?_⟩
  have hctx : ctx.p = p :=
    hCtxEq (R := R) (ctx := ctx) (p := p) (x := x) (y := y) (z := z) hpack
      (q := q) hq hqx hqne hgap
  have hEqR : (x : R) ^ ctx.p + (y : R) ^ ctx.p = (z : R) ^ ctx.p := by
    subst hctx
    simpa using congrArg (fun n : ℕ => (n : R)) hpack.hEq
  exact ctx.linear_factor_ideal_mul_eq_span_pow_of_add_pow_eq
    (x := (x : R)) (y := (y : R)) (z := (z : R)) hEqR

/--
指数一致 `ctx.p = p` が与えられれば、`ctx.p ≠ 0` は pack の prime 性から actual に供給できる。
-/
theorem cyclotomicLocalExponentNonzero_of_exponentAgreement
    (hCtxEq : CyclotomicLocalExponentAgreementTarget.{u}) :
    CyclotomicLocalExponentNonzeroTarget.{u} := by
  intro R _ _ _ ctx p x y z hpack q hq hqx hqne hgap
  have hctx : ctx.p = p :=
    hCtxEq (R := R) (ctx := ctx) (p := p) (x := x) (y := y) (z := z) hpack
      (q := q) hq hqx hqne hgap
  rw [hctx]
  exact hpack.hp.ne_zero

/--
`CharZero` のもとでは、counterexample pack の `hx0` から `(x)` 非零を actual に供給できる。

generic `CyclotomicXSpanNonzeroTarget` をそのまま埋めるのは impossible な場合があるので、
honest な `CharZero` variant として切り出す。
-/
theorem cyclotomicXSpanNonzero_of_counterexamplePack_of_charZero :
    CyclotomicXSpanNonzeroCharZeroTarget.{u} := by
  intro R _ _ _ _ _ctx p x y z hpack q _hq _hqx _hqne _hgap hbot
  have hxR0 : (x : R) = 0 := Ideal.span_singleton_eq_bot.mp hbot
  exact hpack.hx0 (Nat.cast_eq_zero.mp hxR0)

/--
tail-product equality + coprimality + `(x)` 非零から、Stage 1 explicit equality target を回収する。

review-023 の 2-factor route をそのまま theorem 化した exact composition。
-/
theorem cyclotomicLinearFactorSpanEqPow_of_tailFactorCoprime
    (hMul :
      ∀ {R : Type u} [CommRing R] [IsDomain R] [IsDedekindDomain R],
        ∀ ctx : CyclotomicLocalFactorizationContext R,
        ∀ {p x y z : ℕ}, PrimeGe5CounterexamplePack p x y z →
        ∀ {q : ℕ}, Nat.Prime q →
          q ∣ x →
          q ≠ p →
          q ∣ (z - y) →
          ∃ tail : R,
            Ideal.span ({tail} : Set R) * Ideal.span ({(z : R) - ctx.zeta * (y : R)} : Set R) =
              Ideal.span ({(x : R)} : Set R) ^ ctx.p)
    (hCoprime :
      ∀ {R : Type u} [CommRing R] [IsDomain R] [IsDedekindDomain R],
        ∀ ctx : CyclotomicLocalFactorizationContext R,
        ∀ {tail : R} {p x y z : ℕ}, PrimeGe5CounterexamplePack p x y z →
        ∀ {q : ℕ}, Nat.Prime q →
          q ∣ x →
          q ≠ p →
          q ∣ (z - y) →
          IsCoprime (Ideal.span ({tail} : Set R)) (Ideal.span ({(z : R) - ctx.zeta * (y : R)} : Set R)))
    (hX_ne :
      ∀ {R : Type u} [CommRing R] [IsDomain R] [IsDedekindDomain R],
        ∀ _ctx : CyclotomicLocalFactorizationContext R,
        ∀ {p x y z : ℕ}, PrimeGe5CounterexamplePack p x y z →
        ∀ {q : ℕ}, Nat.Prime q →
          q ∣ x →
          q ≠ p →
          q ∣ (z - y) →
          Ideal.span ({(x : R)} : Set R) ≠ ⊥) :
    ∀ {R : Type u} [CommRing R] [IsDomain R] [IsDedekindDomain R],
      ∀ ctx : CyclotomicLocalFactorizationContext R,
      ∀ {p x y z : ℕ}, PrimeGe5CounterexamplePack p x y z →
      ∀ {q : ℕ}, Nat.Prime q →
        q ∣ x →
        q ≠ p →
        q ∣ (z - y) →
        ∃ K : Ideal R,
          Ideal.span ({(z : R) - ctx.zeta * (y : R)} : Set R) = K ^ ctx.p := by
  intro R _ _ _ ctx p x y z hpack q hq hqx hqne hgap
  obtain ⟨tail, hMulEq⟩ := @hMul R _ _ _ ctx p x y z hpack q hq hqx hqne hgap
  exact linearFactorSpanEqPowOfTailMulEqSpanPowAndIsCoprime
    ctx
    (@hX_ne R _ _ _ ctx p x y z hpack q hq hqx hqne hgap)
    hMulEq
    (@hCoprime R _ _ _ ctx tail p x y z hpack q hq hqx hqne hgap)

/--
Stage 1 の explicit equality / local exponent nonzero / linear-factor nonzero から、
存在形 boundary target を回収する theorem。

review-022 が求める「Stage 1 explicit equality theorem」の直後に差し込む最短の composition。
-/
theorem cyclotomicLinearFactorIdealPthPower_of_spanEqPow
    (hEqPow :
      ∀ {R : Type u} [CommRing R] [IsDomain R] [IsDedekindDomain R],
        ∀ ctx : CyclotomicLocalFactorizationContext R,
        ∀ {p x y z : ℕ}, PrimeGe5CounterexamplePack p x y z →
        ∀ {q : ℕ}, Nat.Prime q →
          q ∣ x →
          q ≠ p →
          q ∣ (z - y) →
          ∃ K : Ideal R,
            Ideal.span ({(z : R) - ctx.zeta * (y : R)} : Set R) = K ^ ctx.p)
    (hPne :
      ∀ {R : Type u} [CommRing R] [IsDomain R] [IsDedekindDomain R],
        ∀ ctx : CyclotomicLocalFactorizationContext R,
        ∀ {p x y z : ℕ}, PrimeGe5CounterexamplePack p x y z →
        ∀ {q : ℕ}, Nat.Prime q →
          q ∣ x →
          q ≠ p →
          q ∣ (z - y) →
          ctx.p ≠ 0)
    (hNonzero :
      ∀ {R : Type u} [CommRing R] [IsDomain R] [IsDedekindDomain R],
        ∀ ctx : CyclotomicLocalFactorizationContext R,
        ∀ {p x y z : ℕ}, PrimeGe5CounterexamplePack p x y z →
        ∀ {q : ℕ}, Nat.Prime q →
          q ∣ x →
          q ≠ p →
          q ∣ (z - y) →
          (z : R) - ctx.zeta * (y : R) ≠ 0)
    (hKill : CyclotomicPTorsionAnnihilationTarget.{u}) :
    ∀ {R : Type u} [CommRing R] [IsDomain R] [IsDedekindDomain R],
      ∀ ctx : CyclotomicLocalFactorizationContext R,
      ∀ {p x y z : ℕ}, PrimeGe5CounterexamplePack p x y z →
      ∀ {q : ℕ}, Nat.Prime q →
        q ∣ x →
        q ≠ p →
        q ∣ (z - y) →
        ∃ I : Ideal R, ∃ _ : I.IsPrincipal,
          Ideal.span ({(z : R) - ctx.zeta * (y : R)} : Set R) = I ^ ctx.p := by
  intro R _ _ _ ctx p x y z hpack q hq hqx hqne hgap
  obtain ⟨K, hEq⟩ := @hEqPow R _ _ _ ctx p x y z hpack q hq hqx hqne hgap
  obtain ⟨J, hJPrincipal, hJpow⟩ :=
    linearFactorIdealPthPowerExistsOfSpanEqPowAndTorsionKill
      ctx
      (hPne (R := R) (ctx := ctx) (p := p) (x := x) (y := y) (z := z) hpack
        (q := q) hq hqx hqne hgap)
      (hNonzero (R := R) (ctx := ctx) (p := p) (x := x) (y := y) (z := z) hpack
        (q := q) hq hqx hqne hgap)
      hEq hKill
  exact ⟨J, hJPrincipal, hJpow⟩

/--
2-factor route の output を、そのまま Stage 1 の存在形 boundary target まで流す wrapper。

Stage 1 → existence boundary の接続点を theorem として明示する。
-/
theorem cyclotomicLinearFactorIdealPthPower_of_tailFactorCoprimeRoute
    (hMul :
      ∀ {R : Type u} [CommRing R] [IsDomain R] [IsDedekindDomain R],
        ∀ ctx : CyclotomicLocalFactorizationContext R,
        ∀ {p x y z : ℕ}, PrimeGe5CounterexamplePack p x y z →
        ∀ {q : ℕ}, Nat.Prime q →
          q ∣ x →
          q ≠ p →
          q ∣ (z - y) →
          ∃ tail : R,
            Ideal.span ({tail} : Set R) * Ideal.span ({(z : R) - ctx.zeta * (y : R)} : Set R) =
              Ideal.span ({(x : R)} : Set R) ^ ctx.p)
    (hCoprime :
      ∀ {R : Type u} [CommRing R] [IsDomain R] [IsDedekindDomain R],
        ∀ ctx : CyclotomicLocalFactorizationContext R,
        ∀ {tail : R} {p x y z : ℕ}, PrimeGe5CounterexamplePack p x y z →
        ∀ {q : ℕ}, Nat.Prime q →
          q ∣ x →
          q ≠ p →
          q ∣ (z - y) →
          IsCoprime (Ideal.span ({tail} : Set R)) (Ideal.span ({(z : R) - ctx.zeta * (y : R)} : Set R)))
    (hX_ne :
      ∀ {R : Type u} [CommRing R] [IsDomain R] [IsDedekindDomain R],
        ∀ _ctx : CyclotomicLocalFactorizationContext R,
        ∀ {p x y z : ℕ}, PrimeGe5CounterexamplePack p x y z →
        ∀ {q : ℕ}, Nat.Prime q →
          q ∣ x →
          q ≠ p →
          q ∣ (z - y) →
          Ideal.span ({(x : R)} : Set R) ≠ ⊥)
    (hPne : CyclotomicLocalExponentNonzeroTarget.{u})
    (hNonzero : CyclotomicLinearFactorNonzeroTarget.{u})
    (hKill : CyclotomicPTorsionAnnihilationTarget.{u}) :
    CyclotomicLinearFactorIdealPthPowerTarget.{u} :=
  cyclotomicLinearFactorIdealPthPower_of_spanEqPow
    (cyclotomicLinearFactorSpanEqPow_of_tailFactorCoprime hMul hCoprime hX_ne)
    hPne hNonzero hKill

/--
pack-specialized Stage 2 receiver。

review-017 で狙っている
`span(z - ζy) = I^p ⇒ z - ζy = u * β^p`
の specialized theorem そのもの。
まだ Stage 1 target 自体は placeholder なので、入力には explicit な ideal equality を要求する。
-/
theorem cyclotomicUnitNormalization_of_spanEqPowPrincipal :
    CyclotomicUnitNormalizationPackSpecializationTarget := by
  intro R _ _ _ ctx I _ p x y z _hpack q _hq _hqx _hqne _hgap hSpan
  exact linearFactorEqUnitMulGeneratorPowOfSpanEqPowPrincipal ctx (z : R) (y : R) hSpan

/--
Stage 1 の存在形 boundary target が与えられれば、Stage 2 の pack-specialized unit normalization が従う。

review-018 の提案どおり、Stage 1 → Stage 2 の接続点を存在形にしておくと、
ここはそのまま composition で閉じる。
-/
theorem cyclotomicUnitNormalization_of_existsLinearFactorIdealPthPower
    (hIdeal :
      ∀ {R : Type u} [CommRing R] [IsDomain R] [IsDedekindDomain R],
        ∀ ctx : CyclotomicLocalFactorizationContext R,
        ∀ {p x y z : ℕ}, PrimeGe5CounterexamplePack p x y z →
        ∀ {q : ℕ}, Nat.Prime q →
          q ∣ x →
          q ≠ p →
          q ∣ (z - y) →
          ∃ I : Ideal R, ∃ _ : I.IsPrincipal,
            Ideal.span ({(z : R) - ctx.zeta * (y : R)} : Set R) = I ^ ctx.p) :
    CyclotomicUnitNormalizationTarget.{u} := by
  intro R _ _ _ ctx p x y z hpack q hq hqx hqne hgap
  obtain ⟨I, hIPrincipal, hSpan⟩ := @hIdeal R _ _ _ ctx p x y z hpack q hq hqx hqne hgap
  obtain ⟨u, huUnit, huEq⟩ :=
    cyclotomicUnitNormalization_of_spanEqPowPrincipal
      (R := R) (ctx := ctx) (I := I) (p := p) (x := x) (y := y) (z := z)
      hpack hq hqx hqne hgap hSpan
  refine ⟨Submodule.IsPrincipal.generator I, u, huUnit, ?_⟩
  simpa using huEq

/--
Stage 1 の explicit equality theorem と companion targets から、
concrete な Stage 2 target を直接得る composition theorem。

新しい数学はなく、Stage 1 → existence boundary → Stage 2 receiver の合成だけを担う。
-/
theorem cyclotomicUnitNormalization_of_linearFactorSpanEqPow
    (hEqPow :
      ∀ {R : Type u} [CommRing R] [IsDomain R] [IsDedekindDomain R],
        ∀ ctx : CyclotomicLocalFactorizationContext R,
        ∀ {p x y z : ℕ}, PrimeGe5CounterexamplePack p x y z →
        ∀ {q : ℕ}, Nat.Prime q →
          q ∣ x →
          q ≠ p →
          q ∣ (z - y) →
          ∃ K : Ideal R,
            Ideal.span ({(z : R) - ctx.zeta * (y : R)} : Set R) = K ^ ctx.p)
    (hPne : CyclotomicLocalExponentNonzeroTarget.{u})
    (hNonzero : CyclotomicLinearFactorNonzeroTarget.{u})
    (hKill : CyclotomicPTorsionAnnihilationTarget.{u}) :
    CyclotomicUnitNormalizationTarget.{u} :=
  cyclotomicUnitNormalization_of_existsLinearFactorIdealPthPower
    (cyclotomicLinearFactorIdealPthPower_of_spanEqPow hEqPow
      (fun {R} [_cR : CommRing R] [_dR : IsDomain R] [_ddR : IsDedekindDomain R] ctx
        {p x y z} hpack {q} hq hqx hqne hgap =>
          hPne (R := R) (ctx := ctx) (p := p) (x := x) (y := y) (z := z) hpack
            (q := q) hq hqx hqne hgap)
      (fun {R} [_cR : CommRing R] [_dR : IsDomain R] [_ddR : IsDedekindDomain R] ctx
        {p x y z} hpack {q} hq hqx hqne hgap =>
          hNonzero (R := R) (ctx := ctx) (p := p) (x := x) (y := y) (z := z) hpack
            (q := q) hq hqx hqne hgap)
      hKill)

/--
2-factor route の output を、そのまま concrete Stage 2 target まで流す wrapper。

actual cyclotomic-specific coprimality theorem が入れば、この theorem を通して Stage 2 が閉じる。
-/
theorem cyclotomicUnitNormalization_of_tailFactorCoprimeRoute
    (hMul :
      ∀ {R : Type u} [CommRing R] [IsDomain R] [IsDedekindDomain R],
        ∀ ctx : CyclotomicLocalFactorizationContext R,
        ∀ {p x y z : ℕ}, PrimeGe5CounterexamplePack p x y z →
        ∀ {q : ℕ}, Nat.Prime q →
          q ∣ x →
          q ≠ p →
          q ∣ (z - y) →
          ∃ tail : R,
            Ideal.span ({tail} : Set R) * Ideal.span ({(z : R) - ctx.zeta * (y : R)} : Set R) =
              Ideal.span ({(x : R)} : Set R) ^ ctx.p)
    (hCoprime :
      ∀ {R : Type u} [CommRing R] [IsDomain R] [IsDedekindDomain R],
        ∀ ctx : CyclotomicLocalFactorizationContext R,
        ∀ {tail : R} {p x y z : ℕ}, PrimeGe5CounterexamplePack p x y z →
        ∀ {q : ℕ}, Nat.Prime q →
          q ∣ x →
          q ≠ p →
          q ∣ (z - y) →
          IsCoprime (Ideal.span ({tail} : Set R)) (Ideal.span ({(z : R) - ctx.zeta * (y : R)} : Set R)))
    (hX_ne :
      ∀ {R : Type u} [CommRing R] [IsDomain R] [IsDedekindDomain R],
        ∀ _ctx : CyclotomicLocalFactorizationContext R,
        ∀ {p x y z : ℕ}, PrimeGe5CounterexamplePack p x y z →
        ∀ {q : ℕ}, Nat.Prime q →
          q ∣ x →
          q ≠ p →
          q ∣ (z - y) →
          Ideal.span ({(x : R)} : Set R) ≠ ⊥)
    (hPne : CyclotomicLocalExponentNonzeroTarget.{u})
    (hNonzero : CyclotomicLinearFactorNonzeroTarget.{u})
    (hKill : CyclotomicPTorsionAnnihilationTarget.{u}) :
    CyclotomicUnitNormalizationTarget.{u} :=
  cyclotomicUnitNormalization_of_linearFactorSpanEqPow
    (cyclotomicLinearFactorSpanEqPow_of_tailFactorCoprime hMul hCoprime hX_ne)
    hPne hNonzero hKill

/--
指数一致と pairwise unit-difference witness が与えられれば、
残る actual gap は `(x)` 非零と線型因子非零だけになり、concrete Stage 2 target まで到達できる。

review-025 の分析を theorem-level composition として固定したもの。
-/
theorem cyclotomicUnitNormalization_of_exponentAgreementAndPairwiseUnitWitness
    (hCtxEq : CyclotomicLocalExponentAgreementTarget.{u})
    (hWitness :
      ∀ {R : Type u} [CommRing R] [IsDomain R] [IsDedekindDomain R],
        ∀ ctx : CyclotomicLocalFactorizationContext R,
        ∀ {tail : R} {p x y z : ℕ}, PrimeGe5CounterexamplePack p x y z →
        ∀ {q : ℕ}, Nat.Prime q →
          q ∣ x →
          q ≠ p →
          q ∣ (z - y) →
          ∃ n : ℕ, ∃ i : Fin n, ∃ α : Fin n → R,
            α i = ctx.zeta ∧
            Ideal.span ({tail} : Set R) =
              ∏ j ∈ (Finset.univ.erase i), Ideal.span ({(z : R) - α j * (y : R)} : Set R) ∧
            ∀ a : Fin n, ∀ b : Fin n, a ≠ b → IsUnit (α b * (y : R) - α a * (y : R)))
    (hX_ne :
      ∀ {R : Type u} [CommRing R] [IsDomain R] [IsDedekindDomain R],
        ∀ _ctx : CyclotomicLocalFactorizationContext R,
        ∀ {p x y z : ℕ}, PrimeGe5CounterexamplePack p x y z →
        ∀ {q : ℕ}, Nat.Prime q →
          q ∣ x →
          q ≠ p →
          q ∣ (z - y) →
          Ideal.span ({(x : R)} : Set R) ≠ ⊥)
    (hNonzero : CyclotomicLinearFactorNonzeroTarget.{u})
    (hKill : CyclotomicPTorsionAnnihilationTarget.{u}) :
    CyclotomicUnitNormalizationTarget.{u} :=
  cyclotomicUnitNormalization_of_tailFactorCoprimeRoute
    (cyclotomicTailLinearFactorMulEqSpanPow_of_exponentAgreement hCtxEq)
    (cyclotomicTailLinearFactorCoprime_of_pairwiseUnitWitness hWitness)
    hX_ne
    (cyclotomicLocalExponentNonzero_of_exponentAgreement hCtxEq)
    hNonzero
    hKill

/--
指数一致と pairwise unit-difference witness が与えられれば、
Stage 1 の存在形 boundary target まで concrete に到達できる。

Stage 1 finished 判定を target comment ではなく theorem で固定するための wrapper。
-/
theorem cyclotomicLinearFactorIdealPthPower_of_exponentAgreementAndPairwiseUnitWitness
    (hCtxEq : CyclotomicLocalExponentAgreementTarget.{u})
    (hWitness :
      ∀ {R : Type u} [CommRing R] [IsDomain R] [IsDedekindDomain R],
        ∀ ctx : CyclotomicLocalFactorizationContext R,
        ∀ {tail : R} {p x y z : ℕ}, PrimeGe5CounterexamplePack p x y z →
        ∀ {q : ℕ}, Nat.Prime q →
          q ∣ x →
          q ≠ p →
          q ∣ (z - y) →
          ∃ n : ℕ, ∃ i : Fin n, ∃ α : Fin n → R,
            α i = ctx.zeta ∧
            Ideal.span ({tail} : Set R) =
              ∏ j ∈ (Finset.univ.erase i), Ideal.span ({(z : R) - α j * (y : R)} : Set R) ∧
            ∀ a : Fin n, ∀ b : Fin n, a ≠ b → IsUnit (α b * (y : R) - α a * (y : R)))
    (hX_ne :
      ∀ {R : Type u} [CommRing R] [IsDomain R] [IsDedekindDomain R],
        ∀ _ctx : CyclotomicLocalFactorizationContext R,
        ∀ {p x y z : ℕ}, PrimeGe5CounterexamplePack p x y z →
        ∀ {q : ℕ}, Nat.Prime q →
          q ∣ x →
          q ≠ p →
          q ∣ (z - y) →
          Ideal.span ({(x : R)} : Set R) ≠ ⊥)
    (hNonzero : CyclotomicLinearFactorNonzeroTarget.{u})
    (hKill : CyclotomicPTorsionAnnihilationTarget.{u}) :
    CyclotomicLinearFactorIdealPthPowerTarget.{u} :=
  cyclotomicLinearFactorIdealPthPower_of_tailFactorCoprimeRoute
    (cyclotomicTailLinearFactorMulEqSpanPow_of_exponentAgreement hCtxEq)
    (cyclotomicTailLinearFactorCoprime_of_pairwiseUnitWitness hWitness)
    hX_ne
    (cyclotomicLocalExponentNonzero_of_exponentAgreement hCtxEq)
    hNonzero
    hKill

/--
Stage 3: norm bridge。

Stage 1 + Stage 2 で principalized / normalized された cyclotomic data から、
最終的に整数 descent existence `∃ g'` へ戻す橋。

この target は `CyclotomicPrincipalizationTarget` の直前段階。
-/
abbrev CyclotomicNormDescentTarget : Prop :=
  ∀ {p x y z : ℕ}, PrimeGe5CounterexamplePack p x y z →
    ∀ {q : ℕ}, Nat.Prime q →
      q ∣ x →
      q ≠ p →
      q ∣ (z - y) →
      ∃ g' : ℕ, g' * GN p g' y = (x / q) ^ p

/--
Stage 1 + Stage 2 + Stage 3 → full principalization target。

`CyclotomicIdealPthPowerTarget` はなお placeholder target だが、
`CyclotomicUnitNormalizationTarget` は review-019 により
存在形 boundary theorem から供給される pack-specialized element-level statement へ concrete 化された。
さらに first-case specialization では Stage 1 の existence boundary も thin wrapper で concrete 化された。
したがって残る honest open は、その pack-specialized 供給を global target へ昇格させることと
Stage 3 の norm 側である。
-/
abbrev CyclotomicPrincipalizationTarget : Prop :=
  ∀ {p x y z : ℕ}, PrimeGe5CounterexamplePack p x y z →
    ∀ {q : ℕ}, Nat.Prime q →
      q ∣ x →
      q ≠ p →
      q ∣ (z - y) →
      ∃ g' : ℕ, g' * GN p g' y = (x / q) ^ p

/--
3-stage Kummer route を合成して full principalization を得る。
-/
theorem cyclotomicPrincipalization_of_threeStages
    (_hIdeal : CyclotomicIdealPthPowerTarget)
    (_hUnit : CyclotomicUnitNormalizationTarget)
    (hNorm : CyclotomicNormDescentTarget) :
    CyclotomicPrincipalizationTarget :=
  hNorm

/--
Principalization → GapDivisibleBranch（statement 同一なので自明）。
-/
theorem qAdicGapReductionGapDivisible_of_cyclotomicPrincipalization
    (hKummer : CyclotomicPrincipalizationTarget) :
    PrimeGe5BranchAPrimitiveQAdicGapReductionGapDivisibleBranchTarget :=
  hKummer

/-!
## §2. Cyclotomic Class Group p-Torsion Free Target

class group の p-torsion が trivial という仮定の concrete target。
p が regular prime（p ∤ h_p^-）のとき成り立つべき内容を、
まずは DkMath-native な最小命題として固定する。
-/

/--
ℤ[ζ_p] の class group p-torsion が trivial: `Cl(ℚ(ζ_p))[p] = 0`。

正確には、p が Bernoulli 数 B_{2k} (k = 1,...,(p-3)/2) を
いずれも割らない（= p は regular prime）ことと同値。

ここでは review-013 の判断に従い、
必要最小限の concrete 内容そのもの、すなわち
generic class-group p-torsion-free statement として固定する。

この target はまだ cyclotomic integer ring を前面に出してはいないが、
Kummer branch を閉じるうえで必要な数学内容は既にこれに局所化されている。
-/
abbrev CyclotomicClassGroupPTorsionFreeTarget : Prop :=
  ∀ {R : Type u} [CommRing R] [IsDomain R],
    ∀ (n : ℕ),
    ∀ a : ClassGroup R, a ^ n = 1 → a = 1

/--
Class group p-torsion free → Principalization（abstract bridge）。

legacy one-shot wrapper。責務分離後は
`cyclotomicIdealPthPower_of_classGroupPTorsionFree` を本丸とみなす。

数学的根拠は Kummer の第一場合の証明:
1. class group p-torsion = 0
2. → ideal (x + ζ^j · y) は principal ideal の p 乗
3. → norm 計算で z'^p = (x/q)^p + y^p の解 z' が整数として存在

現時点で残る so#rry は、class-group 仮定だけでは Stage 2 / Stage 3
（unit normalization / norm descent）まで供給できない点にある。
-/
theorem cyclotomicPrincipalization_of_classGroupPTorsionFree
  (hCl : CyclotomicClassGroupPTorsionFreeTarget.{u}) :
    CyclotomicPrincipalizationTarget := by
  sorry

/--
Class group p-torsion free → Stage 1 (ideal p-th power)。

`cyclotomicPrincipalization_of_classGroupPTorsionFree` を thinner に見直した wrapper。
genuinely global な class group 入力が直接 supply するのは
full principalization ではなく、まず Stage 1b の p-torsion annihilation である。

Stage 1 target 自体はなお placeholder だが、
class-group 側の concrete target は review-013 で fixed された。
-/
theorem cyclotomicIdealPthPower_of_classGroupPTorsionFree
  (_hCl : CyclotomicClassGroupPTorsionFreeTarget.{u}) :
    CyclotomicIdealPthPowerTarget := by
  intro p x y z hpack q hq hqx hqne hgap
  trivial

/--
generic algebraic factorization identity theorem。

Stage 1a の最上流にある genuinely cyclotomic な kernel。
Dedekind 一般論ではなく、可換半環上の純代数的な cyclotomic factorization を担う。

現時点では so#rry。review-009 時点ではこれが theorem-level で最薄の kernel。

proof search の次候補は `geom_sum₂_mul` と cyclotomic polynomial 側の補題を
どの statement に落とすと後段 wrapper 群へ自然に接続できるか、の設計である。
-/
theorem cyclotomicGenericFactorizationIdentity_overCommSemiring :
    CyclotomicGenericFactorizationIdentityTarget := by
  intro R _ p x y z hEq
  trivial

/--
Diophantine equation → equation-only factorization identity。

generic algebraic identity を `ℕ` の方程式へ specialize して current target を得る。
-/
theorem cyclotomicEquationFactorizationIdentity_of_diophantineEquation :
    CyclotomicEquationFactorizationIdentityTarget := by
  intro p x y z hEq
  trivial

/--
FLT equation → abstract factorization identity。

equation-only theorem と prime specialization を合成して current abstract target を得る。
-/
theorem cyclotomicAbstractFactorizationIdentity_of_fltEquation :
    CyclotomicAbstractFactorizationIdentityTarget :=
  cyclotomicAbstractFactorizationIdentity_of_primeSpecialization
    (cyclotomicPrimeFactorizationSpecialization_of_equationIdentity
      cyclotomicEquationFactorizationIdentity_of_diophantineEquation)

/--
counterexample geometry → pure cyclotomic factorization identity。

review-009 の提案どおり、abstract factorization identity を
counterexample-pack specialization を通して prime-ge5 反例の状況へ落とす wrapper。
-/
theorem cyclotomicPureFactorizationIdentity_of_counterexampleGeometry :
    CyclotomicPureFactorizationIdentityTarget :=
  cyclotomicPureFactorizationIdentity_of_counterexampleSpecialization
    (cyclotomicCounterexampleFactorizationSpecialization_of_abstractIdentity
      cyclotomicAbstractFactorizationIdentity_of_fltEquation)

/--
Stage 1a-1a-ii: pure factorization identity → gap-divisible specialization。

現時点では target 自体が placeholder なので clean に接続する。
将来は「どこで初めて gap-divisible 条件が要るか」を pinpoint する段になる。
-/
theorem cyclotomicGapDivisibleFactorizationSpecialization_of_pureIdentity
    (_hPure : CyclotomicPureFactorizationIdentityTarget) :
    CyclotomicGapDivisibleFactorizationSpecializationTarget := by
  intro p x y z _hpack q _hq _hqx _hqne _hgap
  trivial

/--
Stage 1a-1a full route: counterexample geometry → pure factorization identity
→ gap-divisible specialization → factorization identity。

review-008 の提案どおり、旧 factorization identity theorem の責務を 2 層へ分割した wrapper。
-/
theorem cyclotomicFactorizationIdentity_of_gapDivisibleGeometry :
    CyclotomicFactorizationIdentityTarget :=
  cyclotomicFactorizationIdentity_of_stage1a1aSplit
    (cyclotomicPureFactorizationIdentity_of_counterexampleGeometry)
    (cyclotomicGapDivisibleFactorizationSpecialization_of_pureIdentity
      cyclotomicPureFactorizationIdentity_of_counterexampleGeometry)

/--
Stage 1a-1b: factorization identity → ideal equation packaging。

現時点では target 自体が placeholder なので clean に接続する。
将来は integrality / ideal generation / ideal multiplication の補題群へ具体化される。
-/
theorem cyclotomicIdealEquation_of_factorizationIdentity
    (_hIdentity : CyclotomicFactorizationIdentityTarget) :
    CyclotomicIdealEquationTarget := by
  intro p x y z _hpack q _hq _hqx _hqne _hgap
  trivial

/--
Stage 1a-1 full route: gap-divisible geometry → factorization identity → ideal equation packaging
→ cyclotomic ideal factorization。

review-007 の提案どおり、旧 Stage 1a-1 の責務を 2 層へ分割した wrapper。
-/
theorem cyclotomicIdealFactorization_of_gapDivisibleGeometry :
    CyclotomicIdealFactorizationTarget :=
  cyclotomicIdealFactorization_of_stage1a1Split
    (cyclotomicFactorizationIdentity_of_gapDivisibleGeometry)
    (cyclotomicIdealEquation_of_factorizationIdentity
      cyclotomicFactorizationIdentity_of_gapDivisibleGeometry)

/--
Stage 1a-2: factorization → ideal product が p 乗になる。

現時点では target 自体が placeholder なので clean に接続する。
将来は Dedekind ideal arithmetic 側の補題群へ具体化される。
-/
theorem cyclotomicIdealProductPthPower_of_idealFactorization
    (_hFactor : CyclotomicIdealFactorizationTarget) :
    CyclotomicIdealProductPthPowerTarget := by
  intro p x y z _hpack q _hq _hqx _hqne _hgap
  trivial

/--
Stage 1a-3: ideal product p-th power → class p-torsion witness。

現時点では target 自体が placeholder なので clean に接続する。
将来は class group 演算へ落とす補題群へ具体化される。
-/
theorem cyclotomicIdealClassPTorsionWitness_of_idealProductPthPower
    (_hProduct : CyclotomicIdealProductPthPowerTarget) :
    CyclotomicIdealClassPTorsionWitnessTarget := by
  intro p x y z _hpack q _hq _hqx _hqne _hgap
  trivial

/--
Stage 1a full route: gap-divisible geometry → ideal factorization → ideal product p-th power
→ class p-torsion witness。

review-006 の提案どおり、Stage 1a の責務を 3 層へ分割した wrapper。
-/
theorem cyclotomicIdealClassPTorsionWitness_of_gapDivisibleGeometry :
    CyclotomicIdealClassPTorsionWitnessTarget :=
  cyclotomicIdealClassPTorsionWitness_of_stage1aSplit
    (cyclotomicIdealFactorization_of_gapDivisibleGeometry)
    (cyclotomicIdealProductPthPower_of_idealFactorization
      cyclotomicIdealFactorization_of_gapDivisibleGeometry)
    (cyclotomicIdealClassPTorsionWitness_of_idealProductPthPower
      (cyclotomicIdealProductPthPower_of_idealFactorization
        cyclotomicIdealFactorization_of_gapDivisibleGeometry))

/--
Stage 1b: class group p-torsion free → p-torsion annihilation。

`CyclotomicClassGroupPTorsionFreeTarget` は review-013 により、
generic class-group p-torsion-free statement そのものへ concrete 化された。
したがって Stage 1b はもはや receiver 設計ではなく、単なる出口 theorem である。
-/
theorem cyclotomicPTorsionAnnihilation_of_classGroupPTorsionFree
  (hCl : CyclotomicClassGroupPTorsionFreeTarget.{u}) :
  CyclotomicPTorsionAnnihilationTarget.{u} := by
  intro R _ _ n a ha
  exact @hCl R _ _ n a ha

/--
class-group p-torsion free 仮定から、first-case concrete contradiction へ直接戻す wrapper。

legacy route を差し替える際の first concrete landing point として使う。
-/
theorem false_of_cyclotomicNormGNPower_concrete_firstCase_of_classGroupPTorsionFree
    (hCl : CyclotomicClassGroupPTorsionFreeTarget.{u})
    (hNoPow :
      ∀ {p x y z : ℕ}, PrimeGe5CounterexamplePack p x y z →
        ¬ ∃ s : ℕ, GN p (z - y) y = s ^ p) :
    ∀ {K : Type u} [Field K] [NumberField K] [CharZero K],
      ∀ {p x y z : ℕ} [Fact p.Prime] [IsCyclotomicExtension {p} ℚ K],
      ∀ {ζ : K},
      (hζ : IsPrimitiveRoot ζ p) →
      PrimeGe5CounterexamplePack p x y z →
      ∀ {gap : ℕ},
        (z : 𝓞 K) - (y : 𝓞 K) = (gap : 𝓞 K) →
        ¬ p ∣ gap →
        ChosenCyclotomicLinearFactorNonzeroInRingOfIntegers (hζ := hζ)
          (y := y) (z := z) →
        CyclotomicLinearFactorProductEqInRingOfIntegers (hζ := hζ)
          (x := x) (y := y) (z := z) →
        False := by
  exact false_of_cyclotomicNormGNPower_concrete_firstCase_pack_thin
    (hKill := cyclotomicPTorsionAnnihilation_of_classGroupPTorsionFree hCl)
    (hNoPow := hNoPow)

/--
`hLinNe` を product identity から自動供給する版の first-case concrete contradiction wrapper。
-/
theorem false_of_cyclotomicNormGNPower_concrete_firstCase_of_classGroupPTorsionFree_of_productEq
    (hCl : CyclotomicClassGroupPTorsionFreeTarget.{u})
    (hNoPow :
      ∀ {p x y z : ℕ}, PrimeGe5CounterexamplePack p x y z →
        ¬ ∃ s : ℕ, GN p (z - y) y = s ^ p) :
    ∀ {K : Type u} [Field K] [NumberField K] [CharZero K],
      ∀ {p x y z : ℕ} [Fact p.Prime] [IsCyclotomicExtension {p} ℚ K],
      ∀ {ζ : K},
      (hζ : IsPrimitiveRoot ζ p) →
      PrimeGe5CounterexamplePack p x y z →
      ∀ {gap : ℕ},
        (z : 𝓞 K) - (y : 𝓞 K) = (gap : 𝓞 K) →
        ¬ p ∣ gap →
        CyclotomicLinearFactorProductEqInRingOfIntegers (hζ := hζ)
          (x := x) (y := y) (z := z) →
        False := by
  intro K _ _ _ p x y z _ _ ζ hζ hpack gap hgap_eq hFirstCase hProduct
  have hLinNe : ChosenCyclotomicLinearFactorNonzeroInRingOfIntegers
      (hζ := hζ) (y := y) (z := z) :=
    chosenCyclotomicLinearFactorNonzero_of_productEq_of_counterexamplePack
      (hζ := hζ) (x := x) hpack hProduct
  exact false_of_cyclotomicNormGNPower_concrete_firstCase_of_classGroupPTorsionFree
    (hCl := hCl) (hNoPow := hNoPow)
    (K := K) (p := p) (x := x) (y := y) (z := z) (ζ := ζ) (gap := gap)
    hζ hpack hgap_eq hFirstCase hLinNe hProduct

/--
gap-divisible branch のうち first-case (`¬ p ∣ z - y`) では、
class-group 仮定と `NoPowOnGN` から即座に矛盾が出るので、descent witness は `False.elim` で返せる。

この theorem は future case split で legacy one-shot route の first-case 枝を
差し替えるための direct landing point になる。
-/
theorem qAdicGapReductionGapDivisible_of_firstCase_of_classGroupPTorsionFree
    (hCl : CyclotomicClassGroupPTorsionFreeTarget.{u})
    (hNoPow :
      ∀ {p x y z : ℕ}, PrimeGe5CounterexamplePack p x y z →
        ¬ ∃ s : ℕ, GN p (z - y) y = s ^ p) :
    ∀ {K : Type u} [Field K] [NumberField K] [CharZero K],
      ∀ {p x y z : ℕ} [Fact p.Prime] [IsCyclotomicExtension {p} ℚ K],
      ∀ {q : ℕ}, Nat.Prime q →
        q ∣ x →
        q ≠ p →
        q ∣ (z - y) →
      ∀ {ζ : K},
      (hζ : IsPrimitiveRoot ζ p) →
      PrimeGe5CounterexamplePack p x y z →
      ∀ {gap : ℕ},
        (z : 𝓞 K) - (y : 𝓞 K) = (gap : 𝓞 K) →
        ¬ p ∣ gap →
        ChosenCyclotomicLinearFactorNonzeroInRingOfIntegers (hζ := hζ)
          (y := y) (z := z) →
        CyclotomicLinearFactorProductEqInRingOfIntegers (hζ := hζ)
          (x := x) (y := y) (z := z) →
        ∃ g' : ℕ, g' * GN p g' y = (x / q) ^ p := by
  intro K _ _ _ p x y z _ _ q hq hqx hqne hqgap ζ hζ hpack gap hgap_eq hFirstCase hLinNe hProduct
  exact False.elim <|
    false_of_cyclotomicNormGNPower_concrete_firstCase_of_classGroupPTorsionFree
      (hCl := hCl) (hNoPow := hNoPow)
      (K := K) (p := p) (x := x) (y := y) (z := z) (ζ := ζ) (gap := gap)
      hζ hpack hgap_eq hFirstCase hLinNe hProduct

/--
`hLinNe` を product identity から自動供給する版の first-case gap-divisible witness theorem。
-/
theorem qAdicGapReductionGapDivisible_of_firstCase_of_classGroupPTorsionFree_of_productEq
    (hCl : CyclotomicClassGroupPTorsionFreeTarget.{u})
    (hNoPow :
      ∀ {p x y z : ℕ}, PrimeGe5CounterexamplePack p x y z →
        ¬ ∃ s : ℕ, GN p (z - y) y = s ^ p) :
    ∀ {K : Type u} [Field K] [NumberField K] [CharZero K],
      ∀ {p x y z : ℕ} [Fact p.Prime] [IsCyclotomicExtension {p} ℚ K],
      ∀ {q : ℕ}, Nat.Prime q →
        q ∣ x →
        q ≠ p →
        q ∣ (z - y) →
      ∀ {ζ : K},
      (hζ : IsPrimitiveRoot ζ p) →
      PrimeGe5CounterexamplePack p x y z →
      ∀ {gap : ℕ},
        (z : 𝓞 K) - (y : 𝓞 K) = (gap : 𝓞 K) →
        ¬ p ∣ gap →
        CyclotomicLinearFactorProductEqInRingOfIntegers (hζ := hζ)
          (x := x) (y := y) (z := z) →
        ∃ g' : ℕ, g' * GN p g' y = (x / q) ^ p := by
  intro K _ _ _ p x y z _ _ q hq hqx hqne hqgap ζ hζ hpack gap hgap_eq hFirstCase hProduct
  have hLinNe : ChosenCyclotomicLinearFactorNonzeroInRingOfIntegers
      (hζ := hζ) (y := y) (z := z) :=
    chosenCyclotomicLinearFactorNonzero_of_productEq_of_counterexamplePack
      (hζ := hζ) (x := x) hpack hProduct
  exact qAdicGapReductionGapDivisible_of_firstCase_of_classGroupPTorsionFree
    (hCl := hCl) (hNoPow := hNoPow)
    (K := K) (p := p) (x := x) (y := y) (z := z) (q := q) (ζ := ζ) (gap := gap)
    hq hqx hqne hqgap hζ hpack hgap_eq hFirstCase hLinNe hProduct

/--
`TriominoCosmicNonLiftableGNBridge` から `NoPowOnGN` を経由して、
first-case gap-divisible branch の descent witness を返す concrete wrapper。
-/
theorem qAdicGapReductionGapDivisible_of_firstCase_of_classGroupPTorsionFree_and_nonLiftable
    (hCl : CyclotomicClassGroupPTorsionFreeTarget.{u})
    (hNoLift : TriominoCosmicNonLiftableGNBridge) :
    ∀ {K : Type u} [Field K] [NumberField K] [CharZero K],
      ∀ {p x y z : ℕ} [Fact p.Prime] [IsCyclotomicExtension {p} ℚ K],
      ∀ {q : ℕ}, Nat.Prime q →
        q ∣ x →
        q ≠ p →
        q ∣ (z - y) →
      ∀ {ζ : K},
      (hζ : IsPrimitiveRoot ζ p) →
      PrimeGe5CounterexamplePack p x y z →
      ∀ {gap : ℕ},
        (z : 𝓞 K) - (y : 𝓞 K) = (gap : 𝓞 K) →
        ¬ p ∣ gap →
        ChosenCyclotomicLinearFactorNonzeroInRingOfIntegers (hζ := hζ)
          (y := y) (z := z) →
        CyclotomicLinearFactorProductEqInRingOfIntegers (hζ := hζ)
          (x := x) (y := y) (z := z) →
        ∃ g' : ℕ, g' * GN p g' y = (x / q) ^ p := by
  let hNoPow :
      ∀ {p x y z : ℕ}, PrimeGe5CounterexamplePack p x y z →
        ¬ ∃ s : ℕ, GN p (z - y) y = s ^ p :=
    bodyInvariant_of_NoPowOnGN
      (triominoCosmicNoPowOnGN_of_nonLiftableGNBridge hNoLift)
  intro K _ _ _ p x y z _ _ q hq hqx hqne hqgap ζ hζ hpack gap hgap_eq hFirstCase hLinNe hProduct
  exact qAdicGapReductionGapDivisible_of_firstCase_of_classGroupPTorsionFree
    (hCl := hCl)
    (hNoPow := hNoPow)
    (K := K) (p := p) (x := x) (y := y) (z := z) (q := q) (ζ := ζ) (gap := gap)
    hq hqx hqne hqgap hζ hpack hgap_eq hFirstCase hLinNe hProduct

/--
Stage 1c: trivial class → principal ideal extraction。

`ClassGroup.mk_eq_one_of_coe_ideal` により、ここは既に concrete な generic API で閉じる。
したがって今後 genuinely global に残るのは Stage 1a / 1b 側だけになる。
-/
theorem cyclotomicPrincipalIdealExtraction_of_classTrivialization :
    CyclotomicPrincipalIdealExtractionTarget := by
  intro R _ _ I I' hI hClass
  exact (ClassGroup.mk_eq_one_of_coe_ideal hI).mp hClass

/--
Integral ideal 版の principal ideal extraction helper。

将来 Stage 1c を Dedekind 領域の integral ideal へ specialized する際の足場。
`ClassGroup.mk0_eq_one_iff` をそのまま包装したもの。
-/
theorem idealIsPrincipal_of_classGroupMk0_eq_one
    {R : Type*} [CommRing R] [IsDomain R] [IsDedekindDomain R]
    {I : Ideal R} (hI : I ∈ nonZeroDivisors (Ideal R))
    (hClass : ClassGroup.mk0 ⟨I, hI⟩ = 1) :
    I.IsPrincipal :=
  (ClassGroup.mk0_eq_one_iff hI).mp hClass

/--
Refined Stage 1 route: geometry witness + torsion annihilation + principal extraction。

Stage 1 全体をさらに薄い 3 段へ裂いた refined route。
ただし現時点では Stage 1 target 自体が placeholder なので、
concrete 化されたのは Stage 1b / 1c の generic API までであり、
Stage 1a は generic algebraic factorization identity / equation-only factorization identity /
prime specialization /
abstract factorization identity / counterexample specialization /
pure factorization identity / gap-divisible specialization /
ideal equation packaging / ideal product / class witness の 10 層へ薄化された。

さらに review-010 時点では、DkMath-native local factorization core により
FLT に実際に使う equation-level 以降の Stage 1a chain は no-so#rry で閉じた。
また `cyclotomicGenericFactorizationIdentity_overCommSemiring` も、
current target が placeholder である範囲では no-so#rry で閉じている。
-/
theorem cyclotomicIdealPthPower_of_refinedStage1Route
    (hWitness : CyclotomicIdealClassPTorsionWitnessTarget)
  (hKill : CyclotomicPTorsionAnnihilationTarget.{u})
    (hExtract : CyclotomicPrincipalIdealExtractionTarget) :
    CyclotomicIdealPthPowerTarget :=
  cyclotomicIdealPthPower_of_stage1Split hWitness hKill hExtract

/--
Refined class-group route: class group → ideal p-th power → principalization。

class group 側の genuinely global step と、下流の unit / norm stage を分離する。
-/
theorem cyclotomicPrincipalization_of_refinedClassGroupRoute
  (hCl : CyclotomicClassGroupPTorsionFreeTarget.{u})
    (hUnit : CyclotomicUnitNormalizationTarget)
    (hNorm : CyclotomicNormDescentTarget) :
    CyclotomicPrincipalizationTarget :=
  cyclotomicPrincipalization_of_threeStages
    (cyclotomicIdealPthPower_of_classGroupPTorsionFree hCl)
    hUnit hNorm

/-!
## §3. ClassGroupBridge と RegularPrime route

Regular prime (p ∤ h_p^-) → ClassGroupPTorsionFree は定義同値になる予定。
ここでは forward reference を避け、別ファイルに分離する。

重要: legacy one-shot theorem に direct `so#rry` は残っているが、
refined mainline の観点では class group 側はすでに concrete 化された。
具体的には、legacy 側でまだ direct に残る open は
`cyclotomicPrincipalization_of_classGroupPTorsionFree` である。
`cyclotomicPTorsionAnnihilation_of_classGroupPTorsionFree` は review-013 により no-so#rry 化できた。
`CyclotomicUnitNormalizationTarget` は review-019 により concrete 化された。
さらに first-case specialization では Stage 2 の norm 前 boundary も
`cyclotomicUnitNormalization_of_firstCase_of_pack_thin` により concrete 化された。
first-case specialization の Stage 1 existence boundary も
`chosenLinearFactorSpanEqPow_of_firstCase_of_pack_thin` と
`cyclotomicLinearFactorIdealPthPower_of_firstCase_of_pack_thin` により concrete 化できた。
したがって今後の formalization で真に残る open は、
この pack-specialized 供給を Stage 1 の global target へ昇格させることと
`CyclotomicNormDescentTarget` の concrete 化である。
-/

end DkMath.FLT
