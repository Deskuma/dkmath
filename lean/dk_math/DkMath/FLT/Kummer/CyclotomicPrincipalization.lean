/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Kummer.GapDivisibleBranch

#print "file: DkMath.FLT.Kummer.CyclotomicPrincipalization"

set_option linter.style.longLine false
set_option linter.style.emptyLine false

open scoped nonZeroDivisors

open DkMath.CosmicFormulaBinom

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
残る honest open は、この target を Stage 1 側からどう supply するかと
Stage 3 の norm descent である。
-/
abbrev CyclotomicUnitNormalizationTarget : Prop :=
  ∀ {R : Type u} [CommRing R] [IsDomain R],
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
  ∀ {R : Type*} [CommRing R] [IsDomain R],
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
  ∀ {R : Type*} [CommRing R] [IsDomain R],
    ∀ ctx : CyclotomicLocalFactorizationContext R,
    ∀ {p x y z : ℕ}, PrimeGe5CounterexamplePack p x y z →
    ∀ {q : ℕ}, Nat.Prime q →
      q ∣ x →
      q ≠ p →
      q ∣ (z - y) →
      ∃ I : Ideal R, ∃ _ : I.IsPrincipal,
        Ideal.span ({(z : R) - ctx.zeta * (y : R)} : Set R) = I ^ ctx.p

/--
pack-specialized Stage 2 receiver。

review-017 で狙っている
`span(z - ζy) = I^p ⇒ z - ζy = u * β^p`
の specialized theorem そのもの。
まだ Stage 1 target 自体は placeholder なので、入力には explicit な ideal equality を要求する。
-/
theorem cyclotomicUnitNormalization_of_spanEqPowPrincipal :
    CyclotomicUnitNormalizationPackSpecializationTarget := by
  intro R _ _ ctx I _ p x y z _hpack q _hq _hqx _hqne _hgap hSpan
  exact linearFactorEqUnitMulGeneratorPowOfSpanEqPowPrincipal ctx (z : R) (y : R) hSpan

/--
Stage 1 の存在形 boundary target が与えられれば、Stage 2 の pack-specialized unit normalization が従う。

review-018 の提案どおり、Stage 1 → Stage 2 の接続点を存在形にしておくと、
ここはそのまま composition で閉じる。
-/
theorem cyclotomicUnitNormalization_of_existsLinearFactorIdealPthPower
    (hIdeal :
      ∀ {R : Type u} [CommRing R] [IsDomain R],
        ∀ ctx : CyclotomicLocalFactorizationContext R,
        ∀ {p x y z : ℕ}, PrimeGe5CounterexamplePack p x y z →
        ∀ {q : ℕ}, Nat.Prime q →
          q ∣ x →
          q ≠ p →
          q ∣ (z - y) →
          ∃ I : Ideal R, ∃ _ : I.IsPrincipal,
            Ideal.span ({(z : R) - ctx.zeta * (y : R)} : Set R) = I ^ ctx.p) :
    CyclotomicUnitNormalizationTarget.{u} := by
  intro R _ _ ctx p x y z hpack q hq hqx hqne hgap
  obtain ⟨I, hIPrincipal, hSpan⟩ := hIdeal (R := R) ctx hpack hq hqx hqne hgap
  obtain ⟨u, huUnit, huEq⟩ :=
    cyclotomicUnitNormalization_of_spanEqPowPrincipal
      (R := R) (ctx := ctx) (I := I) (p := p) (x := x) (y := y) (z := z)
      hpack hq hqx hqne hgap hSpan
  refine ⟨Submodule.IsPrincipal.generator I, u, huUnit, ?_⟩
  simpa using huEq

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
したがって残る honest open は、Stage 1 の存在形 boundary 供給と Stage 3 の norm 側である。
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
したがって今後の formalization で真に残る open は、
Stage 1 から `CyclotomicLinearFactorIdealPthPowerTarget` を供給することと
`CyclotomicNormDescentTarget` の concrete 化である。
-/

end DkMath.FLT
