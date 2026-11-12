/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.NumberTheory.FreyPrimeValuation
import Mathlib.AlgebraicGeometry.EllipticCurve.Reduction
import Mathlib.RingTheory.DedekindDomain.Dvr
import Mathlib.RingTheory.Localization.LocalizationLocalization

#print "file: DkMath.Lib.NumberTheory.FreyLocalReduction"

/-!
# NOTE-006 §4: 単元 c₄ から真の最小モデル・乗法的還元へ

付値は Mathlib の乗法的規約を使うので、最小判別式の加法的付値は最小、
対応する乗法的付値は最大となる。座標変換の倍率 u に対して c₄ は u⁻⁴ 倍、
Δ は u⁻¹² 倍となる。元の c₄ が単元なら、変換後の整性から v(u⁻¹)≤1。
従って v(Δ')≤v(Δ) であり、全ての整な競合モデルに対する最小性が従う。
これは v(Δ) の合同式だけを還元の定義と呼び替える手続きではない。
-/

namespace DkMath.Lib.NumberTheory.FreyLocalReduction
open WeierstrassCurve IsDedekindDomain.HeightOneSpectrum
open WithZero Multiplicative

section DVR
variable {R K : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Field K] [Algebra R K] [IsFractionRing R K]

/-- c₄ が単元の整モデルは最小である。任意の有理座標変換を比較対象に含める。 -/
theorem isMinimal_of_isUnit_c4 (W : WeierstrassCurve R) (hc : IsUnit W.c₄) :
    IsMinimal R (W⁄K) := by
  let v := (IsDiscreteValuationRing.maximalIdeal R).valuation K
  let : IsIntegral R (W⁄K) := ⟨⟨W, rfl⟩⟩
  have hcval : v (W⁄K).c₄ = 1 := by
    rw [baseChange, map_c₄]
    apply (valuation_eq_one_iff_notMem (IsDiscreteValuationRing.maximalIdeal R)).mpr
    simpa only [IsDiscreteValuationRing.maximalIdeal, IsLocalRing.mem_maximalIdeal,
      mem_nonunits_iff, not_not] using hc
  constructor
  refine ⟨by simpa using (inferInstance : IsIntegral R (W⁄K)), ?_⟩
  intro C hC _
  let : IsIntegral R (C • (W⁄K)) := hC
  have hcint : v (C • (W⁄K)).c₄ ≤ 1 := by
    rw [← integralModel_c₄_eq R (C • (W⁄K))]
    exact valuation_le_one _ _
  have hu : v (↑C.u⁻¹ : K) ≤ 1 := by
    rw [variableChange_c₄, map_mul, map_pow, hcval, mul_one] at hcint
    exact (pow_le_one_iff_of_nonneg zero_le (by decide : (4 : ℕ) ≠ 0)).mp hcint
  change (valuation_Δ_aux R (C • (W⁄K)) : ℤᵐ⁰) ≤
    (valuation_Δ_aux R ((1 : VariableChange K) • (W⁄K)) : ℤᵐ⁰)
  rw [one_smul, valuation_Δ_aux_eq_of_isIntegral, valuation_Δ_aux_eq_of_isIntegral]
  change v (C • (W⁄K)).Δ ≤ v (W⁄K).Δ
  rw [variableChange_Δ, map_mul, map_pow]
  exact mul_le_of_le_one_left zero_le (pow_le_one₀ zero_le hu)

/-- 判別式が非単元、c₄ が単元なら、上の最小性と併せて正式な乗法的還元を得る。 -/
theorem hasMultiplicativeReduction_of_c4 (W : WeierstrassCurve R)
    (hc : IsUnit W.c₄) (hd : W.Δ ∈ IsLocalRing.maximalIdeal R) :
    HasMultiplicativeReduction R (W⁄K) := by
  let := isMinimal_of_isUnit_c4 (K := K) W hc
  constructor
  · rw [baseChange, map_Δ]
    exact (valuation_lt_one_iff_mem _ _).mpr hd
  · rw [baseChange, map_c₄]
    apply (valuation_eq_one_iff_notMem (IsDiscreteValuationRing.maximalIdeal R)).mpr
    simpa only [IsDiscreteValuationRing.maximalIdeal, IsLocalRing.mem_maximalIdeal,
      mem_nonunits_iff, not_not] using hc

/-- Δ が単元の整モデルも最小である。全競合モデルの乗法的付値が1以下となる。 -/
theorem isMinimal_of_isUnit_discriminant (W : WeierstrassCurve R) (hd : IsUnit W.Δ) :
    IsMinimal R (W⁄K) := by
  let : IsIntegral R (W⁄K) := ⟨⟨W, rfl⟩⟩
  have hv : (IsDiscreteValuationRing.maximalIdeal R).valuation K (W⁄K).Δ = 1 := by
    rw [baseChange, map_Δ]
    apply (valuation_eq_one_iff_notMem (IsDiscreteValuationRing.maximalIdeal R)).mpr
    simpa only [IsDiscreteValuationRing.maximalIdeal, IsLocalRing.mem_maximalIdeal,
      mem_nonunits_iff, not_not] using hd
  constructor
  refine ⟨by simpa using (inferInstance : IsIntegral R (W⁄K)), ?_⟩
  intro C hC _
  let : IsIntegral R (C • (W⁄K)) := hC
  change (valuation_Δ_aux R (C • (W⁄K)) : ℤᵐ⁰) ≤
    (valuation_Δ_aux R ((1 : VariableChange K) • (W⁄K)) : ℤᵐ⁰)
  rw [one_smul, valuation_Δ_aux_eq_of_isIntegral, valuation_Δ_aux_eq_of_isIntegral, hv,
    ← integralModel_Δ_eq R (C • (W⁄K))]
  exact valuation_le_one _ _

/-- 単元判別式のモデルは、正式な良還元の定義を満たす。 -/
theorem hasGoodReduction_of_isUnit_discriminant (W : WeierstrassCurve R)
    (hd : IsUnit W.Δ) : HasGoodReduction R (W⁄K) := by
  let := isMinimal_of_isUnit_discriminant (K := K) W hd
  constructor
  rw [baseChange, map_Δ]
  apply (valuation_eq_one_iff_notMem (IsDiscreteValuationRing.maximalIdeal R)).mpr
  simpa only [IsDiscreteValuationRing.maximalIdeal, IsLocalRing.mem_maximalIdeal,
    mem_nonunits_iff, not_not] using hd

end DVR

section IntegerLocalization
variable (ℓ : ℕ) [Fact ℓ.Prime]

/-- 素数 ℓ が生成する実際の整数素イデアル。 -/
def primeIdeal : Ideal ℤ := Ideal.span {(ℓ : ℤ)}

/-- ℓ の素数性から局所化に必要な素イデアル性を供給する。 -/
instance primeIdeal_isPrime : (primeIdeal ℓ).IsPrime :=
  (Ideal.span_singleton_prime (by exact_mod_cast (Fact.out : ℓ.Prime).ne_zero)).mpr
    (Int.prime_iff_natAbs_prime.mpr (by simpa using (Fact.out : ℓ.Prime)))

/-- ℓ を割らない整数だけを反転した環 ℤ_(ℓ)。完備化ではない。 -/
abbrev LocalRing := Localization.AtPrime (primeIdeal ℓ)

/-- 非零素イデアルでの整数環の局所化は離散付値環である。 -/
noncomputable instance localRing_dvr : IsDiscreteValuationRing (LocalRing ℓ) :=
  IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain ℤ
    (P := primeIdeal ℓ) (by
      rw [primeIdeal, ne_eq, Ideal.span_singleton_eq_bot]
      exact_mod_cast (Fact.out : ℓ.Prime).ne_zero) _

/-- 局所整数環からℚへの標準埋め込み。分数体を別の仮想体へ置き換えない。 -/
noncomputable instance localRatAlgebra : Algebra (LocalRing ℓ) ℚ :=
  IsLocalization.localizationAlgebraOfSubmonoidLe _ _ (primeIdeal ℓ).primeCompl (nonZeroDivisors ℤ)
    (primeIdeal ℓ).primeCompl_le_nonZeroDivisors

/-- 整数→局所整数→有理数の写像は通常の整数埋め込みと可換する。 -/
instance localRatTower : @IsScalarTower ℤ (LocalRing ℓ) ℚ
    Algebra.toSMul Algebra.toSMul Algebra.toSMul :=
  IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)

/-- 同じℚが ℤ_(ℓ) の分数体である。 -/
instance localRatFractionRing : IsFractionRing (LocalRing ℓ) ℚ :=
  IsFractionRing.isFractionRing_of_isDomain_of_isLocalization
    (primeIdeal ℓ).primeCompl (LocalRing ℓ) ℚ

/-- 整数の非可除性は局所整数環での単元性と同値である。 -/
theorem isUnit_local_iff (n : ℤ) :
    IsUnit (algebraMap ℤ (LocalRing ℓ) n) ↔ ¬ (ℓ : ℤ) ∣ n := by
  rw [IsLocalization.AtPrime.isUnit_to_map_iff _ (primeIdeal ℓ)]
  exact not_congr (Ideal.mem_span_singleton)

/-- 整数の可除性は局所整数環の極大イデアルへの所属と同値である。 -/
theorem mem_maximal_local_iff (n : ℤ) :
    algebraMap ℤ (LocalRing ℓ) n ∈ IsLocalRing.maximalIdeal (LocalRing ℓ) ↔ (ℓ : ℤ) ∣ n := by
  rw [IsLocalization.AtPrime.to_map_mem_maximal_iff _ (primeIdeal ℓ)]
  exact Ideal.mem_span_singleton

/-- 整モデルの c₄ 非可除性から、元の有理モデルの ℓ-最小性を得る。 -/
theorem isMinimal_at_prime_of_not_dvd_c4 (W : WeierstrassCurve ℤ)
    (hc : ¬ (ℓ : ℤ) ∣ W.c₄) : IsMinimal (LocalRing ℓ) (W⁄ℚ) := by
  have h := isMinimal_of_isUnit_c4 (K := ℚ) (W⁄(LocalRing ℓ))
    (by rw [baseChange, map_c₄]; exact (isUnit_local_iff ℓ _).mpr hc)
  simpa only [baseChange, map_map, ← IsScalarTower.algebraMap_eq ℤ (LocalRing ℓ) ℚ] using h

/-- Δ が ℓ で割れ、c₄ は割れないなら有理モデルは乗法的還元を持つ。 -/
theorem hasMultiplicativeReduction_at_prime (W : WeierstrassCurve ℤ)
    (hd : (ℓ : ℤ) ∣ W.Δ) (hc : ¬ (ℓ : ℤ) ∣ W.c₄) :
    HasMultiplicativeReduction (LocalRing ℓ) (W⁄ℚ) := by
  have h := hasMultiplicativeReduction_of_c4 (K := ℚ) (W⁄(LocalRing ℓ))
    (by rw [baseChange, map_c₄]; exact (isUnit_local_iff ℓ _).mpr hc)
    (by rw [baseChange, map_Δ]; exact (mem_maximal_local_iff ℓ _).mpr hd)
  simpa only [baseChange, map_map, ← IsScalarTower.algebraMap_eq ℤ (LocalRing ℓ) ℚ] using h

/-- Δ が ℓ で割れなければ有理モデルは良還元を持ち、最小性も含まれる。 -/
theorem hasGoodReduction_at_prime (W : WeierstrassCurve ℤ)
    (hd : ¬ (ℓ : ℤ) ∣ W.Δ) : HasGoodReduction (LocalRing ℓ) (W⁄ℚ) := by
  have h := hasGoodReduction_of_isUnit_discriminant (K := ℚ) (W⁄(LocalRing ℓ))
    (by rw [baseChange, map_Δ]; exact (isUnit_local_iff ℓ _).mpr hd)
  simpa only [baseChange, map_map, ← IsScalarTower.algebraMap_eq ℤ (LocalRing ℓ) ℚ] using h

end IntegerLocalization
end DkMath.Lib.NumberTheory.FreyLocalReduction
