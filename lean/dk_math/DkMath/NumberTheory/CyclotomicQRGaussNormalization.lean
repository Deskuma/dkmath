/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
-/

import DkMath.NumberTheory.CyclotomicQRIntegralDescent
import DkMath.NumberTheory.PrimeQuadraticDiscriminant
import DkMath.NumberTheory.RationalSquarefreePrime
import Mathlib.NumberTheory.LegendreSymbol.AddCharacter
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.GaussSum

#print "file: DkMath.NumberTheory.CyclotomicQRGaussNormalization"

namespace DkMath.NumberTheory.CyclotomicQRGaussNormalization

open scoped BigOperators

open DkMath.NumberTheory.CyclotomicQRGaloisAction
open DkMath.NumberTheory.CyclotomicQRGaloisRealization
open DkMath.NumberTheory.CyclotomicQRIntegralDescent
open DkMath.NumberTheory.PrimeQuadraticDiscriminant
open DkMath.NumberTheory.RationalSquarefreePrime

noncomputable section

private def quadraticAddChar
    {L : Type*} [Field L] {p : ℕ} [Fact p.Prime]
    (ζ : L) (hζ : IsPrimitiveRoot ζ p) : AddChar (ZMod p) L := by
  letI : NeZero p := ⟨(Fact.out : Nat.Prime p).ne_zero⟩
  exact AddChar.zmodChar p hζ.pow_eq_one

private def quadraticCharL
    {L : Type*} [Field L] {p : ℕ} [Fact p.Prime] :
    MulChar (ZMod p) L :=
  (quadraticChar (ZMod p)).ringHomComp (algebraMap ℤ L)

private theorem algebraMap_int_injective
    {L : Type*} [Field L] [Algebra ℚ L] :
    Function.Injective (algebraMap ℤ L) := by
  intro a b hab
  apply (Int.cast_injective : Function.Injective (algebraMap ℤ ℚ))
  apply (FaithfulSMul.algebraMap_injective ℚ L)
  change algebraMap ℚ L (algebraMap ℤ ℚ a) =
    algebraMap ℚ L (algebraMap ℤ ℚ b)
  rw [← IsScalarTower.algebraMap_apply ℤ ℚ L a,
    ← IsScalarTower.algebraMap_apply ℤ ℚ L b]
  exact hab

/-- The quadratic Gauss element attached to the chosen primitive root. -/
def quadraticGauss
  {L : Type*} [Field L] {p : ℕ} [Fact p.Prime]
    (ζ : L) (hζ : IsPrimitiveRoot ζ p) : L :=
  gaussSum (quadraticCharL (L := L)) (quadraticAddChar ζ hζ)

private theorem quadraticChar_neg_one_mul_card_eq_signedPrimeDiscriminant
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) :
    quadraticChar (ZMod p) (-1) * (p : ℤ) = signedPrimeDiscriminant p := by
  have hp : p.Prime := Fact.out
  have hchar : ringChar (ZMod p) ≠ 2 := by
    rw [ZMod.ringChar_zmod_n]
    exact hp2
  rw [quadraticChar_neg_one hchar, ZMod.χ₄_nat_eq_if_mod_four]
  have hodd : p % 2 = 1 := hp.mod_two_eq_one_iff_ne_two.mpr hp2
  by_cases h : p % 4 = 1
  · simp [signedPrimeDiscriminant, h, hodd]
  · have h3 : p % 4 = 3 := by
      omega
    simp [signedPrimeDiscriminant, h3, hodd]

theorem quadraticGauss_sq
    {L : Type*} [Field L] [Algebra ℚ L]
    {p : ℕ} [Fact p.Prime]
    [IsCyclotomicExtension {p} ℚ L]
    (hp2 : p ≠ 2) (ζ : L) (hζ : IsPrimitiveRoot ζ p) :
    quadraticGauss ζ hζ ^ 2 =
      algebraMap ℤ L (signedPrimeDiscriminant p) := by
  letI : NeZero p := ⟨(Fact.out : Nat.Prime p).ne_zero⟩
  have hchar : ringChar (ZMod p) ≠ 2 := by
    rw [ZMod.ringChar_zmod_n]
    exact hp2
  have hχ : quadraticCharL (L := L) (p := p) ≠ 1 := by
    exact (MulChar.ringHomComp_ne_one_iff
      (algebraMap_int_injective (L := L))).2
      (quadraticChar_ne_one hchar)
  have hquad : MulChar.IsQuadratic (quadraticCharL (L := L) (p := p)) :=
    (quadraticChar_isQuadratic (ZMod p)).comp (algebraMap ℤ L)
  have hsq := gaussSum_sq (χ := quadraticCharL (L := L) (p := p))
    (ψ := quadraticAddChar ζ hζ) hχ hquad
    (AddChar.zmodChar_primitive_of_primitive_root p hζ)
  calc
    quadraticGauss ζ hζ ^ 2 =
        gaussSum (quadraticCharL (L := L)) (quadraticAddChar ζ hζ) ^ 2 := rfl
    _ = quadraticCharL (L := L) (p := p) (-1) * Fintype.card (ZMod p) := hsq
    _ = algebraMap ℤ L (quadraticChar (ZMod p) (-1) * (p : ℤ)) := by
      simp [quadraticCharL]
    _ = algebraMap ℤ L (signedPrimeDiscriminant p) := by
      rw [quadraticChar_neg_one_mul_card_eq_signedPrimeDiscriminant hp2]

theorem quadraticGauss_ne_zero
    {L : Type*} [Field L] [Algebra ℚ L]
    {p : ℕ} [Fact p.Prime]
    [IsCyclotomicExtension {p} ℚ L]
    (hp2 : p ≠ 2) (ζ : L) (hζ : IsPrimitiveRoot ζ p) :
    quadraticGauss ζ hζ ≠ 0 := by
  intro hzero
  have hsq := quadraticGauss_sq hp2 ζ hζ
  rw [hzero, zero_pow (by norm_num : 2 ≠ 0)] at hsq
  have hne : algebraMap ℤ L (signedPrimeDiscriminant p) ≠ 0 := by
    intro hz
    have hz' : signedPrimeDiscriminant p = 0 :=
      (algebraMap_int_injective (L := L)) (by simpa using hz)
    have hp : p.Prime := Fact.out
    have hpz : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
    rcases signedPrimeDiscriminant_eq_or_neg p with h | h <;> omega
  exact hne hsq.symm

/-! The finite-field nonvanishing input needed for a residue-field transport
argument does not require an `Algebra ℚ` structure.  The source of the Gauss
sum is still `ZMod p`, while the target field may have a distinct prime
characteristic `q`; the cardinality hypothesis is exactly `q ∤ p`. -/

theorem quadraticGauss_ne_zero_of_char_ne
    {K : Type*} [Field K] {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    [CharP K q] (hp2 : p ≠ 2) (hq2 : q ≠ 2) (hpq : q ≠ p)
    (ζ : K) (hζ : IsPrimitiveRoot ζ p) :
    quadraticGauss ζ hζ ≠ 0 := by
  have htwo : (2 : K) ≠ 0 := by
    intro hzero
    have hdiv : q ∣ 2 := (CharP.cast_eq_zero_iff K q 2).mp hzero
    have hqle : q ≤ 2 := Nat.le_of_dvd (by norm_num) hdiv
    have hqpos : 2 ≤ q := (Fact.out : Nat.Prime q).two_le
    omega
  have hsource_char : ringChar (ZMod p) ≠ 2 := by
    rw [ZMod.ringChar_zmod_n]
    exact hp2
  have hχ : quadraticCharL (L := K) (p := p) ≠ 1 := by
    obtain ⟨a, ha⟩ := quadraticChar_exists_neg_one' (F := ZMod p) hsource_char
    refine MulChar.ne_one_iff.mpr ⟨a, ?_⟩
    simpa only [quadraticCharL, MulChar.ringHomComp_apply, ha,
      eq_intCast, Int.cast_neg, Int.cast_one] using
      (show (-1 : K) ≠ 1 from by
        intro h
        apply htwo
        calc
          (2 : K) = 1 + 1 := by norm_num
          _ = (-1 : K) + 1 := (congrArg (fun x : K => x + 1) h).symm
          _ = 0 := neg_add_cancel _)
  have hcard : (Fintype.card (ZMod p) : K) ≠ 0 := by
    rw [ZMod.card]
    intro hzero
    have hdiv : q ∣ p := (CharP.cast_eq_zero_iff K q p).mp hzero
    rcases (Nat.dvd_prime (Fact.out : Nat.Prime p)).mp hdiv with hq1 | hqp
    · exact (Fact.out : Nat.Prime q).ne_one hq1
    · exact hpq hqp
  change gaussSum (quadraticCharL (L := K)) (quadraticAddChar ζ hζ) ≠ 0
  exact gaussSum_ne_zero_of_nontrivial hcard hχ
    (AddChar.zmodChar_primitive_of_primitive_root p hζ)

private theorem quadraticAddChar_map
    {L : Type*} [Field L] [Algebra ℚ L]
    {p : ℕ} [Fact p.Prime]
    [IsCyclotomicExtension {p} ℚ L]
    (ζ : L) (hζ : IsPrimitiveRoot ζ p)
    (σ : L ≃ₐ[ℚ] L) (ut : (ZMod p)ˣ)
    (hσζ : σ ζ = ζ ^ (ut : ZMod p).val) (a : ZMod p) :
    σ (quadraticAddChar ζ hζ a) =
      (quadraticAddChar ζ hζ).mulShift (ut : ZMod p) a := by
  letI : NeZero p := ⟨(Fact.out : Nat.Prime p).ne_zero⟩
  rw [quadraticAddChar, AddChar.zmodChar_apply hζ.pow_eq_one, map_pow,
    hσζ, AddChar.mulShift_apply,
    AddChar.zmodChar_apply hζ.pow_eq_one]
  rw [← pow_mul, ZMod.val_mul, pow_eq_pow_mod _ hζ.pow_eq_one]

theorem map_quadraticGauss_of_power
    {L : Type*} [Field L] [Algebra ℚ L]
    {p : ℕ} [Fact p.Prime]
    [IsCyclotomicExtension {p} ℚ L]
    (ζ : L) (hζ : IsPrimitiveRoot ζ p) (σ : L ≃ₐ[ℚ] L)
    (ut : (ZMod p)ˣ) (hσζ : σ ζ = ζ ^ (ut : ZMod p).val) :
    σ (quadraticGauss ζ hζ) =
      algebraMap ℤ L (quadraticChar (ZMod p) (ut : ZMod p)) *
        quadraticGauss ζ hζ := by
  letI : NeZero p := ⟨(Fact.out : Nat.Prime p).ne_zero⟩
  let χL : MulChar (ZMod p) L := quadraticCharL (L := L) (p := p)
  let ψ : AddChar (ZMod p) L := quadraticAddChar ζ hζ
  have hquad : MulChar.IsQuadratic χL :=
    (quadraticChar_isQuadratic (ZMod p)).comp (algebraMap ℤ L)
  have hmap : σ (quadraticGauss ζ hζ) = gaussSum χL (ψ.mulShift ut) := by
    change σ (∑ a : ZMod p, χL a * ψ a) =
      ∑ a : ZMod p, χL a * ψ.mulShift (ut : ZMod p) a
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro a ha
    rw [map_mul]
    congr 1
    · simp [χL, quadraticCharL]
    · exact quadraticAddChar_map ζ hζ σ ut hσζ a
  calc
    σ (quadraticGauss ζ hζ) = gaussSum χL (ψ.mulShift ut) := hmap
    _ = χL⁻¹ ut * gaussSum χL ψ := gaussSum_mulShift_eq χL ψ ut
    _ = χL ut * quadraticGauss ζ hζ := by
      rw [hquad.inv]
      rfl
    _ = algebraMap ℤ L (quadraticChar (ZMod p) (ut : ZMod p)) *
        quadraticGauss ζ hζ := by
      rfl

theorem map_quadraticGauss_of_square
    {L : Type*} [Field L] [Algebra ℚ L]
    {p : ℕ} [Fact p.Prime]
    [IsCyclotomicExtension {p} ℚ L]
    (ζ : L) (hζ : IsPrimitiveRoot ζ p) (σ : L ≃ₐ[ℚ] L)
    (ut : (ZMod p)ˣ) (hut0 : (ut : ZMod p) ≠ 0)
    (htsq : IsSquare (ut : ZMod p))
    (hσζ : σ ζ = ζ ^ (ut : ZMod p).val) :
    σ (quadraticGauss ζ hζ) = quadraticGauss ζ hζ := by
  rw [map_quadraticGauss_of_power ζ hζ σ ut hσζ]
  have hχ : quadraticChar (ZMod p) (ut : ZMod p) = 1 :=
    (quadraticChar_one_iff_isSquare hut0).mpr htsq
  simp [hχ]

theorem map_quadraticGauss_of_nonsquare
    {L : Type*} [Field L] [Algebra ℚ L]
    {p : ℕ} [Fact p.Prime]
    [IsCyclotomicExtension {p} ℚ L]
    (ζ : L) (hζ : IsPrimitiveRoot ζ p) (σ : L ≃ₐ[ℚ] L)
    (ut : (ZMod p)ˣ)
    (htnsq : ¬ IsSquare (ut : ZMod p))
    (hσζ : σ ζ = ζ ^ (ut : ZMod p).val) :
    σ (quadraticGauss ζ hζ) = -quadraticGauss ζ hζ := by
  rw [map_quadraticGauss_of_power ζ hζ σ ut hσζ]
  have hχ : quadraticChar (ZMod p) (ut : ZMod p) = -1 :=
    quadraticChar_neg_one_iff_not_isSquare.mpr htnsq
  simp [hχ]

theorem map_quadraticGauss_of_cyclotomicAut
    {L : Type*} [Field L] [Algebra ℚ L]
    {p : ℕ} [Fact p.Prime]
    [IsCyclotomicExtension {p} ℚ L]
    (ζ : L) (hζ : IsPrimitiveRoot ζ p) (σ : L ≃ₐ[ℚ] L) :
    ∃ ut : (ZMod p)ˣ, (ut : ZMod p) ≠ 0 ∧
      σ (quadraticGauss ζ hζ) =
        algebraMap ℤ L (quadraticChar (ZMod p) (ut : ZMod p)) *
          quadraticGauss ζ hζ := by
  obtain ⟨ut, hut0, hσζ⟩ := cyclotomicAut_power_spec ζ hζ σ
  exact ⟨ut, hut0, map_quadraticGauss_of_power ζ hζ σ ut hσζ⟩

private theorem coeff_Dpoly_map_of_power
    {L : Type*} [Field L] [Algebra ℚ L]
    {p : ℕ} [Fact p.Prime]
    [IsCyclotomicExtension {p} ℚ L]
    (ζ : L) (hζ : IsPrimitiveRoot ζ p) (σ : L ≃ₐ[ℚ] L)
    (ut : (ZMod p)ˣ) (hut0 : (ut : ZMod p) ≠ 0)
    (hσζ : σ ζ = ζ ^ (ut : ZMod p).val) (d : Fin 2 →₀ ℕ) :
    σ (MvPolynomial.coeff d (Dpoly (p := p) ζ)) =
      algebraMap ℤ L (quadraticChar (ZMod p) (ut : ZMod p)) *
        MvPolynomial.coeff d (Dpoly (p := p) ζ) := by
  letI : NeZero p := ⟨(Fact.out : Nat.Prime p).ne_zero⟩
  by_cases hsq : IsSquare (ut : ZMod p)
  · have hpoly := map_Dpoly_of_square ζ hζ (ut : ZMod p)
      σ.toRingEquiv hut0 hsq hσζ
    have hχ : quadraticChar (ZMod p) (ut : ZMod p) = 1 :=
      (quadraticChar_one_iff_isSquare hut0).mpr hsq
    calc
      σ (MvPolynomial.coeff d (Dpoly (p := p) ζ)) =
          MvPolynomial.coeff d
            (MvPolynomial.map σ.toRingEquiv.toRingHom (Dpoly (p := p) ζ)) := by
        symm
        exact MvPolynomial.coeff_map σ.toRingEquiv.toRingHom
          (Dpoly (p := p) ζ) d
      _ = MvPolynomial.coeff d (Dpoly (p := p) ζ) := by rw [hpoly]
      _ = algebraMap ℤ L (quadraticChar (ZMod p) (ut : ZMod p)) *
          MvPolynomial.coeff d (Dpoly (p := p) ζ) := by simp [hχ]
  · have hpoly := map_Dpoly_of_nonsquare ζ hζ (ut : ZMod p)
      σ.toRingEquiv hut0 hsq hσζ
    have hχ : quadraticChar (ZMod p) (ut : ZMod p) = -1 :=
      quadraticChar_neg_one_iff_not_isSquare.mpr hsq
    calc
      σ (MvPolynomial.coeff d (Dpoly (p := p) ζ)) =
          MvPolynomial.coeff d
            (MvPolynomial.map σ.toRingEquiv.toRingHom (Dpoly (p := p) ζ)) := by
        symm
        exact MvPolynomial.coeff_map σ.toRingEquiv.toRingHom
          (Dpoly (p := p) ζ) d
      _ = -MvPolynomial.coeff d (Dpoly (p := p) ζ) := by
        rw [hpoly, MvPolynomial.coeff_neg]
      _ = algebraMap ℤ L (quadraticChar (ZMod p) (ut : ZMod p)) *
          MvPolynomial.coeff d (Dpoly (p := p) ζ) := by simp [hχ]

private theorem coeff_Dpoly_div_quadraticGauss_fixed
    {L : Type*} [Field L] [Algebra ℚ L]
    {p : ℕ} [Fact p.Prime]
    [IsCyclotomicExtension {p} ℚ L]
    (hp2 : p ≠ 2) (ζ : L) (hζ : IsPrimitiveRoot ζ p)
    (d : Fin 2 →₀ ℕ) (σ : L ≃ₐ[ℚ] L) :
    σ (MvPolynomial.coeff d (Dpoly (p := p) ζ) /
      quadraticGauss ζ hζ) =
      MvPolynomial.coeff d (Dpoly (p := p) ζ) /
        quadraticGauss ζ hζ := by
  letI : NeZero p := ⟨(Fact.out : Nat.Prime p).ne_zero⟩
  obtain ⟨ut, hut0, hσζ⟩ := cyclotomicAut_power_spec ζ hζ σ
  let s : L := algebraMap ℤ L (quadraticChar (ZMod p) (ut : ZMod p))
  have hcoeff := coeff_Dpoly_map_of_power ζ hζ σ ut hut0 hσζ d
  have hgauss := map_quadraticGauss_of_power ζ hζ σ ut hσζ
  have hs : s ≠ 0 := by
    rcases quadraticChar_dichotomy hut0 with h | h
    · simp [s, h]
    · simp [s, h]
  have hG : quadraticGauss ζ hζ ≠ 0 :=
    quadraticGauss_ne_zero hp2 ζ hζ
  rw [map_div₀]
  rw [hcoeff, hgauss]
  field_simp [s, hs, hG]

theorem coeff_Dpoly_eq_gauss_mul_rat
    {L : Type*} [Field L] [Algebra ℚ L]
    {p : ℕ} [Fact p.Prime]
    [IsCyclotomicExtension {p} ℚ L]
    (hp2 : p ≠ 2) (ζ : L) (hζ : IsPrimitiveRoot ζ p)
    (d : Fin 2 →₀ ℕ) :
    ∃ q : ℚ,
      MvPolynomial.coeff d (Dpoly (p := p) ζ) =
        algebraMap ℚ L q * quadraticGauss ζ hζ := by
  letI : IsGalois ℚ L := IsCyclotomicExtension.isGalois {p} ℚ L
  letI : FiniteDimensional ℚ L :=
    IsCyclotomicExtension.finiteDimensional {p} ℚ L
  have hrange := (IsGalois.mem_range_algebraMap_iff_fixed
    (MvPolynomial.coeff d (Dpoly (p := p) ζ) / quadraticGauss ζ hζ)).2
    (by
      intro σ
      exact coeff_Dpoly_div_quadraticGauss_fixed hp2 ζ hζ d σ)
  obtain ⟨q, hq⟩ := hrange
  refine ⟨q, ?_⟩
  have hG : quadraticGauss ζ hζ ≠ 0 :=
    quadraticGauss_ne_zero hp2 ζ hζ
  calc
    MvPolynomial.coeff d (Dpoly (p := p) ζ) =
        (MvPolynomial.coeff d (Dpoly (p := p) ζ) /
          quadraticGauss ζ hζ) * quadraticGauss ζ hζ := by
      exact (div_mul_cancel₀ _ hG).symm
    _ = algebraMap ℚ L q * quadraticGauss ζ hζ := by rw [← hq]

private theorem coeff_Dpoly_eq_gauss_mul_int
    {L : Type*} [Field L] [Algebra ℚ L]
    {p : ℕ} [Fact p.Prime]
    [IsCyclotomicExtension {p} ℚ L]
    (hp2 : p ≠ 2) (ζ : L) (hζ : IsPrimitiveRoot ζ p)
    (d : Fin 2 →₀ ℕ) :
    ∃ a : ℤ,
      MvPolynomial.coeff d (Dpoly (p := p) ζ) =
        algebraMap ℤ L a * quadraticGauss ζ hζ := by
  have hp : p.Prime := Fact.out
  obtain ⟨q, hq⟩ := coeff_Dpoly_eq_gauss_mul_rat hp2 ζ hζ d
  have hcint :
      IsIntegral ℤ (MvPolynomial.coeff d (Dpoly (p := p) ζ)) :=
    coeff_Dpoly_isIntegral_int ζ hζ d
  have hc2int :
      IsIntegral ℤ (MvPolynomial.coeff d (Dpoly (p := p) ζ) ^ 2) :=
    hcint.pow 2
  let r : ℚ := (signedPrimeDiscriminant p : ℚ) * q ^ 2
  have hmap : algebraMap ℚ L r =
      MvPolynomial.coeff d (Dpoly (p := p) ζ) ^ 2 := by
    dsimp [r]
    calc
      algebraMap ℚ L ((signedPrimeDiscriminant p : ℚ) * q ^ 2) =
          algebraMap ℤ L (signedPrimeDiscriminant p) *
            (algebraMap ℚ L q) ^ 2 := by
        rw [map_mul, map_pow]
        congr 1
        simp
      _ = (MvPolynomial.coeff d (Dpoly (p := p) ζ)) ^ 2 := by
        rw [hq, mul_pow, quadraticGauss_sq hp2 ζ hζ]
        ring
  have hrint : IsIntegral ℤ r :=
    isIntegral_rat_of_map_isIntegral r
      (MvPolynomial.coeff d (Dpoly (p := p) ζ) ^ 2) hmap hc2int
  obtain ⟨z, hz⟩ := (rat_isIntegral_iff_exists_int r).mp hrint
  obtain ⟨a, ha⟩ := rat_eq_int_of_signedPrime_mul_sq hp
    (signedPrimeDiscriminant_eq_or_neg p) q ⟨z, by simpa [r] using hz⟩
  refine ⟨a, ?_⟩
  calc
    MvPolynomial.coeff d (Dpoly (p := p) ζ) =
        algebraMap ℚ L q * quadraticGauss ζ hζ := hq
    _ = algebraMap ℚ L (a : ℚ) * quadraticGauss ζ hζ := by rw [ha]
    _ = algebraMap ℤ L a * quadraticGauss ζ hζ := by
      congr 1
      simp

theorem exists_Dpoly_over_gauss_int
    {L : Type*} [Field L] [Algebra ℚ L]
    {p : ℕ} [Fact p.Prime]
    [IsCyclotomicExtension {p} ℚ L]
    (hp2 : p ≠ 2) (ζ : L) (hζ : IsPrimitiveRoot ζ p) :
    ∃ SZ : MvPolynomial (Fin 2) ℤ,
      MvPolynomial.C (quadraticGauss ζ hζ) *
          MvPolynomial.map (algebraMap ℤ L) SZ =
        Dpoly (p := p) ζ := by
  classical
  let G : L := quadraticGauss ζ hζ
  let aOf : L → ℤ := fun c =>
    if hc0 : c = 0 then 0 else
      if hc : ∃ a : ℤ, c = algebraMap ℤ L a * G then
        Classical.choose hc
      else 0
  have haOf_zero : aOf 0 = 0 := by
    simp [aOf]
  let SZ : MvPolynomial (Fin 2) ℤ :=
    .ofCoeff <| Finsupp.mapRange aOf haOf_zero <|
      AddMonoidAlgebra.coeff (Dpoly (p := p) ζ)
  have hcoeff_SZ (d : Fin 2 →₀ ℕ) :
      MvPolynomial.coeff d SZ =
        aOf (MvPolynomial.coeff d (Dpoly (p := p) ζ)) := by
    change (Finsupp.mapRange aOf haOf_zero
      (AddMonoidAlgebra.coeff (Dpoly (p := p) ζ))) d = _
    rfl
  have hfactor (d : Fin 2 →₀ ℕ) :
      MvPolynomial.coeff d (Dpoly (p := p) ζ) =
        algebraMap ℤ L (aOf (MvPolynomial.coeff d (Dpoly (p := p) ζ))) * G := by
    by_cases hc0 : MvPolynomial.coeff d (Dpoly (p := p) ζ) = 0
    · simp [hc0, aOf, G]
    · obtain ⟨a, ha⟩ := coeff_Dpoly_eq_gauss_mul_int hp2 ζ hζ d
      have hc : ∃ a : ℤ,
          MvPolynomial.coeff d (Dpoly (p := p) ζ) =
            algebraMap ℤ L a * G := ⟨a, by simpa [G] using ha⟩
      have hchoose :
          MvPolynomial.coeff d (Dpoly (p := p) ζ) =
            algebraMap ℤ L (aOf (MvPolynomial.coeff d (Dpoly (p := p) ζ))) * G := by
        unfold aOf
        split
        · rename_i hzero
          exact (hc0 hzero).elim
        · rename_i hnonzero
          simpa using Classical.choose_spec hc
      exact hchoose
  refine ⟨SZ, ?_⟩
  apply MvPolynomial.ext
  intro d
  rw [MvPolynomial.coeff_C_mul, MvPolynomial.coeff_map, hcoeff_SZ]
  simpa [G, mul_comm] using (hfactor d).symm

theorem exists_Dpoly_square_normalization
    {L : Type*} [Field L] [Algebra ℚ L]
    {p : ℕ} [Fact p.Prime]
    [IsCyclotomicExtension {p} ℚ L]
    (hp2 : p ≠ 2) (ζ : L) (hζ : IsPrimitiveRoot ζ p) :
    ∃ SZ : MvPolynomial (Fin 2) ℤ,
      Dpoly (p := p) ζ ^ 2 =
        MvPolynomial.C (algebraMap ℤ L (signedPrimeDiscriminant p)) *
          (MvPolynomial.map (algebraMap ℤ L) SZ) ^ 2 := by
  obtain ⟨SZ, hSZ⟩ := exists_Dpoly_over_gauss_int hp2 ζ hζ
  refine ⟨SZ, ?_⟩
  calc
    Dpoly (p := p) ζ ^ 2 =
        (MvPolynomial.C (quadraticGauss ζ hζ) *
          MvPolynomial.map (algebraMap ℤ L) SZ) ^ 2 := by rw [hSZ]
    _ = MvPolynomial.C (quadraticGauss ζ hζ ^ 2) *
          (MvPolynomial.map (algebraMap ℤ L) SZ) ^ 2 := by
      simp only [mul_pow, MvPolynomial.C_pow]
    _ = MvPolynomial.C (algebraMap ℤ L (signedPrimeDiscriminant p)) *
          (MvPolynomial.map (algebraMap ℤ L) SZ) ^ 2 := by
      rw [quadraticGauss_sq hp2 ζ hζ]

end

end DkMath.NumberTheory.CyclotomicQRGaussNormalization
