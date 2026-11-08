/-
Copyright (c) 2026 Anthropic, PBC.
Copyright (c) 2026 D. and Wise Wolf.
SPDX-License-Identifier: Apache-2.0
License: RegularKummer/LICENSE
Upstream notices: RegularKummer/ANTHROPIC-NOTICE
Adapted from P2M/Sol/S_ValuationSubring_exists_pow_eq_of_kummer_descent.lean,
commit 115356cbc627159d0d16add0da6e9a2bb3655ed8.
Modified: valuation stability and exact radical descent in the reusable DkMath library.
-/

import DkMath.Lib.NumberTheory.StableValuationHenselian

#print "file: DkMath.Lib.NumberTheory.InertiaUnitExactRoots"

/-! # 単元近似から体内の正確な p 乗根へ
p ≠ q が導関数の可逆性を保証する。 -/
namespace DkMath.Lib.NumberTheory.InertiaResidue
noncomputable section
open Polynomial ValuationInertia
theorem exists_pow_eq_of_pow_sub_mem {R : Type*} [CommRing R] [HenselianLocalRing R] (n : ℕ)
    (hn : IsUnit (n : R)) (u z : R) (hu : IsUnit u) (hz : z ^ n - u ∈ IsLocalRing.maximalIdeal R) :
    ∃ v : R, v ^ n = u ∧ v - z ∈ IsLocalRing.maximalIdeal R := by
  have hn0 : n ≠ 0 := by
    rintro rfl
    rw [Nat.cast_zero] at hn
    exact not_isUnit_zero hn
  have hzn : IsUnit (z ^ n) := by
    by_contra h
    have hmem : z ^ n ∈ IsLocalRing.maximalIdeal R := (IsLocalRing.mem_maximalIdeal _).mpr h
    have : u ∈ IsLocalRing.maximalIdeal R := by
      have := Ideal.sub_mem _ hmem hz
      rwa [sub_sub_cancel] at this
    exact (IsLocalRing.mem_maximalIdeal _).mp this hu
  have hzu : IsUnit z := (isUnit_pow_iff hn0).mp hzn
  have hmonic : (X ^ n - C u : R[X]).Monic := monic_X_pow_sub_C u hn0
  have heval : (X ^ n - C u : R[X]).eval z ∈ IsLocalRing.maximalIdeal R := by
    simpa using hz
  have hderiv : IsUnit ((X ^ n - C u : R[X]).derivative.eval z) := by
    have : (X ^ n - C u : R[X]).derivative.eval z = (n : R) * z ^ (n - 1) := by
      simp [derivative_X_pow]
    rw [this]
    exact hn.mul (hzu.pow _)
  obtain ⟨v, hv, hvz⟩ := HenselianLocalRing.is_henselian (X ^ n - C u) hmonic z heval hderiv
  refine ⟨v, ?_, hvz⟩
  have := hv
  rw [IsRoot.def] at this
  simpa [sub_eq_zero] using this


/-- 異なる剰余標数の素数は、引き戻した付値環でも単元。 -/
theorem prime_isUnit_comap {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A q)
    (E : IntermediateField ℚ (AlgebraicClosure ℚ)) :
    IsUnit (p : A.comap (algebraMap E (AlgebraicClosure ℚ))) := by
  let R := A.comap (algebraMap E (AlgebraicClosure ℚ))
  have hv := InertiaRadical.valuation_prime_eq_one hp hq hpq A hA
  have hi : (p : E)⁻¹ ∈ R := by
    change algebraMap E (AlgebraicClosure ℚ) (p : E)⁻¹ ∈ A
    rw [map_inv₀, map_natCast, ← A.valuation_le_one_iff, map_inv₀, hv, inv_one]
  exact IsUnit.of_mul_eq_one ⟨(p : E)⁻¹, hi⟩
    (Subtype.ext (mul_inv_cancel₀ (by exact_mod_cast hp.ne_zero)))

/-- 元の固定体の上位体に属する、正確な単元 p 乗根。Hensel 入力は内部で証明する。 -/
theorem exact_unit_pRoot {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A q)
    (E : IntermediateField ℚ (AlgebraicClosure ℚ)) (hE : fixedField A ≤ E)
    (u : A.comap (algebraMap E (AlgebraicClosure ℚ))) (hu : IsUnit u) :
    ∃ w : A.comap (algebraMap E (AlgebraicClosure ℚ)), IsUnit w ∧ w ^ p = u := by
  let := StableValuation.overfield_henselian A E hE
  obtain ⟨z, hz⟩ := approximate_unit_pRoot hp hq hpq A hA E hE u hu
  obtain ⟨w, hw, _⟩ := exists_pow_eq_of_pow_sub_mem p
    (prime_isUnit_comap hp hq hpq A hA E) u z hu hz
  exact ⟨w, (isUnit_pow_iff hp.ne_zero).mp (hw.symm ▸ hu), hw⟩
end
end DkMath.Lib.NumberTheory.InertiaResidue

