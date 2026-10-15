/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Seven.PrimeTraceOneDirectCyclotomicCMTorsionPhase

#print "file: DkMath.FLT.Seven.PrimeTraceOneDirectCyclotomicKummerUnit"

/-!
# Kummer's unit lemma for the concrete seventh cyclotomic integer ring

Scalar congruence modulo seven eliminates the relative CM phase and the
real-cubic unit class. The resulting seventh root requires that congruence;
no surjectivity statement for arbitrary units is asserted.
-/

namespace DkMath.FLT.Seven

noncomputable section

local instance : Fact (Nat.Prime 7) := ⟨by norm_num⟩

namespace SevenCyclotomicDegreeSixInt

open SevenRealCubicInt

/-- A unit congruent to an integer modulo seven is fixed by conjugation. -/
theorem unit_eq_starUnit_of_congruent_mod_seven
    (u : Ringˣ)
    (h : DegreeSixUnitCongruentToRationalModSeven (u : Ring)) :
    u = starUnit u := by
  obtain ⟨m, _hm, hcong⟩ := h
  have hstar := star_sub_int_mem_sevenIdeal (u : Ring) m hcong
  have hdiff : (u : Ring) - star (u : Ring) ∈ sevenIdeal := by
    convert sevenIdeal.sub_mem hcong hstar using 1
    ring
  have hphase : u / starUnit u = 1 := by
    apply relativeNormOneScalarUnitAtSeven_unconditional
    · rw [map_div, quadraticNormUnit_star]
      simp
    · have hmul := sevenIdeal.mul_mem_right
        (↑((starUnit u)⁻¹) : Ring) hdiff
      have hinv : (star (u : Ring)) * (↑((starUnit u)⁻¹) : Ring) = 1 := by
        change (↑(starUnit u) : Ring) * (↑((starUnit u)⁻¹) : Ring) = 1
        simp
      change (u : Ring) * (↑((starUnit u)⁻¹) : Ring) - 1 ∈ sevenIdeal
      simpa only [sub_mul, hinv] using hmul
  exact div_eq_one.mp hphase

/-- Scalar congruence modulo seven makes the real norm unit a seventh power. -/
theorem exists_normUnit_seventhPower_of_congruent_mod_seven
    (u : Ringˣ)
    (h : DegreeSixUnitCongruentToRationalModSeven (u : Ring)) :
    ∃ v : SevenRealCubicIntˣ, quadraticNormUnit u = v ^ 7 := by
  obtain ⟨m, _hm, hcong⟩ := h
  rw [sevenIdeal, Ideal.mem_span_singleton] at hcong
  obtain ⟨k, hk⟩ := hcong
  have hu : (u : Ring) = (m : Ring) + 7 * k := by
    linear_combination hk
  let c : SevenRealCubicInt :=
    2 * (m : SevenRealCubicInt) * k.re +
      (alpha - 1) * (m : SevenRealCubicInt) * k.im +
      7 * QuadraticAlgebra.norm k
  have hnorm : (quadraticNormUnit u : SevenRealCubicInt) -
      (m : SevenRealCubicInt) ^ 2 = 7 * c := by
    rw [quadraticNormUnit_apply, hu]
    simp [QuadraticAlgebra.norm_def, c,
      show (7 : Ring).re = (7 : SevenRealCubicInt) from rfl,
      show (7 : Ring).im = 0 from rfl]
    ring
  have hnorm' : (quadraticNormUnit u : SevenRealCubicInt) =
      (m : SevenRealCubicInt) ^ 2 + 7 * c := by
    linear_combination hnorm
  have hlinear : thetaLinearModSeven (quadraticNormUnit u : SevenRealCubicInt) = 0 := by
    rw [hnorm']
    simp [thetaLinearModSeven, pow_two,
      show (7 : SevenRealCubicInt).fst = (7 : ℤ) from rfl,
      show (7 : SevenRealCubicInt).snd = 0 from rfl,
      show (7 : SevenRealCubicInt).thd = 0 from rfl,
      show (7 : ZMod 7) = 0 from by decide]
  have hsquare : thetaSquareModSeven (quadraticNormUnit u : SevenRealCubicInt) = 0 := by
    rw [hnorm']
    simp [thetaSquareModSeven, pow_two,
      show (7 : SevenRealCubicInt).fst = (7 : ℤ) from rfl,
      show (7 : SevenRealCubicInt).snd = 0 from rfl,
      show (7 : SevenRealCubicInt).thd = 0 from rfl,
      show (7 : ZMod 7) = 0 from by decide]
  apply (SevenRealCubic.unit_isSeventhPower_iff_projectiveLog_eq_zero
    (quadraticNormUnit u)).mpr
  rw [projectiveLog_apply]
  ext <;> simp only [unitNilpotentX, unitNilpotentY, hlinear, hsquare] <;> norm_num

/-- The congruence-constrained Kummer unit specification is inhabited for the
concrete degree-six cyclotomic integer ring. -/
theorem degreeSixKummerUnitLemmaAtSeven :
    DegreeSixKummerUnitLemmaAtSeven := by
  intro u h
  obtain ⟨v, hv⟩ := exists_normUnit_seventhPower_of_congruent_mod_seven u h
  have hsq : u ^ 2 = ofRealUnit v ^ 7 :=
    unit_sq_eq_ofReal_normUnit_pow u v
      (unit_eq_starUnit_of_congruent_mod_seven u h) hv
  refine ⟨ofRealUnit v ^ 4 * u⁻¹, ?_⟩
  symm
  calc
    (ofRealUnit v ^ 4 * u⁻¹) ^ 7 = (ofRealUnit v ^ 7) ^ 4 * (u ^ 7)⁻¹ := by
      rw [mul_pow]
      group
    _ = (u ^ 2) ^ 4 * (u ^ 7)⁻¹ := by rw [← hsq]
    _ = u := by group

end SevenCyclotomicDegreeSixInt

end

end DkMath.FLT.Seven
