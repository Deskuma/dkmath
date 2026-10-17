/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Kummer.SevenDescentPhases
import DkMath.Lib.NumberTheory.PrincipalIdealPower
import DkMath.Lib.NumberTheory.IdealPowerFactor

#print "file: DkMath.FLT.Kummer.SevenDescentPowers"

/-! # FLT7教科書：剥離商の七乗根
大域的な原始性を保つため、一段剥離した七商は互いに素となる。
単元をイデアルで消して七乗を配分し、七次PIDで元へ戻す。
-/

namespace DkMath.FLT.Kummer.SevenDescent

open DkMath.FLT.Seven DkMath.FLT.Kummer.SevenPrimaryNorm
open DkMath.FLT.Kummer.SevenRealGN SevenCyclotomicDegreeSixInt
open DkMath.Lib.NumberTheory
open scoped BigOperators

noncomputable section

local instance : Fact (Nat.Prime 7) := ⟨by decide⟩
local notation "CC" => SevenCyclotomicDegreeSixInt.Ring

/-- 異なる二位相の補正係数差は大域的な単元。 -/
theorem phaseSlope_sub_isUnit {i j : Fin 7} (hij : i ≠ j) :
    IsUnit (phaseSlope i - phaseSlope j) := by
  have hr (k : Fin 7) : zeta ^ k.val ∈ Polynomial.nthRootsFinset 7 (1 : CC) := by
    apply (Polynomial.mem_nthRootsFinset (by decide) 1).mpr
    rw [← pow_mul, Nat.mul_comm k.val 7, pow_mul, zeta_pow_seven, one_pow]
  have hne : zeta ^ i.val ≠ zeta ^ j.val := by
    intro he
    exact hij (Fin.ext (zeta_isPrimitiveRoot.pow_inj i.isLt j.isLt he))
  obtain ⟨u, hu⟩ :=
    zeta_isPrimitiveRoot.nthRootsFinset_pairwise_associated_sub_one_sub_of_prime
      (by decide : Nat.Prime 7) (hr i) (hr j) hne
  have he : phaseSlope i - phaseSlope j = -(u : CC) := by
    apply mul_right_cancel₀ ramifiedUniformizer_ne_zero
    have hi := phaseSlope_spec i
    have hj := phaseSlope_spec j
    dsimp [ramifiedUniformizer] at hi hj ⊢
    linear_combination hi - hj - hu
  rw [he]
  exact u.isUnit.neg

/-- 原始性は各剥離商とyの間に残る。 -/
theorem State.quotient_coprime_y {m : ℕ} (E : State m) (hm : 1 ≤ m) (i : Fin 7) :
    IsCoprime (E.quotient hm i) E.y := by
  have hc : IsCoprime (E.x + zeta ^ i.val * E.y) E.y := by
    simpa only [mul_comm] using E.coprime.add_mul_left_left (zeta ^ i.val)
  rw [E.quotient_spec hm i] at hc
  exact hc.of_mul_left_right

/-- 二商の差がyの単元倍なので、七つの商は互いに素。 -/
theorem State.quotients_coprime {m : ℕ} (E : State m) (hm : 1 ≤ m)
    {i j : Fin 7} (hij : i ≠ j) : IsCoprime (E.quotient hm i) (E.quotient hm j) := by
  obtain ⟨t, ht⟩ := phaseSlope_sub_isUnit hij
  have hy : E.y = (↑t⁻¹ : CC) * (E.quotient hm i - E.quotient hm j) := by
    have he : E.quotient hm i - E.quotient hm j = (t : CC) * E.y := by
      rw [ht]
      unfold State.quotient
      ring
    have htinv : (↑t⁻¹ : CC) * (t : CC) = 1 := t.inv_val
    rw [he, ← mul_assoc, htinv, one_mul]
  obtain ⟨a, b, hab⟩ := E.quotient_coprime_y hm i
  refine ⟨a + b * (↑t⁻¹ : CC), -(b * (↑t⁻¹ : CC)), ?_⟩
  rw [hy] at hab
  linear_combination hab

/-- 深度m+1では、七商の積から七つのlambdaを除いてちょうど深度mが残る。 -/
theorem State.quotient_product {m : ℕ} (E : State (m + 1)) :
    (∏ i : Fin 7, E.quotient (by omega) i) =
      (E.epsilon : CC) * (ramifiedUniformizer ^ m * E.z) ^ 7 := by
  apply mul_left_cancel₀ (pow_ne_zero 7 ramifiedUniformizer_ne_zero)
  calc
    _ = E.x ^ 7 + E.y ^ 7 := (E.product_quotients (by omega)).symm
    _ = _ := by rw [E.equation, pow_succ]; ring

/-- 単元は主イデアルで消える。各商のイデアルは七乗である。 -/
theorem State.quotient_ideal_power {m : ℕ} (E : State (m + 1)) (i : Fin 7) :
    ∃ I : Ideal CC, Ideal.span ({E.quotient (by omega) i} : Set CC) = I ^ 7 := by
  classical
  have hp : (∏ j : Fin 7, Ideal.span ({E.quotient (by omega) j} : Set CC)) =
      Ideal.span ({ramifiedUniformizer ^ m * E.z} : Set CC) ^ 7 := by
    rw [Ideal.prod_span_singleton, E.quotient_product,
      Ideal.span_singleton_mul_left_unit E.epsilon.isUnit, Ideal.span_singleton_pow]
  apply Finset.exists_eq_pow_of_mul_eq_pow_of_coprime
    (fun j _ k _ hjk => ?_) hp i (Finset.mem_univ i)
  rw [Ideal.isCoprime_span_singleton_iff]
  exact E.quotients_coprime (by omega) hjk

/-- 既存七次PIDから、七商すべての単元と七乗根を同時に選ぶ。 -/
theorem State.exists_quotient_roots {m : ℕ} (E : State (m + 1)) :
    ∃ (u : Fin 7 → CCˣ) (b : Fin 7 → CC),
      ∀ i, E.quotient (by omega) i = (u i : CC) * b i ^ 7 := by
  have hi (i : Fin 7) : ∃ (u : CCˣ) (b : CC),
      E.quotient (by omega) i = (u : CC) * b ^ 7 := by
    obtain ⟨I, hI⟩ := E.quotient_ideal_power i
    obtain ⟨v, b, hv, _, he⟩ :=
      exists_unit_mul_pow_of_span_eq_pow_of_isPrincipal (inferInstance : I.IsPrincipal) hI
    exact ⟨hv.unit, b, by simpa only [IsUnit.unit_spec] using he⟩
  choose u b hb using hi
  exact ⟨u, b, hb⟩

end
end DkMath.FLT.Kummer.SevenDescent
