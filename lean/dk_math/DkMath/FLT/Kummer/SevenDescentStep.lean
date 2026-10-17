/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Kummer.SevenDescentUnits

#print "file: DkMath.FLT.Kummer.SevenDescentStep"

/-! # FLT7教科書：同じ証人による一段降下
七商の七乗根を使い、特別な位相の根からlambda^mを完全に取り除く。
異なる三位相の一次恒等式から、同じ非分岐根を持つ重み付き方程式を再構成する。
-/

namespace DkMath.FLT.Kummer.SevenDescent

open DkMath.FLT.Seven DkMath.FLT.Kummer.SevenPrimaryNorm
open DkMath.FLT.Kummer.SevenRealGN SevenCyclotomicDegreeSixInt
open scoped BigOperators

noncomputable section

local instance : Fact (Nat.Prime 7) := ⟨by decide⟩
local notation "CC" => SevenCyclotomicDegreeSixInt.Ring

/-- 特別な一位相の根からlambda^mを取り出す。他の六根も同じ族に保持する。 -/
theorem State.exists_descent_roots {m : ℕ} (E : State (m + 1)) :
    ∃ (u : Fin 7 → CCˣ) (b : Fin 7 → CC) (g : CC),
      (∀ i, E.quotient (by omega) i = (u i : CC) * b i ^ 7) ∧
      E.quotient (by omega) (E.distinguishedPhase (by omega)) =
        (u (E.distinguishedPhase (by omega)) : CC) * (ramifiedUniformizer ^ m * g) ^ 7 ∧
      ¬ ramifiedUniformizer ∣ g ∧
      (∀ i, i ≠ E.distinguishedPhase (by omega) → ¬ ramifiedUniformizer ∣ b i) ∧
      (∀ i j, i ≠ j → IsCoprime (b i) (b j)) := by
  classical
  obtain ⟨u, b, hb⟩ := E.exists_quotient_roots
  let i0 := E.distinguishedPhase (by omega)
  let P := ∏ i ∈ (Finset.univ.erase i0), E.quotient (by omega) i
  have hP : ¬ ramifiedUniformizer ∣ P := by
    intro hd
    obtain ⟨i, hi, hd⟩ := (uniformizer_prime.dvd_finsetProd_iff _).mp hd
    exact (Finset.mem_erase.mp hi).1 ((E.quotient_dvd_iff (by omega) i).mp hd)
  have hprod : E.quotient (by omega) i0 * P =
      (E.epsilon : CC) * (ramifiedUniformizer ^ m * E.z) ^ 7 := by
    rw [← E.quotient_product]
    exact Finset.mul_prod_erase _ _ (Finset.mem_univ i0)
  have hdq : ramifiedUniformizer ^ (m * 7) ∣ E.quotient (by omega) i0 := by
    apply uniformizer_prime.pow_dvd_of_dvd_mul_right (m * 7) hP
    rw [hprod, mul_pow, ← pow_mul]
    exact dvd_mul_of_dvd_right (dvd_mul_right _ _) _
  rw [hb i0] at hdq
  have huinv : (↑((u i0)⁻¹) : CC) * (u i0 : CC) = 1 := (u i0).inv_val
  have hdb : ramifiedUniformizer ^ m ∣ b i0 := by
    apply (UniqueFactorizationMonoid.pow_dvd_pow_iff_dvd (by decide : 7 ≠ 0)).mp
    rw [← pow_mul]
    simpa only [← mul_assoc, huinv, one_mul] using
      dvd_mul_of_dvd_right hdq (↑((u i0)⁻¹) : CC)
  obtain ⟨g, hg⟩ := hdb
  have hgfac : E.quotient (by omega) i0 = (u i0 : CC) * (ramifiedUniformizer ^ m * g) ^ 7 := by
    rw [hb i0, hg]
  have hcancel : (u i0 : CC) * g ^ 7 * P = (E.epsilon : CC) * E.z ^ 7 := by
    apply mul_left_cancel₀ (pow_ne_zero (m * 7) ramifiedUniformizer_ne_zero)
    calc
      _ = E.quotient (by omega) i0 * P := by rw [hgfac]; ring
      _ = _ := by rw [hprod]; ring
  have hga : ¬ ramifiedUniformizer ∣ g := by
    intro hd
    have hz := congrArg ramifiedEval hcancel
    have hg0 := (ramifiedEval_eq_zero_iff_dvd _).mpr hd
    simp only [map_mul, map_pow, hg0, zero_pow (by decide : 7 ≠ 0),
      mul_zero, zero_mul] at hz
    have hzpow : ramifiedEval E.z ^ 7 = 0 :=
      (mul_eq_zero.mp hz.symm).resolve_left (E.epsilon.isUnit.map ramifiedEval).ne_zero
    exact E.z_away ((ramifiedEval_eq_zero_iff_dvd _).mp (eq_zero_of_pow_eq_zero hzpow))
  have haway : ∀ i, i ≠ i0 → ¬ ramifiedUniformizer ∣ b i := by
    intro i hi hd
    have hqi : ramifiedUniformizer ∣ E.quotient (by omega) i := by
      rw [hb i]
      exact dvd_mul_of_dvd_right (hd.trans (dvd_pow_self _ (by decide : 7 ≠ 0))) _
    exact hi ((E.quotient_dvd_iff (by omega) i).mp hqi)
  have hbcop : ∀ i j, i ≠ j → IsCoprime (b i) (b j) := by
    intro i j hij
    apply IsCoprime.mono _ _ (E.quotients_coprime (by omega) hij)
    · rw [hb i]
      exact dvd_mul_of_dvd_right (dvd_pow_self _ (by decide : 7 ≠ 0)) _
    · rw [hb j]
      exact dvd_mul_of_dvd_right (dvd_pow_self _ (by decide : 7 ≠ 0)) _
  exact ⟨u, b, g, hb, hgfac, hga, haway, hbcop⟩

/-- 同じ七商の三位相恒等式。元の端点から導き、ノルムの一致で置き換えない。 -/
theorem State.three_phase_identity {m : ℕ} (E : State m) (hm : 1 ≤ m)
    (i0 i1 i2 : Fin 7) :
    (phaseSlope i2 - phaseSlope i0) * E.quotient hm i1 +
      (phaseSlope i0 - phaseSlope i1) * E.quotient hm i2 =
      (phaseSlope i2 - phaseSlope i1) * E.quotient hm i0 := by
  unfold State.quotient
  ring

/-- 三位相を選び、深度mの新しい七乗方程式を非分岐な同じ三根で構成する。 -/
theorem State.exists_weighted_successor {m : ℕ} (E : State (m + 1)) :
    ∃ (x y z : CC) (u v e : CCˣ), IsCoprime x y ∧
      ¬ ramifiedUniformizer ∣ x ∧ ¬ ramifiedUniformizer ∣ y ∧ ¬ ramifiedUniformizer ∣ z ∧
      (u : CC) * x ^ 7 + (v : CC) * y ^ 7 =
        (e : CC) * (ramifiedUniformizer ^ m * z) ^ 7 := by
  classical
  obtain ⟨u, b, g, hb, hgfac, hga, ha, hcop⟩ := E.exists_descent_roots
  let i0 := E.distinguishedPhase (by omega)
  obtain ⟨i1, hi1⟩ := Finset.exists_mem_ne (s := (Finset.univ : Finset (Fin 7)))
    (by simp) i0
  obtain ⟨i2, hi2, hi21⟩ := Finset.exists_mem_ne
    (s := (Finset.univ.erase i0 : Finset (Fin 7))) (by simp) i1
  have h10 : i1 ≠ i0 := hi1.2
  have h20 : i2 ≠ i0 := (Finset.mem_erase.mp hi2).1
  have h21 : i2 ≠ i1 := hi21
  let a := (phaseSlope_sub_isUnit h20).unit
  let b' := (phaseSlope_sub_isUnit h10.symm).unit
  let c := (phaseSlope_sub_isUnit h21).unit
  have ha0 : (a : CC) = phaseSlope i2 - phaseSlope i0 := IsUnit.unit_spec _
  have hb0 : (b' : CC) = phaseSlope i0 - phaseSlope i1 := IsUnit.unit_spec _
  have hc0 : (c : CC) = phaseSlope i2 - phaseSlope i1 := IsUnit.unit_spec _
  refine ⟨b i1, b i2, g, a * u i1, b' * u i2, c * u i0,
    hcop _ _ h21.symm, ha _ h10, ha _ h20, hga, ?_⟩
  have hf := E.three_phase_identity (by omega) i0 i1 i2
  rw [hb i1, hb i2, hgfac] at hf
  simpa only [Units.val_mul, ha0, hb0, hc0, mul_assoc] using hf

/-- 重み付き状態の係数比を単元補題で吸収し、同じ証人をStateへ戻す。 -/
theorem descent_step (m : ℕ) : Nonempty (State (m + 1)) → Nonempty (State m) := by
  rintro ⟨E⟩
  by_cases hm : m = 0
  · subst m
    exact (no_state_one ⟨E⟩).elim
  obtain ⟨x, y, z, u, v, e, hxy, hx, hy, hz, he⟩ := E.exists_weighted_successor
  have hd : (7 : CC) ∣ (u : CC) * x ^ 7 + (v : CC) * y ^ 7 := by
    rw [he, mul_pow, ← pow_mul]
    exact dvd_mul_of_dvd_right
      (dvd_mul_of_dvd_left (seven_dvd_uniformizer_six.trans
        (pow_dvd_pow ramifiedUniformizer (by omega : 6 ≤ m * 7))) _) _
  obtain ⟨k, hk⟩ := ratio_seventh u v hx hd
  obtain ⟨E', _, _, _⟩ := normalize_weighted m x y z u v e k hxy hy hz he hk
  exact ⟨E'⟩

end
end DkMath.FLT.Kummer.SevenDescent
