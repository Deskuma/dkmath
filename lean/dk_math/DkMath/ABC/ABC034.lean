/-
Copyright (c) 2025 D. and Wise Wolf. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/


import DkMath.ABC.ABC033

#print "file: DkMath.ABC.ABC034"

set_option linter.style.longLine false
set_option linter.style.emptyLine false

/- Note:
※細分化前にエラー／警告を出さない補題・定理ファイル。
  ABC.lean で定義されるべき定理のうち、ABC.lean 内で定義されていた定理をここに移動している。
-/

namespace ABC

namespace Chernoff

open scoped BigOperators

open Nat Real Rat Filter Finset
open MeasureTheory ProbabilityTheory

-- ==========================================
-- Layer C: Chernoff Uniform Bound
-- ==========================================
--
-- Core API: t is an ARGUMENT, not fixed internally
-- Returns (C, X0) such that card ≤ C·X·exp(-t·γ·log p) for X ≥ X0

open Classical in
lemma chernoff_single_prime_uniform
    {p : ℕ} [Fact p.Prime] (hp3 : pge3 p)
    (γ : ℝ) (_hγ : 0 < γ)
    (t : ℝ) (ht : 0 < t) (ht_le : t ≤ Real.log 2 / Real.log 3) :
    ∃ (C : ℝ), C = const_C ∧ 0 < C ∧
      ∀ (X : ℕ), X ≥ const_X →
        ((Finset.filter (fun n => n ≤ X ∧ Excess p γ n) (Finset.Icc 0 X)).card : ℝ)
          ≤ C * (X : ℝ) * Real.exp (- t * γ * Real.log (p : ℝ)) := by
  classical
  use const_C
  constructor
  · rfl
  constructor
  · rw [const_C]; norm_num
  · intro X hX
    -- Key: Markov + MGF + absorption
    have hp_pos : 0 < (p : ℝ) := by
      have hp : Nat.Prime p := Fact.out
      exact_mod_cast hp.pos
    have hlogp_pos : 0 < Real.log (p : ℝ) := by
      apply Real.log_pos
      calc (1 : ℝ) < 3 := by norm_num
        _ ≤ p := by exact_mod_cast hp3

    -- Use MGF (mgf_padic_excess_bound_uniform requires const_X ≤ X)
    have hMGF := mgf_padic_excess_bound_uniform (p := p) hp3 t ht ht_le X (by exact hX)

    -- Absorb 4(X+1) ≤ 5·X for X≥100
    have habsorb : (4 : ℝ) * (X + 1) ≤ const_C * X := by
      -- 整数で示してから実数にキャストする
      have h_nat : 4 * X + 4 ≤ const_C * X := by
        rw [const_C]
        -- 4 * X + 4 ≤ 5 * X  ⇔ 4 ≤ X, which holds since hX : 100 ≤ X
        -- const_X = 100, so 4 ≤ const_X
        have : 4 ≤ const_X := by rw [const_X]; norm_num
        have : const_X ≤ X := hX
        linarith
      have : (4 : ℝ) * (↑X + 1) = 4 * ↑X + 4 := by ring
      rw [this]
      exact_mod_cast h_nat

    -- exp(-t·γ·log p) = p^(-t·γ)
    have hExp_rpow : Real.exp (-t * (γ * Real.log (p:ℝ))) = (p:ℝ) ^ (-t * γ) := by
      have hp' : 0 < (p:ℝ) := hp_pos
      simp only [Real.rpow_def_of_pos hp', mul_comm, mul_left_comm, mul_assoc]

    -- フィルタ条件の含意（Excess → ≥ form for Markov）
    have hIncl : (Finset.filter
        (fun n => n ≤ X ∧ Excess p γ n) (Finset.Icc 0 X)).card
      ≤ (Finset.filter
        (fun n => Real.log (p:ℝ) * (((Vp p n : ℤ) : ℝ) - 2) ≥ γ * Real.log (p:ℝ))
        (Finset.Icc 0 X)).card := by
      refine Finset.card_mono ?_
      intro n hn
      simp only [Finset.mem_filter, Finset.mem_Icc] at hn ⊢
      have ⟨hnIcc, ⟨hn_le, hcond⟩⟩ := hn
      have hgt' : γ < ((Vp p n : ℤ) : ℝ) - 2 := hcond
      have hmul : Real.log (p:ℝ) * γ < Real.log (p:ℝ) * (((Vp p n : ℤ) : ℝ) - 2) :=
        mul_lt_mul_of_pos_left hgt' hlogp_pos
      have : γ * Real.log (p:ℝ) < Real.log (p:ℝ) * (((Vp p n : ℤ) : ℝ) - 2) := by
        simpa [mul_comm] using hmul
      exact ⟨hnIcc, this.le⟩

    -- Markov適用
    have hMarkov := card_filter_le_exp_markov
      (s := Finset.Icc 0 X)
      (Z := fun n => Real.log (p:ℝ) * (((Vp p n : ℤ) : ℝ) - 2))
      (γ := γ * Real.log (p:ℝ))
      (t := t)
      (ht := le_of_lt ht)

    -- 結論：calc チェーン
    calc ((Finset.filter (fun n => n ≤ X ∧ Excess p γ n) (Finset.Icc 0 X)).card : ℝ)
        ≤ ((Finset.filter
          (fun n => Real.log (p:ℝ) * (((Vp p n : ℤ) : ℝ) - 2) ≥ γ * Real.log (p:ℝ))
          (Finset.Icc 0 X)).card : ℝ) := by exact_mod_cast hIncl
      _ ≤ Real.exp (-t * (γ * Real.log (p:ℝ))) *
          ∑ n ∈ Finset.Icc 0 X, Real.exp (t * (Real.log (p:ℝ) * (((Vp p n : ℤ) : ℝ) - 2))) := hMarkov
      _ = Real.exp (-t * (γ * Real.log (p:ℝ))) * (p:ℝ) ^ (-2 * t) * (∑ n ∈ Finset.Icc 0 X, (p:ℝ) ^ (t * ((Vp p n : ℤ) : ℝ))) := by
          -- Transform exp to rpow using exp-log identity and rpow factorization
          have hp_pos' : 0 < (p : ℝ) := by norm_cast; exact Nat.Prime.pos (Fact.out : Nat.Prime p)
          have h_exp_rpow : ∀ n, Real.exp (t * (Real.log (p : ℝ) * (((Vp p n : ℤ) : ℝ) - 2))) =
              (p : ℝ) ^ (t * ((Vp p n : ℤ) : ℝ)) * (p : ℝ) ^ (-2 * t) := by
            intro n
            let v := ((Vp p n : ℤ) : ℝ)
            have : t * (Real.log (p : ℝ) * (v - 2)) = (t * (v - 2)) * Real.log (p : ℝ) := by ring
            rw [this]
            rw [mul_comm (t * (v - 2)) (Real.log (p : ℝ))]
            rw [← Real.rpow_def_of_pos hp_pos']
            have : (p : ℝ) ^ (t * (v - 2)) = (p : ℝ) ^ (t * v) * (p : ℝ) ^ (-2 * t) := by
                rw [← Real.rpow_add hp_pos' (t * v) (-2 * t)]
                congr 1
                ring
            rw [this]
          have h_sum :
            ∑ n ∈ Finset.Icc 0 X, Real.exp (t * (Real.log (p : ℝ) * (((Vp p n : ℤ) : ℝ) - 2)))
            = (p : ℝ) ^ (-2 * t) * ∑ n ∈ Finset.Icc 0 X, (p : ℝ) ^ (t * ((Vp p n : ℤ) : ℝ)) := by
            rw [Finset.sum_congr rfl (fun n _ => h_exp_rpow n), ← Finset.sum_mul, mul_comm]
          rw [h_sum, ←mul_assoc, hExp_rpow]
      _ = (p:ℝ) ^ (-t * γ) * (p:ℝ) ^ (-2 * t) * (∑ n ∈ Finset.Icc 0 X, (p:ℝ) ^ (t * ((Vp p n : ℤ) : ℝ))) := by
          rw [hExp_rpow]
      _ = (p:ℝ) ^ (-t * (γ + 2)) * (∑ n ∈ Finset.Icc 0 X, (p:ℝ) ^ (t * ((Vp p n : ℤ) : ℝ))) := by
          have : (p:ℝ) ^ (-t * γ) * (p:ℝ) ^ (-2 * t) = (p:ℝ) ^ (-t * (γ + 2)) := by
            rw [← Real.rpow_add hp_pos]
            congr 1
            ring
          rw [this]
      _ ≤ (p:ℝ) ^ (-t * (γ + 2)) * (4 * (X + 1)) := by
          apply mul_le_mul_of_nonneg_left hMGF
          apply Real.rpow_nonneg; linarith
      _ ≤ (p:ℝ) ^ (-t * (γ + 2)) * (5 * X) := by
          apply mul_le_mul_of_nonneg_left habsorb
          apply Real.rpow_nonneg; linarith
      _ = 5 * (X : ℝ) * ((p:ℝ) ^ (-t * (γ + 2))) := by ring
      _ ≤ 5 * (X : ℝ) * Real.exp (- t * γ * Real.log (p : ℝ)) := by
        apply mul_le_mul_of_nonneg_left
        · have hp_pos' : 0 < (p : ℝ) := hp_pos
          have h_eq_rpow_exp : (p : ℝ) ^ (-t * (γ + 2)) = Real.exp (-t * γ * Real.log (p : ℝ) - 2 * t * Real.log (p : ℝ)) := by
            rw [Real.rpow_def_of_pos hp_pos']
            ring_nf
          have h_exp_le : Real.exp (-t * γ * Real.log (p : ℝ) - 2 * t * Real.log (p : ℝ)) ≤ Real.exp (-t * γ * Real.log (p : ℝ)) := by
            apply Real.exp_le_exp.mpr; nlinarith
          have h_pow_le_exp : (p : ℝ) ^ (-t * (γ + 2)) ≤ Real.exp (-t * γ * Real.log (p : ℝ)) := by
            rw [h_eq_rpow_exp]; exact h_exp_le
          exact h_pow_le_exp
        · norm_num

open Classical in
lemma chernoff_single_prime_uniform_rpow
    {p : ℕ} [Fact p.Prime] (hp3 : pge3 p)
    (γ : ℝ) (_hγ : 0 < γ)
    (t : ℝ) (ht : 0 < t) (ht_le : t ≤ Real.log 2 / Real.log 3) :
    ∀ (X : ℕ), X ≥ const_X →
      ((Finset.filter (fun n => n ≤ X ∧ Excess p γ n) (Finset.Icc 0 X)).card : ℝ)
        ≤ const_C * (X : ℝ) * (p:ℝ) ^ (-t * (γ + 2)) := by
  classical
  intro X hX
  -- Key: Markov + MGF + absorption
  have hp_pos : 0 < (p : ℝ) := by
    have hp : Nat.Prime p := Fact.out
    exact_mod_cast hp.pos
  have hlogp_pos : 0 < Real.log (p : ℝ) := by
    apply Real.log_pos
    calc (1 : ℝ) < 3 := by norm_num
      _ ≤ p := by exact_mod_cast hp3

  -- Use MGF (mgf_padic_excess_bound_uniform requires const_X ≤ X)
  have hMGF := mgf_padic_excess_bound_uniform (p := p) hp3 t ht ht_le X (by exact hX)

  -- Absorb 4(X+1) ≤ 5·X for X≥100
  have habsorb : (4 : ℝ) * (X + 1) ≤ const_C * X := by
    -- 整数で示してから実数にキャストする
    have h_nat : 4 * X + 4 ≤ const_C * X := by
      rw [const_C]
      -- 4 * X + 4 ≤ 5 * X  ⇔ 4 ≤ X, which holds since hX : 100 ≤ X
      -- const_X = 100, so 4 ≤ const_X
      have : 4 ≤ const_X := by rw [const_X]; norm_num
      have : const_X ≤ X := hX
      linarith
    have : (4 : ℝ) * (↑X + 1) = 4 * ↑X + 4 := by ring
    rw [this]
    exact_mod_cast h_nat

  -- exp(-t·γ·log p) = p^(-t·γ)
  have hExp_rpow : Real.exp (-t * (γ * Real.log (p:ℝ))) = (p:ℝ) ^ (-t * γ) := by
    have hp' : 0 < (p:ℝ) := hp_pos
    simp only [Real.rpow_def_of_pos hp', mul_comm, mul_left_comm, mul_assoc]

  -- フィルタ条件の含意（Excess → ≥ form for Markov）
  have hIncl : (Finset.filter
      (fun n => n ≤ X ∧ Excess p γ n) (Finset.Icc 0 X)).card
    ≤ (Finset.filter
      (fun n => Real.log (p:ℝ) * (((Vp p n : ℤ) : ℝ) - 2) ≥ γ * Real.log (p:ℝ))
      (Finset.Icc 0 X)).card := by
    refine Finset.card_mono ?_
    intro n hn
    simp only [Finset.mem_filter, Finset.mem_Icc] at hn ⊢
    have ⟨hnIcc, ⟨hn_le, hcond⟩⟩ := hn
    have hgt' : γ < ((Vp p n : ℤ) : ℝ) - 2 := hcond
    have hmul : Real.log (p:ℝ) * γ < Real.log (p:ℝ) * (((Vp p n : ℤ) : ℝ) - 2) :=
      mul_lt_mul_of_pos_left hgt' hlogp_pos
    have : γ * Real.log (p:ℝ) < Real.log (p:ℝ) * (((Vp p n : ℤ) : ℝ) - 2) := by
      simpa [mul_comm] using hmul
    exact ⟨hnIcc, this.le⟩

  -- Markov適用
  have hMarkov := card_filter_le_exp_markov
    (s := Finset.Icc 0 X)
    (Z := fun n => Real.log (p:ℝ) * (((Vp p n : ℤ) : ℝ) - 2))
    (γ := γ * Real.log (p:ℝ))
    (t := t)
    (ht := le_of_lt ht)

  -- 結論：calc チェーン
  calc ((Finset.filter (fun n => n ≤ X ∧ Excess p γ n) (Finset.Icc 0 X)).card : ℝ)
      ≤ ((Finset.filter
        (fun n => Real.log (p:ℝ) * (((Vp p n : ℤ) : ℝ) - 2) ≥ γ * Real.log (p:ℝ))
        (Finset.Icc 0 X)).card : ℝ) := by exact_mod_cast hIncl
    _ ≤ Real.exp (-t * (γ * Real.log (p:ℝ))) *
        ∑ n ∈ Finset.Icc 0 X, Real.exp (t * (Real.log (p:ℝ) * (((Vp p n : ℤ) : ℝ) - 2))) := hMarkov
    _ = Real.exp (-t * (γ * Real.log (p:ℝ))) * (p:ℝ) ^ (-2 * t) * (∑ n ∈ Finset.Icc 0 X, (p:ℝ) ^ (t * ((Vp p n : ℤ) : ℝ))) := by
        -- Transform exp to rpow using exp-log identity and rpow factorization
        have hp_pos' : 0 < (p : ℝ) := by norm_cast; exact Nat.Prime.pos (Fact.out : Nat.Prime p)
        have h_exp_rpow : ∀ n, Real.exp (t * (Real.log (p : ℝ) * (((Vp p n : ℤ) : ℝ) - 2))) =
            (p : ℝ) ^ (t * ((Vp p n : ℤ) : ℝ)) * (p : ℝ) ^ (-2 * t) := by
          intro n
          let v := ((Vp p n : ℤ) : ℝ)
          have : t * (Real.log (p : ℝ) * (v - 2)) = (t * (v - 2)) * Real.log (p : ℝ) := by ring
          rw [this]
          rw [mul_comm (t * (v - 2)) (Real.log (p : ℝ))]
          rw [← Real.rpow_def_of_pos hp_pos']
          have : (p : ℝ) ^ (t * (v - 2)) = (p : ℝ) ^ (t * v) * (p : ℝ) ^ (-2 * t) := by
              rw [← Real.rpow_add hp_pos' (t * v) (-2 * t)]
              congr 1
              ring
          rw [this]
        have h_sum :
          ∑ n ∈ Finset.Icc 0 X, Real.exp (t * (Real.log (p : ℝ) * (((Vp p n : ℤ) : ℝ) - 2)))
          = (p : ℝ) ^ (-2 * t) * ∑ n ∈ Finset.Icc 0 X, (p : ℝ) ^ (t * ((Vp p n : ℤ) : ℝ)) := by
          rw [Finset.sum_congr rfl (fun n _ => h_exp_rpow n), ← Finset.sum_mul, mul_comm]
        rw [h_sum, ←mul_assoc, hExp_rpow]
    _ = (p:ℝ) ^ (-t * γ) * (p:ℝ) ^ (-2 * t) * (∑ n ∈ Finset.Icc 0 X, (p:ℝ) ^ (t * ((Vp p n : ℤ) : ℝ))) := by
        rw [hExp_rpow]
    _ = (p:ℝ) ^ (-t * (γ + 2)) * (∑ n ∈ Finset.Icc 0 X, (p:ℝ) ^ (t * ((Vp p n : ℤ) : ℝ))) := by
        have : (p:ℝ) ^ (-t * γ) * (p:ℝ) ^ (-2 * t) = (p:ℝ) ^ (-t * (γ + 2)) := by
          rw [← Real.rpow_add hp_pos]
          congr 1
          ring
        rw [this]
    _ ≤ (p:ℝ) ^ (-t * (γ + 2)) * (4 * (X + 1)) := by
        apply mul_le_mul_of_nonneg_left hMGF
        apply Real.rpow_nonneg; linarith
    _ ≤ (p:ℝ) ^ (-t * (γ + 2)) * (5 * X) := by
        apply mul_le_mul_of_nonneg_left habsorb
        apply Real.rpow_nonneg; linarith
    _ = 5 * (X : ℝ) * ((p:ℝ) ^ (-t * (γ + 2))) := by ring

end Chernoff

end ABC
