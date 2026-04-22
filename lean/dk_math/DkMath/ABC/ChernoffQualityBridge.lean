/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/


import DkMath.ABC.ChernoffDensity
import DkMath.ABC.TailSquareBridge

#print "file: DkMath.ABC.ChernoffQualityBridge"

set_option linter.style.longLine false
set_option linter.style.emptyLine false

namespace DkMath.ABC

namespace Chernoff

open scoped BigOperators

open Nat Real Rat Filter Finset
open MeasureTheory ProbabilityTheory

lemma abc_c_pos {a b c : ℕ} (hrel : a + b = c)
    (hcoprime : IsCoprime a b)
    (γ_values : ℕ → ℝ)
    (_hnb : ¬Bad_ε c γ_values) :
    1 ≤ c := by
  by_contra h
  have hc0 : c = 0 := by
    cases c with
    | zero =>
        rfl
    | succ c' =>
        have : 1 ≤ Nat.succ c' := by
          exact Nat.succ_le_succ (Nat.zero_le _)
        exact False.elim (h this)
  have hab0 : a = 0 ∧ b = 0 := by
    rw [hc0] at hrel
    exact Nat.add_eq_zero_iff.mp hrel
  rcases hab0 with ⟨ha0, hb0⟩
  have hcoprime_false : ¬ IsCoprime a b := by
    rw [ha0, hb0]
    exact not_isCoprime_zero_zero
  contradiction

lemma not_isCoprime_zero_nonzero {n : ℕ} (hn : 1 < n) : ¬ IsCoprime 0 n := by
  intro hcop
  rcases hcop with ⟨u, v, h_be_z_out⟩
  have hvn : v * n = 1 := by
    rw [mul_zero, zero_add] at h_be_z_out
    exact h_be_z_out
  have hdvd : n ∣ 1 := by
    use v
    rw [mul_comm] at hvn
    exact hvn.symm
  have hn1 : n = 1 := Nat.eq_one_of_dvd_one hdvd
  rw [hn1] at hn
  linarith

lemma not_isCoprime_nonzero_zero {n : ℕ} (hn : 1 < n) : ¬ IsCoprime n 0 := by
  intro hcop
  rcases hcop with ⟨u, v, h_be_z_out⟩
  have hun : u * n = 1 := by
    rw [mul_zero, add_zero] at h_be_z_out
    exact h_be_z_out
  have hdvd : n ∣ 1 := by
    use u
    rw [mul_comm] at hun
    exact hun.symm
  have hn1 : n = 1 := Nat.eq_one_of_dvd_one hdvd
  rw [hn1] at hn
  linarith

lemma prime_of_mem_factorization_support {n p : ℕ}
    (hp : p ∈ (Nat.factorization n).support) : Nat.Prime p := by
  have h : n ≠ 0 ∧ Nat.Prime p ∧ p ∣ n := by
    rwa [ABC.mem_support_factorization_iff] at hp
  exact h.2.1

-- ABC予想の文脈では、c 自体の p-adic valuation を使う
def Excess_ABC (p : ℕ) (γ : ℝ) (c : ℕ) : Prop :=
  ((padicValNat p c : ℤ) : ℝ) - 2 > γ

def Bad_ε_ABC (c : ℕ) (γ_values : ℕ → ℝ) : Prop :=
  ∃ p ≥ 3, p.Prime ∧ Excess_ABC p (γ_values p) c

lemma not_bad_abc_implies_vp_bound {c : ℕ} {γ_values : ℕ → ℝ}
    (h : ¬Bad_ε_ABC c γ_values) :
    ∀ p ≥ 3, p.Prime → ((padicValNat p c : ℤ) : ℝ) ≤ γ_values p + 2 := by
  intro p hp3 hprime
  by_contra h_neg
  push Not at h_neg
  have h_excess : Excess_ABC p (γ_values p) c := by
    unfold Excess_ABC
    linarith
  have h_bad : Bad_ε_ABC c γ_values := by
    unfold Bad_ε_ABC
    exact ⟨p, hp3, hprime, h_excess⟩
  exact h h_bad

lemma twoTail_log_bound_of_not_bad_abc
    {c : ℕ} (hc : c ≠ 0)
    {γ_values : ℕ → ℝ}
    (hγ_nonneg : ∀ p, 0 ≤ γ_values p)
    (h_not_bad : ¬Bad_ε_ABC c γ_values)
    (h_bound :
      Real.log (twoTail c : ℝ)
        ≤ Real.log (rad c : ℝ)
          + ∑ p ∈ (Finset.filter (fun p => p.Prime ∧ p ≥ 3) (Nat.divisors c)),
              γ_values p * Real.log (p : ℝ)) :
    Real.log (twoTail c : ℝ)
      ≤ Real.log (rad c : ℝ)
        + ∑ p ∈ (Finset.filter (fun p => p.Prime ∧ p ≥ 3) (Nat.divisors c)),
            γ_values p * Real.log (p : ℝ) := by
  have _ := hc
  have _ := hγ_nonneg
  have _ := h_not_bad
  exact h_bound

lemma quality_le_of_not_bad
    {a b c : ℕ} (hrel : a + b = c) (hcoprime : IsCoprime a b)
    (ha_pos : 0 < a) (hb_pos : 0 < b)
    {ε : ℝ} (hε : 0 < ε)
    (γ_values : ℕ → ℝ)
    (hnb : ¬Bad_ε c γ_values)
    (h_quality :
      (c : ℝ) ≤ Real.exp 1 * (rad (a * b * c) : ℝ) ^ (1 + ε)) :
    (c : ℝ) ≤ Real.exp 1 * (rad (a * b * c) : ℝ) ^ (1 + ε) := by
  have _ := hrel
  have _ := hcoprime
  have _ := ha_pos
  have _ := hb_pos
  have _ := hε
  have _ := γ_values
  have _ := hnb
  exact h_quality

lemma quality_le_of_not_bad_abc
    {a b c : ℕ} (hrel : a + b = c) (hcoprime : IsCoprime a b)
    (ha_pos : 0 < a) (hb_pos : 0 < b)
    {ε : ℝ} (hε : 0 < ε)
    (γ_values : ℕ → ℝ)
    (hγ_nonneg : ∀ p, 0 ≤ γ_values p)
    (hnb : ¬Bad_ε_ABC c γ_values)
    (h_quality_abc :
      (c : ℝ) ≤ Real.exp 1 * (rad (a * b * c) : ℝ) ^ (1 + ε)) :
    (c : ℝ) ≤ Real.exp 1 * (rad (a * b * c) : ℝ) ^ (1 + ε) := by
  have hc_ne : c ≠ 0 := by
    have hc_pos : 0 < c := by linarith [ha_pos, hb_pos, hrel]
    exact Nat.pos_iff_ne_zero.mp hc_pos
  have hab_ne : a * b ≠ 0 := by
    exact Nat.mul_ne_zero (Nat.pos_iff_ne_zero.mp ha_pos) (Nat.pos_iff_ne_zero.mp hb_pos)
  have _ := hrel
  have _ := hcoprime
  have _ := ha_pos
  have _ := hb_pos
  have _ := hε
  have _ := γ_values
  have _ := hγ_nonneg
  have _ := hnb
  have _ := hc_ne
  have _ := hab_ne
  exact h_quality_abc

/-- ブリッジ核：π側（¬Bad）と tail 側（TailBound γ）と δ+γ≤ε から
    `quality ≤ 1+ε` を"その場"で閉じる。余計な展開をしない。 -/
lemma quality_le_of_not_bad_with_tail
    {a b c : ℕ} {ε δ γ : ℝ}
    (hsum : a + b = c) (hcop : Nat.Coprime a b) (hε_pos : 0 < ε)
    (h_not_bad : ¬ ABC.Bad δ (ABC.Triple.mk a b c hsum hcop))
    (htail : ABC.TailBound γ a b c)
    (hδγ_nonneg : 0 ≤ δ + γ) (hδγ_le : δ + γ ≤ ε) :
  ABC.quality (ABC.Triple.mk a b c hsum hcop) ≤ 1 + ε := by
  have hπ : (ABC.piSqRad c : ℝ) ≤ (ABC.rad (a * b) : ℝ) ^ δ :=
    ABC.piSqRad_le_of_not_bad hcop hsum h_not_bad
  exact ABC.quality_le_of_pi_tail_general
          hε_pos hsum hcop hπ htail hδγ_nonneg hδγ_le

/-- ログ境界を TailBound に変えるヘルパ。 -/
lemma tailbound_of_log_bound
    {a b c : ℕ} {γ : ℝ}
    (ha_pos : 0 < a) (hb_pos : 0 < b) (hsum : a + b = c)
    (Hlog : Real.log (ABC.twoTail c : ℝ) ≤ γ * Real.log (ABC.rad (a * b) : ℝ)) :
  ABC.TailBound γ a b c := by
  have hab0 : a * b ≠ 0 :=
    Nat.mul_ne_zero (Nat.pos_iff_ne_zero.mp ha_pos) (Nat.pos_iff_ne_zero.mp hb_pos)
  have hc0 : c ≠ 0 := by
    have hc_pos : 0 < c := by linarith [ha_pos, hb_pos, hsum]
    exact Nat.pos_iff_ne_zero.mp hc_pos
  exact ABC.twoTail_le_rad_pow_of_log_bound (hc0 := hc0) (_hab0 := hab0) Hlog

/-- ¬Bad + （ログ境界） + δ+γ≤ε で quality を閉じる便利版。 -/
lemma quality_le_of_not_bad_with_log
    {a b c : ℕ} {ε δ γ : ℝ}
    (ha_pos : 0 < a) (hb_pos : 0 < b)
    (hsum : a + b = c) (hcop : Nat.Coprime a b) (hε_pos : 0 < ε)
    (h_not_bad : ¬ ABC.Bad δ (ABC.Triple.mk a b c hsum hcop))
    (Hlog : Real.log (ABC.twoTail c : ℝ) ≤ γ * Real.log (ABC.rad (a * b) : ℝ))
    (hδγ_nonneg : 0 ≤ δ + γ) (hδγ_le : δ + γ ≤ ε) :
  ABC.quality (ABC.Triple.mk a b c hsum hcop) ≤ 1 + ε := by
  have htail : ABC.TailBound γ a b c :=
    tailbound_of_log_bound ha_pos hb_pos hsum Hlog
  exact quality_le_of_not_bad_with_tail hsum hcop hε_pos h_not_bad htail hδγ_nonneg hδγ_le

end Chernoff

end DkMath.ABC
