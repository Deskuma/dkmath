/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.Legendre.GnomonSmallCarryPhase

#print "file: DkMath.NumberTheory.Legendre.GnomonCentralCarryCompensation"

namespace DkMath.NumberTheory.Legendre
open scoped BigOperators

/-- Central addition n+n in the same prime-power coordinate currency. -/
def gnomonCentralCarryEvents (n : ℕ) : Finset ℕ :=
  (Finset.Icc 1 (2 * n)).filter (fun d => IsPrimePow d ∧ d ≤ n % d + n % d)

/-- The existing Kummer receiver counts central exponent coordinates for each base. -/
theorem gnomonCentralCarry_factorization {n p b : ℕ} (hp : p.Prime)
    (hb : Nat.log p (2 * n) < b) :
    (Nat.choose (2 * n) n).factorization p =
      ((Finset.Ico 1 b).filter (fun a => p ^ a ≤ n % p ^ a + n % p ^ a)).card := by
  have h := Nat.factorization_choose' (n := n) (k := n) hp (by simpa [two_mul] using hb)
  simpa [two_mul] using h

/-- Exact central logarithm, obtained by finite factorial cancellation. -/
theorem gnomonCentralCarry_log_eq (n : ℕ) :
    Real.log (Nat.choose (2 * n) n : ℝ) =
      ∑ d ∈ gnomonCentralCarryEvents n, ArithmeticFunction.vonMangoldt d := by
  have hf : Nat.choose (2 * n) n * n.factorial * n.factorial = (2 * n).factorial := by
    simpa [two_mul] using Nat.add_choose_mul_factorial_mul_factorial n n
  have hc : (Nat.choose (2 * n) n : ℝ) ≠ 0 := by
    exact_mod_cast Nat.choose_ne_zero (show n ≤ 2 * n by omega)
  have hn : (n.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  have hlog := congrArg (fun k : ℕ => Real.log (k : ℝ)) hf
  rw [Nat.cast_mul, Nat.cast_mul, Real.log_mul (mul_ne_zero hc hn) hn,
    Real.log_mul hc hn] at hlog
  have hfloor : Real.log ((2 * n).factorial : ℝ) =
      2 * Real.log (n.factorial : ℝ) +
        ∑ d ∈ gnomonCentralCarryEvents n, ArithmeticFunction.vonMangoldt d := by
    rw [log_factorial_eq_floor (2 * n),
      log_factorial_eq_floor_cutoff (show n ≤ 2 * n by omega)]
    unfold gnomonCentralCarryEvents
    rw [Finset.sum_filter, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro d hd
    have hdpos := (Finset.mem_Icc.mp hd).1
    have hadd := Nat.add_div hdpos (a := n) (b := n)
    rw [← two_mul n] at hadd
    by_cases hp : IsPrimePow d
    · by_cases hcarry : d ≤ n % d + n % d
      · simp only [hp, hcarry, and_self, ite_true] at *
        rw [hadd, Nat.cast_add, Nat.cast_add]
        ring
      · simp only [hp, hcarry, and_false, ite_false] at *
        rw [hadd, Nat.cast_add, Nat.cast_add]
        ring
    · have hz : ArithmeticFunction.vonMangoldt d = 0 := by
        simp [ArithmeticFunction.vonMangoldt_apply, hp]
      simp [hz, hp]
  linarith

def gnomonCommonCarryEvents (n : ℕ) : Finset ℕ :=
  gnomonPascalSmallCarryEvents n ∩ gnomonCentralCarryEvents n

def gnomonSmallOnlyCarryEvents (n : ℕ) : Finset ℕ :=
  gnomonPascalSmallCarryEvents n \ gnomonCentralCarryEvents n

def gnomonCentralOnlyCarryEvents (n : ℕ) : Finset ℕ :=
  gnomonCentralCarryEvents n \ gnomonPascalSmallCarryEvents n

/-- Both carriers split into the same common mass and their respective residual mass. -/
theorem gnomonCarry_common_split (n : ℕ) :
    gnomonPascalSmallCarryMass n =
      (∑ d ∈ gnomonCommonCarryEvents n, ArithmeticFunction.vonMangoldt d) +
        ∑ d ∈ gnomonSmallOnlyCarryEvents n, ArithmeticFunction.vonMangoldt d ∧
    Real.log (Nat.choose (2 * n) n : ℝ) =
      (∑ d ∈ gnomonCommonCarryEvents n, ArithmeticFunction.vonMangoldt d) +
        ∑ d ∈ gnomonCentralOnlyCarryEvents n, ArithmeticFunction.vonMangoldt d := by
  rw [gnomonCentralCarry_log_eq]
  unfold gnomonPascalSmallCarryMass gnomonCommonCarryEvents
    gnomonSmallOnlyCarryEvents gnomonCentralOnlyCarryEvents
  have hs := Finset.sum_sdiff (Finset.inter_subset_left
    (s₁ := gnomonPascalSmallCarryEvents n) (s₂ := gnomonCentralCarryEvents n))
    (f := fun d => ArithmeticFunction.vonMangoldt d)
  have hc := Finset.sum_sdiff (Finset.inter_subset_right
    (s₁ := gnomonPascalSmallCarryEvents n) (s₂ := gnomonCentralCarryEvents n))
    (f := fun d => ArithmeticFunction.vonMangoldt d)
  have heS : gnomonPascalSmallCarryEvents n \ (gnomonPascalSmallCarryEvents n ∩
      gnomonCentralCarryEvents n) = gnomonPascalSmallCarryEvents n \ gnomonCentralCarryEvents n := by
    ext d
    simp
  have heC : gnomonCentralCarryEvents n \ (gnomonPascalSmallCarryEvents n ∩
      gnomonCentralCarryEvents n) = gnomonCentralCarryEvents n \ gnomonPascalSmallCarryEvents n := by
    ext d
    simp
  rw [heS] at hs
  rw [heC] at hc
  constructor <;> linarith

/-- Exact weighted cancellation; this identity supplies no compensation inequality. -/
theorem gnomonCarry_compensation_defect (n : ℕ) :
    gnomonPascalSmallCarryMass n - Real.log (Nat.choose (2 * n) n : ℝ) =
      (∑ d ∈ gnomonSmallOnlyCarryEvents n, ArithmeticFunction.vonMangoldt d) -
      ∑ d ∈ gnomonCentralOnlyCarryEvents n, ArithmeticFunction.vonMangoldt d := by
  obtain ⟨hs, hc⟩ := gnomonCarry_common_split n
  linarith

/-- An exact reformulation of the open weighted comparison, not an unconditional bound. -/
theorem gnomonSmallCarry_le_central_iff_compensation (n : ℕ) :
    gnomonPascalSmallCarryMass n ≤ Real.log (Nat.choose (2 * n) n : ℝ) ↔
      (∑ d ∈ gnomonSmallOnlyCarryEvents n, ArithmeticFunction.vonMangoldt d) ≤
        ∑ d ∈ gnomonCentralOnlyCarryEvents n, ArithmeticFunction.vonMangoldt d := by
  have h := gnomonCarry_compensation_defect n
  constructor <;> intro hh <;> linarith

private theorem log_base_product {s : Finset ℕ} (hs : ∀ d ∈ s, IsPrimePow d) :
    (∑ d ∈ s, ArithmeticFunction.vonMangoldt d) =
      Real.log ((∏ d ∈ s, d.minFac : ℕ) : ℝ) := by
  rw [Nat.cast_prod, Real.log_prod]
  · apply Finset.sum_congr rfl
    intro d hd
    simp [ArithmeticFunction.vonMangoldt_apply, hs d hd]
  · intro d _
    exact_mod_cast (Nat.minFac_pos d).ne'

/-- Positive base products encode multiplicity across distinct exponent labels. -/
theorem gnomonCarry_compensation_iff_product (n : ℕ) :
    gnomonPascalSmallCarryMass n ≤ Real.log (Nat.choose (2 * n) n : ℝ) ↔
      (∏ d ∈ gnomonSmallOnlyCarryEvents n, d.minFac) ≤
        ∏ d ∈ gnomonCentralOnlyCarryEvents n, d.minFac := by
  rw [gnomonSmallCarry_le_central_iff_compensation]
  rw [log_base_product (by
      intro d hd
      exact (mem_gnomonPascalLowCarryEvents.mp
        (Finset.mem_filter.mp (Finset.mem_sdiff.mp hd).1).1).2.2.1),
    log_base_product (by
      intro d hd
      exact (Finset.mem_filter.mp (Finset.mem_sdiff.mp hd).1).2.1)]
  have hs : (0 : ℝ) < ((∏ d ∈ gnomonSmallOnlyCarryEvents n, d.minFac : ℕ) : ℝ) := by
    exact_mod_cast (Finset.prod_pos (fun d _ => Nat.minFac_pos d) :
      0 < ∏ d ∈ gnomonSmallOnlyCarryEvents n, d.minFac)
  have hc : (0 : ℝ) < ((∏ d ∈ gnomonCentralOnlyCarryEvents n, d.minFac : ℕ) : ℝ) := by
    exact_mod_cast (Finset.prod_pos (fun d _ => Nat.minFac_pos d) :
      0 < ∏ d ∈ gnomonCentralOnlyCarryEvents n, d.minFac)
  rw [Real.log_le_log_iff hs hc]
  exact_mod_cast (Iff.rfl :
    (∏ d ∈ gnomonSmallOnlyCarryEvents n, d.minFac) ≤
      (∏ d ∈ gnomonCentralOnlyCarryEvents n, d.minFac) ↔ _)

end DkMath.NumberTheory.Legendre
