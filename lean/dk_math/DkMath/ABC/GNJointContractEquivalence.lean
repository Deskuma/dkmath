/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.ABC.GNExcessLargeBoundaryPacket

#print "file: DkMath.ABC.GNJointContractEquivalence"

set_option linter.style.longLine false
set_option linter.style.emptyLine false

/-!
# Equivalence audit for the odd-prime GN joint contract

This module shows that existence of the uniform odd-prime joint-pressure
contract is equivalent to the raw ABC bound.  The reverse construction fixes
the exponent at `p = 3`.

This is an equivalence audit only.  It neither constructs an unconditional
contract nor removes `abc_main_axiom`.
-/

namespace DkMath.ABC

open DkMath.CosmicFormulaBinom

/-- The raw natural-number ABC bound, with the same quantifiers as
`abc_main`. -/
def ABCRawBound (ε : ℝ) : Prop :=
  ∃ K : ℝ, 1 ≤ K ∧
    ∀ a b c : ℕ, a + b = c → Nat.Coprime a b →
      (c : ℝ) ≤
        K * (rad (a * b * c) : ℝ) ^ (1 + ε)

/-- Elementary cubic GN size estimate used in the reverse audit. -/
theorem GN_three_le_three_mul_add_sq
    (a b : ℕ) :
    GN 3 a b ≤ 3 * (a + b) ^ 2 := by
  rw [GN_eq_geom_sum₂]
  norm_num [Finset.sum_range_succ]
  nlinarith [Nat.zero_le a, Nat.zero_le b]

/-- A raw ABC bound constructs a joint-pressure contract at the fixed odd
prime exponent `3`. -/
theorem GNOddPrimeJointContract_of_ABCRawBound
    {ε : ℝ}
    (hε : 0 < ε)
    (Habc : ABCRawBound ε) :
    Nonempty (ABCGNOddPrimeJointContract ε) := by
  rcases Habc with ⟨K, hK, Habc⟩
  have hKpos : 0 < K := lt_of_lt_of_le zero_lt_one hK
  let ρ : ℝ := 2 * (1 + ε)
  let C : ℝ := Real.log 3 + 2 * Real.log K
  refine ⟨{
    hε := hε
    p := 3
    hp := by norm_num
    hpOdd := by decide
    ρ := ρ
    C := C
    margin := ?_
    jointBudget := ?_ }⟩
  · dsimp [ρ]
    norm_num
  · intro T ha hb
    have hc : 0 < T.c := by
      rw [← T.hsum]
      omega
    let R : ℝ := (rad (T.a * T.b * T.c) : ℕ)
    have habc : 0 < T.a * T.b * T.c :=
      Nat.mul_pos (Nat.mul_pos ha hb) hc
    have hRpos : 0 < R := by
      change 0 < (rad (T.a * T.b * T.c) : ℝ)
      exact_mod_cast rad_pos habc
    have habcBound :
        (T.c : ℝ) ≤ K * R ^ (1 + ε) := by
      exact Habc T.a T.b T.c T.hsum T.hcop
    have hrpowpos : 0 < R ^ (1 + ε) :=
      Real.rpow_pos_of_pos hRpos _
    have hlogc :
        Real.log (T.c : ℝ) ≤
          Real.log K + (1 + ε) * Real.log R := by
      have hlog :=
        Real.log_le_log (by exact_mod_cast hc) habcBound
      rw [Real.log_mul hKpos.ne' hrpowpos.ne',
        Real.log_rpow hRpos] at hlog
      exact hlog
    have hGNpos : 0 < GN 3 T.a T.b := by
      exact Nat.pos_of_ne_zero
        (GN_ne_zero_nat_of_two_le (by norm_num) ha hb)
    have hGNle :
        GN 3 T.a T.b ≤ 3 * T.c ^ 2 := by
      rw [← T.hsum]
      exact GN_three_le_three_mul_add_sq T.a T.b
    have hlogGN :
        Real.log ((GN 3 T.a T.b : ℕ) : ℝ) ≤
          ρ * Real.log R + C := by
      have hsize :
          Real.log ((GN 3 T.a T.b : ℕ) : ℝ) ≤
            Real.log ((3 : ℝ) * (T.c : ℝ) ^ 2) := by
        apply Real.log_le_log
        · exact_mod_cast hGNpos
        · exact_mod_cast hGNle
      have hcR : (T.c : ℝ) ≠ 0 := by exact_mod_cast hc.ne'
      rw [Real.log_mul (by norm_num : (3 : ℝ) ≠ 0)
          (pow_ne_zero 2 hcR),
        Real.log_pow] at hsize
      calc
        Real.log ((GN 3 T.a T.b : ℕ) : ℝ) ≤
            Real.log 3 + 2 * Real.log (T.c : ℝ) := by
          simpa using hsize
        _ ≤ Real.log 3 +
            2 * (Real.log K +
              (1 + ε) * Real.log R) := by
          linarith
        _ = ρ * Real.log R + C := by
          dsimp [ρ, C]
          ring
    apply
      (T.oddPrimeJointPressure_iff_nonExceptionalChannelMass
        (by norm_num) ha hb).mpr
    apply
      (T.nonExceptionalChannelMassBudget_iff_log_GN_le
        (by norm_num) (by decide) ha hb).mpr
    have hexceptional :
        0 ≤ Real.log
          (GNExceptionalSupportProduct 3 T.a T.b : ℝ) := by
      apply Real.log_nonneg
      exact_mod_cast
        (Nat.one_le_iff_ne_zero.mpr
          (Nat.ne_of_gt
            (GNExceptionalSupportProduct_pos 3 T.a T.b)))
    dsimp [ρ, C] at hlogGN ⊢
    linarith

/-- The raw ABC statement is equivalent to existence of the uniform
odd-prime joint-pressure contract. -/
theorem ABCRawBound_iff_nonempty_GNOddPrimeJointContract
    {ε : ℝ}
    (hε : 0 < ε) :
    ABCRawBound ε ↔
      Nonempty (ABCGNOddPrimeJointContract ε) := by
  constructor
  · exact GNOddPrimeJointContract_of_ABCRawBound hε
  · rintro ⟨H⟩
    exact abc_of_GNOddPrimeJointContract H

end DkMath.ABC
