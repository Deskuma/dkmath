/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.ABC.GNCubicPetalWieferich
import DkMath.ABC.GNJointContractEquivalence

#print "file: DkMath.ABC.GNCubicOrientedContract"

set_option linter.style.longLine false
set_option linter.style.emptyLine false

/-!
# Oriented cubic GN contract

The cubic contract is allowed to choose either left-coordinate orientation at
each positive triple.  This matches the reduced Petal branch exactly.

The final equivalence with `ABCRawBound` is an audit only.  It does not
construct an unconditional contract or prove ABC.
-/

namespace DkMath.ABC

open DkMath.CosmicFormulaBinom

/-- A cubic joint-pressure budget in either left-coordinate orientation. -/
def GNCubicOrientedJointBudgetAffine
    (T : Triple) (ρ C : ℝ) : Prop :=
  GNOddPrimeJointPressureBudgetAffine T 3 ρ C ∨
    GNOddPrimeJointPressureBudgetAffine T.swap 3 ρ C

/-- A uniform cubic joint-pressure contract aligned with Petal orientation. -/
structure ABCGNCubicOrientedContract (ε : ℝ) where
  hε : 0 < ε
  ρ : ℝ
  C : ℝ
  margin : ρ ≤ 2 * (1 + ε)
  orientedBudget :
    ∀ T : Triple, 0 < T.a → 0 < T.b →
      GNCubicOrientedJointBudgetAffine T ρ C

/-- A uniform oriented cubic contract yields the positive-triple ABC bound. -/
theorem abc_positive_of_GNCubicOrientedContract
    {ε : ℝ}
    (H : ABCGNCubicOrientedContract ε) :
    ∃ K : ℝ, 1 ≤ K ∧
      ∀ T : Triple, 0 < T.a → 0 < T.b →
        (T.c : ℝ) ≤
          K * (rad (T.a * T.b * T.c) : ℝ) ^ (1 + ε) := by
  refine
    ⟨GNABCConstant 3 H.C 0,
      one_le_GNABCConstant _ _ _, ?_⟩
  intro T ha hb
  rcases H.orientedBudget T ha hb with hT | hswap
  · exact
      T.abc_bound_of_oddPrime_jointPressure
        Nat.prime_three (by decide) ha hb H.margin hT
  · have hbound :=
      T.swap.abc_bound_of_oddPrime_jointPressure
        Nat.prime_three (by decide) hb ha H.margin hswap
    exact
      (T.abcBound_swap_iff
        (GNABCConstant 3 H.C 0) ε).mp hbound

/-- An oriented cubic contract implies the full raw ABC bound, including the
zero-coordinate endpoints. -/
theorem ABCRawBound_of_GNCubicOrientedContract
    {ε : ℝ}
    (H : ABCGNCubicOrientedContract ε) :
    ABCRawBound ε := by
  obtain ⟨K, hK, hpositive⟩ :=
    abc_positive_of_GNCubicOrientedContract H
  refine ⟨K, hK, ?_⟩
  intro a b c hab hcop
  by_cases ha0 : a = 0
  · subst a
    have hb1 : b = 1 := by simpa using hcop
    subst b
    have hc1 : c = 1 := by omega
    subst c
    simpa using hK
  by_cases hb0 : b = 0
  · subst b
    have ha1 : a = 1 := by simpa using hcop
    subst a
    have hc1 : c = 1 := by omega
    subst c
    simpa using hK
  let T : Triple :=
    { a := a
      b := b
      c := c
      hsum := hab
      hcop := hcop }
  exact hpositive T
    (Nat.pos_of_ne_zero ha0)
    (Nat.pos_of_ne_zero hb0)

/--
Reverse audit: a raw ABC bound constructs the oriented cubic contract by
using the ordinary orientation at every point.
-/
theorem GNCubicOrientedContract_of_ABCRawBound
    {ε : ℝ}
    (hε : 0 < ε)
    (Habc : ABCRawBound ε) :
    Nonempty (ABCGNCubicOrientedContract ε) := by
  rcases Habc with ⟨K, hK, Habc⟩
  have hKpos : 0 < K := lt_of_lt_of_le zero_lt_one hK
  let ρ : ℝ := 2 * (1 + ε)
  let C : ℝ := Real.log 3 + 2 * Real.log K
  refine ⟨{
    hε := hε
    ρ := ρ
    C := C
    margin := le_rfl
    orientedBudget := ?_ }⟩
  intro T ha hb
  apply Or.inl
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
      (T.c : ℝ) ≤ K * R ^ (1 + ε) :=
    Habc T.a T.b T.c T.hsum T.hcop
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
    have hcR : (T.c : ℝ) ≠ 0 := by
      exact_mod_cast hc.ne'
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
      Nat.prime_three ha hb).mpr
  apply
    (T.nonExceptionalChannelMassBudget_iff_log_GN_le
      Nat.prime_three (by decide) ha hb).mpr
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

/-- The oriented cubic contract has exactly raw-ABC strength. -/
theorem ABCRawBound_iff_nonempty_GNCubicOrientedContract
    {ε : ℝ}
    (hε : 0 < ε) :
    ABCRawBound ε ↔
      Nonempty (ABCGNCubicOrientedContract ε) := by
  constructor
  · exact GNCubicOrientedContract_of_ABCRawBound hε
  · rintro ⟨H⟩
    exact ABCRawBound_of_GNCubicOrientedContract H

end DkMath.ABC
