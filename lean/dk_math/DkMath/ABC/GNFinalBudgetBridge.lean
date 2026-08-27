/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.ABC.GNSupportReturn

#print "file: DkMath.ABC.GNFinalBudgetBridge"

set_option linter.style.longLine false
set_option linter.style.emptyLine false

/-!
# Two-budget final ABC bridge

This module combines a prime-support growth budget with an independent
valuation-multiplicity budget.  It proves an explicit pointwise ABC bound and
packages the genuinely uniform hypotheses needed for a positive-triple
global theorem.
-/

namespace DkMath.ABC

/-- Affine upper budget for the full GN valuation excess. -/
def GNValuationExcessBudgetAffine
    (T : Triple) (n : ℕ) (τ D : ℝ) : Prop :=
  GNValuationExcess n T.a T.b ≤
    τ * Real.log (rad (T.a * T.b * T.c) : ℝ) + D

/-- Affine upper budget for exponent-exceptional valuation excess. -/
def GNExceptionalExcessBudgetAffine
    (T : Triple) (n : ℕ) (τ D : ℝ) : Prop :=
  GNExceptionalValuationExcess n T.a T.b ≤
    τ * Real.log (rad (T.a * T.b * T.c) : ℝ) + D

/-- Affine upper budget for non-exceptional valuation excess. -/
def GNNonExceptionalExcessBudgetAffine
    (T : Triple) (n : ℕ) (τ D : ℝ) : Prop :=
  GNNonExceptionalValuationExcess n T.a T.b ≤
    τ * Real.log (rad (T.a * T.b * T.c) : ℝ) + D

/-- Exceptional and non-exceptional multiplicity budgets add exactly. -/
theorem GNValuationExcessBudgetAffine.of_split
    {T : Triple} {n : ℕ} {τe De τn Dn : ℝ}
    (he : GNExceptionalExcessBudgetAffine T n τe De)
    (hn : GNNonExceptionalExcessBudgetAffine T n τn Dn) :
    GNValuationExcessBudgetAffine T n (τe + τn) (De + Dn) := by
  have hsplit :=
    GNValuationExcess_eq_exceptional_add_nonExceptional n T.a T.b
  dsimp [GNExceptionalExcessBudgetAffine] at he
  dsimp [GNNonExceptionalExcessBudgetAffine] at hn
  dsimp [GNValuationExcessBudgetAffine]
  nlinarith

/-- Support and multiplicity budgets give a direct logarithmic height bound. -/
theorem Triple.log_c_mul_pred_le_of_support_and_excessBudget
    (T : Triple) {n : ℕ} {σ Cs τ Ce : ℝ}
    (hn : 2 ≤ n) (ha : 0 < T.a) (hb : 0 < T.b)
    (hsupport : GNSupportBudgetAffine T n σ Cs)
    (hexcess : GNValuationExcessBudgetAffine T n τ Ce) :
    (((n - 1 : ℕ) : ℝ) * Real.log (T.c : ℝ)) ≤
      (σ + τ) * Real.log (rad (T.a * T.b * T.c) : ℝ) +
        (Cs + Ce) := by
  have hreturn := T.log_c_mul_pred_le_log_GN hn ha hb
  have hidentity := T.log_GN_eq_log_rad_add_GNValuationExcess hn ha hb
  change Real.log (rad (DkMath.CosmicFormulaBinom.GN n T.a T.b) : ℝ) ≤
    σ * Real.log (rad (T.a * T.b * T.c) : ℝ) + Cs at hsupport
  dsimp [GNValuationExcessBudgetAffine] at hexcess
  nlinarith

/-- Lifted support growth plus multiplicity gives the final logarithmic bound. -/
theorem Triple.log_c_mul_pred_le_of_liftGrowth_and_excessBudget
    (T : Triple) {n : ℕ} {σ Cs τ Ce : ℝ}
    (hn : 2 ≤ n) (ha : 0 < T.a) (hb : 0 < T.b)
    (hlift : GNLiftRadicalGrowthBudgetAffine T n σ Cs)
    (hexcess : GNValuationExcessBudgetAffine T n τ Ce) :
    (((n - 1 : ℕ) : ℝ) * Real.log (T.c : ℝ)) ≤
      (σ + τ) * Real.log (rad (T.a * T.b * T.c) : ℝ) +
        (Cs + Ce + Real.log (rad n : ℝ)) := by
  have hsupport := T.GNSupportBudgetAffine_of_liftGrowth hn ha hb hlift
  have h := T.log_c_mul_pred_le_of_support_and_excessBudget
    hn ha hb hsupport hexcess
  nlinarith

/--
Explicit ABC constant for the two-budget bridge.

The absolute value avoids a sign split when the affine constant is negative.
It depends only on `n`, the support constant, and the excess constant.
-/
noncomputable def GNABCConstant
    (n : ℕ) (Cs Ce : ℝ) : ℝ :=
  max 1 (Real.exp
    |Cs + Ce + Real.log (rad n : ℝ)|)

theorem one_le_GNABCConstant (n : ℕ) (Cs Ce : ℝ) :
    (1 : ℝ) ≤ GNABCConstant n Cs Ce :=
  le_max_left _ _

/-- Pointwise ABC bound obtained from the two independent budgets. -/
theorem Triple.abc_bound_of_liftGrowth_and_excessBudget
    (T : Triple) {n : ℕ} {ε σ Cs τ Ce : ℝ}
    (hn : 2 ≤ n)
    (ha : 0 < T.a) (hb : 0 < T.b)
    (hmargin :
      σ + τ ≤ ((n - 1 : ℕ) : ℝ) * (1 + ε))
    (hlift : GNLiftRadicalGrowthBudgetAffine T n σ Cs)
    (hexcess : GNValuationExcessBudgetAffine T n τ Ce) :
    (T.c : ℝ) ≤
      GNABCConstant n Cs Ce *
        (rad (T.a * T.b * T.c) : ℝ) ^ (1 + ε) := by
  let d : ℝ := ((n - 1 : ℕ) : ℝ)
  let R : ℝ := (rad (T.a * T.b * T.c) : ℝ)
  let B : ℝ := Cs + Ce + Real.log (rad n : ℝ)
  have hd : 1 ≤ d := by
    dsimp [d]
    exact_mod_cast (show 1 ≤ n - 1 by omega)
  have hdpos : 0 < d := lt_of_lt_of_le zero_lt_one hd
  have hRlog : 0 ≤ Real.log R := by
    exact le_of_lt (T.log_rad_abc_pos ha hb)
  have hheight := T.log_c_mul_pred_le_of_liftGrowth_and_excessBudget
    hn ha hb hlift hexcess
  change d * Real.log (T.c : ℝ) ≤ (σ + τ) * Real.log R + B at hheight
  have hcoef :
      (σ + τ) * Real.log R ≤
        (d * (1 + ε)) * Real.log R :=
    mul_le_mul_of_nonneg_right hmargin hRlog
  have hB : B ≤ d * |B| := by
    have h1 : B ≤ |B| := le_abs_self B
    have h2 : |B| ≤ d * |B| := by
      nlinarith [abs_nonneg B]
    exact h1.trans h2
  have hlog :
      Real.log (T.c : ℝ) ≤
        (1 + ε) * Real.log R + |B| := by
    nlinarith
  have hc : 0 < (T.c : ℝ) := by
    exact_mod_cast (by rw [← T.hsum]; omega : 0 < T.c)
  have hR : 0 < R := by
    dsimp [R]
    exact_mod_cast rad_pos (by
      have hcNat : 0 < T.c := by rw [← T.hsum]; omega
      exact Nat.mul_pos (Nat.mul_pos ha hb) hcNat)
  have hexp := Real.exp_le_exp.mpr hlog
  rw [Real.exp_log hc, Real.exp_add] at hexp
  have hrpow :
      Real.exp ((1 + ε) * Real.log R) = R ^ (1 + ε) := by
    rw [mul_comm]
    exact (Real.rpow_def_of_pos hR _).symm
  rw [hrpow] at hexp
  have hconst :
      Real.exp |B| ≤ GNABCConstant n Cs Ce := by
    exact le_max_right _ _
  have hrpow_nonneg : 0 ≤ R ^ (1 + ε) :=
    Real.rpow_nonneg (le_of_lt hR) _
  calc
    (T.c : ℝ) ≤ R ^ (1 + ε) * Real.exp |B| := hexp
    _ = Real.exp |B| * R ^ (1 + ε) := mul_comm _ _
    _ ≤ GNABCConstant n Cs Ce * R ^ (1 + ε) :=
      mul_le_mul_of_nonneg_right hconst hrpow_nonneg

/-- Uniform two-budget contract sufficient for positive-triple ABC. -/
structure ABCGNFinalBudgetContract (ε : ℝ) where
  hε : 0 < ε
  n : ℕ
  hn : 2 ≤ n
  σ : ℝ
  Cs : ℝ
  τe : ℝ
  De : ℝ
  τn : ℝ
  Dn : ℝ
  margin :
    σ + (τe + τn) ≤ ((n - 1 : ℕ) : ℝ) * (1 + ε)
  liftBudget :
    ∀ T : Triple, 0 < T.a → 0 < T.b →
      GNLiftRadicalGrowthBudgetAffine T n σ Cs
  exceptionalExcessBudget :
    ∀ T : Triple, 0 < T.a → 0 < T.b →
      GNExceptionalExcessBudgetAffine T n τe De
  nonExceptionalExcessBudget :
    ∀ T : Triple, 0 < T.a → 0 < T.b →
      GNNonExceptionalExcessBudgetAffine T n τn Dn

/-- The uniform final contract yields a global ABC theorem for positive triples. -/
theorem abc_positive_of_GNFinalBudgetContract
    {ε : ℝ}
    (H : ABCGNFinalBudgetContract ε) :
    ∃ K : ℝ, 1 ≤ K ∧
      ∀ T : Triple, 0 < T.a → 0 < T.b →
        (T.c : ℝ) ≤
          K * (rad (T.a * T.b * T.c) : ℝ) ^ (1 + ε) := by
  refine ⟨GNABCConstant H.n H.Cs (H.De + H.Dn),
    one_le_GNABCConstant _ _ _, ?_⟩
  intro T ha hb
  apply T.abc_bound_of_liftGrowth_and_excessBudget
    H.hn ha hb H.margin (H.liftBudget T ha hb)
  exact GNValuationExcessBudgetAffine.of_split
    (H.exceptionalExcessBudget T ha hb)
    (H.nonExceptionalExcessBudget T ha hb)

end DkMath.ABC
