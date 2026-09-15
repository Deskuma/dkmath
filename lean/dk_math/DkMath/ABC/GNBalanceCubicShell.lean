/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.ABC.GNBalanceDepthLayers
import DkMath.ABC.GNExcessCubicComplement

#print "file: DkMath.ABC.GNBalanceCubicShell"

set_option linter.style.longLine false
set_option linter.style.emptyLine false

/-!
# Exact shell coordinates for GN balance

This module audits the existing repeated-prime-power shell against the
BCAL-003 signed balance.  The non-exceptional shell retains the single layer
and `twoTail` retains only over-depth.  The cubic `q = 3` channel is kept
explicit: the existing full cubic complement may contain that exceptional
single layer, while the BCAL channel omits it.

No shell counting, mutation, Hensel transport, or global optimality claim is
made here.
-/

namespace DkMath.ABC

open DkMath.CosmicFormulaBinom
open DkMath.NumberTheory

/-- The squarefree single layer of the non-exceptional GN part. -/
noncomputable def GNNonExceptionalSingleLayer
    (p a b : ℕ) : ℕ :=
  repeatedPrimePowerComplement (GNNonExceptionalPart p a b)

/-! The generic complement keeps exactly the valuation-one layer. -/

theorem repeatedPrimePowerComplement_factorization
    {n : ℕ} (hn : n ≠ 0) (q : ℕ) :
    (repeatedPrimePowerComplement n).factorization q =
      if q ∈ n.factorization.support ∧ n.factorization q = 1 then 1 else 0 := by
  have hd := repeatedPrimePowerPart_dvd hn
  rw [repeatedPrimePowerComplement, Nat.factorization_div hd,
    Finsupp.tsub_apply, repeatedPrimePowerPart_factorization]
  by_cases hq : q ∈ n.factorization.support
  · have hq_one : 1 ≤ n.factorization q :=
      one_le_factorization_of_mem_support hq
    by_cases htwo : 2 ≤ n.factorization q
    · rw [if_pos ⟨hq, htwo⟩, if_neg (by omega)]
      omega
    · have hone : n.factorization q = 1 := by omega
      have hnot : ¬(q ∈ n.factorization.support ∧
          2 ≤ n.factorization q) := by
        exact fun h => htwo h.2
      rw [if_neg hnot, if_pos ⟨hq, hone⟩]
      simp [hone]
  · have hzero : n.factorization q = 0 := by
      by_contra hne
      exact hq (Finsupp.mem_support_iff.mpr hne)
    have hnot_two : ¬(q ∈ n.factorization.support ∧
        2 ≤ n.factorization q) := by
      exact fun h => hq h.1
    have hnot_one : ¬(q ∈ n.factorization.support ∧
        n.factorization q = 1) := by
      exact fun h => hq h.1
    rw [if_neg hnot_two, if_neg hnot_one, hzero]

theorem twoTail_eq_overDepthProduct (n : ℕ) :
    twoTail n =
      (n.factorization.support.filter
        (fun q => 3 ≤ n.factorization q)).prod
        (fun q => q ^ (n.factorization q - 2)) := by
  classical
  unfold twoTail
  rw [← Finset.prod_filter_mul_prod_filter_not
    n.factorization.support (fun q => 3 ≤ n.factorization q)]
  have hshallow :
      (n.factorization.support.filter
        (fun q => ¬ 3 ≤ n.factorization q)).prod
        (fun q => q ^ (n.factorization q - 2)) = 1 := by
    apply Finset.prod_eq_one
    intro q hq
    have hnot : ¬ 3 ≤ n.factorization q :=
      (Finset.mem_filter.mp hq).2
    have hle : n.factorization q ≤ 2 := by
      omega
    simp [Nat.sub_eq_zero_of_le hle]
  rw [hshallow, mul_one]

theorem GNNonExceptionalSingleLayer_pos
    (p a b : ℕ) :
    0 < GNNonExceptionalSingleLayer p a b := by
  unfold GNNonExceptionalSingleLayer
  have hN : GNNonExceptionalPart p a b ≠ 0 :=
    Nat.ne_of_gt (GNNonExceptionalPart_pos p a b)
  have hrec := repeatedPrimePowerPart_mul_complement hN
  have hS : repeatedPrimePowerComplement (GNNonExceptionalPart p a b) ≠ 0 := by
    intro hzero
    rw [hzero, mul_zero] at hrec
    exact hN hrec.symm
  exact Nat.pos_of_ne_zero hS

/-! ## Generic non-exceptional bridge -/

/--
The BCAL signed channel balance is exactly
`log(single layer) - log(over-depth)` for the non-exceptional GN part.

The `piSqRad` square is the neutral valuation-two pivot and disappears from
this difference.
-/
theorem GNChannelBalance_eq_log_singleLayer_sub_log_twoTail
    (T : Triple) (p : ℕ) :
    GNChannelBalance T p =
      Real.log (GNNonExceptionalSingleLayer p T.a T.b : ℝ) -
        Real.log (twoTail (GNNonExceptionalPart p T.a T.b) : ℝ) := by
  have hN : GNNonExceptionalPart p T.a T.b ≠ 0 :=
    Nat.ne_of_gt (GNNonExceptionalPart_pos p T.a T.b)
  have hS : 0 < GNNonExceptionalSingleLayer p T.a T.b :=
    GNNonExceptionalSingleLayer_pos p T.a T.b
  have hR : 0 < piSqRad (GNNonExceptionalPart p T.a T.b) := by
    exact Nat.lt_of_lt_of_le Nat.zero_lt_one
      (piSqRad_ge_one (GNNonExceptionalPart p T.a T.b))
  have hD : 0 < twoTail (GNNonExceptionalPart p T.a T.b) := by
    unfold twoTail
    exact Finset.prod_pos fun q hq => pow_pos
      (mem_support_factorization_iff.mp hq).2.1.pos _
  have hP : 0 < repeatedPrimePowerPart (GNNonExceptionalPart p T.a T.b) :=
    repeatedPrimePowerPart_pos _
  have hPcast :
      (repeatedPrimePowerPart (GNNonExceptionalPart p T.a T.b) : ℝ) ≠ 0 := by
    exact_mod_cast hP.ne'
  have hScast :
      (repeatedPrimePowerComplement (GNNonExceptionalPart p T.a T.b) : ℝ) ≠ 0 := by
    exact_mod_cast hS.ne'
  have hRcast :
      (piSqRad (GNNonExceptionalPart p T.a T.b) : ℝ) ≠ 0 := by
    exact_mod_cast hR.ne'
  have hDcast :
      (twoTail (GNNonExceptionalPart p T.a T.b) : ℝ) ≠ 0 := by
    exact_mod_cast hD.ne'
  have hrad :
      0 < rad (GNNonExceptionalPart p T.a T.b) :=
    rad_pos (Nat.pos_of_ne_zero hN)
  have hradcast :
      (rad (GNNonExceptionalPart p T.a T.b) : ℝ) ≠ 0 := by
    exact_mod_cast hrad.ne'
  have hval :
      valuationExcess (GNNonExceptionalPart p T.a T.b) =
        Real.log (piSqRad (GNNonExceptionalPart p T.a T.b) : ℝ) +
          Real.log (twoTail (GNNonExceptionalPart p T.a T.b) : ℝ) := by
    simpa only [valuationExcess_GNNonExceptionalPart_eq p T.a T.b] using
      (GNNonExceptionalValuationExcess_eq_log_piSqRad_add_log_twoTail
        p T.a T.b)
  have hlog_rad :
      Real.log (GNNonExceptionalPart p T.a T.b : ℝ) =
        Real.log (rad (GNNonExceptionalPart p T.a T.b) : ℝ) +
          valuationExcess (GNNonExceptionalPart p T.a T.b) :=
    log_eq_log_rad_add_valuationExcess hN
  have hlog_rep :
      Real.log (repeatedPrimePowerPart (GNNonExceptionalPart p T.a T.b) : ℝ) =
        2 * Real.log (piSqRad (GNNonExceptionalPart p T.a T.b) : ℝ) +
          Real.log (twoTail (GNNonExceptionalPart p T.a T.b) : ℝ) := by
    rw [repeatedPrimePowerPart_eq_piSqRad_sq_mul_twoTail hN,
      Nat.cast_mul, Nat.cast_pow,
      Real.log_mul (pow_ne_zero 2 hRcast) hDcast,
      Real.log_pow]
    ring
  have hlog_single :
      Real.log (GNNonExceptionalPart p T.a T.b : ℝ) =
        Real.log (repeatedPrimePowerPart (GNNonExceptionalPart p T.a T.b) : ℝ) +
          Real.log (GNNonExceptionalSingleLayer p T.a T.b : ℝ) := by
    have hrec := repeatedPrimePowerPart_mul_complement hN
    change Real.log (GNNonExceptionalPart p T.a T.b : ℝ) =
      Real.log (repeatedPrimePowerPart (GNNonExceptionalPart p T.a T.b) : ℝ) +
        Real.log (repeatedPrimePowerComplement (GNNonExceptionalPart p T.a T.b) : ℝ)
    have hrec_real :
        (repeatedPrimePowerPart (GNNonExceptionalPart p T.a T.b) : ℝ) *
            (repeatedPrimePowerComplement (GNNonExceptionalPart p T.a T.b) : ℝ) =
          (GNNonExceptionalPart p T.a T.b : ℝ) := by
      exact_mod_cast hrec
    calc
      Real.log (GNNonExceptionalPart p T.a T.b : ℝ) =
          Real.log
            ((repeatedPrimePowerPart (GNNonExceptionalPart p T.a T.b) : ℝ) *
              (repeatedPrimePowerComplement (GNNonExceptionalPart p T.a T.b) : ℝ)) := by
            exact congrArg Real.log hrec_real.symm
      _ = Real.log (repeatedPrimePowerPart (GNNonExceptionalPart p T.a T.b) : ℝ) +
          Real.log (repeatedPrimePowerComplement (GNNonExceptionalPart p T.a T.b) : ℝ) := by
            rw [Real.log_mul hPcast hScast]
  have hrad_log :
      Real.log (rad (GNNonExceptionalPart p T.a T.b) : ℝ) =
        Real.log (piSqRad (GNNonExceptionalPart p T.a T.b) : ℝ) +
          Real.log (GNNonExceptionalSingleLayer p T.a T.b : ℝ) := by
    linarith [hlog_rad, hlog_rep, hlog_single, hval]
  unfold GNChannelBalance GNChannelSupportMass GNChannelDepthMass
  rw [← rad_GNNonExceptionalPart_eq_supportProduct,
    ← valuationExcess_GNNonExceptionalPart_eq, hrad_log, hval]
  ring

/-! ## Cubic specialization and the exceptional prime three -/

/-- In the canonical cubic family, prime `3` cannot occur to depth two. -/
theorem GN_cubic_three_factorization_eq_one_of_dvd
    {a : ℕ} (h3 : 3 ∣ GN 3 a 1) :
    (GN 3 a 1).factorization 3 = 1 := by
  have hGN : GN 3 a 1 ≠ 0 := by
    rw [GN_three_dual_explicit]
    positivity
  have hpos : 0 < (GN 3 a 1).factorization 3 := by
    have hmem : 3 ∈ (GN 3 a 1).factorization.support :=
      mem_support_factorization_iff.mpr ⟨hGN, Nat.prime_three, h3⟩
    exact Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hmem)
  have hnot : ¬ 2 ≤ (GN 3 a 1).factorization 3 := by
    intro h2
    apply not_nine_dvd_GN_three_one_value a
    exact (Nat.prime_three.pow_dvd_iff_le_factorization hGN).mpr h2
  omega

private theorem GNNonExceptionalPart_eq_GN_of_not_dvd_three
    {a : ℕ} (h3 : ¬ 3 ∣ GN 3 a 1) :
    GNNonExceptionalPart 3 a 1 = GN 3 a 1 := by
  have hGN : GN 3 a 1 ≠ 0 := by
    rw [GN_three_dual_explicit]
    positivity
  have hsupport :
      GNNonExceptionalSupport 3 a 1 =
        (GN 3 a 1).factorization.support := by
    ext q
    simp only [GNNonExceptionalSupport, Finset.mem_filter]
    constructor
    · exact And.left
    · intro hq
      refine ⟨hq, ?_⟩
      intro hq3
      have hqprime := (mem_support_factorization_iff.mp hq).2.1
      rcases (Nat.dvd_prime Nat.prime_three).mp hq3 with hqone | hqeq
      · exact False.elim (hqprime.ne_one hqone)
      · subst q
        exact h3 (mem_support_factorization_iff.mp hq).2.2
  apply Nat.eq_of_factorization_eq
    (GNNonExceptionalPart_pos 3 a 1).ne' hGN
  intro q
  rw [GNNonExceptionalPart_factorization]
  by_cases hq : q ∈ (GN 3 a 1).factorization.support
  · rw [if_pos (by simpa [hsupport] using hq)]
  · rw [if_neg (by simpa [hsupport] using hq)]
    by_contra hne
    have hfac : (GN 3 a 1).factorization q ≠ 0 := by
      intro hzero
      exact hne hzero.symm
    exact hq (Finsupp.mem_support_iff.mpr hfac)

/-- Away from the exceptional `3`-channel, the existing cubic complement is
the BCAL single layer and the exact bridge specializes without correction. -/
theorem GNChannelBalance_cubic_eq_log_complement_sub_log_twoTail
    {a : ℕ} (h3 : ¬ 3 ∣ GN 3 a 1) :
    GNChannelBalance (Triple.mk a 1 (a + 1) rfl (by simp)) 3 =
      Real.log (GNExcessCubicComplement a : ℝ) -
        Real.log (twoTail (GN 3 a 1) : ℝ) := by
  have hpart := GNNonExceptionalPart_eq_GN_of_not_dvd_three h3
  have hGN : GN 3 a 1 ≠ 0 := by
    rw [GN_three_dual_explicit]
    positivity
  have hrep := GNNonExceptionalRepeatedPart_three_one_eq_repeatedPrimePowerPart a
  rw [GNChannelBalance_eq_log_singleLayer_sub_log_twoTail
      (Triple.mk a 1 (a + 1) rfl (by simp)) 3]
  unfold GNNonExceptionalSingleLayer GNExcessCubicComplement
  rw [hpart, hrep]
  simp [repeatedPrimePowerComplement]

end DkMath.ABC
