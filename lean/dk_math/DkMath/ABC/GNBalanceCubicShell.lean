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
    · rw [ite_eq_left ⟨hq, htwo⟩, ite_eq_right (by omega)]
      omega
    · have hone : n.factorization q = 1 := by omega
      have hnot : ¬(q ∈ n.factorization.support ∧
          2 ≤ n.factorization q) := by
        exact fun h => htwo h.2
      rw [ite_eq_right hnot, ite_eq_left ⟨hq, hone⟩]
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
    rw [ite_eq_right hnot_two, ite_eq_right hnot_one, hzero]

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
  · rw [ite_eq_left (by simpa [hsupport] using hq)]
  · rw [ite_eq_right (by simpa [hsupport] using hq)]
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

/-! ## Unconditional exceptional support completion -/

theorem GNExceptionalSupportProduct_three_one_eq_if
    (a : ℕ) :
    GNExceptionalSupportProduct 3 a 1 =
      if 3 ∣ GN 3 a 1 then 3 else 1 := by
  have hGN : GN 3 a 1 ≠ 0 := by
    rw [GN_three_dual_explicit]
    positivity
  by_cases h3 : 3 ∣ GN 3 a 1
  · have hmem3 : 3 ∈ (GN 3 a 1).factorization.support :=
      mem_support_factorization_iff.mpr ⟨hGN, Nat.prime_three, h3⟩
    have hE : GNExceptionalSupport 3 a 1 = {3} := by
      ext q
      constructor
      · intro hq
        have hq' := Finset.mem_filter.mp hq
        have hqprime := (mem_support_factorization_iff.mp hq'.1).2.1
        have hqeq : q = 3 :=
          ((Nat.dvd_prime Nat.prime_three).mp hq'.2).resolve_left hqprime.ne_one
        subst q
        simp
      · intro hq
        have hqeq : q = 3 := by simpa using hq
        subst q
        exact Finset.mem_filter.mpr ⟨hmem3, by simp⟩
    rw [GNExceptionalSupportProduct, hE, ite_eq_left h3]
    rfl
  · have hE : GNExceptionalSupport 3 a 1 = ∅ := by
      ext q
      constructor
      · intro hq
        have hq' := Finset.mem_filter.mp hq
        have hqprime := (mem_support_factorization_iff.mp hq'.1).2.1
        have hqeq : q = 3 :=
          ((Nat.dvd_prime Nat.prime_three).mp hq'.2).resolve_left hqprime.ne_one
        subst q
        exact False.elim (h3 (mem_support_factorization_iff.mp hq'.1).2.2)
      · simp
    rw [GNExceptionalSupportProduct, hE, ite_eq_right h3]
    rfl

theorem GN_cubic_eq_exceptional_mul_nonExceptionalPart
    (a : ℕ) :
    GN 3 a 1 =
      GNExceptionalSupportProduct 3 a 1 * GNNonExceptionalPart 3 a 1 := by
  have hGN : GN 3 a 1 ≠ 0 := by
    rw [GN_three_dual_explicit]
    positivity
  have hEpos : 0 < GNExceptionalSupportProduct 3 a 1 :=
    GNExceptionalSupportProduct_pos 3 a 1
  have hNpos : 0 < GNNonExceptionalPart 3 a 1 :=
    GNNonExceptionalPart_pos 3 a 1
  have hEprime : ∀ q ∈ GNExceptionalSupport 3 a 1, Nat.Prime q := by
    intro q hq
    exact (mem_support_factorization_iff.mp
      (Finset.mem_filter.mp hq).1).2.1
  apply Nat.eq_of_factorization_eq hGN
    (mul_ne_zero hEpos.ne' hNpos.ne')
  intro q
  have hEpos' : 0 < (GNExceptionalSupport 3 a 1).prod id := by
    exact hEpos
  rw [GNExceptionalSupportProduct]
  rw [Nat.factorization_mul hEpos'.ne' hNpos.ne']
  change (GN 3 a 1).factorization q =
    ((GNExceptionalSupport 3 a 1).prod (fun p => p)).factorization q +
      (GNNonExceptionalPart 3 a 1).factorization q
  rw [factorization_prod_primes q (GNExceptionalSupport 3 a 1) hEprime,
    GNNonExceptionalPart_factorization]
  by_cases hqE : q ∈ GNExceptionalSupport 3 a 1
  · have hqN : q ∉ GNNonExceptionalSupport 3 a 1 := by
      intro hqN
      exact Finset.disjoint_left.mp
        (GNExceptionalSupport_disjoint_nonExceptional 3 a 1) hqE hqN
    have hq' := Finset.mem_filter.mp hqE
    have hqprime := (mem_support_factorization_iff.mp hq'.1).2.1
    have hqeq : q = 3 :=
      ((Nat.dvd_prime Nat.prime_three).mp hq'.2).resolve_left hqprime.ne_one
    have h3 : 3 ∣ GN 3 a 1 := by
      simpa only [hqeq] using (mem_support_factorization_iff.mp hq'.1).2.2
    subst q
    have hv := GN_cubic_three_factorization_eq_one_of_dvd h3
    rw [ite_eq_left hqE, ite_eq_right hqN, hv]
  · by_cases hqN : q ∈ GNNonExceptionalSupport 3 a 1
    · rw [ite_eq_right hqE, ite_eq_left hqN]
      simp only [zero_add]
    · have hqF : q ∉ (GN 3 a 1).factorization.support := by
        intro hqF
        have hu : q ∈ GNExceptionalSupport 3 a 1 ∪
            GNNonExceptionalSupport 3 a 1 := by
          rw [← GN_support_eq_exceptional_union_nonExceptional]
          exact hqF
        rcases Finset.mem_union.mp hu with hqE' | hqN'
        · exact hqE hqE'
        · exact hqN hqN'
      have hzero : (GN 3 a 1).factorization q = 0 := by
        by_contra hne
        exact hqF (Finsupp.mem_support_iff.mpr hne)
      rw [ite_eq_right hqE, ite_eq_right hqN, hzero]

theorem GNExcessCubicComplement_eq_exceptional_mul_nonExceptionalSingleLayer
    (a : ℕ) :
    GNExcessCubicComplement a =
      GNExceptionalSupportProduct 3 a 1 * GNNonExceptionalSingleLayer 3 a 1 := by
  have hN : GNNonExceptionalPart 3 a 1 ≠ 0 :=
    Nat.ne_of_gt (GNNonExceptionalPart_pos 3 a 1)
  have hPdvd : repeatedPrimePowerPart (GNNonExceptionalPart 3 a 1) ∣
      GNNonExceptionalPart 3 a 1 :=
    repeatedPrimePowerPart_dvd hN
  have hrep := GNNonExceptionalRepeatedPart_three_one_eq_repeatedPrimePowerPart a
  have hquot :
      GN 3 a 1 / repeatedPrimePowerPart (GN 3 a 1) =
        (GNExceptionalSupportProduct 3 a 1 *
          GNNonExceptionalPart 3 a 1) /
          repeatedPrimePowerPart (GNNonExceptionalPart 3 a 1) := by
    congr 1
    · exact GN_cubic_eq_exceptional_mul_nonExceptionalPart a
    · exact hrep.symm
  unfold GNExcessCubicComplement GNNonExceptionalSingleLayer
  rw [hrep, hquot]
  exact Nat.mul_div_assoc _ hPdvd

theorem twoTail_GN_cubic_eq_twoTail_nonExceptionalPart
    (a : ℕ) :
    twoTail (GN 3 a 1) =
      twoTail (GNNonExceptionalPart 3 a 1) := by
  classical
  have hdis := GNExceptionalSupport_disjoint_nonExceptional 3 a 1
  have hEone :
      (GNExceptionalSupport 3 a 1).prod
        (fun q => q ^ ((GN 3 a 1).factorization q - 2)) = 1 := by
    apply Finset.prod_eq_one
    intro q hq
    have hq' := Finset.mem_filter.mp hq
    have hqprime := (mem_support_factorization_iff.mp hq'.1).2.1
    have hqeq : q = 3 :=
      ((Nat.dvd_prime Nat.prime_three).mp hq'.2).resolve_left hqprime.ne_one
    have h3 : 3 ∣ GN 3 a 1 := by
      simpa only [hqeq] using (mem_support_factorization_iff.mp hq'.1).2.2
    subst q
    have hv := GN_cubic_three_factorization_eq_one_of_dvd h3
    rw [hv]
    norm_num
  calc
    twoTail (GN 3 a 1) =
        (GN 3 a 1).factorization.support.prod
          (fun q => q ^ ((GN 3 a 1).factorization q - 2)) := rfl
    _ = (GNExceptionalSupport 3 a 1 ∪
        GNNonExceptionalSupport 3 a 1).prod
          (fun q => q ^ ((GN 3 a 1).factorization q - 2)) := by
      rw [GN_support_eq_exceptional_union_nonExceptional]
    _ = (GNExceptionalSupport 3 a 1).prod
          (fun q => q ^ ((GN 3 a 1).factorization q - 2)) *
        (GNNonExceptionalSupport 3 a 1).prod
          (fun q => q ^ ((GN 3 a 1).factorization q - 2)) :=
      Finset.prod_union hdis
    _ = (GNNonExceptionalSupport 3 a 1).prod
          (fun q => q ^ ((GN 3 a 1).factorization q - 2)) := by
      rw [hEone, one_mul]
    _ = twoTail (GNNonExceptionalPart 3 a 1) := by
      rw [← GNNonExceptionalPart_factorization_support]
      apply Finset.prod_congr rfl
      intro q hq
      have hqS : q ∈ GNNonExceptionalSupport 3 a 1 := by
        rw [← GNNonExceptionalPart_factorization_support]
        exact hq
      rw [GNNonExceptionalPart_factorization, ite_eq_left hqS]

/-! ## The unconditional full-shell balance and gauge form -/

theorem GNChannelBalance_cubic_eq_log_fullComplement_sub_log_twoTail_sub_log_exceptional
    (a : ℕ) :
    GNChannelBalance (Triple.mk a 1 (a + 1) rfl (by simp)) 3 =
      Real.log (GNExcessCubicComplement a : ℝ) -
        Real.log (twoTail (GN 3 a 1) : ℝ) -
        Real.log (GNExceptionalSupportProduct 3 a 1 : ℝ) := by
  have hEpos : 0 < GNExceptionalSupportProduct 3 a 1 :=
    GNExceptionalSupportProduct_pos 3 a 1
  have hSpos : 0 < GNNonExceptionalSingleLayer 3 a 1 :=
    GNNonExceptionalSingleLayer_pos 3 a 1
  have hEcast : (GNExceptionalSupportProduct 3 a 1 : ℝ) ≠ 0 :=
    by exact_mod_cast hEpos.ne'
  have hScast : (GNNonExceptionalSingleLayer 3 a 1 : ℝ) ≠ 0 :=
    by exact_mod_cast hSpos.ne'
  calc
    GNChannelBalance (Triple.mk a 1 (a + 1) rfl (by simp)) 3 =
        Real.log (GNNonExceptionalSingleLayer 3 a 1 : ℝ) -
          Real.log (twoTail (GNNonExceptionalPart 3 a 1) : ℝ) := by
      simpa using GNChannelBalance_eq_log_singleLayer_sub_log_twoTail
        (Triple.mk a 1 (a + 1) rfl (by simp)) 3
    _ = Real.log (GNExcessCubicComplement a : ℝ) -
          Real.log (twoTail (GN 3 a 1) : ℝ) -
          Real.log (GNExceptionalSupportProduct 3 a 1 : ℝ) := by
      rw [twoTail_GN_cubic_eq_twoTail_nonExceptionalPart,
        GNExcessCubicComplement_eq_exceptional_mul_nonExceptionalSingleLayer,
        Nat.cast_mul, Real.log_mul hEcast hScast]
      ring

theorem GNChannelBalance_cubic_eq_log_complement_sub_log_twoTail_recovered
    {a : ℕ} (h3 : ¬ 3 ∣ GN 3 a 1) :
    GNChannelBalance (Triple.mk a 1 (a + 1) rfl (by simp)) 3 =
      Real.log (GNExcessCubicComplement a : ℝ) -
        Real.log (twoTail (GN 3 a 1) : ℝ) := by
  rw [GNChannelBalance_cubic_eq_log_fullComplement_sub_log_twoTail_sub_log_exceptional,
    GNExceptionalSupportProduct_three_one_eq_if, ite_eq_right h3]
  norm_num

theorem GNChannelBalance_cubic_eq_fullShell_sub_radLog_add_gaugeSlack
    (a : ℕ) :
    GNChannelBalance (Triple.mk a 1 (a + 1) rfl (by simp)) 3 =
      (Real.log (GNExcessCubicComplement a : ℝ) -
        Real.log (twoTail (GN 3 a 1) : ℝ)) -
        Real.log (rad 3 : ℝ) +
        GNExceptionalGaugeSlack (Triple.mk a 1 (a + 1) rfl (by simp)) 3 := by
  rw [GNChannelBalance_cubic_eq_log_fullComplement_sub_log_twoTail_sub_log_exceptional]
  unfold GNExceptionalGaugeSlack
  ring

end DkMath.ABC
