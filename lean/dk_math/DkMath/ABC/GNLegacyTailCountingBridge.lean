/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.ABC.GNDepthPressure
import DkMath.ABC.SquareTailBasic
import DkMath.ABC.LayerCakeBasic

#print "file: DkMath.ABC.GNLegacyTailCountingBridge"

set_option linter.style.longLine false
set_option linter.style.emptyLine false

/-!
# Legacy tail and counting bridges for the non-exceptional GN channel

This module reconnects two earlier ABC proof vocabularies to the current
odd-prime joint-pressure campaign.

First, it packages the complete non-exceptional prime-power part of `GN` as a
natural number. Its radical is the current non-exceptional support product, and
its valuation excess is the current non-exceptional excess. Consequently the
old `piSqRad`/`twoTail` decomposition gives an exact two-layer representation
of that excess.

Second, it packages the old residue-class counting and finite layer-cake APIs.
A finite residue cover gives the desired interval-cardinality bound, while a
separate wrapper feeds GN p-adic depths into `exp_layer_cake`.

The module does not construct the Hensel residue cover and does not turn a
density estimate into the pointwise `ABCGNOddPrimeJointContract`.
-/

namespace DkMath.ABC

open DkMath.CosmicFormulaBinom

/--
The natural number carrying exactly the non-exceptional prime powers of `GN`.

Unlike `GNNonExceptionalSupportProduct`, this retains the full factorization
depth at every non-exceptional prime.
-/
noncomputable def GNNonExceptionalPart (p a b : ℕ) : ℕ :=
  (GNNonExceptionalSupport p a b).prod
    (fun q => q ^ (GN p a b).factorization q)

/-- Factorization of the packaged non-exceptional GN part. -/
theorem GNNonExceptionalPart_factorization
    (p a b r : ℕ) :
    (GNNonExceptionalPart p a b).factorization r =
      if r ∈ GNNonExceptionalSupport p a b then
        (GN p a b).factorization r
      else 0 := by
  classical
  let S := GNNonExceptionalSupport p a b
  let f := fun q => q ^ (GN p a b).factorization q
  have hprime :
      ∀ q ∈ S, Nat.Prime q := by
    intro q hq
    exact (mem_support_factorization_iff.mp
      (Finset.mem_filter.mp hq).1).2.1
  have hnonzero :
      ∀ q ∈ S, f q ≠ 0 := by
    intro q hq
    exact pow_ne_zero _ (hprime q hq).ne_zero
  have hfac :=
    congrArg (fun g : ℕ →₀ ℕ => g r)
      (Nat.factorization_prod hnonzero)
  have hfac' :
      (GNNonExceptionalPart p a b).factorization r =
        (∑ q ∈ S, (f q).factorization r) := by
    simpa only [GNNonExceptionalPart, S, f,
      Finsupp.coe_finset_sum, Finset.sum_apply] using hfac
  change
    (GNNonExceptionalPart p a b).factorization r =
      if r ∈ GNNonExceptionalSupport p a b then
        (GN p a b).factorization r
      else 0
  rw [hfac']
  simp only [f, Nat.factorization_pow, Finsupp.coe_smul,
    Pi.smul_apply, nsmul_eq_mul]
  by_cases hr : r ∈ S
  · rw [if_pos hr]
    calc
      ∑ q ∈ S,
          (GN p a b).factorization q * q.factorization r =
        (GN p a b).factorization r * r.factorization r := by
          apply Finset.sum_eq_single r
          · intro q hq hqr
            rw [(hprime q hq).factorization, Finsupp.single_apply]
            simp [hqr]
          · intro hrnot
            exact False.elim (hrnot hr)
      _ = (GN p a b).factorization r := by
          rw [(hprime r hr).factorization, Finsupp.single_eq_same]
          simp
  · rw [if_neg hr]
    apply Finset.sum_eq_zero
    intro q hq
    rw [(hprime q hq).factorization, Finsupp.single_apply]
    simp only [mul_eq_zero]
    right
    simp only [ite_eq_right_iff]
    intro hqr
    subst q
    exact False.elim (hr hq)

/-- The packaged non-exceptional GN part is always positive. -/
theorem GNNonExceptionalPart_pos (p a b : ℕ) :
    0 < GNNonExceptionalPart p a b := by
  classical
  unfold GNNonExceptionalPart
  exact Finset.prod_pos fun q hq =>
    pow_pos (mem_support_factorization_iff.mp
      (Finset.mem_filter.mp hq).1).2.1.pos _

/-- The packaged part has exactly the non-exceptional factorization support. -/
theorem GNNonExceptionalPart_factorization_support
    (p a b : ℕ) :
    (GNNonExceptionalPart p a b).factorization.support =
      GNNonExceptionalSupport p a b := by
  classical
  ext r
  rw [Finsupp.mem_support_iff,
    GNNonExceptionalPart_factorization]
  by_cases hr : r ∈ GNNonExceptionalSupport p a b
  · rw [if_pos hr]
    exact iff_of_true
      (Finsupp.mem_support_iff.mp
        (Finset.mem_filter.mp hr).1)
      hr
  · simp [hr]

/-- Its radical is the current non-exceptional support product. -/
theorem rad_GNNonExceptionalPart_eq_supportProduct
    (p a b : ℕ) :
    rad (GNNonExceptionalPart p a b) =
      GNNonExceptionalSupportProduct p a b := by
  unfold rad GNNonExceptionalSupportProduct
  rw [GNNonExceptionalPart_factorization_support]
  simp

/-- Its generic valuation excess is exactly the current non-exceptional excess. -/
theorem valuationExcess_GNNonExceptionalPart_eq
    (p a b : ℕ) :
    valuationExcess (GNNonExceptionalPart p a b) =
      GNNonExceptionalValuationExcess p a b := by
  classical
  unfold valuationExcess GNNonExceptionalValuationExcess
  rw [GNNonExceptionalPart_factorization_support]
  apply Finset.sum_congr rfl
  intro q hq
  rw [GNNonExceptionalPart_factorization, if_pos hq]

/--
The current non-exceptional valuation excess is the logarithm of the old
square-free tail quotient.
-/
theorem GNNonExceptionalValuationExcess_eq_log_sqTail
    (p a b : ℕ) :
    GNNonExceptionalValuationExcess p a b =
      Real.log (sqTail (GNNonExceptionalPart p a b) : ℝ) := by
  let N := GNNonExceptionalPart p a b
  have hN : N ≠ 0 := Nat.ne_of_gt (GNNonExceptionalPart_pos p a b)
  have hlog := log_eq_log_rad_add_valuationExcess hN
  have hdecomp := nat_eq_sqTail_mul_rad_real N hN
  have hsquare : (sqTail N : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt (by
      rw [sqTail_eq_piSqRad_mul_twoTail N hN]
      exact Nat.mul_pos
        (Nat.lt_of_lt_of_le Nat.zero_lt_one (piSqRad_ge_one N))
        (by
          unfold twoTail
          exact Finset.prod_pos fun q hq => pow_pos
            (mem_support_factorization_iff.mp hq).2.1.pos _))
  have hrad : (rad N : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt (rad_pos (Nat.pos_of_ne_zero hN))
  have hmul :
      Real.log (N : ℝ) =
        Real.log (sqTail N : ℝ) + Real.log (rad N : ℝ) := by
    rw [hdecomp, Real.log_mul hsquare hrad]
  rw [valuationExcess_GNNonExceptionalPart_eq] at hlog
  linarith

/--
Exact bridge from the current excess to the legacy second-layer and deep-tail
coordinates.
-/
theorem GNNonExceptionalValuationExcess_eq_log_piSqRad_add_log_twoTail
    (p a b : ℕ) :
    GNNonExceptionalValuationExcess p a b =
      Real.log (piSqRad (GNNonExceptionalPart p a b) : ℝ) +
        Real.log (twoTail (GNNonExceptionalPart p a b) : ℝ) := by
  let N := GNNonExceptionalPart p a b
  have hN : N ≠ 0 := Nat.ne_of_gt (GNNonExceptionalPart_pos p a b)
  have hsquare := sqTail_eq_piSqRad_mul_twoTail_real N hN
  have hpi : (piSqRad N : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt
      (Nat.lt_of_lt_of_le Nat.zero_lt_one (piSqRad_ge_one N))
  have htail : (twoTail N : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt (by
      unfold twoTail
      exact Finset.prod_pos fun q hq => pow_pos
        (mem_support_factorization_iff.mp hq).2.1.pos _)
  rw [GNNonExceptionalValuationExcess_eq_log_sqTail,
    hsquare, Real.log_mul hpi htail]

/--
A finite set of residue addresses covering every deep GN lift at fixed
`p`, `q`, `b`, and depth `k`.

The Hensel/cyclotomic argument constructing a cover of size at most `p - 1`
is deliberately a separate arithmetic obligation.
-/
def GNDeepLiftResidueCover
    (p q b k : ℕ) (R : Finset ℕ) : Prop :=
  ∀ a, q ^ k ∣ GN p a b →
    ∃ r ∈ R, Nat.ModEq (q ^ k) a r

/-- A finite residue cover gives the corresponding interval count. -/
theorem card_gn_deep_lift_range_le_of_residueCover
    {p q b k X : ℕ} {R : Finset ℕ}
    (hq : Nat.Prime q)
    (hcover : GNDeepLiftResidueCover p q b k R) :
    ((Finset.range (X + 1)).filter
      (fun a => q ^ k ∣ GN p a b)).card ≤
        R.card * ((X + 1) / q ^ k + 1) := by
  classical
  let m := q ^ k
  let C := fun r =>
    (Finset.range (X + 1)).filter (fun a => Nat.ModEq m a r)
  have hm : 0 < m := pow_pos hq.pos _
  have hsub :
      (Finset.range (X + 1)).filter
          (fun a => q ^ k ∣ GN p a b) ⊆
        R.biUnion C := by
    intro a ha
    rcases Finset.mem_filter.mp ha with ⟨haX, haGN⟩
    obtain ⟨r, hrR, har⟩ := hcover a haGN
    exact Finset.mem_biUnion.mpr
      ⟨r, hrR, Finset.mem_filter.mpr ⟨haX, har⟩⟩
  calc
    ((Finset.range (X + 1)).filter
        (fun a => q ^ k ∣ GN p a b)).card
        ≤ (R.biUnion C).card :=
          Finset.card_le_card hsub
    _ ≤ ∑ r ∈ R, (C r).card :=
          Finset.card_biUnion_le
    _ ≤ ∑ _r ∈ R, ((X + 1) / m + 1) := by
          apply Finset.sum_le_sum
          intro r _hr
          have hcount :=
            Nat.count_modEq_card (X + 1) hm r
          have hcount' :
              (C r).card =
                (X + 1) / m +
                  if r % m < (X + 1) % m then 1 else 0 := by
            simpa [C, Nat.count_eq_card_filter_range] using hcount
          rw [hcount']
          split_ifs <;> omega
    _ = R.card * ((X + 1) / q ^ k + 1) := by
          simp [m]

/-- A cover with at most `p - 1` addresses gives the memo's GN count shape. -/
theorem card_gn_deep_lift_range_le
    {p q b k X : ℕ} {R : Finset ℕ}
    (hq : Nat.Prime q)
    (hcard : R.card ≤ p - 1)
    (hcover : GNDeepLiftResidueCover p q b k R) :
    ((Finset.range (X + 1)).filter
      (fun a => q ^ k ∣ GN p a b)).card ≤
        (p - 1) * ((X + 1) / q ^ k + 1) := by
  calc
    ((Finset.range (X + 1)).filter
      (fun a => q ^ k ∣ GN p a b)).card
        ≤ R.card * ((X + 1) / q ^ k + 1) :=
          card_gn_deep_lift_range_le_of_residueCover hq hcover
    _ ≤ (p - 1) * ((X + 1) / q ^ k + 1) :=
          Nat.mul_le_mul_right _ hcard

/-- `Finset.Icc` form of the finite-address GN count. -/
theorem card_gn_deep_lift_residue_classes_le
    {p q b k X : ℕ} {R : Finset ℕ}
    (hq : Nat.Prime q)
    (hcard : R.card ≤ p - 1)
    (hcover : GNDeepLiftResidueCover p q b k R) :
    ((Finset.Icc 0 X).filter
      (fun a => q ^ k ∣ GN p a b)).card ≤
        (p - 1) * ((X + 1) / q ^ k + 1) := by
  rw [← Nat.range_succ_eq_Icc_zero]
  exact card_gn_deep_lift_range_le hq hcard hcover

/-- Divisibility layers and p-adic-depth layers are the same when GN is nonzero. -/
theorem gn_deep_lift_filter_eq_padic_depth_filter
    {p q b k X : ℕ}
    (hq : Nat.Prime q)
    (hGN :
      ∀ a ∈ Finset.Icc 0 X, GN p a b ≠ 0) :
    (Finset.Icc 0 X).filter
        (fun a => q ^ k ∣ GN p a b) =
      (Finset.Icc 0 X).filter
        (fun a => k ≤ padicValNat q (GN p a b)) := by
  ext a
  simp only [Finset.mem_filter]
  constructor
  · intro ha
    exact ⟨ha.1,
      (padicValNat_le_iff_dvd hq (hGN a ha.1) k).2 ha.2⟩
  · intro ha
    exact ⟨ha.1,
      (padicValNat_le_iff_dvd hq (hGN a ha.1) k).1 ha.2⟩

/-- Feed GN p-adic depth directly into the legacy finite exponential layer-cake. -/
theorem exp_gn_padic_layer_cake
    {p q b X : ℕ} {t : ℝ}
    (ht : 0 < t)
    (hVbd :
      ∀ a ≤ X, padicValNat q (GN p a b) ≤ X + 1) :
    (∑ a ∈ Finset.Icc 0 X,
        Real.exp (t * (padicValNat q (GN p a b) : ℝ))) ≤
      (X + 1 : ℝ) + (Real.exp t - 1) *
        (∑ k ∈ Finset.Icc 1 (X + 1),
          Real.exp (t * ((k : ℝ) - 1)) *
            (((Finset.Icc 0 X).filter
              (fun a =>
                a ≤ X ∧
                  k ≤ padicValNat q (GN p a b))).card : ℝ)) := by
  exact exp_layer_cake X t ht
    (fun a => padicValNat q (GN p a b)) hVbd

end DkMath.ABC
