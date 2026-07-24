/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.ABC.GNQualityExcessBridge
import DkMath.ABC.MassBridge

#print "file: DkMath.ABC.GNSupportReturn"

set_option linter.style.longLine false
set_option linter.style.emptyLine false

/-!
# Exceptional GN support and lifted-radical return

Exponent-prime support is absorbed into `rad n`.  The complementary GN
support is fresh relative to the original ABC triple and returns as new
squarefree support in the GN power lift.
-/

namespace DkMath.ABC

open DkMath.CosmicFormulaBinom

def GNExceptionalSupport (n a b : ℕ) : Finset ℕ :=
  (GN n a b).factorization.support.filter (fun q => q ∣ n)

def GNNonExceptionalSupport (n a b : ℕ) : Finset ℕ :=
  (GN n a b).factorization.support.filter (fun q => ¬ q ∣ n)

def GNExceptionalSupportProduct (n a b : ℕ) : ℕ :=
  (GNExceptionalSupport n a b).prod id

def GNNonExceptionalSupportProduct (n a b : ℕ) : ℕ :=
  (GNNonExceptionalSupport n a b).prod id

theorem GNExceptionalSupportProduct_pos (n a b : ℕ) :
    0 < GNExceptionalSupportProduct n a b := by
  unfold GNExceptionalSupportProduct
  apply Finset.prod_pos
  intro q hq
  exact Nat.Prime.pos
    (mem_support_factorization_iff.mp (Finset.mem_filter.mp hq).1).2.1

theorem GNNonExceptionalSupportProduct_pos (n a b : ℕ) :
    0 < GNNonExceptionalSupportProduct n a b := by
  unfold GNNonExceptionalSupportProduct
  apply Finset.prod_pos
  intro q hq
  exact Nat.Prime.pos
    (mem_support_factorization_iff.mp (Finset.mem_filter.mp hq).1).2.1

/-- Exact finite partition of GN prime support by divisibility of the exponent. -/
theorem GN_support_eq_exceptional_union_nonExceptional
    (n a b : ℕ) :
    (GN n a b).factorization.support =
      GNExceptionalSupport n a b ∪ GNNonExceptionalSupport n a b := by
  classical
  ext q
  simp only [GNExceptionalSupport, GNNonExceptionalSupport,
    Finset.mem_union, Finset.mem_filter]
  tauto

/-- The two exponent layers of GN support are disjoint. -/
theorem GNExceptionalSupport_disjoint_nonExceptional
    (n a b : ℕ) :
    Disjoint (GNExceptionalSupport n a b)
      (GNNonExceptionalSupport n a b) := by
  classical
  refine Finset.disjoint_left.mpr ?_
  intro q hqE hqN
  exact (Finset.mem_filter.mp hqN).2 (Finset.mem_filter.mp hqE).2

/-- Exact radical product identity for the two GN support layers. -/
theorem rad_GN_eq_exceptional_mul_nonExceptional
    (n a b : ℕ) :
    rad (GN n a b) =
      GNExceptionalSupportProduct n a b *
        GNNonExceptionalSupportProduct n a b := by
  unfold rad GNExceptionalSupportProduct GNNonExceptionalSupportProduct
  rw [GN_support_eq_exceptional_union_nonExceptional]
  exact Finset.prod_union
    (GNExceptionalSupport_disjoint_nonExceptional n a b)

/-- All exponent-exceptional GN support is absorbed by the radical of `n`. -/
theorem GNExceptionalSupportProduct_dvd_rad
    {n a b : ℕ} (hn : 1 ≤ n) :
    GNExceptionalSupportProduct n a b ∣ rad n := by
  rw [← supportMass_eq_abc_rad]
  apply prime_channel_family_prod_dvd_supportMass (Nat.ne_of_gt hn)
  intro q hq
  have hq' := Finset.mem_filter.mp hq
  exact ⟨(mem_support_factorization_iff.mp hq'.1).2.1, hq'.2⟩

/-- Logarithmic absorption of exceptional GN support. -/
theorem log_GNExceptionalSupportProduct_le_log_rad
    {n a b : ℕ} (hn : 1 ≤ n) :
    Real.log (GNExceptionalSupportProduct n a b : ℝ) ≤
      Real.log (rad n : ℝ) := by
  have hdiv := GNExceptionalSupportProduct_dvd_rad
    (n := n) (a := a) (b := b) hn
  have hpos : 0 < (GNExceptionalSupportProduct n a b : ℝ) := by
    exact_mod_cast GNExceptionalSupportProduct_pos n a b
  apply Real.log_le_log hpos
  exact_mod_cast Nat.le_of_dvd (rad_pos (Nat.zero_lt_of_lt hn)) hdiv

/-- Full GN support is bounded by the exponent radical plus fresh support. -/
theorem log_rad_GN_le_log_rad_exp_add_log_nonExceptional
    {n a b : ℕ} (hn : 1 ≤ n) :
    Real.log (rad (GN n a b) : ℝ) ≤
      Real.log (rad n : ℝ) +
        Real.log (GNNonExceptionalSupportProduct n a b : ℝ) := by
  rw [rad_GN_eq_exceptional_mul_nonExceptional, Nat.cast_mul,
    Real.log_mul
      (by exact_mod_cast (Nat.ne_of_gt (GNExceptionalSupportProduct_pos n a b)))
      (by exact_mod_cast (Nat.ne_of_gt (GNNonExceptionalSupportProduct_pos n a b)))]
  linarith [log_GNExceptionalSupportProduct_le_log_rad
    (n := n) (a := a) (b := b) hn]

/-- A non-exceptional GN support prime is fresh relative to all original coordinates. -/
theorem Triple.nonExceptionalSupport_fresh
    (T : Triple) {n q : ℕ}
    (hn : 1 ≤ n) (ha : 0 < T.a)
    (hq : q ∈ GNNonExceptionalSupport n T.a T.b) :
    Nat.Prime q ∧ q ∣ GN n T.a T.b ∧
      ¬ q ∣ T.a ∧ ¬ q ∣ T.b ∧ ¬ q ∣ T.c ∧
        ¬ q ∣ T.a * T.b * T.c := by
  have hmem := Finset.mem_filter.mp hq
  rcases mem_support_factorization_iff.mp hmem.1 with ⟨_, hprime, hqGN⟩
  have hqa := T.not_dvd_boundary_of_not_dvd_exp_of_dvd_GN
    hn ha hmem.2 hqGN
  have hqLiftA : q ∣ (T.gnPowerLift n).a :=
    dvd_mul_of_dvd_right hqGN T.a
  have hqb : ¬ q ∣ T.b := by
    intro hqb
    have hqLiftB : q ∣ (T.gnPowerLift n).b :=
      dvd_pow hqb (Nat.ne_of_gt hn)
    have hqgcd : q ∣ Nat.gcd (T.gnPowerLift n).a
        (T.gnPowerLift n).b := Nat.dvd_gcd hqLiftA hqLiftB
    have hcop := (T.gnPowerLift n).hcop
    rw [Nat.coprime_iff_gcd_eq_one] at hcop
    rw [hcop] at hqgcd
    exact hprime.not_dvd_one hqgcd
  have hqc : ¬ q ∣ T.c := by
    intro hqc
    have hqLiftC : q ∣ (T.gnPowerLift n).c :=
      dvd_pow hqc (Nat.ne_of_gt hn)
    have hcopAC : Nat.Coprime (T.gnPowerLift n).a
        (T.gnPowerLift n).c := by
      rw [← (T.gnPowerLift n).hsum]
      simpa [add_comm] using
        (Nat.coprime_add_self_right).2 (T.gnPowerLift n).hcop
    have hqgcd : q ∣ Nat.gcd (T.gnPowerLift n).a
        (T.gnPowerLift n).c := Nat.dvd_gcd hqLiftA hqLiftC
    rw [hcopAC] at hqgcd
    exact hprime.not_dvd_one hqgcd
  refine ⟨hprime, hqGN, hqa, hqb, hqc, ?_⟩
  intro hqabc
  rcases hprime.dvd_mul.mp hqabc with hqab | hqc'
  · rcases hprime.dvd_mul.mp hqab with hqa' | hqb'
    · exact hqa hqa'
    · exact hqb hqb'
  · exact hqc hqc'

/--
The original radical together with all fresh non-exceptional GN support
divides the radical of the lifted ABC product.
-/
theorem Triple.rad_mul_nonExceptionalProduct_dvd_lift_rad
    (T : Triple) {n : ℕ}
    (hn : 2 ≤ n) (ha : 0 < T.a) (hb : 0 < T.b) :
    rad (T.a * T.b * T.c) *
        GNNonExceptionalSupportProduct n T.a T.b ∣
      rad ((T.gnPowerLift n).a *
        (T.gnPowerLift n).b * (T.gnPowerLift n).c) := by
  let S := (T.a * T.b * T.c).factorization.support ∪
    GNNonExceptionalSupport n T.a T.b
  have hdis :
      Disjoint (T.a * T.b * T.c).factorization.support
        (GNNonExceptionalSupport n T.a T.b) := by
    refine Finset.disjoint_left.mpr ?_
    intro q hqabc hqGN
    exact (T.nonExceptionalSupport_fresh (Nat.one_le_of_lt hn) ha hqGN).2.2.2.2.2
      (mem_support_factorization_iff.mp hqabc).2.2
  have hprod :
      S.prod id =
        rad (T.a * T.b * T.c) *
          GNNonExceptionalSupportProduct n T.a T.b := by
    unfold S GNNonExceptionalSupportProduct rad
    simpa only [id_eq] using Finset.prod_union hdis
  rw [← hprod, ← supportMass_eq_abc_rad]
  apply prime_channel_family_prod_dvd_supportMass
    (by
      simp only [Triple.gnPowerLift_a, Triple.gnPowerLift_b,
        Triple.gnPowerLift_c]
      exact Nat.mul_ne_zero
        (Nat.mul_ne_zero
            (Nat.mul_ne_zero (Nat.ne_of_gt ha)
            (GN_ne_zero_nat_of_two_le hn ha hb))
          (pow_ne_zero n (Nat.ne_of_gt hb)))
        (pow_ne_zero n (by
          rw [← T.hsum]
          omega)))
  intro q hqS
  rcases Finset.mem_union.mp hqS with hqabc | hqGN
  · rcases mem_support_factorization_iff.mp hqabc with ⟨_, hp, hd⟩
    refine ⟨hp, ?_⟩
    rcases hp.dvd_mul.mp hd with hab | hc
    · rcases hp.dvd_mul.mp hab with ha' | hb'
      · change q ∣ (T.a * GN n T.a T.b) * T.b ^ n * T.c ^ n
        exact dvd_mul_of_dvd_left
          (dvd_mul_of_dvd_left
            (dvd_mul_of_dvd_left ha' (GN n T.a T.b)) _) _
      · change q ∣ (T.a * GN n T.a T.b) * T.b ^ n * T.c ^ n
        exact dvd_mul_of_dvd_left
          (dvd_mul_of_dvd_right
            (dvd_pow hb' (Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_two hn))) _) _
    · change q ∣ (T.a * GN n T.a T.b) * T.b ^ n * T.c ^ n
      exact dvd_mul_of_dvd_right
        (dvd_pow hc (Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_two hn))) _
  · have hfresh := T.nonExceptionalSupport_fresh (Nat.one_le_of_lt hn) ha hqGN
    refine ⟨hfresh.1, ?_⟩
    change q ∣ (T.a * GN n T.a T.b) * T.b ^ n * T.c ^ n
    exact dvd_mul_of_dvd_left
      (dvd_mul_of_dvd_left
        (dvd_mul_of_dvd_right hfresh.2.1 T.a) (T.b ^ n)) _

/-- Logarithmic form of fresh radical growth in the GN power lift. -/
theorem Triple.log_rad_add_log_nonExceptional_le_log_lift_rad
    (T : Triple) {n : ℕ}
    (hn : 2 ≤ n) (ha : 0 < T.a) (hb : 0 < T.b) :
    Real.log (rad (T.a * T.b * T.c) : ℝ) +
        Real.log (GNNonExceptionalSupportProduct n T.a T.b : ℝ) ≤
      Real.log (rad ((T.gnPowerLift n).a *
        (T.gnPowerLift n).b * (T.gnPowerLift n).c) : ℝ) := by
  have hc : 0 < T.c := by
    rw [← T.hsum]
    omega
  have habcPos : 0 < T.a * T.b * T.c :=
    Nat.mul_pos (Nat.mul_pos ha hb) hc
  rw [← Real.log_mul
    (by exact_mod_cast (Nat.ne_of_gt
      (rad_pos habcPos)))
    (by exact_mod_cast (Nat.ne_of_gt
      (GNNonExceptionalSupportProduct_pos n T.a T.b))),
    ← Nat.cast_mul]
  apply Real.log_le_log (by
    exact_mod_cast Nat.mul_pos (rad_pos habcPos)
      (GNNonExceptionalSupportProduct_pos n T.a T.b))
  have hliftPos :
      0 < (T.gnPowerLift n).a *
        (T.gnPowerLift n).b * (T.gnPowerLift n).c := by
    simp only [Triple.gnPowerLift_a, Triple.gnPowerLift_b,
      Triple.gnPowerLift_c]
    exact Nat.mul_pos
      (Nat.mul_pos (Nat.mul_pos ha
        (Nat.pos_of_ne_zero (GN_ne_zero_nat_of_two_le hn ha hb)))
        (pow_pos hb n))
      (pow_pos (by rw [← T.hsum]; omega) n)
  exact_mod_cast Nat.le_of_dvd (rad_pos hliftPos)
    (T.rad_mul_nonExceptionalProduct_dvd_lift_rad hn ha hb)

/-- Affine upper budget for the radical growth of the GN power lift. -/
def GNLiftRadicalGrowthBudgetAffine
    (T : Triple) (n : ℕ) (σ C : ℝ) : Prop :=
  Real.log (rad ((T.gnPowerLift n).a *
      (T.gnPowerLift n).b * (T.gnPowerLift n).c) : ℝ) ≤
    (1 + σ) * Real.log (rad (T.a * T.b * T.c) : ℝ) + C

/-- Affine upper budget for fresh non-exceptional GN support. -/
def GNNonExceptionalSupportBudgetAffine
    (T : Triple) (n : ℕ) (σ C : ℝ) : Prop :=
  Real.log (GNNonExceptionalSupportProduct n T.a T.b : ℝ) ≤
    σ * Real.log (rad (T.a * T.b * T.c) : ℝ) + C

/-- Lifted-radical growth controls fresh non-exceptional support. -/
theorem Triple.nonExceptionalSupportBudgetAffine_of_liftGrowth
    (T : Triple) {n : ℕ} {σ C : ℝ}
    (hn : 2 ≤ n) (ha : 0 < T.a) (hb : 0 < T.b)
    (h : GNLiftRadicalGrowthBudgetAffine T n σ C) :
    GNNonExceptionalSupportBudgetAffine T n σ C := by
  have hlower := T.log_rad_add_log_nonExceptional_le_log_lift_rad hn ha hb
  change Real.log (rad ((T.gnPowerLift n).a *
      (T.gnPowerLift n).b * (T.gnPowerLift n).c) : ℝ) ≤
    (1 + σ) * Real.log (rad (T.a * T.b * T.c) : ℝ) + C at h
  dsimp [GNNonExceptionalSupportBudgetAffine]
  linarith

/-- Fresh-support budget plus finite exponent support gives the full affine budget. -/
theorem Triple.GNSupportBudgetAffine_of_nonExceptional
    (T : Triple) {n : ℕ} {σ C : ℝ}
    (hn : 1 ≤ n)
    (h : GNNonExceptionalSupportBudgetAffine T n σ C) :
    GNSupportBudgetAffine T n σ
      (C + Real.log (rad n : ℝ)) := by
  have hsplit := log_rad_GN_le_log_rad_exp_add_log_nonExceptional
    (n := n) (a := T.a) (b := T.b) hn
  dsimp [GNNonExceptionalSupportBudgetAffine] at h
  change Real.log (rad (GN n T.a T.b) : ℝ) ≤
    σ * Real.log (rad (T.a * T.b * T.c) : ℝ) +
      (C + Real.log (rad n : ℝ))
  linarith

/-- Deterministic affine transport from lifted-radical growth to full GN support. -/
theorem Triple.GNSupportBudgetAffine_of_liftGrowth
    (T : Triple) {n : ℕ} {σ C : ℝ}
    (hn : 2 ≤ n) (ha : 0 < T.a) (hb : 0 < T.b)
    (h : GNLiftRadicalGrowthBudgetAffine T n σ C) :
    GNSupportBudgetAffine T n σ
      (C + Real.log (rad n : ℝ)) :=
  T.GNSupportBudgetAffine_of_nonExceptional (Nat.one_le_of_lt hn)
    (T.nonExceptionalSupportBudgetAffine_of_liftGrowth hn ha hb h)

/-- Quality-to-excess theorem whose only transport input is lifted-radical growth. -/
theorem Triple.GNValuationExcess_gt_of_quality_gt_liftGrowth
    (T : Triple) {n : ℕ} {ε σ C : ℝ}
    (hn : 2 ≤ n) (ha : 0 < T.a) (hb : 0 < T.b)
    (hquality : 1 + ε < quality T)
    (hgrowth : GNLiftRadicalGrowthBudgetAffine T n σ C) :
    ((((n - 1 : ℕ) : ℝ) * (1 + ε) - σ) *
          Real.log (rad (T.a * T.b * T.c) : ℝ)) -
        (C + Real.log (rad n : ℝ)) <
      GNValuationExcess n T.a T.b := by
  exact T.GNValuationExcess_gt_of_quality_gt_pred_affine hn ha hb hquality
    (T.GNSupportBudgetAffine_of_liftGrowth
      hn ha hb hgrowth)

end DkMath.ABC
