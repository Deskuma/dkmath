/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.ABC.GNExcessRealizedFibers

#print "file: DkMath.ABC.GNExcessRealizedMoment"

namespace DkMath.ABC

/-! ## Exact weighted fiber reindex -/

/-- The pointwise exponential moment is exactly the sum over realized fibers.
-/
theorem exp_GNExcessMassAt_sum_eq_realizedFiberSum
    {Q : Finset ℕ} {p b X : ℕ} {t : ℝ} :
    ∑ a ∈ Finset.Icc 0 X,
        Real.exp (t * GNExcessMassAt Q p b a) =
      ∑ excess ∈ GNExcessRealizedProfileSpace Q p b X,
        ((GNExactExcessProfileEvent Q excess p b X).card : ℝ) *
          Real.exp (t * GNExcessActiveProfileMass Q excess) := by
  classical
  let S := Finset.Icc 0 X
  let P := GNExcessRealizedProfileSpace Q p b X
  let profile := GNExcessDepthProfileAt Q p b
  have hmaps : ∀ a ∈ S, profile a ∈ P := by
    intro a ha
    exact point_profile_mem_realizedProfileSpace ha
  rw [← Finset.sum_fiberwise_of_maps_to hmaps
    (fun a => Real.exp (t * GNExcessMassAt Q p b a))]
  apply Finset.sum_congr rfl
  intro excess hexcess
  let E := GNExactExcessProfileEvent Q excess p b X
  have hfiber : {a ∈ S | profile a = excess} = E := by
    rfl
  rw [hfiber]
  calc
    ∑ a ∈ E, Real.exp (t * GNExcessMassAt Q p b a) =
        ∑ _a ∈ E,
          Real.exp (t * GNExcessActiveProfileMass Q excess) := by
      apply Finset.sum_congr rfl
      intro a ha
      rw [GNExcessMassAt_eq_activeProfileMass
        (Finset.mem_filter.mp ha).2]
    _ = (E.card : ℝ) *
        Real.exp (t * GNExcessActiveProfileMass Q excess) := by
      simp

/-! ## Realized small profiles -/

/-- Realized profiles whose active modulus fits in the interval length. -/
noncomputable def GNExcessRealizedSmallProfileSpace
    (Q : Finset ℕ) (p b X : ℕ) :
    Finset (∀ q ∈ Q, ℕ) := by
  classical
  exact (GNExcessRealizedProfileSpace Q p b X).filter
    (fun excess =>
      GNExcessJointDepthModulus Q excess ≤ X + 1)

/-- The realized small-profile density contribution. -/
noncomputable def GNExcessRealizedSmallDensityProfileSum
    (Q : Finset ℕ) (p b X : ℕ) (t : ℝ) : ℝ :=
  ∑ excess ∈ GNExcessRealizedSmallProfileSpace Q p b X,
    GNExcessProfileDensityWeight Q p excess t

/-- Membership in the realized small space is realizedness plus smallness. -/
theorem mem_realizedSmallProfileSpace_iff
    {Q : Finset ℕ} {p b X : ℕ}
    {excess : ∀ q ∈ Q, ℕ} :
    excess ∈ GNExcessRealizedSmallProfileSpace Q p b X ↔
      excess ∈ GNExcessRealizedProfileSpace Q p b X ∧
        GNExcessJointDepthModulus Q excess ≤ X + 1 := by
  classical
  simp [GNExcessRealizedSmallProfileSpace]

/-- The realized small space lies inside the historical formal small space.
-/
theorem realizedSmallProfileSpace_subset_smallProfileSpace
    (Q : Finset ℕ) (p b X : ℕ) (hb : 0 < b) :
    GNExcessRealizedSmallProfileSpace Q p b X ⊆
      GNExcessSmallProfileSpace Q p b X := by
  classical
  intro excess h
  rcases mem_realizedSmallProfileSpace_iff.mp h with ⟨hreal, hsmall⟩
  apply Finset.mem_filter.mpr
  exact ⟨GNExcessRealizedProfileSpace_subset_depthProfileSpace
    Q p b X hb hreal, hsmall⟩

/-- The realized small density sum is bounded by the historical small sum. -/
theorem GNExcessRealizedSmallDensityProfileSum_le
    (Q : Finset ℕ) (p b X : ℕ) (t : ℝ) (hb : 0 < b) :
    GNExcessRealizedSmallDensityProfileSum Q p b X t ≤
      GNExcessSmallDensityProfileSum Q p b X t := by
  classical
  unfold GNExcessRealizedSmallDensityProfileSum
    GNExcessSmallDensityProfileSum
  exact Finset.sum_le_sum_of_subset_of_nonneg
    (realizedSmallProfileSpace_subset_smallProfileSpace Q p b X hb)
    (fun _ _ _ => GNExcessProfileDensityWeight_nonneg)

/-! ## Realized small/large split -/

/-- Large realized membership is realizedness together with the modulus test.
-/
theorem mem_realizedLargeProfileSpace_iff_realized_and_large
    {Q : Finset ℕ} {p b X : ℕ}
    {excess : ∀ q ∈ Q, ℕ} (hb : 0 < b) :
    excess ∈ GNExcessRealizedLargeProfileSpace Q p b X ↔
      excess ∈ GNExcessRealizedProfileSpace Q p b X ∧
        X + 1 < GNExcessJointDepthModulus Q excess := by
  constructor
  · intro h
    have h' := mem_realizedLargeProfileSpace_iff.mp h
    exact ⟨mem_GNExcessRealizedProfileSpace_iff.mpr h'.2,
      (Finset.mem_filter.mp h'.1).2⟩
  · rintro ⟨hreal, hlarge⟩
    apply mem_realizedLargeProfileSpace_iff.mpr
    refine ⟨?_, GNExcessProfileRealized_iff.mpr
      (mem_GNExcessRealizedProfileSpace_iff.mp hreal)⟩
    apply Finset.mem_filter.mpr
    exact ⟨GNExcessRealizedProfileSpace_subset_depthProfileSpace
      Q p b X hb hreal, hlarge⟩

/-- The realized large space is the large filter of the exact realized image.
-/
theorem realizedLargeProfileSpace_eq_realizedProfileSpace_filter_large
    (Q : Finset ℕ) (p b X : ℕ) (hb : 0 < b) :
    GNExcessRealizedLargeProfileSpace Q p b X =
      (GNExcessRealizedProfileSpace Q p b X).filter
        (fun excess =>
          X + 1 < GNExcessJointDepthModulus Q excess) := by
  ext excess
  simp [mem_realizedLargeProfileSpace_iff_realized_and_large hb]

/-- Every realized profile is in exactly one of the small and large spaces. -/
theorem realizedProfileSpace_eq_small_union_large
    (Q : Finset ℕ) (p b X : ℕ) (hb : 0 < b) :
    GNExcessRealizedProfileSpace Q p b X =
      GNExcessRealizedSmallProfileSpace Q p b X ∪
        GNExcessRealizedLargeProfileSpace Q p b X := by
  ext excess
  constructor
  · intro hreal
    by_cases hsmall : GNExcessJointDepthModulus Q excess ≤ X + 1
    · exact Finset.mem_union.mpr
        (Or.inl (mem_realizedSmallProfileSpace_iff.mpr
          ⟨hreal, hsmall⟩))
    · exact Finset.mem_union.mpr
        (Or.inr ((mem_realizedLargeProfileSpace_iff_realized_and_large
          (Q := Q) (p := p) (b := b) (X := X) (excess := excess) hb).mpr
          ⟨hreal, Nat.lt_of_not_ge hsmall⟩))
  · intro hsplit
    rcases Finset.mem_union.mp hsplit with hsmall | hlarge
    · exact (mem_realizedSmallProfileSpace_iff.mp hsmall).1
    · have h' :=
        (mem_realizedLargeProfileSpace_iff_realized_and_large
          (Q := Q) (p := p) (b := b) (X := X) (excess := excess) hb).mp
          hlarge
      exact h'.1

/-- The realized small and large profile spaces are disjoint. -/
theorem disjoint_realizedSmallProfileSpace_realizedLargeProfileSpace
    (Q : Finset ℕ) (p b X : ℕ) (hb : 0 < b) :
    Disjoint
      (GNExcessRealizedSmallProfileSpace Q p b X)
      (GNExcessRealizedLargeProfileSpace Q p b X) := by
  rw [Finset.disjoint_left]
  intro excess hsmall hlarge
  have h' :=
    (mem_realizedLargeProfileSpace_iff_realized_and_large
      (Q := Q) (p := p) (b := b) (X := X) (excess := excess) hb).mp
      hlarge
  exact (Nat.not_lt_of_ge
    (mem_realizedSmallProfileSpace_iff.mp hsmall).2) h'.2

/-! ## Ghost-free moment bridge -/

/-- The pointwise exponential moment uses only realized large profiles. -/
theorem exp_GNExcessMassAt_sum_le_small_add_realizedLarge
    {Q : Finset ℕ} {p b X : ℕ} {t : ℝ}
    (hp : Nat.Prime p)
    (hb : 0 < b)
    (hQprime : ∀ q ∈ Q, Nat.Prime q)
    (hQp : ∀ q ∈ Q, ¬ q ∣ p)
    (hQb : ∀ q ∈ Q, ¬ q ∣ b) :
    ∑ a ∈ Finset.Icc 0 X,
        Real.exp (t * GNExcessMassAt Q p b a) ≤
      2 * (X + 1 : ℝ) *
          GNExcessSmallDensityProfileSum Q p b X t +
        GNExcessRealizedLargeBoundaryProfileSum Q p b X t := by
  classical
  let S := Finset.Icc 0 X
  let P := GNExcessRealizedProfileSpace Q p b X
  let profile := GNExcessDepthProfileAt Q p b
  have hmaps : ∀ a ∈ S, profile a ∈ P := by
    intro a ha
    exact point_profile_mem_realizedProfileSpace ha
  rw [← Finset.sum_fiberwise_of_maps_to hmaps
    (fun a => Real.exp (t * GNExcessMassAt Q p b a))]
  calc
    ∑ excess ∈ P,
        ∑ a ∈ S with profile a = excess,
          Real.exp (t * GNExcessMassAt Q p b a) ≤
        ∑ excess ∈ P,
          if GNExcessJointDepthModulus Q excess ≤ X + 1 then
            2 * (X + 1 : ℝ) *
              GNExcessProfileDensityWeight Q p excess t
          else
            (((p - 1) ^
                (GNExcessActivePrimeSet Q excess).card : ℕ) : ℝ) *
              Real.exp (t * GNExcessActiveProfileMass Q excess) := by
      apply Finset.sum_le_sum
      intro excess hexcess
      let E := GNExactExcessProfileEvent Q excess p b X
      have hfiber : {a ∈ S | profile a = excess} = E := by
        rfl
      rw [hfiber]
      have hmass :
          ∑ a ∈ E,
              Real.exp (t * GNExcessMassAt Q p b a) =
            (E.card : ℝ) *
              Real.exp (t * GNExcessActiveProfileMass Q excess) := by
        calc
          ∑ a ∈ E,
              Real.exp (t * GNExcessMassAt Q p b a) =
              ∑ _a ∈ E,
                Real.exp
                  (t * GNExcessActiveProfileMass Q excess) := by
            apply Finset.sum_congr rfl
            intro a ha
            rw [GNExcessMassAt_eq_activeProfileMass
              (Finset.mem_filter.mp ha).2]
          _ = (E.card : ℝ) *
              Real.exp (t * GNExcessActiveProfileMass Q excess) := by
            simp
      rw [hmass]
      by_cases hsmall :
          GNExcessJointDepthModulus Q excess ≤ X + 1
      · rw [if_pos hsmall]
        unfold GNExcessProfileDensityWeight
        calc
          (E.card : ℝ) *
              Real.exp (t * GNExcessActiveProfileMass Q excess) ≤
              (2 * (X + 1 : ℝ) *
                ((((p - 1) ^
                  (GNExcessActivePrimeSet Q excess).card : ℕ) : ℝ) /
                    (GNExcessJointDepthModulus Q excess : ℝ))) *
                Real.exp
                  (t * GNExcessActiveProfileMass Q excess) := by
            exact mul_le_mul_of_nonneg_right
              (card_GNExactExcessProfileEvent_le_smallDensity
                hp hQprime hQp hQb hsmall)
              (Real.exp_pos _).le
          _ = 2 * (X + 1 : ℝ) *
              ((((p - 1) ^
                (GNExcessActivePrimeSet Q excess).card : ℕ) : ℝ) /
                  (GNExcessJointDepthModulus Q excess : ℝ) *
                Real.exp
                  (t * GNExcessActiveProfileMass Q excess)) := by
            ring
      · rw [if_neg hsmall]
        apply mul_le_mul_of_nonneg_right
        · exact_mod_cast
            card_GNExactExcessProfileEvent_le_largeBoundary
              hp hQprime hQp hQb (Nat.lt_of_not_ge hsmall)
        · exact (Real.exp_pos _).le
    _ = 2 * (X + 1 : ℝ) *
          GNExcessRealizedSmallDensityProfileSum Q p b X t +
        GNExcessRealizedLargeBoundaryProfileSum Q p b X t := by
      unfold GNExcessRealizedLargeBoundaryProfileSum
      rw [realizedLargeProfileSpace_eq_realizedProfileSpace_filter_large
        Q p b X hb]
      simp only [P, GNExcessRealizedSmallDensityProfileSum,
        GNExcessRealizedSmallProfileSpace,
        GNExcessRealizedProfileSpace,
        Finset.sum_filter]
      rw [Finset.mul_sum]
      simp only [mul_ite, mul_zero]
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro excess hexcess
      split_ifs with hsmall hlarge
      · omega
      · simp
      · simp
      · omega
    _ ≤ 2 * (X + 1 : ℝ) *
          GNExcessSmallDensityProfileSum Q p b X t +
        GNExcessRealizedLargeBoundaryProfileSum Q p b X t := by
      exact add_le_add
        (mul_le_mul_of_nonneg_left
          (GNExcessRealizedSmallDensityProfileSum_le Q p b X t hb)
          (by positivity))
        (le_refl _)

/-- Finite Euler-density version of the ghost-free moment bridge. -/
theorem exp_GNExcessMassAt_sum_le_finiteEuler_add_realizedLarge
    {Q : Finset ℕ} {p b X : ℕ} {t : ℝ}
    (hp : Nat.Prime p)
    (hb : 0 < b)
    (hQprime : ∀ q ∈ Q, Nat.Prime q)
    (hQp : ∀ q ∈ Q, ¬ q ∣ p)
    (hQb : ∀ q ∈ Q, ¬ q ∣ b) :
    ∑ a ∈ Finset.Icc 0 X,
        Real.exp (t * GNExcessMassAt Q p b a) ≤
      2 * (X + 1 : ℝ) *
          GNExcessFiniteEulerDensity Q p b X t +
        GNExcessRealizedLargeBoundaryProfileSum Q p b X t := by
  have hcoef : 0 ≤ 2 * (X + 1 : ℝ) := by
    norm_num
    positivity
  have hsmall :
      2 * (X + 1 : ℝ) *
          GNExcessSmallDensityProfileSum Q p b X t ≤
        2 * (X + 1 : ℝ) *
          GNExcessFiniteEulerDensity Q p b X t :=
    mul_le_mul_of_nonneg_left
      (GNExcessSmallDensityProfileSum_le_finiteEulerDensity
        (Q := Q) (p := p) (b := b) (X := X) (t := t))
      hcoef
  exact (exp_GNExcessMassAt_sum_le_small_add_realizedLarge
    hp hb hQprime hQp hQb).trans
      (add_le_add hsmall (le_refl _))

/-! ## Canonical cubic consumer -/

/-- Canonical cubic specialization of the ghost-free finite-Euler bridge. -/
theorem exp_GNExcessMassAt_sum_le_finiteEuler_add_realizedLarge_cubic
    {X : ℕ} {t : ℝ} :
    ∑ a ∈ Finset.Icc 0 X,
        Real.exp (t * GNExcessMassAt
          (GNNonExceptionalIntervalPrimeFamily 3 1 X) 3 1 a) ≤
      2 * (X + 1 : ℝ) *
          GNExcessFiniteEulerDensity
            (GNNonExceptionalIntervalPrimeFamily 3 1 X) 3 1 X t +
        GNExcessRealizedLargeBoundaryProfileSum
          (GNNonExceptionalIntervalPrimeFamily 3 1 X) 3 1 X t := by
  apply exp_GNExcessMassAt_sum_le_finiteEuler_add_realizedLarge
    (Q := GNNonExceptionalIntervalPrimeFamily 3 1 X)
    (p := 3) (b := 1)
  · norm_num
  · norm_num
  · exact fun q hq => GNNonExceptionalIntervalPrimeFamily_prime hq
  · exact fun q hq => GNNonExceptionalIntervalPrimeFamily_not_dvd_exponent hq
  · exact fun q hq => GNNonExceptionalIntervalPrimeFamily_not_dvd_boundary hq

end DkMath.ABC
