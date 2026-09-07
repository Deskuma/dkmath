/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.ABC.GNExcessCubicRealizedBoundary

#print "file: DkMath.ABC.GNExcessCubicRealizedModuli"

namespace DkMath.ABC

open DkMath.CosmicFormulaBinom DkMath.NumberTheory

/-! ## Factorization coordinates and injectivity -/

/-- At a family prime, the joint modulus factorization records the encoded
active depth, and records zero for an inactive coordinate. -/
theorem GNExcessJointDepthModulus_factorization_at
    {Q : Finset ℕ} {excess : ∀ q ∈ Q, ℕ}
    (hQprime : ∀ q ∈ Q, Nat.Prime q)
    {q : ℕ} (hqQ : q ∈ Q) :
    (GNExcessJointDepthModulus Q excess).factorization q =
      if 0 < GNExcessProfileValue Q excess q then
        GNExcessProfileValue Q excess q + 1 else 0 := by
  classical
  let S := GNExcessActivePrimeSet Q excess
  let f := fun r : ℕ => r ^ (GNExcessProfileValue Q excess r + 1)
  have hprime : ∀ r ∈ S, Nat.Prime r := by
    intro r hr
    exact hQprime r (Finset.mem_filter.mp hr).1
  have hnonzero : ∀ r ∈ S, f r ≠ 0 := by
    intro r hr
    exact pow_ne_zero _ (hprime r hr).ne_zero
  have hfac := congrArg (fun g : ℕ →₀ ℕ => g q)
    (Nat.factorization_prod hnonzero)
  have hfac' :
      (GNExcessJointDepthModulus Q excess).factorization q =
        ∑ r ∈ S, (f r).factorization q := by
    simpa only [GNExcessJointDepthModulus_eq_prod, S, f,
      Finsupp.coe_finsetSum, Finset.sum_apply] using hfac
  rw [hfac']
  simp only [f, Nat.factorization_pow, Finsupp.coe_smul,
    Pi.smul_apply, nsmul_eq_mul]
  by_cases hactive : 0 < GNExcessProfileValue Q excess q
  · have hqS : q ∈ S := by
      exact Finset.mem_filter.mpr ⟨hqQ, hactive⟩
    rw [if_pos hactive]
    calc
      ∑ r ∈ S,
          (GNExcessProfileValue Q excess r + 1) * r.factorization q =
        (GNExcessProfileValue Q excess q + 1) * q.factorization q := by
          apply Finset.sum_eq_single q
          · intro r hr hrq
            rw [(hprime r hr).factorization, Finsupp.single_apply]
            simp [hrq]
          · intro hqnot
            exact False.elim (hqnot hqS)
      _ = GNExcessProfileValue Q excess q + 1 := by
          rw [(hprime q hqS).factorization, Finsupp.single_eq_same]
          simp
  · have hqnot : q ∉ S := by
      intro hqS
      exact hactive (Finset.mem_filter.mp hqS).2
    rw [if_neg hactive]
    apply Finset.sum_eq_zero
    intro r hr
    rw [(hprime r hr).factorization, Finsupp.single_apply]
    simp only [mul_eq_zero]
    right
    simp only [ite_eq_right_iff]
    intro hrq
    subst r
    exact False.elim (hqnot hr)

/-- The joint modulus map is injective on profiles over a finite prime family.
Inactive coordinates are recovered as zero; active coordinates are recovered
from their factorization exponents. -/
theorem GNExcessJointDepthModulus_injective
    {Q : Finset ℕ}
    (hQprime : ∀ q ∈ Q, Nat.Prime q) :
    Function.Injective (GNExcessJointDepthModulus Q) := by
  intro e₁ e₂ hM
  funext q hq
  have hfac := congrArg (fun n : ℕ => n.factorization q) hM
  have hfac' := hfac
  rw [GNExcessJointDepthModulus_factorization_at hQprime hq,
    GNExcessJointDepthModulus_factorization_at hQprime hq] at hfac'
  by_cases h₁ : 0 < GNExcessProfileValue Q e₁ q
  · have h₂ : 0 < GNExcessProfileValue Q e₂ q := by
      by_contra hn
      have hz : GNExcessProfileValue Q e₂ q = 0 :=
        Nat.eq_zero_of_not_pos hn
      have hfac'' := hfac'
      simp [h₁, hz] at hfac''
    have hfac'' := hfac'
    simp [h₁, h₂] at hfac''
    have hv : GNExcessProfileValue Q e₁ q =
        GNExcessProfileValue Q e₂ q := by omega
    simpa [GNExcessProfileValue, hq] using hv
  · have hz₁ : GNExcessProfileValue Q e₁ q = 0 :=
      Nat.eq_zero_of_not_pos h₁
    have h₂ : ¬ 0 < GNExcessProfileValue Q e₂ q := by
      intro hp
      have hfac'' := hfac'
      simp [hz₁, hp] at hfac''
    have hz₂ : GNExcessProfileValue Q e₂ q = 0 :=
      Nat.eq_zero_of_not_pos h₂
    have hv : GNExcessProfileValue Q e₁ q =
        GNExcessProfileValue Q e₂ q := hz₁.trans hz₂.symm
    simpa [GNExcessProfileValue, hq] using hv

/-! ## Distinct realized cubic moduli -/

/-- The finite set of distinct joint moduli of realized canonical cubic large
profiles. -/
noncomputable def GNExcessCubicRealizedLargeModulusSpace (X : ℕ) : Finset ℕ :=
  (GNExcessRealizedLargeProfileSpace
    (GNNonExceptionalIntervalPrimeFamily 3 1 X) 3 1 X).image
      (GNExcessJointDepthModulus
        (GNNonExceptionalIntervalPrimeFamily 3 1 X))

/-- Membership in the realized modulus space is witnessed by a realized large
profile and its joint-modulus equality. -/
theorem mem_GNExcessCubicRealizedLargeModulusSpace_iff
    {X M : ℕ} :
    M ∈ GNExcessCubicRealizedLargeModulusSpace X ↔
      ∃ excess ∈ GNExcessRealizedLargeProfileSpace
        (GNNonExceptionalIntervalPrimeFamily 3 1 X) 3 1 X,
        GNExcessJointDepthModulus
          (GNNonExceptionalIntervalPrimeFamily 3 1 X) excess = M := by
  classical
  simp [GNExcessCubicRealizedLargeModulusSpace]

/-- The realized cubic modulus space preserves profile cardinality. -/
theorem card_GNExcessCubicRealizedLargeModulusSpace
    {X : ℕ} :
    (GNExcessCubicRealizedLargeModulusSpace X).card =
      (GNExcessRealizedLargeProfileSpace
        (GNNonExceptionalIntervalPrimeFamily 3 1 X) 3 1 X).card := by
  classical
  unfold GNExcessCubicRealizedLargeModulusSpace
  apply Finset.card_image_of_injective
  exact GNExcessJointDepthModulus_injective
    (fun q hq => GNNonExceptionalIntervalPrimeFamily_prime hq)

/-- The cubic realized modulus moment is exactly a sum over distinct integer
moduli rather than profile coordinates. -/
theorem GNExcessCubicRealizedLargeModulusMoment_eq_sum_modulusSpace
    {X : ℕ} :
    GNExcessCubicRealizedLargeModulusMoment X =
      ∑ M ∈ GNExcessCubicRealizedLargeModulusSpace X,
        (M : ℝ) ^ (3 / 8 : ℝ) := by
  classical
  unfold GNExcessCubicRealizedLargeModulusMoment
    GNExcessCubicRealizedLargeModulusSpace
  rw [Finset.sum_image]
  · intro x hx y hy hxy
    exact GNExcessJointDepthModulus_injective
      (fun q hq => GNNonExceptionalIntervalPrimeFamily_prime hq) hxy

/-! ## Witness and quadratic divisor bridge -/

/-- Every realized cubic modulus has a positive interval witness and is the
repeated part at that witness. -/
theorem GNExcessCubicRealizedLargeModulusSpace_exists_witness
    {X M : ℕ}
    (hM : M ∈ GNExcessCubicRealizedLargeModulusSpace X) :
    ∃ a : ℕ,
      0 < a ∧
      a ∈ Finset.Icc 0 X ∧
      M = GNNonExceptionalRepeatedPart 3 a 1 := by
  obtain ⟨excess, hexcess, hmod⟩ :=
    (mem_GNExcessCubicRealizedLargeModulusSpace_iff (X := X) (M := M)).mp hM
  obtain ⟨a, ha, haE⟩ :=
    GNExcessRealizedLargeProfileSpace_exists_positive_point hexcess
  obtain ⟨haI, haProfile⟩ := Finset.mem_filter.mp haE
  refine ⟨a, ha, haI, ?_⟩
  calc
    M = GNExcessJointDepthModulus
        (GNNonExceptionalIntervalPrimeFamily 3 1 X) excess := hmod.symm
    _ = GNExcessJointDepthModulus
        (GNNonExceptionalIntervalPrimeFamily 3 1 X)
          (GNExcessDepthProfileAt
            (GNNonExceptionalIntervalPrimeFamily 3 1 X) 3 1 a) := by
      rw [haProfile]
    _ = GNNonExceptionalRepeatedPart 3 a 1 := by
      exact GNExcessJointDepthModulus_target_eq_repeatedPart
        (p := 3) (b := 1) (a := a) (X := X)
        Nat.prime_three haI (by simp)

/-- Every realized cubic modulus divides the corresponding cubic GN value. -/
theorem GNExcessCubicRealizedLargeModulusSpace_dvd_GN
    {X M : ℕ}
    (hM : M ∈ GNExcessCubicRealizedLargeModulusSpace X) :
    ∃ a : ℕ, 0 < a ∧ a ≤ X ∧ M ∣ GN 3 a 1 := by
  obtain ⟨a, ha, haI, hEq⟩ :=
    GNExcessCubicRealizedLargeModulusSpace_exists_witness hM
  refine ⟨a, ha, (Finset.mem_Icc.mp haI).2, ?_⟩
  rw [hEq]
  exact GNNonExceptionalRepeatedPart_dvd_GN (by
    rw [DkMath.NumberTheory.GN_three_dual_explicit]
    positivity)

/-- Every realized cubic modulus divides `a^2 + 3*a + 3` for a positive
interval witness. -/
theorem GNExcessCubicRealizedLargeModulusSpace_dvd_quadratic
    {X M : ℕ}
    (hM : M ∈ GNExcessCubicRealizedLargeModulusSpace X) :
    ∃ a : ℕ, 0 < a ∧ a ≤ X ∧ M ∣ a ^ 2 + 3 * a + 3 := by
  obtain ⟨a, ha, haX, hdiv⟩ :=
    GNExcessCubicRealizedLargeModulusSpace_dvd_GN hM
  refine ⟨a, ha, haX, ?_⟩
  rw [DkMath.NumberTheory.GN_three_dual_explicit] at hdiv
  simpa using hdiv

/-! ## Structural arithmetic of the extracted moduli -/

/-- Every extracted modulus is larger than the interval length. -/
theorem GNExcessCubicRealizedLargeModulusSpace_interval_lt
    {X M : ℕ}
    (hM : M ∈ GNExcessCubicRealizedLargeModulusSpace X) :
    X + 1 < M := by
  obtain ⟨excess, hexcess, hmod⟩ :=
    (mem_GNExcessCubicRealizedLargeModulusSpace_iff (X := X) (M := M)).mp hM
  have hlarge := mem_realizedLargeProfileSpace_large hexcess
  exact hmod ▸ (Finset.mem_filter.mp hlarge).2

/-- Every extracted modulus satisfies the canonical cubic height bound. -/
theorem GNExcessCubicRealizedLargeModulusSpace_height_le
    {X M : ℕ}
    (hM : M ∈ GNExcessCubicRealizedLargeModulusSpace X) :
    M ≤ 3 * (X + 1)^2 := by
  obtain ⟨excess, hexcess, hmod⟩ :=
    (mem_GNExcessCubicRealizedLargeModulusSpace_iff (X := X) (M := M)).mp hM
  have hheight := mem_realizedLargeProfileSpace_cubic_heightAdmissible hexcess
  change GNExcessJointDepthModulus
      (GNNonExceptionalIntervalPrimeFamily 3 1 X) excess ≤
    3 * (X + 1)^2 at hheight
  exact hmod ▸ hheight

/-- Every extracted modulus is positive. -/
theorem GNExcessCubicRealizedLargeModulusSpace_pos
    {X M : ℕ}
    (hM : M ∈ GNExcessCubicRealizedLargeModulusSpace X) :
    0 < M := by
  have hlarge := GNExcessCubicRealizedLargeModulusSpace_interval_lt hM
  omega

/-- Every prime divisor of an extracted modulus occurs at least squared. -/
theorem GNExcessCubicRealizedLargeModulusSpace_prime_sq_dvd
    {X M q : ℕ}
    (hM : M ∈ GNExcessCubicRealizedLargeModulusSpace X)
    (hq : Nat.Prime q) (hqdvd : q ∣ M) :
    q ^ 2 ∣ M := by
  obtain ⟨a, ha, haI, hEq⟩ :=
    GNExcessCubicRealizedLargeModulusSpace_exists_witness hM
  rw [hEq] at hqdvd ⊢
  unfold GNNonExceptionalRepeatedPart at hqdvd ⊢
  exact prime_sq_dvd_repeatedPrimePowerPart hq hqdvd

/-- Every prime divisor of an extracted cubic modulus is one modulo three. -/
theorem GNExcessCubicRealizedLargeModulusSpace_prime_mod_three_eq_one
    {X M q : ℕ}
    (hM : M ∈ GNExcessCubicRealizedLargeModulusSpace X)
    (hq : Nat.Prime q) (hqdvd : q ∣ M) :
    q % 3 = 1 := by
  obtain ⟨a, ha, haI, hEq⟩ :=
    GNExcessCubicRealizedLargeModulusSpace_exists_witness hM
  have hqrep : q ∣ GNNonExceptionalRepeatedPart 3 a 1 := by
    rw [← hEq]
    exact hqdvd
  have hqS : q ∈ GNNonExceptionalSupport 3 a 1 :=
    prime_mem_GNNonExceptionalSupport_of_dvd_repeatedPart hq hqrep
  let T : Triple := Triple.mk a 1 (a + 1) rfl (by simp)
  exact T.mod_eq_one_of_mem_GNNonExceptionalSupport
    Nat.prime_three ha hqS

/-! ## Human-readable final moment bridge -/

/-- The cubic pointwise moment is bounded by the finite-Euler term plus a sum
over distinct realized integer moduli. -/
theorem exp_GNExcessMassAt_sum_cubic_three_eighths_le_finiteEuler_add_realizedModuli
    {X : ℕ} :
    ∑ a ∈ Finset.Icc 0 X,
        Real.exp ((3 / 8 : ℝ) * GNExcessMassAt
          (GNNonExceptionalIntervalPrimeFamily 3 1 X) 3 1 a) ≤
      2 * (X + 1 : ℝ) *
          GNExcessFiniteEulerDensity
            (GNNonExceptionalIntervalPrimeFamily 3 1 X) 3 1 X
            (3 / 8 : ℝ) +
        ∑ M ∈ GNExcessCubicRealizedLargeModulusSpace X,
          (M : ℝ) ^ (3 / 8 : ℝ) := by
  calc
    _ ≤ 2 * (X + 1 : ℝ) *
          GNExcessFiniteEulerDensity
            (GNNonExceptionalIntervalPrimeFamily 3 1 X) 3 1 X
            (3 / 8 : ℝ) +
        GNExcessCubicRealizedLargeModulusMoment X :=
      exp_GNExcessMassAt_sum_cubic_three_eighths_le_finiteEuler_add_modulusMoment
        (X := X)
    _ = _ := by
      rw [GNExcessCubicRealizedLargeModulusMoment_eq_sum_modulusSpace]

end DkMath.ABC
