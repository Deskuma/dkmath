/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.ABC.GNExcessCubicPrimitivePell

#print "file: DkMath.ABC.GNExcessCubicShellFiberUniqueness"

/-!
# Deterministic uniqueness for a refined cubic shell fiber

This module freezes the elementary norm-minus-three separation argument for
the production Pell coordinates.  It proves uniqueness after fixing the Pell
parameter `T`, the odd cube-core `r`, and one dyadic modulus shell.  It also
proves injectivity of the canonical `(r,S)` coordinates inside one shell.

No asymptotic estimate, external theorem, Mordell counting statement, or ABC
claim is present here.  In particular, this module does not assert that
`a ↦ M(a)` is globally injective or that a fixed `T` or `S` has bounded global
multiplicity.
-/

namespace DkMath.ABC

/-! ## Integer conic separation -/

/-- Eliminating the common conic parameter gives an exact integer identity. -/
theorem conic_cross_identity {T y₁ y₂ d₁ d₂ : ℤ}
    (h₁ : y₁ ^ 2 + 3 = 4 * T * d₁ ^ 2)
    (h₂ : y₂ ^ 2 + 3 = 4 * T * d₂ ^ 2) :
    (y₂ * d₁) ^ 2 + 3 * d₁ ^ 2 = (y₁ * d₂) ^ 2 + 3 * d₂ ^ 2 := by
  have h₁' := congrArg (fun z : ℤ => z * d₂ ^ 2) h₁
  have h₂' := congrArg (fun z : ℤ => z * d₁ ^ 2) h₂
  nlinarith only [h₁', h₂']

/-- A nonnegative conic solution with `T ≥ 2` satisfies `y ≥ 2d`. -/
theorem conic_y_lower {T y d : ℤ} (hT : 2 ≤ T) (hy : 0 ≤ y) (hd : 0 < d)
    (h : y ^ 2 + 3 = 4 * T * d ^ 2) : 2 * d ≤ y := by
  have hd2 : 1 ≤ d ^ 2 := by nlinarith
  have hmul : 2 * d ^ 2 ≤ T * d ^ 2 :=
    mul_le_mul_of_nonneg_right hT (sq_nonneg d)
  nlinarith

/-- Distinct positive denominators on this conic are separated by a square
factor of at least two. -/
theorem conic_no_close_denominators {T y₁ y₂ d₁ d₂ : ℤ}
    (hT : 2 ≤ T) (hy₁ : 0 ≤ y₁) (hy₂ : 0 ≤ y₂)
    (hd₁ : 0 < d₁) (horder : d₁ < d₂)
    (h₁ : y₁ ^ 2 + 3 = 4 * T * d₁ ^ 2)
    (h₂ : y₂ ^ 2 + 3 = 4 * T * d₂ ^ 2) :
    2 * d₁ ^ 2 ≤ d₂ ^ 2 := by
  have hc := conic_cross_identity h₁ h₂
  have hlow₁ := conic_y_lower hT hy₁ hd₁ h₁
  have hlow₂ := conic_y_lower hT hy₂ (lt_trans hd₁ horder) h₂
  have hA : 0 ≤ y₂ * d₁ := mul_nonneg hy₂ (le_of_lt hd₁)
  have hB : 0 ≤ y₁ * d₂ := mul_nonneg hy₁ (by omega)
  have hsq : d₁ ^ 2 < d₂ ^ 2 := by nlinarith
  have hcross : y₁ * d₂ < y₂ * d₁ := by
    nlinarith [sq_nonneg (y₁ * d₂ - y₂ * d₁)]
  have hstep : y₁ * d₂ + 1 ≤ y₂ * d₁ := by omega
  have hbLow : 2 * d₁ * d₂ ≤ y₁ * d₂ :=
    mul_le_mul_of_nonneg_right hlow₁ (by omega)
  have habLow : 2 * (y₁ * d₂) + 1 ≤
      (y₂ * d₁) ^ 2 - (y₁ * d₂) ^ 2 := by
    nlinarith [sq_nonneg (y₂ * d₁ - y₁ * d₂ - 1)]
  nlinarith [mul_nonneg (show 0 ≤ d₁ by omega)
    (show 0 ≤ d₂ - d₁ by omega)]

/-- The production conic parameter is at least two. -/
theorem cubic_parameter_ge_two {a T d : ℕ}
    (h : (2 * a + 3) ^ 2 + 3 = 4 * T * d ^ 2) : 2 ≤ T := by
  by_contra hnot
  have hcases : T = 0 ∨ T = 1 := by omega
  rcases hcases with rfl | rfl
  · simp at h
  · have heq : a ^ 2 + 3 * a + 3 = d ^ 2 := by nlinarith
    exact cubicQuadratic_ne_square a d heq

/-- An abstract dyadic shell has at most one nonnegative conic solution. -/
theorem conic_shell_unique {T r D y₁ y₂ d₁ d₂ : ℕ}
    (hT : 2 ≤ T) (hd₁ : 0 < d₁) (hd₂ : 0 < d₂)
    (h₁ : y₁ ^ 2 + 3 = 4 * T * d₁ ^ 2)
    (h₂ : y₂ ^ 2 + 3 = 4 * T * d₂ ^ 2)
    (hlo₁ : D ≤ r * d₁ ^ 2) (hhi₁ : r * d₁ ^ 2 < 2 * D)
    (hlo₂ : D ≤ r * d₂ ^ 2) (hhi₂ : r * d₂ ^ 2 < 2 * D) :
    y₁ = y₂ ∧ d₁ = d₂ := by
  have hone (y₁ y₂ d₁ d₂ : ℕ) (hd₁ : 0 < d₁) (ho : d₁ < d₂)
      (h₁ : y₁ ^ 2 + 3 = 4 * T * d₁ ^ 2)
      (h₂ : y₂ ^ 2 + 3 = 4 * T * d₂ ^ 2)
      (hlo : D ≤ r * d₁ ^ 2) (hhi : r * d₂ ^ 2 < 2 * D) : False := by
    have hgapZ := conic_no_close_denominators
      (T := (T : ℤ)) (y₁ := (y₁ : ℤ)) (y₂ := (y₂ : ℤ))
      (d₁ := (d₁ : ℤ)) (d₂ := (d₂ : ℤ))
      (by exact_mod_cast hT) (by positivity) (by positivity)
      (by exact_mod_cast hd₁) (by exact_mod_cast ho)
      (by exact_mod_cast h₁) (by exact_mod_cast h₂)
    have hgap : 2 * d₁ ^ 2 ≤ d₂ ^ 2 := by exact_mod_cast hgapZ
    have hmul := Nat.mul_le_mul_left r hgap
    nlinarith
  have hd : d₁ = d₂ := by
    rcases lt_trichotomy d₁ d₂ with ho | he | ho
    · exact False.elim (hone y₁ y₂ d₁ d₂ hd₁ ho h₁ h₂ hlo₁ hhi₂)
    · exact he
    · exact False.elim (hone y₂ y₁ d₂ d₁ hd₂ ho h₂ h₁ hlo₂ hhi₁)
  refine ⟨?_, hd⟩
  subst d₂
  nlinarith

/-! ## Refined production fiber -/

/-- The production Pell fiber refined by the odd cube-core of the repeated
modulus. -/
noncomputable def GNExcessCubicRealizedLargeModulusShellPellCubeCoreFiber
    (X D T r : ℕ) : Finset ℕ :=
  (GNExcessCubicRealizedLargeModulusShellPellParameterFiber X D T).filter
    (fun a => oddPart (GNExcessCubicFullRepeatedModulus a) = r)

theorem mem_GNExcessCubicRealizedLargeModulusShellPellCubeCoreFiber_iff
    {X D T r a : ℕ} :
    a ∈ GNExcessCubicRealizedLargeModulusShellPellCubeCoreFiber X D T r ↔
      a ∈ GNExcessCubicRealizedLargeModulusShellPellParameterFiber X D T ∧
        oddPart (GNExcessCubicFullRepeatedModulus a) = r := by
  simp [GNExcessCubicRealizedLargeModulusShellPellCubeCoreFiber]

/-- Two members of one refined production fiber coincide. -/
theorem GNExcessCubicRealizedLargeModulusShellPellCubeCoreFiber_subsingleton
    (X D T r : ℕ) :
    ∀ a ∈ GNExcessCubicRealizedLargeModulusShellPellCubeCoreFiber X D T r,
      ∀ b ∈ GNExcessCubicRealizedLargeModulusShellPellCubeCoreFiber X D T r,
        a = b := by
  intro a ha b hb
  obtain ⟨haT, har⟩ :=
    mem_GNExcessCubicRealizedLargeModulusShellPellCubeCoreFiber_iff.mp ha
  obtain ⟨hbT, hbr⟩ :=
    mem_GNExcessCubicRealizedLargeModulusShellPellCubeCoreFiber_iff.mp hb
  have haP := GNExcessCubicRealizedLargeModulusShellPellParameterFiber_primitive_packet haT
  have hbP := GNExcessCubicRealizedLargeModulusShellPellParameterFiber_primitive_packet hbT
  have haW :=
    (mem_GNExcessCubicRealizedLargeModulusShellPellParameterFiber_iff.mp haT).1
  have hbW :=
    (mem_GNExcessCubicRealizedLargeModulusShellPellParameterFiber_iff.mp hbT).1
  have haI : (GNExcessCubicFullRepeatedModulus a,
      GNExcessCubicComplement a) ∈
      GNExcessCubicRealizedLargeModulusShellIncidencePairSpace X D :=
    Finset.mem_image.mpr ⟨a, haW, rfl⟩
  have hbI : (GNExcessCubicFullRepeatedModulus b,
      GNExcessCubicComplement b) ∈
      GNExcessCubicRealizedLargeModulusShellIncidencePairSpace X D :=
    Finset.mem_image.mpr ⟨b, hbW, rfl⟩
  have haC :=
    GNExcessCubicRealizedLargeModulusShellIncidencePair_squareful_packet haI
  have hbC :=
    GNExcessCubicRealizedLargeModulusShellIncidencePair_squareful_packet hbI
  have haS := mem_GNExcessCubicRealizedLargeModulusShellWitnessSpace_iff.mp haW
  have hbS := mem_GNExcessCubicRealizedLargeModulusShellWitnessSpace_iff.mp hbW
  have hra : GNExcessCubicFullRepeatedModulus a =
      r * (evenPart (GNExcessCubicFullRepeatedModulus a)) ^ 2 := by
    simpa only [har] using haC.1
  have hrb : GNExcessCubicFullRepeatedModulus b =
      r * (evenPart (GNExcessCubicFullRepeatedModulus b)) ^ 2 := by
    simpa only [hbr] using hbC.1
  have hu := conic_shell_unique (cubic_parameter_ge_two haP.2.2.1)
    haP.1 hbP.1 haP.2.2.1 hbP.2.2.1
    (le_of_le_of_eq haS.2.1 hra) (lt_of_eq_of_lt hra.symm haS.2.2)
    (le_of_le_of_eq hbS.2.1 hrb) (lt_of_eq_of_lt hrb.symm hbS.2.2)
  omega

/-- The refined production fiber has cardinality at most one. -/
theorem GNExcessCubicRealizedLargeModulusShellPellCubeCoreFiber_card_le_one
    (X D T r : ℕ) :
    (GNExcessCubicRealizedLargeModulusShellPellCubeCoreFiber X D T r).card ≤ 1 :=
  Finset.card_le_one.mpr
    (GNExcessCubicRealizedLargeModulusShellPellCubeCoreFiber_subsingleton
      X D T r)

/-! ## Canonical pair injectivity inside one shell -/

/-- Within one shell, the canonical `(r,S)` coordinates are injective. -/
theorem GNExcessCubicRealizedLargeModulusShellWitness_pair_injective
    (X D : ℕ) :
    Set.InjOn
      (fun a =>
        (oddPart (GNExcessCubicFullRepeatedModulus a),
          GNExcessCubicComplement a))
      (GNExcessCubicRealizedLargeModulusShellWitnessSpace X D : Set ℕ) := by
  intro a ha b hb hab
  have hr := congrArg Prod.fst hab
  have hS := congrArg Prod.snd hab
  dsimp only at hr hS
  let r := oddPart (GNExcessCubicFullRepeatedModulus a)
  let T := r * GNExcessCubicComplement a
  refine GNExcessCubicRealizedLargeModulusShellPellCubeCoreFiber_subsingleton
    X D T r a ?_ b ?_
  · apply mem_GNExcessCubicRealizedLargeModulusShellPellCubeCoreFiber_iff.mpr
    exact ⟨mem_GNExcessCubicRealizedLargeModulusShellPellParameterFiber_iff.mpr
      ⟨ha, rfl⟩, rfl⟩
  · apply mem_GNExcessCubicRealizedLargeModulusShellPellCubeCoreFiber_iff.mpr
    refine ⟨mem_GNExcessCubicRealizedLargeModulusShellPellParameterFiber_iff.mpr
      ⟨hb, ?_⟩, hr.symm⟩
    dsimp [T, r]
    rw [hr, hS]

end DkMath.ABC

#print axioms DkMath.ABC.conic_no_close_denominators
#print axioms DkMath.ABC.conic_shell_unique
#print axioms DkMath.ABC.GNExcessCubicRealizedLargeModulusShellPellCubeCoreFiber_card_le_one
#print axioms DkMath.ABC.GNExcessCubicRealizedLargeModulusShellWitness_pair_injective
