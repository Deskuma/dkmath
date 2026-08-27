/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.MirrorThreatModel
import Mathlib.Analysis.Complex.Norm
import Mathlib.Tactic

#print "file: DkMath.RH.CFBRC.MirrorRootOfUnity"

namespace DkMath.RH.CFBRCProjection

/-- Left complex state in the mirror CFBRC model. -/
noncomputable def mirrorLeft (X Θ : ℝ) : ℂ :=
  (X : ℂ) + Complex.I * (Θ : ℂ)

/-- Right complex state in the mirror CFBRC model. -/
noncomputable def mirrorRight (X Θ : ℝ) : ℂ :=
  (-X : ℂ) + Complex.I * (Θ : ℂ)

/-- The right mirror state is nonzero away from the centered line. -/
theorem mirrorRight_ne_zero_of_x_ne_zero
    {X Θ : ℝ} (hX : X ≠ 0) :
    mirrorRight X Θ ≠ 0 := by
  intro h
  have hre := congrArg Complex.re h
  simp [mirrorRight] at hre
  exact hX (by linarith)

/--
Mirror closure gives equality of the natural powers of the two mirror states.
-/
theorem mirror_pow_eq_of_mirrorCFBRC_eq_zero
    {d : ℕ} {X Θ : ℝ}
    (hzero : mirrorCFBRC d X Θ = 0) :
    mirrorLeft X Θ ^ d = mirrorRight X Θ ^ d := by
  apply sub_eq_zero.mp
  simpa [mirrorCFBRC, mirrorLeft, mirrorRight] using hzero

/--
Away from `X = 0`, every mirror closure produces a root-of-unity quotient
`ω = mirrorLeft / mirrorRight` carrying the right state to the left state.
-/
theorem exists_rootOfUnity_witness_of_mirrorCFBRC_eq_zero
    {d : ℕ} {X Θ : ℝ}
    (hX : X ≠ 0)
    (hzero : mirrorCFBRC d X Θ = 0) :
    ∃ ω : ℂ,
      ω ^ d = 1 ∧
      mirrorLeft X Θ = ω * mirrorRight X Θ := by
  have hR : mirrorRight X Θ ≠ 0 :=
    mirrorRight_ne_zero_of_x_ne_zero hX
  have hp : mirrorLeft X Θ ^ d = mirrorRight X Θ ^ d :=
    mirror_pow_eq_of_mirrorCFBRC_eq_zero hzero
  refine ⟨mirrorLeft X Θ / mirrorRight X Θ, ?_, ?_⟩
  · rw [div_pow, hp]
    exact div_self (pow_ne_zero d hR)
  · exact (div_mul_cancel₀ (mirrorLeft X Θ) hR).symm

/--
A mirror-state multiplier cannot be `1` away from the centered line.
-/
theorem mirror_multiplier_ne_one_of_x_ne_zero
    {X Θ : ℝ} (hX : X ≠ 0) {ω : ℂ}
    (hmap : mirrorLeft X Θ = ω * mirrorRight X Θ) :
    ω ≠ 1 := by
  intro hω
  subst ω
  have hEq : mirrorLeft X Θ = mirrorRight X Θ := by
    simpa using hmap
  have hre := congrArg Complex.re hEq
  simp [mirrorLeft, mirrorRight] at hre
  exact hX (by linarith)

/--
Every off-centered mirror closure lies on a nontrivial `d`-th root-of-unity
branch.  This is the discrete threat model a future zeta bridge must avoid.
-/
theorem exists_nontrivial_rootOfUnity_witness_of_mirrorCFBRC_eq_zero
    {d : ℕ} {X Θ : ℝ}
    (hX : X ≠ 0)
    (hzero : mirrorCFBRC d X Θ = 0) :
    ∃ ω : ℂ,
      ω ^ d = 1 ∧
      ω ≠ 1 ∧
      mirrorLeft X Θ = ω * mirrorRight X Θ := by
  rcases exists_rootOfUnity_witness_of_mirrorCFBRC_eq_zero hX hzero with
    ⟨ω, hpow, hmap⟩
  exact ⟨ω, hpow, mirror_multiplier_ne_one_of_x_ne_zero hX hmap, hmap⟩

/--
The mirror multiplier equation is equivalent to two real linear branch
equations.  These equations are the algebraic precursor of the later
half-angle tangent classification.
-/
theorem mirror_map_implies_linear_branch_equations
    {X Θ : ℝ} {ω : ℂ}
    (hmap : mirrorLeft X Θ = ω * mirrorRight X Θ) :
    (1 + ω.re) * X + ω.im * Θ = 0 ∧
      ω.im * X + (1 - ω.re) * Θ = 0 := by
  have hre := congrArg Complex.re hmap
  have him := congrArg Complex.im hmap
  constructor
  · simp [mirrorLeft, mirrorRight, Complex.mul_re] at hre
    linarith
  · simp [mirrorLeft, mirrorRight, Complex.mul_im] at him
    linarith

/--
Every off-centered mirror closure therefore lies on a nontrivial root-of-unity
branch satisfying an explicit pair of real polynomial equations.
-/
theorem exists_nontrivial_rootOfUnity_linear_branch_of_mirrorCFBRC_eq_zero
    {d : ℕ} {X Θ : ℝ}
    (hX : X ≠ 0)
    (hzero : mirrorCFBRC d X Θ = 0) :
    ∃ ω : ℂ,
      ω ^ d = 1 ∧
      ω ≠ 1 ∧
      (1 + ω.re) * X + ω.im * Θ = 0 ∧
      ω.im * X + (1 - ω.re) * Θ = 0 := by
  rcases exists_nontrivial_rootOfUnity_witness_of_mirrorCFBRC_eq_zero hX hzero with
    ⟨ω, hpow, hω, hmap⟩
  rcases mirror_map_implies_linear_branch_equations hmap with ⟨hre, him⟩
  exact ⟨ω, hpow, hω, hre, him⟩

/-- A positive-degree complex root of unity has norm one. -/
theorem norm_eq_one_of_pow_eq_one
    {d : ℕ} (hd : 0 < d) {ω : ℂ}
    (hpow : ω ^ d = 1) :
    ‖ω‖ = 1 := by
  have hnormPow := congrArg (fun z : ℂ => ‖z‖) hpow
  have hpowReal : ‖ω‖ ^ d = (1 : ℝ) ^ d := by
    simpa only [Complex.norm_pow, norm_one, one_pow] using hnormPow
  exact
    (pow_left_inj₀
      (Complex.norm_nonneg ω)
      (show (0 : ℝ) ≤ 1 by norm_num)
      (Nat.ne_of_gt hd)).mp hpowReal

/-- Real and imaginary components of a positive-degree root of unity lie on the unit circle. -/
theorem re_sq_add_im_sq_eq_one_of_pow_eq_one
    {d : ℕ} (hd : 0 < d) {ω : ℂ}
    (hpow : ω ^ d = 1) :
    ω.re ^ 2 + ω.im ^ 2 = 1 := by
  have hnorm : ‖ω‖ = 1 := norm_eq_one_of_pow_eq_one hd hpow
  have hnormSq : Complex.normSq ω = 1 := by
    rw [Complex.normSq_eq_norm_sq, hnorm]
    norm_num
  simpa [Complex.normSq_apply, pow_two] using hnormSq

/-- The first real branch equation in multiplicative slope form. -/
theorem mirror_branch_slope_mul_eq
    {X Θ : ℝ} {ω : ℂ}
    (hmap : mirrorLeft X Θ = ω * mirrorRight X Θ) :
    (1 + ω.re) * X = -ω.im * Θ := by
  have hlin := (mirror_map_implies_linear_branch_equations hmap).1
  linarith

/--
On a non-antipodal branch, solve the first real branch equation for `X`.
-/
theorem mirror_branch_x_eq_ratio_mul_theta
    {X Θ : ℝ} {ω : ℂ}
    (hmap : mirrorLeft X Θ = ω * mirrorRight X Θ)
    (hden : 1 + ω.re ≠ 0) :
    X = (-ω.im * Θ) / (1 + ω.re) := by
  apply (eq_div_iff hden).2
  have hmul := mirror_branch_slope_mul_eq hmap
  simpa [mul_comm] using hmul

/--
The antipodal root-of-unity branch forces the phase coordinate `Θ` to vanish.
-/
theorem theta_eq_zero_of_antipodal_root_branch
    {d : ℕ} (hd : 0 < d) {X Θ : ℝ} {ω : ℂ}
    (hpow : ω ^ d = 1)
    (hmap : mirrorLeft X Θ = ω * mirrorRight X Θ)
    (hanti : 1 + ω.re = 0) :
    Θ = 0 := by
  have hcircle : ω.re ^ 2 + ω.im ^ 2 = 1 :=
    re_sq_add_im_sq_eq_one_of_pow_eq_one hd hpow
  have hre : ω.re = -1 := by
    linarith
  have him : ω.im = 0 := by
    rw [hre] at hcircle
    nlinarith
  have hlin := (mirror_map_implies_linear_branch_equations hmap).2
  rw [hre, him] at hlin
  norm_num at hlin
  linarith

/--
Complete algebraic split of an off-centered mirror closure into the antipodal
branch and the ordinary rational-slope branches.
-/
theorem exists_rootOfUnity_branch_split_of_mirrorCFBRC_eq_zero
    {d : ℕ} (hd : 0 < d) {X Θ : ℝ}
    (hX : X ≠ 0)
    (hzero : mirrorCFBRC d X Θ = 0) :
    ∃ ω : ℂ,
      ω ^ d = 1 ∧
      ω ≠ 1 ∧
      ((1 + ω.re = 0 ∧ Θ = 0) ∨
        (1 + ω.re ≠ 0 ∧ X = (-ω.im * Θ) / (1 + ω.re))) := by
  rcases exists_nontrivial_rootOfUnity_witness_of_mirrorCFBRC_eq_zero hX hzero with
    ⟨ω, hpow, hω, hmap⟩
  refine ⟨ω, hpow, hω, ?_⟩
  by_cases hden : 1 + ω.re = 0
  · exact Or.inl ⟨hden, theta_eq_zero_of_antipodal_root_branch hd hpow hmap hden⟩
  · exact Or.inr ⟨hden, mirror_branch_x_eq_ratio_mul_theta hmap hden⟩

end DkMath.RH.CFBRCProjection
