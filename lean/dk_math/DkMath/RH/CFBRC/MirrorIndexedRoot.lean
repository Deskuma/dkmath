/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.MirrorAngleBranch
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.Tactic

#print "file: DkMath.RH.CFBRC.MirrorIndexedRoot"

namespace DkMath.RH.CFBRCProjection

/-- The trigonometric branch unit is the standard complex exponential root. -/
theorem indexedRootBranchUnit_eq_exp
    {d : ℕ} (hd : 0 < d) (k : ℕ) :
    indexedRootBranchUnit d k =
      Complex.exp
        (2 * Real.pi * Complex.I * ((k : ℂ) / (d : ℂ))) := by
  have hdC : (d : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hd)
  rw [indexedRootBranchUnit, unitCircleAt, rootBranchHalfAngle]
  rw [mul_comm Complex.I (Real.sin (2 * (Real.pi * (k : ℝ) / (d : ℝ))) : ℂ)]
  rw [← Complex.ofReal_cos, ← Complex.ofReal_sin, ← Complex.exp_mul_I]
  congr 1
  push_cast
  field_simp [hdC]
  ring

/-- Every positive-degree complex root of unity has a finite branch index. -/
theorem exists_indexed_root_branch_unit_of_pow_eq_one
    {d : ℕ} (hd : 0 < d) {ω : ℂ}
    (hpow : ω ^ d = 1) :
    ∃ k < d, indexedRootBranchUnit d k = ω := by
  letI : NeZero d := ⟨Nat.ne_of_gt hd⟩
  have hdn : d ≠ 0 := Nat.ne_of_gt hd
  obtain ⟨k, hk, hgen⟩ :=
    (Complex.isPrimitiveRoot_exp d hdn).eq_pow_of_pow_eq_one hpow
  refine ⟨k, hk, ?_⟩
  rw [indexedRootBranchUnit_eq_exp hd k]
  have hexp :
      Complex.exp
          (2 * Real.pi * Complex.I * ((k : ℂ) / (d : ℂ))) = ω := by
    rw [← hgen, ← Complex.exp_nat_mul]
    congr 1
    ring
  exact hexp

@[simp] theorem indexedRootBranchUnit_zero
    {d : ℕ} (hd : 0 < d) :
    indexedRootBranchUnit d 0 = 1 := by
  rw [indexedRootBranchUnit_eq_exp hd 0]
  simp

/--
Every off-centered mirror closure is carried by a nonzero finite branch index
`k < d`.  This converts the abstract root-of-unity witness into a discrete
threat branch.
-/
theorem exists_nonzero_indexed_branch_of_mirrorCFBRC_eq_zero
    {d : ℕ} (hd : 0 < d) {X Θ : ℝ}
    (hX : X ≠ 0)
    (hzero : mirrorCFBRC d X Θ = 0) :
    ∃ k < d,
      k ≠ 0 ∧
      mirrorLeft X Θ = indexedRootBranchUnit d k * mirrorRight X Θ := by
  rcases exists_nontrivial_rootOfUnity_witness_of_mirrorCFBRC_eq_zero hX hzero with
    ⟨ω, hpow, hω, hmap⟩
  rcases exists_indexed_root_branch_unit_of_pow_eq_one hd hpow with
    ⟨k, hk, hkω⟩
  have hk0 : k ≠ 0 := by
    intro hkzero
    subst k
    have hωone : ω = 1 := by
      rw [← hkω]
      exact indexedRootBranchUnit_zero hd
    exact hω hωone
  refine ⟨k, hk, hk0, ?_⟩
  rwa [hkω]

/--
For every non-antipodal indexed branch, mirror closure lies on the explicit
line `X = -tan(π k / d) Θ`.
-/
theorem exists_indexed_tangent_branch_of_mirrorCFBRC_eq_zero
    {d : ℕ} (hd : 0 < d) {X Θ : ℝ}
    (hX : X ≠ 0)
    (hzero : mirrorCFBRC d X Θ = 0)
    (hcos : ∀ k < d, k ≠ 0 →
      Real.cos (rootBranchHalfAngle d k) ≠ 0) :
    ∃ k < d,
      k ≠ 0 ∧
      X = -Real.tan (rootBranchHalfAngle d k) * Θ := by
  rcases exists_nonzero_indexed_branch_of_mirrorCFBRC_eq_zero hd hX hzero with
    ⟨k, hk, hk0, hmap⟩
  exact ⟨k, hk, hk0,
    mirror_branch_x_eq_indexed_neg_tan_mul_theta hmap (hcos k hk hk0)⟩

end DkMath.RH.CFBRCProjection
