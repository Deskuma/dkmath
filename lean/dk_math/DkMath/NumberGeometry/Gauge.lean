/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberGeometry.Basic

namespace DkMath.NumberGeometry
noncomputable section

/-!
# Relative unit gauge and natural counting shells

This module interprets an active two-point kernel as a relative square-mass
unit.  The primary shell predicate is denominator-free; normalized mass is a
secondary quotient view whose arithmetic interpretation requires activity.
-/

/-- The relative square-mass unit supplied by a two-point kernel. -/
def massGauge (K : TwoPointKernel) : ℝ :=
  pairMass K.source K.target

/-- A point lies on natural shell `n` when its source mass is `n` gauge units. -/
def OnNatShell (K : TwoPointKernel) (n : ℕ) (P : Point) : Prop :=
  pairMass K.source P = (n : ℝ) * massGauge K

/-- The source point lies on the zero natural shell. -/
@[simp]
theorem onNatShell_zero_source (K : TwoPointKernel) :
    OnNatShell K 0 K.source := by
  simp [OnNatShell, massGauge]

/-- The target point lies on the unit natural shell. -/
@[simp]
theorem onNatShell_one_target (K : TwoPointKernel) :
    OnNatShell K 1 K.target := by
  simp [OnNatShell, massGauge]

/-- Unfolding a natural shell gives its source-mass equation. -/
theorem onNatShell_iff (K : TwoPointKernel) (n : ℕ) (P : Point) :
    OnNatShell K n P ↔
      pairMass K.source P = (n : ℝ) * pairMass K.source K.target := by
  rfl

/-- The zero shell consists exactly of the source point. -/
theorem onNatShell_zero_iff (K : TwoPointKernel) (P : Point) :
    OnNatShell K 0 P ↔ P = K.source := by
  constructor
  · intro hP
    have hzero : pairMass K.source P = 0 := by
      simpa [OnNatShell, massGauge] using hP
    exact (pairMass_eq_zero_iff K.source P).mp hzero |>.symm
  · intro hP
    subst P
    exact onNatShell_zero_source K

/-- The mass gauge vanishes exactly for a degenerate kernel. -/
@[simp]
theorem massGauge_eq_zero_iff (K : TwoPointKernel) :
    massGauge K = 0 ↔ K.source = K.target := by
  exact pairMass_eq_zero_iff K.source K.target

/-- The mass gauge is positive exactly when the kernel is active. -/
theorem massGauge_pos_iff_active (K : TwoPointKernel) :
    0 < massGauge K ↔ K.Active := by
  simpa [massGauge, TwoPointKernel.Active] using
    (pairMass_pos_iff K.source K.target)

/-- An active kernel has a nonzero relative square-mass unit. -/
theorem massGauge_ne_zero_of_active
    (K : TwoPointKernel) (hK : K.Active) :
    massGauge K ≠ 0 := by
  exact ne_of_gt ((massGauge_pos_iff_active K).2 hK)

/-- The secondary normalized mass of a point relative to the kernel gauge. -/
def normalizedMass (K : TwoPointKernel) (P : Point) : ℝ :=
  pairMass K.source P / massGauge K

/-- An active shell point has normalized mass equal to its natural index. -/
theorem normalizedMass_eq_nat_of_onNatShell
    (K : TwoPointKernel) (hK : K.Active)
    {n : ℕ} {P : Point}
    (hP : OnNatShell K n P) :
    normalizedMass K P = (n : ℝ) := by
  have hmass : pairMass K.source P = (n : ℝ) * massGauge K := by
    simpa [OnNatShell] using hP
  rw [normalizedMass, hmass]
  field_simp [massGauge_ne_zero_of_active K hK]

/-- A natural normalized mass determines the corresponding shell for an active kernel. -/
theorem onNatShell_of_normalizedMass_eq_nat
    (K : TwoPointKernel) (hK : K.Active)
    {n : ℕ} {P : Point}
    (h : normalizedMass K P = (n : ℝ)) :
    OnNatShell K n P := by
  have hcross : pairMass K.source P = (n : ℝ) * massGauge K := by
    apply (div_eq_iff (massGauge_ne_zero_of_active K hK)).mp
    simpa [normalizedMass] using h
  simpa [OnNatShell] using hcross

/-- A shell successor adds exactly one relative square-mass unit. -/
theorem pairMass_eq_add_massGauge_of_onNatShell_succ
    (K : TwoPointKernel)
    {n : ℕ} {P : Point}
    (hP : OnNatShell K (n + 1) P) :
    pairMass K.source P =
      (n : ℝ) * massGauge K + massGauge K := by
  calc
    pairMass K.source P = ((n + 1 : ℕ) : ℝ) * massGauge K := by
      simpa [OnNatShell] using hP
    _ = (n : ℝ) * massGauge K + massGauge K := by
      rw [Nat.cast_add, Nat.cast_one, add_mul, one_mul]

/-- Shell membership gives the corresponding squared-distance equation. -/
theorem dist_sq_eq_nat_mul_dist_sq_of_onNatShell
    (K : TwoPointKernel)
    {n : ℕ} {P : Point}
    (hP : OnNatShell K n P) :
    dist K.source P ^ 2 =
      (n : ℝ) * dist K.source K.target ^ 2 := by
  calc
    dist K.source P ^ 2 = pairMass K.source P :=
      (pairMass_eq_dist_sq K.source P).symm
    _ = (n : ℝ) * massGauge K := by
      simpa [OnNatShell] using hP
    _ = (n : ℝ) * dist K.source K.target ^ 2 := by
      rw [massGauge, pairMass_eq_dist_sq]

end
end DkMath.NumberGeometry
