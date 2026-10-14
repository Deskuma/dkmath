/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberGeometry.LevelSet

namespace DkMath.NumberGeometry
noncomputable section

/-!
# Multiplicative transitions between relative square-mass gauges

The denominator-free relation `MassScalesBy u K1 K2` records that the gauge of
`K2` is `u` times the gauge of `K1`.  Quotient notation is secondary and is
used only when the source gauge is nonzero.
-/

/-- The gauge of `K2` is `u` times the gauge of `K1`. -/
def MassScalesBy (u : ℝ) (K1 K2 : TwoPointKernel) : Prop :=
  massGauge K2 = u * massGauge K1

/-- Unfolding a multiplicative gauge transition gives its defining equation. -/
theorem massScalesBy_iff (u : ℝ) (K1 K2 : TwoPointKernel) :
    MassScalesBy u K1 K2 ↔ massGauge K2 = u * massGauge K1 := by
  rfl

/-- Every kernel transitions to itself with factor one. -/
theorem massScalesBy_refl (K : TwoPointKernel) :
    MassScalesBy 1 K K := by
  simp [MassScalesBy]

namespace MassScalesBy

/-- Factors compose in the order `u` then `v`, producing `u * v`. -/
theorem trans
    {u v : ℝ} {K1 K2 K3 : TwoPointKernel}
    (h12 : MassScalesBy u K1 K2)
    (h23 : MassScalesBy v K2 K3) :
    MassScalesBy (u * v) K1 K3 := by
  rw [MassScalesBy] at h12 h23 ⊢
  calc
    massGauge K3 = v * massGauge K2 := h23
    _ = v * (u * massGauge K1) := by rw [h12]
    _ = (u * v) * massGauge K1 := by ring

/-- An active source determines the transition factor uniquely. -/
theorem factor_unique
    {u v : ℝ} {K1 K2 : TwoPointKernel}
    (hK1 : K1.Active)
    (hu : MassScalesBy u K1 K2)
    (hv : MassScalesBy v K1 K2) :
    u = v := by
  have hmass : 0 < massGauge K1 :=
    (massGauge_pos_iff_active K1).2 hK1
  have hmul : u * massGauge K1 = v * massGauge K1 := by
    calc
      u * massGauge K1 = massGauge K2 := by
        symm
        exact hu
      _ = v * massGauge K1 := hv
  exact mul_right_cancel₀ (ne_of_gt hmass) hmul

/-- Active source and target kernels force a positive transition factor. -/
theorem factor_pos
    {u : ℝ} {K1 K2 : TwoPointKernel}
    (h : MassScalesBy u K1 K2)
    (h1 : K1.Active)
    (h2 : K2.Active) :
    0 < u := by
  have h1pos : 0 < massGauge K1 :=
    (massGauge_pos_iff_active K1).2 h1
  have h2pos : 0 < massGauge K2 :=
    (massGauge_pos_iff_active K2).2 h2
  have hmul : 0 < u * massGauge K1 := by
    rw [← h]
    exact h2pos
  exact (mul_pos_iff_of_pos_right h1pos).mp hmul

/-- A transition between active kernels has a nonzero factor. -/
theorem factor_ne_zero
    {u : ℝ} {K1 K2 : TwoPointKernel}
    (h : MassScalesBy u K1 K2)
    (h1 : K1.Active)
    (h2 : K2.Active) :
    u ≠ 0 := by
  exact ne_of_gt (factor_pos h h1 h2)

/-- A nonzero transition factor gives the reverse inverse transition. -/
theorem inv
    {u : ℝ} {K1 K2 : TwoPointKernel}
    (h : MassScalesBy u K1 K2)
    (hu : u ≠ 0) :
    MassScalesBy u⁻¹ K2 K1 := by
  rw [MassScalesBy] at h ⊢
  rw [h]
  field_simp [hu]

end MassScalesBy

/-- The quotient gauge ratio from `K1` to `K2`. -/
def massGaugeRatio (K1 K2 : TwoPointKernel) : ℝ :=
  massGauge K2 / massGauge K1

/-- An active source identifies the quotient ratio with a transition factor. -/
theorem massGaugeRatio_eq_of_massScalesBy
    {u : ℝ} {K1 K2 : TwoPointKernel}
    (h1 : K1.Active)
    (h : MassScalesBy u K1 K2) :
    massGaugeRatio K1 K2 = u := by
  rw [massGaugeRatio, h]
  field_simp [massGauge_ne_zero_of_active K1 h1]

/-- A quotient ratio recovers the denominator-free transition relation. -/
theorem massScalesBy_of_massGaugeRatio_eq
    {u : ℝ} {K1 K2 : TwoPointKernel}
    (h1 : K1.Active)
    (h : massGaugeRatio K1 K2 = u) :
    MassScalesBy u K1 K2 := by
  rw [massGaugeRatio] at h
  exact (div_eq_iff (massGauge_ne_zero_of_active K1 h1)).mp h

/-- For an active source, ratio equality and transition are equivalent. -/
theorem massScalesBy_iff_massGaugeRatio_eq
    {u : ℝ} {K1 K2 : TwoPointKernel}
    (h1 : K1.Active) :
    MassScalesBy u K1 K2 ↔ massGaugeRatio K1 K2 = u := by
  constructor
  · exact massGaugeRatio_eq_of_massScalesBy h1
  · exact massScalesBy_of_massGaugeRatio_eq h1

/-- Gauge ratios compose multiplicatively for active intermediate kernels. -/
theorem massGaugeRatio_trans
    {K1 K2 K3 : TwoPointKernel}
    (h1 : K1.Active)
    (h2 : K2.Active) :
    massGaugeRatio K1 K3 =
      massGaugeRatio K1 K2 * massGaugeRatio K2 K3 := by
  have h1ne := massGauge_ne_zero_of_active K1 h1
  have h2ne := massGauge_ne_zero_of_active K2 h2
  rw [massGaugeRatio, massGaugeRatio, massGaugeRatio]
  field_simp [h1ne, h2ne]

/-- A transition is exactly the corresponding squared-distance equation. -/
theorem massScalesBy_iff_dist_sq
    (u : ℝ) (K1 K2 : TwoPointKernel) :
    MassScalesBy u K1 K2 ↔
      dist K2.source K2.target ^ 2 =
        u * dist K1.source K1.target ^ 2 := by
  simp [MassScalesBy, massGauge, pairMass_eq_dist_sq]

/-- A similarity creates a transition with factor `c ^ 2`. -/
theorem massScalesBy_similarity
    (t : Point) (c : ℝ)
    (R : Point ≃ₗᵢ[ℝ] Point)
    (K : TwoPointKernel) :
    MassScalesBy (c ^ 2) K
      (K.map (similarityMap t c R)) := by
  rw [MassScalesBy]
  exact massGauge_similarity t c R K

namespace MassScalesBy

/-- Applying one similarity to both kernels preserves their transition factor. -/
theorem similarity
    {u : ℝ} {K1 K2 : TwoPointKernel}
    (h : MassScalesBy u K1 K2)
    (t : Point) (c : ℝ)
    (R : Point ≃ₗᵢ[ℝ] Point) :
    MassScalesBy u
      (K1.map (similarityMap t c R))
      (K2.map (similarityMap t c R)) := by
  rw [MassScalesBy, massGauge_similarity, massGauge_similarity]
  rw [h]
  ring

end MassScalesBy

namespace TwoPointKernel

/-- Replace a kernel target while keeping its source fixed. -/
def retarget (K : TwoPointKernel) (P : Point) : TwoPointKernel where
  source := K.source
  target := P

/-- Retargeting leaves the source unchanged. -/
@[simp]
theorem retarget_source (K : TwoPointKernel) (P : Point) :
    (K.retarget P).source = K.source := rfl

/-- Retargeting assigns the requested point as target. -/
@[simp]
theorem retarget_target (K : TwoPointKernel) (P : Point) :
    (K.retarget P).target = P := rfl

end TwoPointKernel

/-- Retargeting gives the new kernel exactly the source-to-point mass gauge. -/
theorem massGauge_retarget (K : TwoPointKernel) (P : Point) :
    massGauge (K.retarget P) = pairMass K.source P := by
  rfl

/-- A natural shell point creates a transition with its shell index as factor. -/
theorem massScalesBy_retarget_of_onNatShell
    (K : TwoPointKernel) {n : ℕ} {P : Point}
    (hP : OnNatShell K n P) :
    MassScalesBy (n : ℝ) K (K.retarget P) := by
  change pairMass K.source P = (n : ℝ) * massGauge K
  exact hP

/-- A transition scales the natural-shell mass parameter by the same factor. -/
theorem natShell_massLevel_scale
    {u : ℝ} {K1 K2 : TwoPointKernel}
    (h : MassScalesBy u K1 K2) (n : ℕ) :
    (n : ℝ) * massGauge K2 =
      u * ((n : ℝ) * massGauge K1) := by
  rw [h]
  ring

end
end DkMath.NumberGeometry
