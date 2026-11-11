import DkMath.CosmicFormula.Rotation.CF2D.IntrinsicPolygon

/-! The supremum of the algebraic area candidates, defined independently of trigonometry. -/
namespace DkMath.CosmicFormula.Rotation.CF2D
open Filter
open scoped Topology

noncomputable def intrinsicPi : ℝ := sSup (Set.range areaApprox)

theorem areaApprox_bddAbove : BddAbove (Set.range areaApprox) :=
  ⟨4, by rintro _ ⟨n, rfl⟩; exact areaApprox_le_four n⟩

theorem areaApprox_le_intrinsicPi (n : ℕ) : areaApprox n ≤ intrinsicPi :=
  le_csSup areaApprox_bddAbove ⟨n, rfl⟩

theorem intrinsicPi_le_four : intrinsicPi ≤ 4 := by
  apply csSup_le (Set.range_nonempty areaApprox)
  rintro _ ⟨n, rfl⟩
  exact areaApprox_le_four n

theorem intrinsicPi_pos : 0 < intrinsicPi := by
  have h := areaApprox_le_intrinsicPi 0
  rw [areaApprox_zero] at h
  linarith

theorem tendsto_areaApprox_intrinsicPi : Tendsto areaApprox atTop (𝓝 intrinsicPi) := by
  simpa only [intrinsicPi, sSup_range] using tendsto_atTop_ciSup areaApprox_monotone areaApprox_bddAbove

end DkMath.CosmicFormula.Rotation.CF2D
