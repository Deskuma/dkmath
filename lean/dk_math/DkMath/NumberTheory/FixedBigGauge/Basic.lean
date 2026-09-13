/-
Copyright (c) 2026 DkMath contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: DkMath contributors.
-/
import DkMath.CosmicFormula.Projection.WorldModulus
import DkMath.NumberTheory.Primitive.SquareBody

/-! # Fixed edge, variable arithmetic unit

The edge is a real length. Primality remains a predicate on natural labels.
Positive resolution is required for conservation; nonzero edge is required
when dividing by the edge or by the square unit.
-/

namespace DkMath.NumberTheory.FixedBigGauge

open DkMath.CosmicFormula.Projection
open DkMath.CosmicFormula.Rotation.CF2D
open DkMath.NumberTheory.Primitive
open DkMath.NumberTheory.StructuralArithmetic

noncomputable section

/-- Physical length of one cell at resolution `k`. -/
def fixedBigUnit (R : ℝ) (k : ℕ) : ℝ := R / (k : ℝ)

theorem fixedBigUnit_pos {R : ℝ} {k : ℕ} (hR : 0 < R) (hk : 0 < k) :
    0 < fixedBigUnit R k := div_pos hR (by exact_mod_cast hk)

theorem scale_unit_conservation (R : ℝ) {k : ℕ} (hk : 0 < k) :
    (k : ℝ) * fixedBigUnit R k = R := by
  unfold fixedBigUnit
  have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  field_simp

theorem fixedBig_decomposition (R : ℝ) {k : ℕ} (hk : 0 < k) :
    (k : ℝ) ^ 2 * fixedBigUnit R k ^ 2 = R ^ 2 := by
  rw [← mul_pow, scale_unit_conservation R hk]

theorem unit_eq_iff_scale_mul_eq {R u : ℝ} {k : ℕ} (hk : 0 < k) :
    u = fixedBigUnit R k ↔ (k : ℝ) * u = R := by
  have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  simp only [fixedBigUnit, eq_div_iff hkR, mul_comm u]

theorem fixedBigUnit_div_edge {R : ℝ} (hR : R ≠ 0) (k : ℕ) :
    fixedBigUnit R k / R = 1 / (k : ℝ) := by
  unfold fixedBigUnit
  rw [div_right_comm, div_self hR]

theorem fixedBigUnit_div_edge_eq_projectionGap {R : ℝ} (hR : R ≠ 0)
    (k : ℕ) :
    fixedBigUnit R k / R = U ((k : ℝ) - 1) := by
  rw [fixedBigUnit_div_edge hR]
  simp [U]

theorem fixedBigUnit_div_edge_eq_regularPhaseStep {R : ℝ} (hR : R ≠ 0)
    {k : ℕ} (hk : 0 < k) :
    fixedBigUnit R k / R = regularPhaseStep k := by
  rw [fixedBigUnit_div_edge_eq_projectionGap hR]
  exact projectionGap_eq_regularPhaseStep hk

theorem normalized_unit_bounds {R : ℝ} (hR : R ≠ 0)
    {k : ℕ} (hk : 0 < k) :
    0 < fixedBigUnit R k / R ∧ fixedBigUnit R k / R ≤ 1 := by
  rw [fixedBigUnit_div_edge hR]
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  exact ⟨one_div_pos.mpr (by linarith), (div_le_one (by linarith)).mpr hkR⟩

theorem fixedBig_squareBody_normalization {R : ℝ} (hR : R ≠ 0) (P : ℕ) :
    (R ^ 2 - fixedBigUnit R (P + 1) ^ 2) / fixedBigUnit R (P + 1) ^ 2 =
      (squareBody P : ℝ) := by
  have hkR : ((P : ℝ) + 1) ≠ 0 := by positivity
  simp only [fixedBigUnit, Nat.cast_add, Nat.cast_one, squareBody,
    Nat.cast_pow, Nat.cast_mul, Nat.cast_ofNat]
  field_simp
  ring

theorem fixedBigUnit_transport (R : ℝ) {k l : ℕ} (hk : 0 < k) :
    fixedBigUnit R l = ((k : ℝ) / (l : ℝ)) * fixedBigUnit R k := by
  have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  simp only [fixedBigUnit]
  rw [div_mul_div_comm, mul_comm (l : ℝ) (k : ℝ), mul_div_mul_left R (l : ℝ) hkR]

theorem fixedBigUnit_refinement (R : ℝ) (q k : ℕ) :
    fixedBigUnit R (q * k) = fixedBigUnit R k / (q : ℝ) := by
  simp only [fixedBigUnit, Nat.cast_mul, div_div, mul_comm]

theorem world_unit_eq_edge_mul_projectionGap (R : ℝ)
    {S : Finset ℕ} (hS : KnownPrimeScales S) :
    fixedBigUnit R (primeWorldModulus S) =
      R * U ((primeWorldModulus S : ℝ) - 1) := by
  rw [worldModulus_projection_gap hS]
  simp [fixedBigUnit, div_eq_mul_inv]

theorem freshPrime_fixedBigUnit_refinement (R : ℝ)
    {S : Finset ℕ} (hS : KnownPrimeScales S)
    {q : ℕ} (hq : Nat.Prime q) (hqS : q ∉ S) :
    fixedBigUnit R (primeWorldModulus (insert q S)) =
      fixedBigUnit R (primeWorldModulus S) / (q : ℝ) := by
  have h := congrArg (fun t : ℝ => R * t) (freshPrime_refinement_mesh hS hq hqS)
  simpa only [fixedBigUnit, mul_div, mul_one] using h

end
end DkMath.NumberTheory.FixedBigGauge
