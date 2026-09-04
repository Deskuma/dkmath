/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Three.EisensteinCubeExtraction

#print "file: DkMath.FLT.Three.EisensteinUnitSectors"

namespace DkMath.FLT.Three

open DkMath.NumberTheory.TraceOneQuadratic

/-!
# Eisenstein unit classes modulo cubes

The positive-definite norm classifies the six units in the trace-one basis.
Since `tau ^ 3 = -1`, signs are absorbed into cube factors, leaving the
three representatives `1`, `tau`, and `tau ^ 2`.  No sector is excluded here.
-/

/-- A ring unit is exactly an Eisenstein element of norm one. -/
theorem eisenstein_isUnit_iff_norm_eq_one {x : EisensteinInt} :
    IsUnit x ↔ norm x = 1 := by
  constructor
  · intro hx
    rcases isUnit_iff_exists_inv.mp hx with ⟨y, hxy⟩
    have hy : IsUnit y := by
      apply isUnit_iff_exists_inv.mpr
      exact ⟨x, by simpa [mul_comm] using hxy⟩
    have hxNorm : 0 ≤ norm x := eisenstein_norm_nonneg x
    have hyNorm : 0 ≤ norm y := eisenstein_norm_nonneg y
    have hxPos : 0 < norm x := by
      have hne : norm x ≠ 0 := by
        intro h
        exact hx.ne_zero ((eisenstein_norm_eq_zero_iff x).mp h)
      omega
    have hyPos : 0 < norm y := by
      have hne : norm y ≠ 0 := by
        intro h
        exact hy.ne_zero ((eisenstein_norm_eq_zero_iff y).mp h)
      omega
    have hprod : norm x * norm y = 1 := by
      rw [← traceOne_norm_mul, hxy]
      rfl
    nlinarith
  · exact eisenstein_isUnit_of_norm_eq_one

/-- Exact coordinate classification of the norm-one Eisenstein elements. -/
theorem eisenstein_norm_eq_one_iff_coords (x : EisensteinInt) :
    norm x = 1 ↔
      (x.fst = 1 ∧ x.snd = 0) ∨
      (x.fst = -1 ∧ x.snd = 0) ∨
      (x.fst = 0 ∧ x.snd = 1) ∨
      (x.fst = 0 ∧ x.snd = -1) ∨
      (x.fst = -1 ∧ x.snd = 1) ∨
      (x.fst = 1 ∧ x.snd = -1) := by
  rcases x with ⟨r, s⟩
  change norm (eisensteinCoord r s) = 1 ↔
    (r = 1 ∧ s = 0) ∨
    (r = -1 ∧ s = 0) ∨
    (r = 0 ∧ s = 1) ∨
    (r = 0 ∧ s = -1) ∨
    (r = -1 ∧ s = 1) ∨
    (r = 1 ∧ s = -1)
  rw [eisenstein_norm_coords]
  constructor
  · intro h
    have hs_sq_lt : s ^ 2 < 2 := by
      nlinarith [sq_nonneg (2 * r + s)]
    have hs_sq : s ^ 2 ≤ 1 := by omega
    have hs_bounds : -1 ≤ s ∧ s ≤ 1 := by
      constructor <;> nlinarith [sq_nonneg (s - 1), sq_nonneg (s + 1)]
    have hs_cases : s = -1 ∨ s = 0 ∨ s = 1 := by omega
    rcases hs_cases with rfl | rfl | rfl
    · have hfactor : r * (r - 1) = 0 := by nlinarith
      rcases mul_eq_zero.mp hfactor with hr | hr
      · right; right; right; left; exact ⟨by omega, rfl⟩
      · right; right; right; right; right; exact ⟨by omega, rfl⟩
    · have hfactor : (r - 1) * (r + 1) = 0 := by nlinarith
      rcases mul_eq_zero.mp hfactor with hr | hr
      · left; exact ⟨by omega, rfl⟩
      · right; left; exact ⟨by omega, rfl⟩
    · have hfactor : r * (r + 1) = 0 := by nlinarith
      rcases mul_eq_zero.mp hfactor with hr | hr
      · right; right; left; exact ⟨by omega, rfl⟩
      · right; right; right; right; left; exact ⟨by omega, rfl⟩
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;> norm_num

/-- The six norm-one elements in the trace-one Eisenstein convention. -/
theorem eisenstein_norm_eq_one_iff_six_units (x : EisensteinInt) :
    norm x = 1 ↔
      x = 1 ∨
      x = -1 ∨
      x = eisensteinTau ∨
      x = -eisensteinTau ∨
      x = eisensteinTau ^ 2 ∨
      x = -(eisensteinTau ^ 2) := by
  constructor
  · intro hx
    rcases (eisenstein_norm_eq_one_iff_coords x).mp hx with
      ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · apply Or.inl
      apply traceOne_ext <;> simp [h1, h2]
    · apply Or.inr; apply Or.inl
      apply traceOne_ext <;> simp [h1, h2]
    · apply Or.inr; apply Or.inr; apply Or.inl
      apply traceOne_ext <;> simp [h1, h2, eisensteinTau, tau]
    · apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inl
      apply traceOne_ext <;> simp [h1, h2, eisensteinTau, tau]
    · apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inl
      rw [eisenstein_tau_sq]
      apply traceOne_ext <;> simp [h1, h2, eisensteinTau, tau]
    · apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr
      rw [eisenstein_tau_sq]
      apply traceOne_ext <;> simp [h1, h2, eisensteinTau, tau]
  · rintro (rfl | rfl | rfl | rfl | rfl | rfl)
    · norm_num [DkMath.NumberTheory.TraceOneQuadratic.norm]
    · norm_num [DkMath.NumberTheory.TraceOneQuadratic.norm]
    · exact eisenstein_tau_norm
    · norm_num [DkMath.NumberTheory.TraceOneQuadratic.norm,
        eisensteinTau, tau]
    · rw [pow_two, traceOne_norm_mul]
      simp [eisenstein_tau_norm]
    · norm_num [DkMath.NumberTheory.TraceOneQuadratic.norm,
        eisensteinTau, tau, pow_two,
        DkMath.NumberTheory.TraceOneQuadratic.mul]

/-- Units-facing public classification. -/
theorem eisensteinUnit_cases (epsilon : EisensteinIntˣ) :
    (epsilon : EisensteinInt) = 1 ∨
      (epsilon : EisensteinInt) = -1 ∨
      (epsilon : EisensteinInt) = eisensteinTau ∨
      (epsilon : EisensteinInt) = -eisensteinTau ∨
      (epsilon : EisensteinInt) = eisensteinTau ^ 2 ∨
      (epsilon : EisensteinInt) = -(eisensteinTau ^ 2) := by
  exact (eisenstein_norm_eq_one_iff_six_units (epsilon : EisensteinInt)).mp
    (eisenstein_isUnit_iff_norm_eq_one.mp epsilon.isUnit)

/-- Multiplication by `tau` absorbs a negative cube. -/
theorem tau_mul_cube_absorbs_neg (gamma : EisensteinInt) :
    (eisensteinTau * gamma) ^ 3 = -(gamma ^ 3) := by
  rw [mul_pow, eisenstein_tau_cube]
  ring

/-- The three canonical unit sectors modulo cubes. -/
inductive EisensteinUnitSector
  | one
  | tau
  | tauSq
  deriving DecidableEq, Repr

def EisensteinUnitSector.rep : EisensteinUnitSector → EisensteinInt
  | .one => 1
  | .tau => eisensteinTau
  | .tauSq => eisensteinTau ^ 2

theorem EisensteinUnitSector.rep_norm (sector : EisensteinUnitSector) :
    norm sector.rep = 1 := by
  cases sector with
  | one => norm_num [EisensteinUnitSector.rep,
      DkMath.NumberTheory.TraceOneQuadratic.norm]
  | tau => exact eisenstein_tau_norm
  | tauSq =>
      rw [EisensteinUnitSector.rep, pow_two, traceOne_norm_mul]
      simp [eisenstein_tau_norm]

theorem EisensteinUnitSector.rep_isUnit (sector : EisensteinUnitSector) :
    IsUnit sector.rep :=
  eisenstein_isUnit_of_norm_eq_one sector.rep_norm

/-- Every unit is a canonical sector representative times a unit cube. -/
theorem exists_sector_mul_cube_of_unit (epsilon : EisensteinIntˣ) :
    ∃ sector : EisensteinUnitSector,
      ∃ delta : EisensteinInt,
        IsUnit delta ∧
          (epsilon : EisensteinInt) = sector.rep * delta ^ 3 := by
  rcases eisensteinUnit_cases epsilon with h | h | h | h | h | h
  · refine ⟨.one, 1, by simp, ?_⟩
    simpa [EisensteinUnitSector.rep] using h
  · refine ⟨.one, eisensteinTau,
      eisenstein_isUnit_iff_norm_eq_one.mpr eisenstein_tau_norm, ?_⟩
    rw [EisensteinUnitSector.rep, h, eisenstein_tau_cube]
    simp
  · refine ⟨.tau, 1, by simp, ?_⟩
    simpa [EisensteinUnitSector.rep] using h
  · refine ⟨.tau, eisensteinTau,
      eisenstein_isUnit_iff_norm_eq_one.mpr eisenstein_tau_norm, ?_⟩
    rw [EisensteinUnitSector.rep, h, eisenstein_tau_cube]
    ring
  · refine ⟨.tauSq, 1, by simp, ?_⟩
    simpa [EisensteinUnitSector.rep] using h
  · refine ⟨.tauSq, eisensteinTau,
      eisenstein_isUnit_iff_norm_eq_one.mpr eisenstein_tau_norm, ?_⟩
    rw [EisensteinUnitSector.rep, h, eisenstein_tau_cube]
    ring

/-- A cube-up-to-unit packet normalized to one of the three sectors. -/
structure EisensteinCubeSectorPacket
    (a b c : ℕ) : Type where
  cubeUpToUnit : EisensteinCubeUpToUnitPacket a b c
  sector : EisensteinUnitSector
  gamma : EisensteinInt
  beta_eq :
    cubeUpToUnit.conjugateCoprime.stripped.beta =
      sector.rep * gamma ^ 3

/-- Normalize a cube-up-to-unit packet to a canonical unit sector. -/
noncomputable def eisensteinCubeSectorPacket_of_cubeUpToUnit
    {a b c : ℕ} (p : EisensteinCubeUpToUnitPacket a b c) :
    EisensteinCubeSectorPacket a b c := by
  classical
  let hSector := exists_sector_mul_cube_of_unit p.epsilon
  let sector := Classical.choose hSector
  have hSectorData := Classical.choose_spec hSector
  let delta := Classical.choose hSectorData
  have hDeltaData := Classical.choose_spec hSectorData
  have hEpsilon := hDeltaData.2
  have hBeta :
      p.conjugateCoprime.stripped.beta =
        sector.rep * (delta * p.gamma) ^ 3 := by
    calc
      p.conjugateCoprime.stripped.beta =
          (p.epsilon : EisensteinInt) * p.gamma ^ 3 := p.beta_eq
      _ = (sector.rep * delta ^ 3) * p.gamma ^ 3 := by rw [hEpsilon]
      _ = sector.rep * (delta * p.gamma) ^ 3 := by
        rw [mul_pow]
        ring
  exact ⟨p, sector, delta * p.gamma, hBeta⟩

end DkMath.FLT.Three
