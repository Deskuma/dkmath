import DkMath.CosmicFormula.Rotation.CF2D.Basic

/-! First-quadrant unit kernels and their nonnegative algebraic halves. -/
namespace DkMath.CosmicFormula.Rotation.CF2D

structure QuadrantUnitKernel where
  kernel : UnitKernel ℝ
  core_nonneg : 0 ≤ kernel.val.core
  beam_nonneg : 0 ≤ kernel.val.beam

namespace QuadrantUnitKernel

def core (u : QuadrantUnitKernel) : ℝ := u.kernel.val.core
def beam (u : QuadrantUnitKernel) : ℝ := u.kernel.val.beam

theorem norm (u : QuadrantUnitKernel) : u.core ^ 2 + u.beam ^ 2 = 1 := u.kernel.q2_eq_one

theorem core_le_one (u : QuadrantUnitKernel) : u.core ≤ 1 := by
  have := u.norm
  have := u.core_nonneg
  have := sq_nonneg u.beam
  dsimp [core] at *
  nlinarith

def initial : QuadrantUnitKernel :=
  ⟨⟨⟨0, 1⟩, by norm_num [Vec.q2]⟩, by norm_num, by norm_num⟩

noncomputable def half (u : QuadrantUnitKernel) : QuadrantUnitKernel := by
  have h : 0 ≤ (1 - u.core) / 2 := by have := u.core_le_one; linarith
  refine ⟨⟨⟨Real.sqrt ((1 + u.core) / 2), Real.sqrt ((1 - u.core) / 2)⟩, ?_⟩,
    Real.sqrt_nonneg _, Real.sqrt_nonneg _⟩
  change Real.sqrt ((1 + u.core) / 2) ^ 2 + Real.sqrt ((1 - u.core) / 2) ^ 2 = 1
  rw [Real.sq_sqrt (by have := u.core_nonneg; dsimp [core] at *; linarith), Real.sq_sqrt h]
  ring

theorem half_star (u : QuadrantUnitKernel) :
    Vec.star (half u).kernel.val (half u).kernel.val = u.kernel.val := by
  have hc : 0 ≤ (1 + u.core) / 2 := by have := u.core_nonneg; dsimp [core] at *; linarith
  have hs : 0 ≤ (1 - u.core) / 2 := by have := u.core_le_one; linarith
  have h1 := Real.sq_sqrt hc
  have h2 := Real.sq_sqrt hs
  have hn := u.norm
  have hb := u.beam_nonneg
  have hp : 0 ≤ Real.sqrt ((1 + u.core) / 2) * Real.sqrt ((1 - u.core) / 2) :=
    mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hsq : (2 * (Real.sqrt ((1 + u.core) / 2) * Real.sqrt ((1 - u.core) / 2))) ^ 2 = u.beam ^ 2 := by
    calc
      _ = 4 * (Real.sqrt ((1 + u.core) / 2) ^ 2) * (Real.sqrt ((1 - u.core) / 2) ^ 2) := by ring
      _ = u.beam ^ 2 := by rw [h1, h2]; nlinarith [hn]
  have he : 2 * (Real.sqrt ((1 + u.core) / 2) * Real.sqrt ((1 - u.core) / 2)) = u.beam := by
    change 0 ≤ u.beam at hb
    nlinarith
  cases hv : u.kernel.val with
  | mk c s =>
    simp only [Vec.star, half, core, beam, hv] at *
    congr 1 <;> nlinarith

noncomputable def sequence : ℕ → QuadrantUnitKernel
  | 0 => initial
  | n + 1 => half (sequence n)

theorem sequence_star (n : ℕ) :
    Vec.star (sequence (n+1)).kernel.val (sequence (n+1)).kernel.val = (sequence n).kernel.val :=
  half_star _

end QuadrantUnitKernel
end DkMath.CosmicFormula.Rotation.CF2D
