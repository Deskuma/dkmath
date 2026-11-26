/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.CosmicFormula.Rotation.CF2D.DyadicPhase

#print "file: DkMath.CosmicFormula.Rotation.CF2D.DyadicCone"

/-! # 二分核の非負錐による平面の被覆 -/

namespace DkMath.CosmicFormula.Rotation.CF2D
namespace QuadrantUnitKernel

/-- 二つのベクトルが張る非負錐。境界の半直線と原点も含む。 -/
def nonnegativeCone {E : Type*} [AddCommGroup E] [Module ℝ E] (p q : E) : Set E :=
  {x | ∃ a b : ℝ, 0 ≤ a ∧ 0 ≤ b ∧ x = a • p + b • q}

/-- 中点を通る半直線で非負錐を二分する。係数の小さい方を共通項として取り出す。 -/
theorem nonnegativeCone_split {E : Type*} [AddCommGroup E] [Module ℝ E]
    {p w q : E} {c : ℝ} (hc : 0 < c) (h : p + q = c • w) :
    nonnegativeCone p q = nonnegativeCone p w ∪ nonnegativeCone w q := by
  have hw : w = c⁻¹ • (p + q) := by rw [h, smul_smul, inv_mul_cancel₀ hc.ne', one_smul]
  ext x
  constructor
  · rintro ⟨a, b, ha, hb, rfl⟩
    rcases le_total b a with hab | hab
    · left
      refine ⟨a - b, b * c, sub_nonneg.mpr hab, mul_nonneg hb hc.le, ?_⟩
      rw [← smul_smul, ← h]
      module
    · right
      refine ⟨a * c, b - a, mul_nonneg ha hc.le, sub_nonneg.mpr hab, ?_⟩
      rw [← smul_smul, ← h]
      module
  · rintro (⟨a, b, ha, hb, rfl⟩ | ⟨a, b, ha, hb, rfl⟩)
    · refine ⟨a + b * c⁻¹, b * c⁻¹, by positivity, by positivity, ?_⟩
      rw [hw]
      module
    · refine ⟨a * c⁻¹, a * c⁻¹ + b, by positivity, by positivity, ?_⟩
      rw [hw]
      module

/-- 直接軌道の頂点を実数の座標対として読む。 -/
noncomputable def orbitPair (n : ℕ) (j : Fin (4 * 2 ^ n)) : ℝ × ℝ :=
  ((directVertex n j).core, (directVertex n j).beam)

/-- 第 j 頂点とその巡回後継が張る非負錐。 -/
def DyadicCone (n : ℕ) (j : Fin (4 * 2 ^ n)) : Set (ℝ × ℝ) :=
  nonnegativeCone (orbitPair n j) (orbitPair n (directVertexNext n j))

/-- 二分核の正規化中点公式により、各錐は二つの子錐の和集合になる。 -/
theorem dyadicCone_refinement (n : ℕ) (j : Fin (4 * 2 ^ n)) :
    DyadicCone n j = DyadicCone (n + 1) (evenIndex n j) ∪ DyadicCone (n + 1) (oddIndex n j) := by
  unfold DyadicCone
  rw [directVertexNext_even, directVertexNext_odd]
  have he (k : Fin (4 * 2 ^ n)) : orbitPair (n + 1) (evenIndex n k) = orbitPair n k := by
    unfold orbitPair
    rw [directVertex_even]
  rw [he, he]
  apply nonnegativeCone_split (c := 2 * (sequence (n + 1)).core)
    (mul_pos (by norm_num) (core_succ_pos n))
  have h := directVertex_odd_scaled n j
  exact Prod.ext h.1.symm h.2.symm

private theorem orbitPair_zero (j : Fin 4) :
    orbitPair 0 j = ![(1, 0), (0, 1), (-1, 0), (0, -1)] j := by
  fin_cases j <;>
    norm_num [orbitPair, directVertex_eq_rawVertex, rawVertex, sequence, initial,
      pow_succ, UnitKernel.mul_eq_star, UnitKernel.star, UnitKernel.one, Vec.star, Vec.one]
  exact ⟨rfl, rfl⟩

private theorem dyadicCones_cover_zero (x : ℝ × ℝ) : ∃ j, x ∈ DyadicCone 0 j := by
  rcases x with ⟨x, y⟩
  rcases le_total 0 x with hx | hx <;> rcases le_total 0 y with hy | hy
  · refine ⟨0, x, y, hx, hy, ?_⟩
    change (x, y) = x • orbitPair 0 0 + y • orbitPair 0 1
    simp [orbitPair_zero]
  · refine ⟨3, -y, x, neg_nonneg.mpr hy, hx, ?_⟩
    change (x, y) = -y • orbitPair 0 3 + x • orbitPair 0 0
    simp [orbitPair_zero]
  · refine ⟨1, y, -x, hy, neg_nonneg.mpr hx, ?_⟩
    change (x, y) = y • orbitPair 0 1 + -x • orbitPair 0 2
    simp [orbitPair_zero]
  · refine ⟨2, -x, -y, neg_nonneg.mpr hx, neg_nonneg.mpr hy, ?_⟩
    change (x, y) = -x • orbitPair 0 2 + -y • orbitPair 0 3
    simp [orbitPair_zero]

/-- 各段階の巡回軌道の非負錐は平面全体を覆う。
初期段階は四象限であり、二分のたびに各錐を二つの子錐で置き換える。 -/
theorem dyadicCones_cover_plane (n : ℕ) : (⋃ j, DyadicCone n j) = Set.univ := by
  apply Set.eq_univ_of_forall
  intro x
  induction n with
  | zero => exact Set.mem_iUnion.mpr (dyadicCones_cover_zero x)
  | succ n ih =>
    obtain ⟨j, hj⟩ := Set.mem_iUnion.mp ih
    rw [dyadicCone_refinement] at hj
    rcases hj with h | h
    · exact Set.mem_iUnion.mpr ⟨evenIndex n j, h⟩
    · exact Set.mem_iUnion.mpr ⟨oddIndex n j, h⟩

end QuadrantUnitKernel
end DkMath.CosmicFormula.Rotation.CF2D
