/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.CosmicFormula.Rotation.CF2D.DyadicPhase
import Mathlib.Topology.Algebra.Module.Basic

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

/-- 二つの子錐の共通部分は、中点を通る半直線である。
親錐の二方向が一次独立なら、中点を両方向の和で置き換えた後の係数は一意に決まる。
両側の非負係数を比較すると、共通方向以外の係数は零になる。 -/
theorem nonnegativeCone_children_inter {E : Type*} [AddCommGroup E] [Module ℝ E]
    {p w q : E} {c : ℝ} (hc : 0 < c) (h : p + q = c • w)
    (hind : LinearIndependent ℝ ![p, q]) :
    nonnegativeCone p w ∩ nonnegativeCone w q = {x | ∃ t : ℝ, 0 ≤ t ∧ x = t • w} := by
  have hw : w = c⁻¹ • (p + q) := by
    rw [h, smul_smul, inv_mul_cancel₀ hc.ne', one_smul]
  ext x
  constructor
  · rintro ⟨⟨a, b, ha, hb, he⟩, ⟨s, d, _, hd, hf⟩⟩
    have heq : (a + b * c⁻¹) • p + (b * c⁻¹) • q =
        (s * c⁻¹) • p + (s * c⁻¹ + d) • q := by
      have hh := he.symm.trans hf
      rw [hw] at hh
      simpa only [smul_add, smul_smul, add_smul, add_assoc] using hh
    have hz : (a + b * c⁻¹ - s * c⁻¹) • p +
        (b * c⁻¹ - (s * c⁻¹ + d)) • q = 0 := by
      calc
        _ = ((a + b * c⁻¹) • p + (b * c⁻¹) • q) -
            ((s * c⁻¹) • p + (s * c⁻¹ + d) • q) := by module
        _ = 0 := sub_eq_zero.mpr heq
    obtain ⟨h₁, h₂⟩ := LinearIndependent.pair_iff.mp hind _ _ hz
    have ha0 : a = 0 := by linarith
    exact ⟨b, hb, by simpa [ha0] using he⟩
  · rintro ⟨t, ht, rfl⟩
    exact ⟨⟨0, t, le_rfl, ht, by simp⟩, ⟨t, 0, ht, le_rfl, by simp⟩⟩

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

private theorem pair_independent_of_det {p q : ℝ × ℝ}
    (h : p.1 * q.2 - p.2 * q.1 ≠ 0) : LinearIndependent ℝ ![p, q] := by
  rw [LinearIndependent.pair_iff]
  intro a b he
  have h₁ : a * p.1 + b * q.1 = 0 := congrArg Prod.fst he
  have h₂ : a * p.2 + b * q.2 = 0 := congrArg Prod.snd he
  constructor
  · apply (mul_eq_zero.mp (show a * (p.1 * q.2 - p.2 * q.1) = 0 by
      linear_combination q.2 * h₁ - q.1 * h₂)).resolve_right h
  · apply (mul_eq_zero.mp (show b * (p.1 * q.2 - p.2 * q.1) = 0 by
      linear_combination p.1 * h₂ - p.2 * h₁)).resolve_right h

/-- 同じ親錐から生じる二つの錐は、新頂点の半直線を共有する。 -/
theorem dyadicCone_children_inter (n : ℕ) (j : Fin (4 * 2 ^ n)) :
    DyadicCone (n + 1) (evenIndex n j) ∩ DyadicCone (n + 1) (oddIndex n j) =
      {x | ∃ t : ℝ, 0 ≤ t ∧ x = t • orbitPair (n + 1) (oddIndex n j)} := by
  unfold DyadicCone
  rw [directVertexNext_even, directVertexNext_odd]
  have he (k : Fin (4 * 2 ^ n)) : orbitPair (n + 1) (evenIndex n k) = orbitPair n k := by
    unfold orbitPair
    rw [directVertex_even]
  rw [he, he]
  apply nonnegativeCone_children_inter (c := 2 * (sequence (n + 1)).core)
    (mul_pos (by norm_num) (core_succ_pos n))
  · have h := directVertex_odd_scaled n j
    exact Prod.ext h.1.symm h.2.symm
  · apply pair_independent_of_det
    change refinementCross (directVertex n j) (directVertex n (directVertexNext n j)) ≠ 0
    rw [refinement_old_cross]
    exact (beam_pos n).ne'

private theorem interior_empty_of_ker_subset {s : Set (ℝ × ℝ)}
    (f : (ℝ × ℝ) →ₗ[ℝ] ℝ) (hf : f ≠ 0) (hs : s ⊆ (f.ker : Set (ℝ × ℝ))) :
    interior s = ∅ := by
  apply Set.not_nonempty_iff_eq_empty.mp
  intro h
  have htop := f.ker.eq_top_of_nonempty_interior' (h.mono (interior_mono hs))
  exact hf (LinearMap.ker_eq_top.mp htop)

private theorem children_disjoint (n : ℕ) (j : Fin (4 * 2 ^ n)) :
    Disjoint (interior (DyadicCone (n + 1) (evenIndex n j)))
      (interior (DyadicCone (n + 1) (oddIndex n j))) := by
  rw [Set.disjoint_iff_inter_eq_empty, ← interior_inter, dyadicCone_children_inter]
  let w := orbitPair (n + 1) (oddIndex n j)
  let f : (ℝ × ℝ) →ₗ[ℝ] ℝ := w.2 • LinearMap.fst ℝ ℝ ℝ - w.1 • LinearMap.snd ℝ ℝ ℝ
  apply interior_empty_of_ker_subset f
  · intro h
    have hh := congrArg (fun g : (ℝ × ℝ) →ₗ[ℝ] ℝ => g (orbitPair n j)) h
    rw [LinearMap.zero_apply] at hh
    simp only [f, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.fst_apply, LinearMap.snd_apply, smul_eq_mul] at hh
    apply (refinement_vertex_cross_pos n j).1.ne'
    unfold refinementCross
    dsimp [w, orbitPair] at hh
    linarith
  · rintro x ⟨t, _, rfl⟩
    change w.2 * (t * w.1) - w.1 * (t * w.2) = 0
    ring

private theorem initial_disjoint :
    Pairwise (fun i j => Disjoint (interior (DyadicCone 0 i)) (interior (DyadicCone 0 j))) := by
  intro i j hij
  rw [Set.disjoint_iff_inter_eq_empty, ← interior_inter]
  have hfst : LinearMap.fst ℝ ℝ ℝ ≠ 0 := by
    intro h
    have e := congrArg (fun f : (ℝ × ℝ) →ₗ[ℝ] ℝ => f (1, 0)) h
    norm_num at e
  have hsnd : LinearMap.snd ℝ ℝ ℝ ≠ 0 := by
    intro h
    have e := congrArg (fun f : (ℝ × ℝ) →ₗ[ℝ] ℝ => f (0, 1)) h
    norm_num at e
  have hn (k : Fin 4) : directVertexNext 0 k = k + 1 := by
    fin_cases k <;> decide
  fin_cases i <;> fin_cases j
  all_goals
    first
    | contradiction
    | apply interior_empty_of_ker_subset _ hfst
      rintro x ⟨⟨a, b, ha, hb, he⟩, ⟨c, d, hc, hd, hf⟩⟩
      have h₁ := congrArg Prod.fst he
      have h₂ := congrArg Prod.fst hf
      norm_num [hn, orbitPair_zero, Fin.add_def] at h₁ h₂
      change x.1 = 0
      linarith
    | apply interior_empty_of_ker_subset _ hsnd
      rintro x ⟨⟨a, b, ha, hb, he⟩, ⟨c, d, hc, hd, hf⟩⟩
      have h₁ := congrArg Prod.snd he
      have h₂ := congrArg Prod.snd hf
      norm_num [hn, orbitPair_zero, Fin.add_def] at h₁ h₂
      change x.2 = 0
      linarith

/-- 全段階で、異なる錐の内部は互いに交わらない。
異なる親から来る子錐は親錐の内部非交差を継承し、同じ親の子錐は共通半直線だけで接する。 -/
theorem dyadicCones_pairwise_interior_disjoint (n : ℕ) :
    Pairwise (fun i j => Disjoint (interior (DyadicCone n i)) (interior (DyadicCone n j))) := by
  induction n with
  | zero => exact initial_disjoint
  | succ n ih =>
    intro i j hij
    obtain ⟨u, hu⟩ | ⟨u, hu⟩ := refinement_index_even_or_odd n i <;>
      obtain ⟨v, hv⟩ | ⟨v, hv⟩ := refinement_index_even_or_odd n j <;>
      subst i <;> subst j
    · exact (ih (fun h => hij (congrArg (evenIndex n) h))).mono
        (interior_mono (by rw [dyadicCone_refinement n u]; exact Set.subset_union_left))
        (interior_mono (by rw [dyadicCone_refinement n v]; exact Set.subset_union_left))
    · by_cases h : u = v
      · subst v
        exact children_disjoint n u
      · exact (ih h).mono
          (interior_mono (by rw [dyadicCone_refinement n u]; exact Set.subset_union_left))
          (interior_mono (by rw [dyadicCone_refinement n v]; exact Set.subset_union_right))
    · by_cases h : u = v
      · subst v
        exact (children_disjoint n u).symm
      · exact (ih h).mono
          (interior_mono (by rw [dyadicCone_refinement n u]; exact Set.subset_union_right))
          (interior_mono (by rw [dyadicCone_refinement n v]; exact Set.subset_union_left))
    · exact (ih (fun h => hij (congrArg (oddIndex n) h))).mono
        (interior_mono (by rw [dyadicCone_refinement n u]; exact Set.subset_union_right))
        (interior_mono (by rw [dyadicCone_refinement n v]; exact Set.subset_union_right))

/-- 巡回添字で並べた錐は平面を覆い、内部は互いに交わらず、
次の錐とは後継頂点の半直線を共有する。末尾から先頭への接続も含む。 -/
theorem dyadicCones_cyclic_order (n : ℕ) :
    (⋃ j, DyadicCone n j) = Set.univ ∧
    Pairwise (fun i j => Disjoint (interior (DyadicCone n i)) (interior (DyadicCone n j))) ∧
    ∀ j, {x | ∃ t : ℝ, 0 ≤ t ∧ x = t • orbitPair n (directVertexNext n j)} ⊆
      DyadicCone n j ∩ DyadicCone n (directVertexNext n j) := by
  refine ⟨dyadicCones_cover_plane n, dyadicCones_pairwise_interior_disjoint n, ?_⟩
  rintro j x ⟨t, ht, rfl⟩
  exact ⟨⟨0, t, le_rfl, ht, by simp⟩, ⟨t, 0, ht, le_rfl, by simp⟩⟩

end QuadrantUnitKernel
end DkMath.CosmicFormula.Rotation.CF2D
