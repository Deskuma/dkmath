/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.CosmicFormula.Rotation.CF2D.IntrinsicOriginTriangleLinear

#print "file: DkMath.CosmicFormula.Rotation.CF2D.IntrinsicStandardTriangleMeasure"

/-!
# 標準三角形の面積

標準三角形を `x ≥ 0`、`y ≥ 0`、`x+y ≤ 1` で特徴付ける。単位正方形は
この三角形と中心反転像の和集合であり、両者の共通部分は測度零の対角線に含まれる。
反転は測度を保ち、正方形の測度は 1 なので、三角形の測度は `1/2` となる。
これを既存の線形像の測度公式と合わせ、原点ファンの各三角形の面積を求める。
-/
namespace DkMath.CosmicFormula.Rotation.CF2D

/-- 標準三角形の凸包定義と、座標の３つの不等式は同値である。 -/
theorem mem_standardTriangle_iff (x : Fin 2 → ℝ) : x ∈ standardTriangle ↔ 0 ≤ x 0 ∧ 0 ≤ x 1 ∧ x 0 + x 1 ≤ 1 := by
  constructor
  · intro hx
    have hc : Convex ℝ {x : Fin 2 → ℝ | 0 ≤ x 0 ∧ 0 ≤ x 1 ∧ x 0 + x 1 ≤ 1} := by
      intro x hx y hy a b ha hb hab
      simp only [Set.mem_ofPred_eq] at *
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      constructor
      · exact add_nonneg (mul_nonneg ha hx.1) (mul_nonneg hb hy.1)
      constructor
      · exact add_nonneg (mul_nonneg ha hx.2.1) (mul_nonneg hb hy.2.1)
      · nlinarith [mul_nonneg ha (sub_nonneg.mpr hx.2.2), mul_nonneg hb (sub_nonneg.mpr hy.2.2)]
    apply convexHull_min (t := {x : Fin 2 → ℝ | 0 ≤ x 0 ∧ 0 ≤ x 1 ∧ x 0 + x 1 ≤ 1}) _ hc hx
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl | rfl <;> norm_num [Pi.single_apply]
  · intro hx
    let v : Fin 3 → (Fin 2 → ℝ) := ![0, Pi.single 0 1, Pi.single 1 1]
    let w : Fin 3 → ℝ := ![1 - x 0 - x 1, x 0, x 1]
    have hv (i : Fin 3) : v i ∈ standardTriangle := by
      apply subset_convexHull ℝ _
      fin_cases i <;> simp [v]
    have hw (i : Fin 3) : 0 ≤ w i := by
      fin_cases i <;> simp [w] <;> linarith [hx.1, hx.2.1, hx.2.2]
    have hw1 : (∑ i, w i) = 1 := by simp [Fin.sum_univ_succ, w]
    have hsum := (convex_convexHull ℝ ({0, Pi.single 0 1, Pi.single 1 1} : Set (Fin 2 → ℝ))).sum_mem
      (t := Finset.univ) (w := w) (z := v) (by simp [hw]) (by simpa using hw1) (by intro i _; exact hv i)
    have heq : (∑ i, w i • v i) = x := by
      ext i
      fin_cases i <;> simp [Fin.sum_univ_succ, w, v]
    rw [heq] at hsum
    exact hsum

open MeasureTheory
private noncomputable def rflTriangle (x : Fin 2 → ℝ) : Fin 2 → ℝ := 1 - x
private noncomputable def upperTriangle : Set (Fin 2 → ℝ) := rflTriangle ⁻¹' standardTriangle
private noncomputable def unitSquare : Set (Fin 2 → ℝ) := Set.Icc 0 1

private theorem square_union : unitSquare = standardTriangle ∪ upperTriangle := by
  ext x
  simp only [unitSquare, Set.mem_Icc, Set.mem_union, upperTriangle, Set.mem_preimage, mem_standardTriangle_iff,
    rflTriangle, Pi.sub_apply, Pi.one_apply]
  constructor
  · intro h
    have hx0 := h.1 0
    have hx1 := h.1 1
    have hy0 := h.2 0
    have hy1 := h.2 1
    simp only [Pi.zero_apply, Pi.one_apply] at hx0 hx1 hy0 hy1
    by_cases hh : x 0 + x 1 ≤ 1
    · exact Or.inl ⟨hx0, hx1, hh⟩
    · exact Or.inr ⟨by linarith, by linarith, by linarith⟩
  · intro h
    rcases h with h | h
    · constructor <;> intro i <;> fin_cases i <;> simp_all <;> linarith
    · constructor <;> intro i <;> fin_cases i <;> simp_all <;> linarith

private theorem square_volume : volume unitSquare = 1 := by
  simp [unitSquare, Real.volume_Icc_pi]

private theorem upper_volume : volume upperTriangle = volume standardTriangle := by
  apply (volume.measurePreserving_sub_left (1 : Fin 2 → ℝ)).measure_preimage
  exact ((Set.toFinite _).isCompact_convexHull ℝ).isClosed.measurableSet.nullMeasurableSet


private noncomputable def diagonalAffine : AffineSubspace ℝ (Fin 2 → ℝ) :=
  AffineSubspace.mk' (Pi.single 0 1) ((LinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 0 + LinearMap.proj 1 : (Fin 2 → ℝ) →ₗ[ℝ] ℝ).ker)

private theorem diagonal_ne_top : diagonalAffine ≠ ⊤ := by
  intro h
  have hz : (0 : Fin 2 → ℝ) ∈ diagonalAffine := by
    rw [h]
    exact AffineSubspace.mem_top ℝ _ _
  simp [diagonalAffine, AffineSubspace.mem_mk', LinearMap.mem_ker] at hz

private theorem intersection_zero : volume (standardTriangle ∩ upperTriangle) = 0 := by
  have hdiag : diagonalAffine ≠ ⊤ := diagonal_ne_top
  apply measure_mono_null _ (Measure.addHaar_affineSubspace volume diagonalAffine hdiag)
  intro x hx
  have hl := (mem_standardTriangle_iff x).1 hx.1
  have hu := (mem_standardTriangle_iff (rflTriangle x)).1 hx.2
  have he : x 0 + x 1 = 1 := by simp [rflTriangle] at hu; linarith [hl.2.2, hu.2.2]
  simp [diagonalAffine, AffineSubspace.mem_mk', LinearMap.mem_ker]
  linarith


/-- 単位正方形の反転対称性から得られる標準三角形の測度。 -/
theorem standardTriangle_volume : volume standardTriangle = ENNReal.ofReal (1 / 2) := by
  have hm : MeasurableSet upperTriangle := by
    exact (measurable_const.sub measurable_id) ((Set.toFinite _).isCompact_convexHull ℝ).measurableSet
  have hsub : standardTriangle ⊆ unitSquare := by rw [square_union]; exact Set.subset_union_left
  have hfinite : volume standardTriangle ≠ ⊤ := by
    apply ne_of_lt
    calc
      volume standardTriangle ≤ volume unitSquare := measure_mono hsub
      _ = 1 := square_volume
      _ < ⊤ := ENNReal.one_lt_top
  have hu := measure_union_add_inter (μ := volume) standardTriangle hm
  rw [← square_union, intersection_zero, add_zero, square_volume, upper_volume] at hu
  have hr := congrArg ENNReal.toReal hu
  rw [ENNReal.toReal_add hfinite hfinite] at hr
  have he : (volume standardTriangle).toReal = (1 / 2 : ℝ) := by norm_num at hr; linarith
  rw [← ENNReal.ofReal_toReal hfinite, he]


/-- 各原点三角形の測度は隣接する回転核の beam の半分である。 -/
theorem intrinsicOriginTriangle_volume (n : ℕ) (j : Fin (dyadicSides n)) :
    MeasureTheory.volume (intrinsicOriginTriangle n j) =
      ENNReal.ofReal ((QuadrantUnitKernel.sequence n).beam / 2) :=
  intrinsicOriginTriangle_volume_of_standard n j standardTriangle_volume

/-- 原点ファンの被覆と互いの重なりの測度零を仮定した、凸包の面積公式。 -/
theorem intrinsicPolygonRegion_volume_of_origin_fan_geometry (n : ℕ)
    (hcover : intrinsicPolygonRegion n = ⋃ j, intrinsicOriginTriangle n j)
    (hdisjoint : Pairwise (Function.onFun (MeasureTheory.AEDisjoint MeasureTheory.volume)
      (intrinsicOriginTriangle n))) :
    MeasureTheory.volume (intrinsicPolygonRegion n) = ENNReal.ofReal (areaApprox n) :=
  intrinsicPolygonRegion_volume_of_origin_fan n hcover hdisjoint (intrinsicOriginTriangle_volume n)

end DkMath.CosmicFormula.Rotation.CF2D
