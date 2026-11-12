/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.CosmicFormula.Rotation.CF2D.IntrinsicPolygonAdjacent

#print "file: DkMath.CosmicFormula.Rotation.CF2D.IntrinsicPolygonFan"

/-!
# 原点ファンの集合と測度

原点ファンを有限個の三角形の和集合として定義する。この集合は可測で多角形の
凸包に含まれ、その測度は各三角形の測度の和 `A_n` 以下である。
全ての相異なる三角形が測度の意味で交わらないという仮定の下では、
ファンの測度が `A_n` に等しい。凸包がファンに含まれることと、一般の
三角形対の測度零の重なりは別途証明する必要がある。
-/
namespace DkMath.CosmicFormula.Rotation.CF2D
open QuadrantUnitKernel MeasureTheory
/-- 全ての原点三角形の和集合。 -/
noncomputable def intrinsicOriginFan (n : ℕ) : Set EuclideanPlane := ⋃ j, intrinsicOriginTriangle n j

/-- 原点ファンは多角形領域に含まれる。 -/
theorem intrinsicOriginFan_subset_region (n : ℕ) : intrinsicOriginFan n ⊆ intrinsicPolygonRegion n := by
  intro x hx
  obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hx
  exact intrinsicOriginTriangle_subset_region_unconditional n j hj

/-- 有限の可測な三角形の和集合なのでファンは可測である。 -/
theorem intrinsicOriginFan_measurable (n : ℕ) : MeasurableSet (intrinsicOriginFan n) := by
  exact MeasurableSet.iUnion (intrinsicOriginTriangle_measurable n)

/-- 個々の三角形の測度を全て足すと面積候補に等しい。 -/
theorem intrinsicOriginTriangle_sum_volume (n : ℕ) : (∑ j : Fin (dyadicSides n), volume (intrinsicOriginTriangle n j)) =
    ENNReal.ofReal (areaApprox n) := by
  simp_rw [intrinsicOriginTriangle_volume]
  rw [← ENNReal.ofReal_sum_of_nonneg (by
    intro i hi
    have h := (sequence n).beam_nonneg
    change 0 ≤ (sequence n).beam at h
    positivity)]
  congr 1
  change (∑ _j : Fin (dyadicSides n), (sequence n).beam / 2) = areaApprox n
  rw [Finset.sum_const, Finset.card_fin]
  simp [areaApprox, dyadicSides, pow_succ]
  ring

/-- 測度の劣加法性により、ファンの測度は面積候補以下である。 -/
theorem intrinsicOriginFan_volume_le_areaApprox (n : ℕ) : volume (intrinsicOriginFan n) ≤ ENNReal.ofReal (areaApprox n) := by
  calc
    _ ≤ ∑' j : Fin (dyadicSides n), volume (intrinsicOriginTriangle n j) := measure_iUnion_le _
    _ = _ := by rw [tsum_fintype]; exact intrinsicOriginTriangle_sum_volume n

/-- ファンの測度はそれを含む多角形領域の測度以下である。 -/
theorem intrinsicOriginFan_volume_le_region (n : ℕ) : volume (intrinsicOriginFan n) ≤ volume (intrinsicPolygonRegion n) :=
  measure_mono (intrinsicOriginFan_subset_region n)

/-- 全ての異なる三角形の重なりが測度零なら、ファンの測度は面積候補に等しい。 -/
theorem intrinsicOriginFan_volume_of_pairwise (n : ℕ)
    (hdisjoint : Pairwise (Function.onFun (AEDisjoint volume) (intrinsicOriginTriangle n))) :
    volume (intrinsicOriginFan n) = ENNReal.ofReal (areaApprox n) := by
  rw [intrinsicOriginFan, measure_iUnion₀ hdisjoint (fun j => (intrinsicOriginTriangle_measurable n j).nullMeasurableSet), tsum_fintype]
  exact intrinsicOriginTriangle_sum_volume n


/-- 向かい合う２枚の三角形を使った、多角形領域の測度の下界。 -/
theorem intrinsicPolygonRegion_volume_ge_beam (n : ℕ) (j : Fin (dyadicSides n)) :
    ENNReal.ofReal ((sequence n).beam) ≤ volume (intrinsicPolygonRegion n) := by
  have ha := intrinsicOriginTriangle_aedisjoint_opposite n j
  have hu : intrinsicOriginTriangle n j ∪ intrinsicOriginTriangle n (intrinsicOppositeIndex n j) ⊆
      intrinsicPolygonRegion n := Set.union_subset (intrinsicOriginTriangle_subset_region_unconditional n j)
        (intrinsicOriginTriangle_subset_region_unconditional n (intrinsicOppositeIndex n j))
  have hv := measure_mono (μ := volume) hu
  rw [measure_union₀ (intrinsicOriginTriangle_measurable n (intrinsicOppositeIndex n j)).nullMeasurableSet ha,
    intrinsicOriginTriangle_volume, intrinsicOriginTriangle_volume] at hv
  have hnon : 0 ≤ (sequence n).beam / 2 := by
    have h := (sequence n).beam_nonneg
    change 0 ≤ (sequence n).beam at h
    linarith
  rw [← ENNReal.ofReal_add hnon hnon] at hv
  have hsum : (sequence n).beam / 2 + (sequence n).beam / 2 = (sequence n).beam := by ring
  simpa only [hsum] using hv

/-- 各段階の凸包は正の測度を持つ。 -/
theorem intrinsicPolygonRegion_volume_pos (n : ℕ) :
    0 < volume (intrinsicPolygonRegion n) := by
  exact lt_of_lt_of_le (ENNReal.ofReal_pos.mpr (beam_pos n))
    (intrinsicPolygonRegion_volume_ge_beam n ⟨0, dyadicSides_pos n⟩)


/-- 正方形の原点ファンは測度 2 を持つ。凸包の被覆を仮定しない。 -/
theorem intrinsicOriginFan_zero_volume : volume (intrinsicOriginFan 0) = ENNReal.ofReal 2 := by
  rw [intrinsicOriginFan_volume_of_pairwise 0 intrinsicOriginTriangle_zero_pairwise_aedisjoint,
    areaApprox_zero]

/-- 正方形の凸包の測度は少なくとも 2 である。 -/
theorem intrinsicPolygonRegion_zero_volume_ge_two :
    ENNReal.ofReal 2 ≤ volume (intrinsicPolygonRegion 0) := by
  rw [← intrinsicOriginFan_zero_volume]
  exact intrinsicOriginFan_volume_le_region 0

end DkMath.CosmicFormula.Rotation.CF2D
