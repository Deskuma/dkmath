/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.CosmicFormula.Rotation.CF2D.IntrinsicPolygonMeasure
import DkMath.CosmicFormula.Rotation.CF2D.IntrinsicBounds

#print "file: DkMath.CosmicFormula.Rotation.CF2D.IntrinsicPolygonCircumscribed"

/-!
# 原点を中心とする三角形と拡大領域

内接多角形の凸包を `c_(n + 1)⁻¹` 倍した集合を定義する。スカラー拡大による
測度の倍率は二次元で `c_(n + 1)⁻²` となる。また、原点と隣接頂点から作る
三角形を定義する。これらの定理は、原点ファンの被覆・重なりや、単位円盤が
拡大領域に含まれることを仮定せず、そうした未証明の包含も主張しない。
-/
namespace DkMath.CosmicFormula.Rotation.CF2D
open QuadrantUnitKernel Filter
open scoped Pointwise Topology InnerProductSpace


/-- 正多角形の半周先にある頂点の添字。 -/
def intrinsicHalfIndex (n : ℕ) : Fin (dyadicSides n) :=
  ⟨2 * 2 ^ n, by unfold dyadicSides; have := Nat.two_pow_pos n; omega⟩

/-- 半周先の頂点は `(-1,0)` である。 -/
theorem regularVertex_intrinsicHalfIndex (n : ℕ) : regularVertex (dyadicSides n) (intrinsicHalfIndex n) = ⟨-1, 0⟩ := by
  unfold regularVertex kernelOrbitVertex
  rw [UnitKernel.act_vecOne, regularKernel, ← normalizedRealKernelFamily.kernel_nsmul]
  change (realTrigKernelFamily.kernel (normalizedPhaseAngle ((intrinsicHalfIndex n).val • regularPhaseStep (dyadicSides n)))).val = _
  have h : normalizedPhaseAngle ((intrinsicHalfIndex n).val • regularPhaseStep (dyadicSides n)) = Real.pi := by
    simp only [intrinsicHalfIndex, nsmul_eq_mul, normalizedPhaseAngle, regularPhaseStep,
      DkMath.Analysis.DkNNRealQ.normalizedCycleStep, dyadicSides, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow]
    have hn : (2 : ℝ) ^ n ≠ 0 := pow_ne_zero _ (by norm_num)
    field_simp
    ring
  rw [h]
  simp [realTrigKernelFamily, Real.cos_pi, Real.sin_pi]

/-- 対向頂点の中点として原点は多角形の凸包に含まれる。 -/
theorem intrinsicPolygonRegion_origin_mem (n : ℕ) : (0 : EuclideanPlane) ∈ intrinsicPolygonRegion n := by
  let first : Fin (dyadicSides n) := ⟨0, dyadicSides_pos n⟩
  have hv0 : regularVertex (dyadicSides n) first = Vec.one ℝ := by
    simp [regularVertex, kernelOrbitVertex, first, UnitKernel.one]
  have he : (intrinsicRegularPolygon n).vertices (intrinsicHalfIndex n) =
      - (intrinsicRegularPolygon n).vertices first := by
    simp only [intrinsicRegularPolygon, euclideanRegularVertex, regularVertex_intrinsicHalfIndex, hv0]
    ext i
    fin_cases i <;> simp [pairToEuclideanPlane, Vec.toProd, Vec.one]
  have h0 : (intrinsicRegularPolygon n).vertices first ∈ intrinsicPolygonRegion n :=
    subset_convexHull ℝ _ ⟨first, rfl⟩
  have h1 : (intrinsicRegularPolygon n).vertices (intrinsicHalfIndex n) ∈ intrinsicPolygonRegion n :=
    subset_convexHull ℝ _ ⟨intrinsicHalfIndex n, rfl⟩
  have hm := (convex_convexHull ℝ (Set.range (intrinsicRegularPolygon n).vertices)).midpoint_mem h0 h1
  rw [he, midpoint_eq_smul_add, add_neg_cancel, smul_zero] at hm
  exact hm

/-- 原点と隣接する二つの頂点の凸包。 -/
noncomputable def intrinsicOriginTriangle (n : ℕ) (j : Fin (dyadicSides n)) : Set EuclideanPlane :=
  convexHull ℝ {0, (intrinsicRegularPolygon n).vertices j,
    (intrinsicRegularPolygon n).vertices (regularVertexNext (dyadicSides_pos n) j)}

/-- 原点を共通頂点とする各三角形はコンパクトである。 -/
theorem intrinsicOriginTriangle_compact (n : ℕ) (j : Fin (dyadicSides n)) :
    IsCompact (intrinsicOriginTriangle n j) := by
  exact (Set.toFinite _).isCompact_convexHull ℝ


/-- 隣接頂点の外積は正であり、原点ファンの向きは一貫している。 -/
theorem intrinsicOriginTriangle_vertexCross_pos (n : ℕ) (j : Fin (dyadicSides n)) :
    0 < vertexCross ((intrinsicRegularPolygon n).vertices j)
      ((intrinsicRegularPolygon n).vertices (regularVertexNext (dyadicSides_pos n) j)) := by
  rw [intrinsicPolygon_vertexCross]
  exact beam_pos n

/-- 原点ファンの各三角形は測度に関して可測である。 -/
theorem intrinsicOriginTriangle_measurable (n : ℕ) (j : Fin (dyadicSides n)) :
    MeasurableSet (intrinsicOriginTriangle n j) :=
  (intrinsicOriginTriangle_compact n j).isClosed.measurableSet

/-- 原点が多角形領域に属するとき、原点ファンの三角形も領域に含まれる。 -/
theorem intrinsicOriginTriangle_subset_region (n : ℕ) (j : Fin (dyadicSides n))
    (hzero : (0 : EuclideanPlane) ∈ intrinsicPolygonRegion n) :
    intrinsicOriginTriangle n j ⊆ intrinsicPolygonRegion n := by
  unfold intrinsicOriginTriangle
  apply convexHull_min _ (convex_convexHull ℝ _)
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl
  · exact hzero
  · exact subset_convexHull ℝ _ ⟨_, rfl⟩
  · exact subset_convexHull ℝ _ ⟨_, rfl⟩



/-- 原点ファンの三角形は追加の仮定なしに多角形領域に含まれる。 -/
theorem intrinsicOriginTriangle_subset_region_unconditional (n : ℕ) (j : Fin (dyadicSides n)) :
    intrinsicOriginTriangle n j ⊆ intrinsicPolygonRegion n :=
  intrinsicOriginTriangle_subset_region n j (intrinsicPolygonRegion_origin_mem n)

/--
原点ファンの測度を加算するための条件付き組立て。

被覆、異なる三角形の測度零の重なり、および各三角形の面積公式は
明示的な仮定であり、この定理自体はそれらを証明しない。
-/
theorem intrinsicPolygonRegion_volume_of_origin_fan (n : ℕ)
    (hcover : intrinsicPolygonRegion n = ⋃ j, intrinsicOriginTriangle n j)
    (hdisjoint : Pairwise (Function.onFun (MeasureTheory.AEDisjoint MeasureTheory.volume)
      (intrinsicOriginTriangle n)))
    (htriangle : ∀ j : Fin (dyadicSides n),
      MeasureTheory.volume (intrinsicOriginTriangle n j) =
        ENNReal.ofReal ((sequence n).beam / 2)) :
    MeasureTheory.volume (intrinsicPolygonRegion n) = ENNReal.ofReal (areaApprox n) := by
  rw [hcover, MeasureTheory.measure_iUnion₀ hdisjoint (fun j =>
    (intrinsicOriginTriangle_measurable n j).nullMeasurableSet), tsum_fintype]
  simp_rw [htriangle]
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


/-- 各辺の中点から原点までの距離は `c_(n + 1)` に等しい。

隣接頂点の二乗和と核の保存量を使った局所的な距離公式であり、
この定理だけでは閉円盤の凸包への包含は意味しない。 -/
theorem intrinsicPolygon_edge_midpoint_norm (n : ℕ) (j : Fin (dyadicSides n)) :
    ‖midpoint ℝ ((intrinsicRegularPolygon n).vertices j)
      ((intrinsicRegularPolygon n).vertices (regularVertexNext (dyadicSides_pos n) j))‖ =
      (sequence (n + 1)).core := by
  have hv := regularVertex_next (dyadicSides_pos n) j
  rw [regularKernel_dyadic n] at hv
  have hq := regularVertex_q2 (dyadicSides n) j
  simp only [Vec.q2] at hq
  have hk := (sequence n).norm
  have hsq := core_succ_sq n
  have hp : 0 ≤ (sequence (n + 1)).core := le_of_lt (core_succ_pos n)
  apply (sq_eq_sq₀ (norm_nonneg _) hp).mp
  rw [midpoint_eq_smul_add, EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two]
  unfold intrinsicRegularPolygon euclideanRegularVertex
  dsimp only
  rw [hv]
  simp only [PiLp.smul_apply, PiLp.add_apply, smul_eq_mul, UnitKernel.act_core, UnitKernel.act_beam,
    Vec.toProd, pairToEuclideanPlane]
  rw [hsq]
  change (sequence n).kernel.val.core ^ 2 + (sequence n).kernel.val.beam ^ 2 = 1 at hk
  have hfact : (((regularVertex (dyadicSides n) j).core +
      ((sequence n).kernel.val.core * (regularVertex (dyadicSides n) j).core -
       (sequence n).kernel.val.beam * (regularVertex (dyadicSides n) j).beam)) / 2) ^ 2 +
      (((regularVertex (dyadicSides n) j).beam +
      ((sequence n).kernel.val.core * (regularVertex (dyadicSides n) j).beam +
       (sequence n).kernel.val.beam * (regularVertex (dyadicSides n) j).core)) / 2) ^ 2 =
      (((1 + (sequence n).kernel.val.core)^2 + (sequence n).kernel.val.beam^2) / 4) *
      ((regularVertex (dyadicSides n) j).core^2 + (regularVertex (dyadicSides n) j).beam^2) := by ring
  change _ = (1 + (sequence n).kernel.val.core) / 2
  simp only [invOf_eq_inv]
  change ((2 : ℝ)⁻¹ * ((regularVertex (dyadicSides n) j).core +
      ((sequence n).kernel.val.core * (regularVertex (dyadicSides n) j).core -
       (sequence n).kernel.val.beam * (regularVertex (dyadicSides n) j).beam))) ^ 2 +
      ((2 : ℝ)⁻¹ * ((regularVertex (dyadicSides n) j).beam +
      ((sequence n).kernel.val.core * (regularVertex (dyadicSides n) j).beam +
       (sequence n).kernel.val.beam * (regularVertex (dyadicSides n) j).core))) ^ 2 = _
  have hf : ((1 + (sequence n).kernel.val.core)^2 + (sequence n).kernel.val.beam^2) / 4 =
      (1 + (sequence n).kernel.val.core) / 2 := by nlinarith [hk]
  rw [hq, mul_one, hf] at hfact
  nlinarith [hfact]


/-- 隣接頂点の中点へ向かうベクトルは、その辺の方向と直交する。

両頂点が単位円上にあることから、内積を展開して平方ノルムの差を消す。
この局所的な直交性だけでは辺が凸包を支持することは主張しない。 -/
theorem intrinsicPolygon_edge_midpoint_orthogonal (n : ℕ) (j : Fin (dyadicSides n)) :
    ⟪midpoint ℝ ((intrinsicRegularPolygon n).vertices j)
      ((intrinsicRegularPolygon n).vertices (regularVertexNext (dyadicSides_pos n) j)),
      (intrinsicRegularPolygon n).vertices (regularVertexNext (dyadicSides_pos n) j) -
        (intrinsicRegularPolygon n).vertices j ⟫_ℝ = 0 := by
  have hp := norm_euclideanRegularVertex (dyadicSides n) j
  have hq := norm_euclideanRegularVertex (dyadicSides n) (regularVertexNext (dyadicSides_pos n) j)
  change ‖(intrinsicRegularPolygon n).vertices j‖ = 1 at hp
  change ‖(intrinsicRegularPolygon n).vertices (regularVertexNext (dyadicSides_pos n) j)‖ = 1 at hq
  rw [midpoint_eq_smul_add]
  simp only [real_inner_smul_left, inner_add_left, inner_sub_right, real_inner_self_eq_norm_sq, hp, hq]
  rw [real_inner_comm ((intrinsicRegularPolygon n).vertices j)
    ((intrinsicRegularPolygon n).vertices (regularVertexNext (dyadicSides_pos n) j))]
  ring

/-- 内接多角形の凸包を `c_(n + 1)⁻¹` 倍した外側の領域候補。 -/
noncomputable def intrinsicPolygonOuterRegion (n : ℕ) : Set EuclideanPlane :=
  ((sequence (n + 1)).core)⁻¹ • intrinsicPolygonRegion n


/--
半径 `c_(n + 1)` の閉円盤が内接領域に含まれれば、単位閉円盤は拡大領域に含まれる。
必要な内接円の包含は明示的な仮定である。
-/
theorem closedBall_subset_outerRegion_of_innerBall_subset (n : ℕ)
    (hin : Metric.closedBall (0 : EuclideanPlane) (sequence (n + 1)).core ⊆ intrinsicPolygonRegion n) :
    Metric.closedBall (0 : EuclideanPlane) 1 ⊆ intrinsicPolygonOuterRegion n := by
  intro x hx
  have hp := core_succ_pos n
  have hxnorm : ‖x‖ ≤ 1 := by simpa [Metric.mem_closedBall, dist_zero_right] using hx
  have hy : (sequence (n + 1)).core • x ∈ intrinsicPolygonRegion n := by
    apply hin
    rw [Metric.mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_pos hp]
    nlinarith
  unfold intrinsicPolygonOuterRegion
  apply Set.mem_smul_set.2
  refine ⟨(sequence (n + 1)).core • x, hy, ?_⟩
  rw [smul_smul, inv_mul_cancel₀ (ne_of_gt hp), one_smul]


/--
単位円盤が拡大領域に含まれることと、半径 `c_(n + 1)` の円盤が
元の多角形領域に含まれることは同値である。
-/
theorem closedBall_subset_outerRegion_iff_innerBall_subset (n : ℕ) :
    Metric.closedBall (0 : EuclideanPlane) 1 ⊆ intrinsicPolygonOuterRegion n ↔
      Metric.closedBall (0 : EuclideanPlane) (sequence (n + 1)).core ⊆ intrinsicPolygonRegion n := by
  constructor
  · intro hout y hy
    have hp := core_succ_pos n
    have hynorm : ‖y‖ ≤ (sequence (n + 1)).core := by
      simpa [Metric.mem_closedBall, dist_zero_right] using hy
    have hx : (sequence (n + 1)).core⁻¹ • y ∈ Metric.closedBall (0 : EuclideanPlane) 1 := by
      rw [Metric.mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs,
        abs_of_pos (inv_pos.mpr hp)]
      rw [← div_eq_inv_mul]
      exact (div_le_one hp).2 hynorm
    have hmem := hout hx
    unfold intrinsicPolygonOuterRegion at hmem
    obtain ⟨z, hz, heq⟩ := Set.mem_smul_set.1 hmem
    have heq' : z = y := by
      apply_fun (fun v : EuclideanPlane => (sequence (n + 1)).core • v) at heq
      simpa [smul_smul, mul_inv_cancel₀ (ne_of_gt hp)] using heq
    simpa [heq'] using hz
  · exact closedBall_subset_outerRegion_of_innerBall_subset n


/-- 半径 `c_(n + 1)` の円盤上の点は、各辺の中点が定める半平面に入る。

コーシー・シュワルツの不等式と中点のノルムの公式を使う。この主張は
それらの半平面の共通部分が多角形の凸包に含まれることとは独立である。 -/
theorem innerBall_mem_edge_halfspace (n : ℕ) (j : Fin (dyadicSides n)) (x : EuclideanPlane)
    (hx : x ∈ Metric.closedBall (0 : EuclideanPlane) (sequence (n + 1)).core) :
    ⟪midpoint ℝ ((intrinsicRegularPolygon n).vertices j)
      ((intrinsicRegularPolygon n).vertices (regularVertexNext (dyadicSides_pos n) j)), x⟫_ℝ ≤
      (sequence (n + 1)).core ^ 2 := by
  have hx' : ‖x‖ ≤ (sequence (n + 1)).core := by
    simpa [Metric.mem_closedBall, dist_zero_right] using hx
  have hp := core_succ_pos n
  have hh := real_inner_le_norm
    (midpoint ℝ ((intrinsicRegularPolygon n).vertices j)
      ((intrinsicRegularPolygon n).vertices (regularVertexNext (dyadicSides_pos n) j))) x
  rw [intrinsicPolygon_edge_midpoint_norm n j] at hh
  nlinarith

/-- 各辺の中点を法線とする内側の半平面の共通部分。 -/
def intrinsicEdgeHalfSpaces (n : ℕ) : Set EuclideanPlane :=
  {x | ∀ j : Fin (dyadicSides n),
    ⟪midpoint ℝ ((intrinsicRegularPolygon n).vertices j)
      ((intrinsicRegularPolygon n).vertices (regularVertexNext (dyadicSides_pos n) j)), x⟫_ℝ ≤
      (sequence (n + 1)).core ^ 2}

/-- 半径 `c_(n + 1)` の円盤は辺の半平面の共通部分に含まれる。 -/
theorem intrinsicInnerBall_subset_edgeHalfSpaces (n : ℕ) :
    Metric.closedBall (0 : EuclideanPlane) (sequence (n + 1)).core ⊆ intrinsicEdgeHalfSpaces n := by
  intro x hx j
  exact innerBall_mem_edge_halfspace n j x hx

/-- 辺の半平面の共通部分が凸包に含まれれば、必要な内接円盤の包含が従う。 -/
theorem intrinsicPolygonRegion_innerBall_subset_of_halfSpaces (n : ℕ)
    (h : intrinsicEdgeHalfSpaces n ⊆ intrinsicPolygonRegion n) :
    Metric.closedBall (0 : EuclideanPlane) (sequence (n + 1)).core ⊆ intrinsicPolygonRegion n :=
  (intrinsicInnerBall_subset_edgeHalfSpaces n).trans h

/-- 拡大領域もコンパクトかつ可測である。 -/
theorem intrinsicPolygonOuterRegion_compact (n : ℕ) :
    IsCompact (intrinsicPolygonOuterRegion n) := by
  change IsCompact ((fun x : EuclideanPlane => (sequence (n + 1)).core⁻¹ • x) '' intrinsicPolygonRegion n)
  exact (intrinsicPolygonRegion_compact n).image (continuous_id.const_smul ((sequence (n + 1)).core⁻¹))

/-- 平面の測度は拡大倍率の二乗で変化する。 -/
theorem intrinsicPolygonOuterRegion_volume (n : ℕ) :
    MeasureTheory.volume (intrinsicPolygonOuterRegion n) =
      ENNReal.ofReal (((sequence (n + 1)).core)⁻¹ ^ 2) *
        MeasureTheory.volume (intrinsicPolygonRegion n) := by
  unfold intrinsicPolygonOuterRegion
  rw [MeasureTheory.Measure.addHaar_smul]
  simp only [finrank_euclideanSpace_fin, abs_of_nonneg (sq_nonneg ((sequence (n + 1)).core⁻¹))]


/--
内接領域の測度が `A_n` であることを仮定すると、拡大領域の測度は `U_n` になる。
測度の同一性は仮定であり、領域の被覆や三角形の測度はこの定理では導いていない。
-/
theorem intrinsicPolygonOuterRegion_volume_of_region (n : ℕ)
    (harea : MeasureTheory.volume (intrinsicPolygonRegion n) = ENNReal.ofReal (areaApprox n)) :
    MeasureTheory.volume (intrinsicPolygonOuterRegion n) = ENNReal.ofReal (outerApprox n) := by
  rw [intrinsicPolygonOuterRegion_volume, harea, ← ENNReal.ofReal_mul (sq_nonneg _)]
  congr 1
  rw [outerApprox_eq_areaApprox_div_core_sq]
  ring


/--
内接領域の面積公式と単位円盤の外側領域への包含を仮定した、測度による挟み込み。

両仮定を各段階で証明できれば、円盤の実数値測度が内在的定数に一致する。
この条件付き定理は既存の円周率との同一性を利用しない。
-/
theorem disk_measureReal_eq_intrinsicPi_of_polygon_sandwich
    (harea : ∀ n, MeasureTheory.volume (intrinsicPolygonRegion n) = ENNReal.ofReal (areaApprox n))
    (hcover : ∀ n, Metric.closedBall (0 : EuclideanPlane) 1 ⊆ intrinsicPolygonOuterRegion n) :
    MeasureTheory.volume.real (Metric.closedBall (0 : EuclideanPlane) 1) = intrinsicPi := by
  have hlower : ∀ n, areaApprox n ≤ MeasureTheory.volume.real (Metric.closedBall (0 : EuclideanPlane) 1) := by
    intro n
    have h := MeasureTheory.measureReal_mono (μ := MeasureTheory.volume)
      (intrinsicPolygonRegion_subset_closedBall n)
      ((isCompact_closedBall (0 : EuclideanPlane) 1).measure_lt_top.ne)
    rw [MeasureTheory.measureReal_def, harea n, ENNReal.toReal_ofReal (areaApprox_nonneg n)] at h
    exact h
  have hupper : ∀ n, MeasureTheory.volume.real (Metric.closedBall (0 : EuclideanPlane) 1) ≤ outerApprox n := by
    intro n
    have hfinite : MeasureTheory.volume (intrinsicPolygonOuterRegion n) ≠ ⊤ := by
      rw [intrinsicPolygonOuterRegion_volume_of_region n (harea n)]
      exact ENNReal.ofReal_ne_top
    have h := MeasureTheory.measureReal_mono (μ := MeasureTheory.volume) (hcover n) hfinite
    simp only [MeasureTheory.measureReal_def] at h
    rw [intrinsicPolygonOuterRegion_volume_of_region n (harea n), ENNReal.toReal_ofReal] at h
    · exact h
    · unfold outerApprox
      exact div_nonneg (areaApprox_nonneg (n + 1)) (le_of_lt (core_succ_pos n))
  apply le_antisymm
  · exact le_of_tendsto_of_tendsto' tendsto_const_nhds tendsto_outerApprox_intrinsicPi hupper
  · exact le_of_tendsto_of_tendsto' tendsto_areaApprox_intrinsicPi tendsto_const_nhds hlower

end DkMath.CosmicFormula.Rotation.CF2D
