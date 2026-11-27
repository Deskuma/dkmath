/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import Mathlib.Analysis.Convex.Topology
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Tactic

#print "file: DkMath.CosmicFormula.Rotation.CF2D.TriangleMeasure"

/-! # 標準三角形と行列式による平面三角形の測度 -/

namespace DkMath.CosmicFormula.Rotation.CF2D
open MeasureTheory

/-- 座標平面の原点と二つの標準基底からなる三角形。 -/
noncomputable def standardTriangle : Set (Fin 2 → ℝ) :=
  convexHull ℝ {0, Pi.single 0 1, Pi.single 1 1}

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


/-- 三角形の測度は、一頂点 p から伸びる二辺 w − p と q − p の行列式の絶対値の半分である。標準三角形を二辺を列に持つ行列で移し、さらに p だけ平行移動する。測度の倍率は行列式の絶対値で、平行移動は測度を保つ。頂点が共線の場合も含む。 -/
theorem euclideanTriangle_volume_eq_abs_det (p w q : (EuclideanSpace ℝ (Fin 2))) :
    volume (convexHull ℝ {p, w, q}) =
      ENNReal.ofReal (|((w - p) 0 * (q - p) 1 - (w - p) 1 * (q - p) 0)| / 2) := by
  let M : Matrix (Fin 2) (Fin 2) ℝ :=
    !![(w - p) 0, (q - p) 0; (w - p) 1, (q - p) 1]
  let f := Matrix.toLin' M
  let a := WithLp.ofLp p
  let g : (Fin 2 → ℝ) →ᵃ[ℝ] (Fin 2 → ℝ) :=
    AffineMap.mk' (fun x => f x + a) f 0 (by simp)
  let L := (WithLp.linearEquiv 2 ℝ (Fin 2 → ℝ)).toLinearMap
  have hf0 : g 0 = a := by change f 0 + a = a; simp
  have hf1 : g (Pi.single 0 1) = WithLp.ofLp w := by
    funext i
    fin_cases i <;> change (Matrix.mulVec M (Pi.single 0 1) + a) _ = _ <;>
      simp [M, a]
  have hf2 : g (Pi.single 1 1) = WithLp.ofLp q := by
    funext i
    fin_cases i <;> change (Matrix.mulVec M (Pi.single 1 1) + a) _ = _ <;>
      simp [M, a]
  have hi : g '' standardTriangle = convexHull ℝ {a, WithLp.ofLp w, WithLp.ofLp q} := by
    rw [standardTriangle, AffineMap.image_convexHull]
    simp [hf0, hf1, hf2]
  have hpre : (WithLp.ofLp : (EuclideanSpace ℝ (Fin 2)) → (Fin 2 → ℝ)) ⁻¹' (g '' standardTriangle) =
      convexHull ℝ {p, w, q} := by
    have he : L '' convexHull ℝ {p, w, q} = g '' standardTriangle := by
      rw [L.image_convexHull, hi]
      simp [L, a]
    rw [← he]
    exact Set.preimage_image_eq _ (WithLp.linearEquiv 2 ℝ (Fin 2 → ℝ)).injective
  have hc : IsCompact (f '' standardTriangle) :=
    ((Set.toFinite _).isCompact_convexHull ℝ).image
      (LinearMap.continuous_of_finiteDimensional f)
  have htrans : (fun x : Fin 2 → ℝ => x - a) ⁻¹' (f '' standardTriangle) =
      g '' standardTriangle := by
    ext y
    constructor
    · rintro ⟨x, hx, he⟩
      exact ⟨x, hx, eq_sub_iff_add_eq.mp he⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x, hx, by change f x = f x + a - a; simp⟩
  have hm := (PiLp.volume_preserving_ofLp (Fin 2)).measure_preimage
    (s := g '' standardTriangle) (by rw [hi]; exact ((Set.toFinite _).isCompact_convexHull ℝ).isClosed.measurableSet.nullMeasurableSet)
  rw [hpre] at hm
  rw [hm, ← htrans]
  -- 平行移動は測度を保ち、線形部分の測度倍率は行列式の絶対値である。
  have ht' : volume ((fun x : Fin 2 → ℝ => x - a) ⁻¹' (f '' standardTriangle)) =
      volume (f '' standardTriangle) :=
    by
      have h := (volume.measurePreserving_sub_left (-a)).comp
        (volume.measurePreserving_sub_left (0 : Fin 2 → ℝ))
      have he : (fun x : Fin 2 → ℝ => -a - (0 - x)) = fun x => x - a := by
        funext x
        abel
      change MeasurePreserving (fun x : Fin 2 → ℝ => -a - (0 - x)) volume volume at h
      rw [he] at h
      exact h.measure_preimage hc.isClosed.measurableSet.nullMeasurableSet
  rw [ht', Measure.addHaar_image_linearMap, standardTriangle_volume]
  have hd : LinearMap.det f = ((w - p) 0 * (q - p) 1 - (w - p) 1 * (q - p) 0) := by
    rw [← LinearMap.det_toMatrix (Pi.basisFun ℝ (Fin 2))]
    simp [f, M, Matrix.det_fin_two, mul_comm]
  rw [hd, ← ENNReal.ofReal_mul (abs_nonneg _)]
  congr 1
  ring

end DkMath.CosmicFormula.Rotation.CF2D
