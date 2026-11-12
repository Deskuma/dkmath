/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.CosmicFormula.Rotation.CF2D.IntrinsicPolygonAntipodal

#print "file: DkMath.CosmicFormula.Rotation.CF2D.IntrinsicPolygonAdjacent"

/-!
# 隣接する原点三角形の交わり

隣接する三角形の共通点を、共有頂点と原点を通る直線に含める。
標準三角形の座標は非負であり、両三角形から見た共有頂点との外積は
互いに反対の符号を持つので、共通点の非共有頂点方向の係数は零となる。
共有頂点の張る直線は平面の真部分空間であるため、交わりの測度は零である。
この結果だけでは非隣接の任意の三角形対についての測度零を主張しない。
-/
namespace DkMath.CosmicFormula.Rotation.CF2D
open QuadrantUnitKernel MeasureTheory

/-- 隣接する原点三角形の共通部分は二次元測度零である。 -/
theorem intrinsicOriginTriangle_aedisjoint_next (n : ℕ) (j : Fin (dyadicSides n)) :
    AEDisjoint volume (intrinsicOriginTriangle n j)
      (intrinsicOriginTriangle n (regularVertexNext (dyadicSides_pos n) j)) := by
  let k := regularVertexNext (dyadicSides_pos n) j
  let p := (intrinsicRegularPolygon n).vertices j
  let q := (intrinsicRegularPolygon n).vertices k
  let r := (intrinsicRegularPolygon n).vertices (regularVertexNext (dyadicSides_pos n) k)
  let S : Submodule ℝ EuclideanPlane := ℝ ∙ q
  have hcross1 : vertexCross p q = (sequence n).beam := intrinsicPolygon_vertexCross n j
  have hcross2 : vertexCross q r = (sequence n).beam := intrinsicPolygon_vertexCross n k
  have hb := beam_pos n
  have hproper : S ≠ ⊤ := by
    intro htop
    have hmem : p ∈ S := by rw [htop]; trivial
    obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.mp hmem
    rw [← ht] at hcross1
    simp only [vertexCross, PiLp.smul_apply, smul_eq_mul] at hcross1
    nlinarith
  apply measure_mono_null _ (Measure.addHaar_submodule volume S hproper)
  rintro x ⟨hx, hy⟩
  rw [← originTriangleLinearMap_image] at hx hy
  obtain ⟨a, ha, hax⟩ := hx
  obtain ⟨b, hb', hbx⟩ := hy
  have ha0 := ((mem_standardTriangle_iff a).1 ha).1
  have hb1 := ((mem_standardTriangle_iff b).1 hb').2.1
  have hcrossa : vertexCross q x = -(a 0) * (sequence n).beam := by
    rw [← hax]
    change vertexCross q (a 0 • p + a 1 • q) = _
    have h : vertexCross q (a 0 • p + a 1 • q) = -a 0 * vertexCross p q := by
      simp only [vertexCross, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
      ring
    rw [h, hcross1]
  have hcrossb : vertexCross q x = b 1 * (sequence n).beam := by
    rw [← hbx]
    change vertexCross q (b 0 • q + b 1 • r) = _
    have h : vertexCross q (b 0 • q + b 1 • r) = b 1 * vertexCross q r := by
      simp only [vertexCross, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
      ring
    rw [h, hcross2]
  have haeq : a 0 = 0 := by nlinarith [hcrossa, hcrossb]
  apply Submodule.mem_span_singleton.mpr
  refine ⟨a 1, ?_⟩
  rw [← hax]
  change a 1 • q = a 0 • p + a 1 • q
  simp [haeq]

/-- 正方形の４枚の原点三角形は、異なる添字同士で測度に関して互いに素である。

４頂点の場合、異なる二つの添字は隣接または対向する。この定理は一般の
辺数に対する三角形対の分離を主張しない。 -/
theorem intrinsicOriginTriangle_zero_pairwise_aedisjoint : Pairwise (Function.onFun (AEDisjoint volume) (intrinsicOriginTriangle 0)) := by
  let h0 := intrinsicOriginTriangle_aedisjoint_next 0 ⟨0, by norm_num [dyadicSides]⟩
  let h1 := intrinsicOriginTriangle_aedisjoint_next 0 ⟨1, by norm_num [dyadicSides]⟩
  let h2 := intrinsicOriginTriangle_aedisjoint_next 0 ⟨2, by norm_num [dyadicSides]⟩
  let h3 := intrinsicOriginTriangle_aedisjoint_next 0 ⟨3, by norm_num [dyadicSides]⟩
  let o0 := intrinsicOriginTriangle_aedisjoint_opposite 0 ⟨0, by norm_num [dyadicSides]⟩
  let o1 := intrinsicOriginTriangle_aedisjoint_opposite 0 ⟨1, by norm_num [dyadicSides]⟩
  simp only [regularVertexNext, intrinsicOppositeIndex, intrinsicHalfIndex, dyadicSides, pow_zero, mul_one,
    Nat.reduceAdd, Nat.reduceMod] at h0 h1 h2 h3 o0 o1
  intro i j hij
  change AEDisjoint volume (intrinsicOriginTriangle 0 i) (intrinsicOriginTriangle 0 j)
  change Fin 4 at i j
  fin_cases i <;> fin_cases j <;> dsimp only at *
  all_goals first | contradiction | exact h0 | exact h1 | exact h2 | exact h3 | exact o0 | exact o1 |
    exact h0.symm | exact h1.symm | exact h2.symm | exact h3.symm | exact o0.symm | exact o1.symm

end DkMath.CosmicFormula.Rotation.CF2D
