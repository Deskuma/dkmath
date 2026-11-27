/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.CosmicFormula.Rotation.CF2D.HalfKernelRefinement
import DkMath.CosmicFormula.Rotation.CF2D.IntrinsicBounds

#print "file: DkMath.CosmicFormula.Rotation.CF2D.HalfKernelRefinementGeometry"

/-!
# 二分化で生じる頂点の局所配置

座標の内積と外積を使い、旧辺の中点に垂直な直線に対して新頂点が
原点と反対側へ厳密に移ること、および二つの新しい隣接対の向きを示す。
このファイルでは円周率や三角関数を使用しない。旧辺の大域的な支持性は仮定しない。
-/
namespace DkMath.CosmicFormula.Rotation.CF2D
namespace QuadrantUnitKernel

/-- ２座標の標準的な内積。 -/
def refinementDot (p q : Vec ℝ) : ℝ := p.core * q.core + p.beam * q.beam
/-- ２座標の向き付き外積。 -/
def refinementCross (p q : Vec ℝ) : ℝ := p.core * q.beam - p.beam * q.core

/-- 保存量 `q2 = 1` と核の作用から、旧隣接頂点の外積は beam に等しい。 -/
theorem refinement_old_cross (n : ℕ) (j : Fin (4 * 2 ^ n)) :
 refinementCross (directVertex n j) (directVertex n (directVertexNext n j)) = (sequence n).beam := by
  have hq := directVertex_q2 n j
  change (directVertex n j).core ^ 2 + (directVertex n j).beam ^ 2 = 1 at hq
  rw [directVertex_next]
  simp only [refinementCross, UnitKernel.act, Vec.star]
  change (directVertex n j).core * ((sequence n).core * (directVertex n j).beam + (sequence n).beam * (directVertex n j).core) - (directVertex n j).beam * ((sequence n).core * (directVertex n j).core - (sequence n).beam * (directVertex n j).beam) = _
  calc
    _ = (sequence n).beam * ((directVertex n j).core ^ 2 + (directVertex n j).beam ^ 2) := by ring
    _ = _ := by rw [hq]; ring

/-- 新しい二つの隣接対の外積は共に `s_n / (2 c_(n+1))`。 -/
theorem refinement_vertex_cross (n : ℕ) (j : Fin (4 * 2 ^ n)) :
 refinementCross (directVertex n j) (directVertex (n+1) (oddIndex n j)) = (sequence n).beam / (2 * (sequence (n+1)).core) ∧
 refinementCross (directVertex (n+1) (oddIndex n j)) (directVertex n (directVertexNext n j)) = (sequence n).beam / (2 * (sequence (n+1)).core) := by
  have hp : 0 < 2 * (sequence (n+1)).core := by have := core_succ_pos n; positivity
  have h := directVertex_odd_scaled n j
  have hc := refinement_old_cross n j
  have h1 := congrArg (fun x : ℝ => (directVertex n j).core * x) h.2
  have h2 := congrArg (fun x : ℝ => (directVertex n j).beam * x) h.1
  have h3 := congrArg (fun x : ℝ => (directVertex n (directVertexNext n j)).beam * x) h.1
  have h4 := congrArg (fun x : ℝ => (directVertex n (directVertexNext n j)).core * x) h.2
  constructor <;> apply (eq_div_iff (ne_of_gt hp)).2 <;> unfold refinementCross at * <;> nlinarith

/-- ２頂点の座標ごとの中点。 -/
noncomputable def refinementMidpoint (p q : Vec ℝ) : Vec ℝ := ⟨(p.core + q.core) / 2, (p.beam + q.beam) / 2⟩

/-- 旧隣接頂点の内積は回転核の core に等しい。 -/
theorem refinement_old_dot (n : ℕ) (j : Fin (4 * 2 ^ n)) :
 refinementDot (directVertex n j) (directVertex n (directVertexNext n j)) = (sequence n).core := by
  have hq := directVertex_q2 n j
  change (directVertex n j).core ^ 2 + (directVertex n j).beam ^ 2 = 1 at hq
  rw [directVertex_next]
  simp only [refinementDot, UnitKernel.act, Vec.star]
  change (directVertex n j).core * ((sequence n).core * (directVertex n j).core - (sequence n).beam * (directVertex n j).beam) + (directVertex n j).beam * ((sequence n).core * (directVertex n j).beam + (sequence n).beam * (directVertex n j).core) = _
  calc
    _ = (sequence n).core * ((directVertex n j).core ^ 2 + (directVertex n j).beam ^ 2) := by ring
    _ = _ := by rw [hq]; ring

/-- 旧辺中点との内積を計算する。両端では `c²`、新頂点では `c` になる。 -/
theorem refinement_midpoint_dot (n : ℕ) (j : Fin (4 * 2 ^ n)) :
 let p := directVertex n j
 let q := directVertex n (directVertexNext n j)
 let w := directVertex (n+1) (oddIndex n j)
 refinementDot (refinementMidpoint p q) p = (sequence (n+1)).core ^ 2 ∧
 refinementDot (refinementMidpoint p q) q = (sequence (n+1)).core ^ 2 ∧
 refinementDot (refinementMidpoint p q) w = (sequence (n+1)).core := by
  dsimp only
  have hp := directVertex_q2 n j
  have hq := directVertex_q2 n (directVertexNext n j)
  have hw := directVertex_q2 (n+1) (oddIndex n j)
  change (directVertex n j).core ^ 2 + (directVertex n j).beam ^ 2 = 1 at hp
  change (directVertex n (directVertexNext n j)).core ^ 2 + (directVertex n (directVertexNext n j)).beam ^ 2 = 1 at hq
  change (directVertex (n+1) (oddIndex n j)).core ^ 2 + (directVertex (n+1) (oddIndex n j)).beam ^ 2 = 1 at hw
  have hd := refinement_old_dot n j
  have hh := refinement_core n
  have hs := directVertex_odd_scaled n j
  have h1 := congrArg (fun x : ℝ => (directVertex (n+1) (oddIndex n j)).core * x) hs.1
  have h2 := congrArg (fun x : ℝ => (directVertex (n+1) (oddIndex n j)).beam * x) hs.2
  have hwc := congrArg (fun x : ℝ => (sequence (n+1)).core * x) hw
  simp only [refinementDot, refinementMidpoint] at *
  constructor
  · nlinarith
  constructor
  · nlinarith
  · nlinarith [mul_comm (sequence (n+1)).core ((directVertex (n+1) (oddIndex n j)).core ^ 2 + (directVertex (n+1) (oddIndex n j)).beam ^ 2)]

/-- 新頂点は旧辺を含む直線に対して原点と反対側にある。ここでは旧辺が凸包の支持線であるとは主張しない。 -/
theorem refinement_vertex_strictly_outside_old_edge_line (n : ℕ) (j : Fin (4 * 2 ^ n)) :
 let p := directVertex n j
 let q := directVertex n (directVertexNext n j)
 let w := directVertex (n+1) (oddIndex n j)
 refinementDot (refinementMidpoint p q) p = refinementDot (refinementMidpoint p q) q ∧
 refinementDot (refinementMidpoint p q) p < refinementDot (refinementMidpoint p q) w ∧
 0 < refinementDot (refinementMidpoint p q) w := by
  dsimp only
  have h := refinement_midpoint_dot n j
  dsimp only at h
  have hp := core_succ_pos n
  have hl := core_lt_one (n+1)
  constructor
  · linarith [h.1, h.2.1]
  constructor
  · nlinarith [h.1, h.2.2]
  · linarith [h.2.2]

/-- beam と半角 core の正性から、新しい二つの隣接対は正の向きを持つ。 -/
theorem refinement_vertex_cross_pos (n : ℕ) (j : Fin (4 * 2 ^ n)) :
 0 < refinementCross (directVertex n j) (directVertex (n+1) (oddIndex n j)) ∧
 0 < refinementCross (directVertex (n+1) (oddIndex n j)) (directVertex n (directVertexNext n j)) := by
  rw [(refinement_vertex_cross n j).1, (refinement_vertex_cross n j).2]
  exact ⟨div_pos (beam_pos n) (mul_pos (by norm_num) (core_succ_pos n)), div_pos (beam_pos n) (mul_pos (by norm_num) (core_succ_pos n))⟩
end QuadrantUnitKernel
end DkMath.CosmicFormula.Rotation.CF2D
