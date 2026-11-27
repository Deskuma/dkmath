/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.CosmicFormula.Rotation.CF2D.HalfKernelOrder
import DkMath.CosmicFormula.Rotation.CF2D.IntrinsicPolygon

#print "file: DkMath.CosmicFormula.Rotation.CF2D.HalfKernelRefinement"

/-!
# 二分核による有限軌道の細分化

`g_(n+1)^2 = g_n` から、新しい偶数番目の頂点は元の頂点と等しい。
さらに `1+g_n = 2 c_(n+1) g_(n+1)` を座標ごとに示すと、新しい奇数番目の
頂点は元の隣接頂点の和を `2 c_(n+1)` で割ったものである。
最後の辺の折り返しは核の周期を用いて扱う。
このファイルでは、凸性や幾何学的な巡回順序は主張しない。
-/
namespace DkMath.CosmicFormula.Rotation.CF2D
namespace QuadrantUnitKernel

/-- 自然数添字の直接軌道。周期を用いる前の計算に使う。 -/
noncomputable def rawVertex (n j : ℕ) : Vec ℝ :=
  ((sequence n).kernel ^ j).val

/-- 第 `n+1` 段階の頂点数は第 `n` 段階の２倍。 -/
theorem refinement_count (n : ℕ) : 4 * 2 ^ (n+1) = 2 * (4 * 2 ^ n) := by ring

/-- 古い頂点に対応する新しい偶数添字。 -/
def evenIndex (n : ℕ) (j : Fin (4 * 2 ^ n)) : Fin (4 * 2 ^ (n+1)) :=
  ⟨2 * j.val, by have h := j.isLt; rw [refinement_count]; omega⟩

/-- 古い辺に対応する新しい奇数添字。 -/
def oddIndex (n : ℕ) (j : Fin (4 * 2 ^ n)) : Fin (4 * 2 ^ (n+1)) :=
  ⟨2 * j.val + 1, by have h := j.isLt; rw [refinement_count]; omega⟩


/-- 偶数頂点の次は、同じ古い辺に対応する奇数頂点である。 -/
theorem directVertexNext_even (n : ℕ) (j : Fin (4 * 2 ^ n)) :
    directVertexNext (n+1) (evenIndex n j) = oddIndex n j := by
  apply Fin.ext
  change (2 * j.val + 1) % (4 * 2 ^ (n+1)) = 2 * j.val + 1
  exact Nat.mod_eq_of_lt (oddIndex n j).isLt

/-- 奇数頂点の次は、古い辺の終点に対応する偶数頂点である。

最後の辺では両側が巡回添字の先頭に戻る。 -/
theorem directVertexNext_odd (n : ℕ) (j : Fin (4 * 2 ^ n)) :
    directVertexNext (n+1) (oddIndex n j) = evenIndex n (directVertexNext n j) := by
  apply Fin.ext
  change (2 * j.val + 1 + 1) % (4 * 2 ^ (n+1)) = 2 * ((j.val + 1) % (4 * 2 ^ n))
  rw [refinement_count]
  convert Nat.mul_mod_mul_left 2 (j.val + 1) (4 * 2 ^ n) using 1

/-- 偶数番目の自然数添字における軌道の一致。 -/
theorem rawVertex_even (n j : ℕ) : rawVertex (n+1) (2*j) = rawVertex n j := by
  unfold rawVertex
  rw [pow_mul, sequence_kernel_sq]

/-- 直接軌道は、対応する自然数添字の核そのものである。 -/
theorem directVertex_eq_rawVertex (n : ℕ) (j : Fin (4 * 2 ^ n)) :
    directVertex n j = rawVertex n j.val := by
  simp [directVertex, rawVertex, UnitKernel.act]

/-- 偶数番目の新頂点は元の頂点である。 -/
theorem directVertex_even (n : ℕ) (j : Fin (4 * 2 ^ n)) :
    directVertex (n+1) (evenIndex n j) = directVertex n j := by
  rw [directVertex_eq_rawVertex, directVertex_eq_rawVertex]
  exact rawVertex_even n j.val

/-- 半角核の core と元の core の二乗関係。 -/
theorem refinement_core (n : ℕ) :
    1 + (sequence n).core = 2 * (sequence (n+1)).core ^ 2 := by
  have h := core_succ_sq n
  linarith

/-- 元の beam は半角核の座標の積の２倍である。 -/
theorem refinement_beam (n : ℕ) :
    (sequence n).beam = 2 * (sequence (n+1)).core * (sequence (n+1)).beam := by
  have h := congrArg Vec.beam (sequence_star n)
  change (sequence (n+1)).core * (sequence (n+1)).beam +
    (sequence (n+1)).beam * (sequence (n+1)).core = (sequence n).beam at h
  linarith

/-- 隣接核の和と半角核の関係を座標で表す。 -/
theorem refinement_kernel_identity (n : ℕ) :
    1 + (sequence n).core = 2 * (sequence (n+1)).core * (sequence (n+1)).core ∧
    (sequence n).beam = 2 * (sequence (n+1)).core * (sequence (n+1)).beam := by
  constructor
  · have h := refinement_core n
    nlinarith
  · exact refinement_beam n

/-- 奇数番目の軌道に対する、分母を除いた中点関係。 -/
theorem rawVertex_odd_scaled (n j : ℕ) :
    (2 * (sequence (n+1)).core) * (rawVertex (n+1) (2*j+1)).core =
        (rawVertex n j).core + (rawVertex n (j+1)).core ∧
    (2 * (sequence (n+1)).core) * (rawVertex (n+1) (2*j+1)).beam =
        (rawVertex n j).beam + (rawVertex n (j+1)).beam := by
  have heven := rawVertex_even n j
  have hc := (refinement_kernel_identity n).1
  have hs := (refinement_kernel_identity n).2
  unfold rawVertex at heven ⊢
  rw [pow_succ, pow_succ, UnitKernel.mul_eq_star, UnitKernel.star_val,
    UnitKernel.mul_eq_star, UnitKernel.star_val]
  rw [heven]
  change (2 * (sequence (n+1)).core) *
      (((sequence n).kernel ^ j).val.core * (sequence (n+1)).core -
        ((sequence n).kernel ^ j).val.beam * (sequence (n+1)).beam) =
      ((sequence n).kernel ^ j).val.core +
        (((sequence n).kernel ^ j).val.core * (sequence n).core -
          ((sequence n).kernel ^ j).val.beam * (sequence n).beam) ∧
    (2 * (sequence (n+1)).core) *
      (((sequence n).kernel ^ j).val.core * (sequence (n+1)).beam +
        ((sequence n).kernel ^ j).val.beam * (sequence (n+1)).core) =
      ((sequence n).kernel ^ j).val.beam +
        (((sequence n).kernel ^ j).val.core * (sequence n).beam +
          ((sequence n).kernel ^ j).val.beam * (sequence n).core)
  have hc' : (sequence n).core = 2 * (sequence (n+1)).core * (sequence (n+1)).core - 1 := by linarith
  rw [hc', hs]
  constructor <;> ring


/-- 循環後継は自然数添字 `j+1` の軌道に対応する。 -/
theorem directVertex_next_eq_raw (n : ℕ) (j : Fin (4 * 2 ^ n)) :
    directVertex n (directVertexNext n j) = rawVertex n (j.val+1) := by
  rw [directVertex_eq_rawVertex]
  unfold directVertexNext rawVertex
  dsimp only
  congr 1
  simpa only [sequence_kernel_orderOf] using (pow_mod_orderOf (sequence n).kernel (j.val+1))

/-- 最終辺の折り返しを含む、奇数頂点の分母を除いた中点関係。 -/
theorem directVertex_odd_scaled (n : ℕ) (j : Fin (4 * 2 ^ n)) :
    (2 * (sequence (n+1)).core) * (directVertex (n+1) (oddIndex n j)).core =
        (directVertex n j).core + (directVertex n (directVertexNext n j)).core ∧
    (2 * (sequence (n+1)).core) * (directVertex (n+1) (oddIndex n j)).beam =
        (directVertex n j).beam + (directVertex n (directVertexNext n j)).beam := by
  rw [directVertex_eq_rawVertex, directVertex_eq_rawVertex, directVertex_next_eq_raw]
  exact rawVertex_odd_scaled n j.val

/-- 奇数頂点は古い辺の中点を単位核に正規化した点である。

分母 `2 c_(n+1)` の正性は `core_succ_pos` から従う。最終辺では
`directVertexNext` が最初の頂点に戻る。 -/
theorem directVertex_odd_normalized_midpoint (n : ℕ) (j : Fin (4 * 2 ^ n)) :
    directVertex (n+1) (oddIndex n j) =
      ⟨((directVertex n j).core + (directVertex n (directVertexNext n j)).core) /
          (2 * (sequence (n+1)).core),
       ((directVertex n j).beam + (directVertex n (directVertexNext n j)).beam) /
          (2 * (sequence (n+1)).core)⟩ := by
  have hp : 2 * (sequence (n+1)).core ≠ 0 := ne_of_gt (mul_pos (by norm_num) (core_succ_pos n))
  have h := directVertex_odd_scaled n j
  have hc : (directVertex (n+1) (oddIndex n j)).core =
      ((directVertex n j).core + (directVertex n (directVertexNext n j)).core) /
        (2 * (sequence (n+1)).core) := by
    apply (eq_div_iff hp).2
    nlinarith [h.1]
  have hs : (directVertex (n+1) (oddIndex n j)).beam =
      ((directVertex n j).beam + (directVertex n (directVertexNext n j)).beam) /
        (2 * (sequence (n+1)).core) := by
    apply (eq_div_iff hp).2
    nlinarith [h.2]
  cases hv : directVertex (n+1) (oddIndex n j) with
  | mk a b =>
    simp only [hv] at hc hs ⊢
    exact congrArg₂ Vec.mk hc hs

/-- 細分後の各添字は、元の頂点に対応する偶数か、新頂点に対応する奇数である。 -/
theorem refinement_index_even_or_odd (n : ℕ) (k : Fin (4 * 2 ^ (n + 1))) :
    (∃ j, evenIndex n j = k) ∨ (∃ j, oddIndex n j = k) := by
  have hc := refinement_count n
  have hj : k.val / 2 < 4 * 2 ^ n := by
    have hk : k.val < 2 * (4 * 2 ^ n) := hc ▸ k.isLt
    omega
  let j : Fin (4 * 2 ^ n) := ⟨k.val / 2, hj⟩
  rcases Nat.mod_two_eq_zero_or_one k.val with h | h
  · left
    refine ⟨j, ?_⟩
    apply Fin.ext
    simp only [evenIndex, j]
    omega
  · right
    refine ⟨j, ?_⟩
    apply Fin.ext
    simp only [oddIndex, j]
    omega

end QuadrantUnitKernel

end DkMath.CosmicFormula.Rotation.CF2D
