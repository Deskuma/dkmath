/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.CosmicFormula.Rotation.CF2D.HalfKernel
import DkMath.CosmicFormula.Rotation.CF2D.KernelPower

#print "file: DkMath.CosmicFormula.Rotation.CF2D.HalfKernelOrder"

/-!
# 二分核の正確な位数

二分核 `g_n` の平方は `g_(n-1)` である。よって `g_n^(2^n)=g_0`。
初期核は二乗すると `(-1,0)`、四乗すると単位核となるので、
`g_n` の位数は正確に `4·2^n` である。角度や三角関数を使わない。
-/
namespace DkMath.CosmicFormula.Rotation.CF2D
namespace QuadrantUnitKernel

/-- 次段階の核の二乗は前段階の核に等しい。 -/
theorem sequence_kernel_sq (n : ℕ) : (sequence (n+1)).kernel ^ 2 = (sequence n).kernel := by
  apply UnitKernel.ext
  simpa [pow_two] using sequence_star n

/-- 第 `n` 核を `2^n` 回合成すると初期核に戻る。 -/
theorem sequence_kernel_pow_two_pow (n : ℕ) :
    (sequence n).kernel ^ (2 ^ n) = initial.kernel := by
  induction n with
  | zero => simp [sequence]
  | succ n ih =>
    rw [pow_succ, mul_comm, pow_mul, sequence_kernel_sq, ih]

/-- 初期核の二乗は `(-1,0)` である。 -/
theorem initial_kernel_sq_val : (initial.kernel ^ 2).val = ⟨-1, 0⟩ := by
  norm_num [pow_two, UnitKernel.mul_eq_star, UnitKernel.star, Vec.star, initial]

/-- 初期核の四乗は単位核である。 -/
theorem initial_kernel_pow_four : initial.kernel ^ 4 = 1 := by
  apply UnitKernel.ext
  change (initial.kernel ^ 4).val = Vec.one ℝ
  norm_num [pow_succ, UnitKernel.mul_eq_star, UnitKernel.star, UnitKernel.one, Vec.star, Vec.one, initial]

/-- 半周の累乗は `(-1,0)` である。 -/
theorem sequence_kernel_pow_half_val (n : ℕ) :
    ((sequence n).kernel ^ (2 ^ (n+1))).val = ⟨-1, 0⟩ := by
  rw [pow_succ, pow_mul, sequence_kernel_pow_two_pow]
  exact initial_kernel_sq_val

/-- 全周の累乗は単位核である。 -/
theorem sequence_kernel_pow_full (n : ℕ) :
    (sequence n).kernel ^ (2 ^ (n+2)) = 1 := by
  have h : 2 ^ (n+2) = 2 ^ n * 4 := by ring
  rw [h, pow_mul, sequence_kernel_pow_two_pow, initial_kernel_pow_four]

/-- 半周で得る核は単位核ではない。 -/
theorem sequence_kernel_pow_half_ne_one (n : ℕ) :
    (sequence n).kernel ^ (2 ^ (n+1)) ≠ 1 := by
  intro h
  have hv := congrArg (fun x : UnitKernel ℝ => x.val.core) h
  have hs := congrArg Vec.core (sequence_kernel_pow_half_val n)
  simp [UnitKernel.one, Vec.one] at hv hs
  linarith

/-- 二分核の位数は正確に `4·2^n` である。 -/
theorem sequence_kernel_orderOf (n : ℕ) :
    orderOf (sequence n).kernel = 4 * 2 ^ n := by
  have hp : orderOf (sequence n).kernel = 2 ^ ((n+1)+1) := by
    apply orderOf_eq_prime_pow (p := 2) (n := n+1)
    · exact sequence_kernel_pow_half_ne_one n
    · simpa [Nat.add_assoc] using sequence_kernel_pow_full n
  rw [hp]
  ring


/-- 二分核の冪を初期ベクトルに作用させた、π-free な有限軌道の頂点。 -/
noncomputable def directVertex (n : ℕ) (j : Fin (4 * 2 ^ n)) : Vec ℝ :=
  UnitKernel.act ((sequence n).kernel ^ j.val) (Vec.one ℝ)

/-- 有限軌道の各頂点は二乗和 `1` を保つ。 -/
theorem directVertex_q2 (n : ℕ) (j : Fin (4 * 2 ^ n)) : Vec.q2 (directVertex n j) = 1 := by
  rw [directVertex, UnitKernel.q2_act]
  norm_num [Vec.q2, Vec.one]


/-- 直接生成した核の冪は `4·2^n` を周期とする。 -/
theorem sequence_kernel_pow_period (n j : ℕ) :
    (sequence n).kernel ^ (j + 4 * 2 ^ n) = (sequence n).kernel ^ j := by
  have h : (sequence n).kernel ^ (4 * 2 ^ n) = 1 := by
    have e : 4 * 2 ^ n = 2 ^ (n+2) := by ring
    rw [e, sequence_kernel_pow_full]
  rw [pow_add, h, mul_one]


/-- 軌道の添字を一歩進め、末尾から先頭へ巡回させる。 -/
def directVertexNext (n : ℕ) (j : Fin (4 * 2 ^ n)) : Fin (4 * 2 ^ n) :=
  ⟨(j.val + 1) % (4 * 2 ^ n), Nat.mod_lt _ (by positivity)⟩

/-- 巡回後継も二分核による一回の作用であり、末尾の折り返しも含む。 -/
theorem directVertex_next (n : ℕ) (j : Fin (4 * 2 ^ n)) :
    directVertex n (directVertexNext n j) = UnitKernel.act (sequence n).kernel (directVertex n j) := by
  unfold directVertex directVertexNext
  dsimp only
  have hmod : (sequence n).kernel ^ ((j.val + 1) % (4 * 2 ^ n)) =
      (sequence n).kernel ^ (j.val + 1) := by
    simpa only [sequence_kernel_orderOf] using (pow_mod_orderOf (sequence n).kernel (j.val + 1))
  rw [hmod, pow_succ', UnitKernel.mul_eq_star, UnitKernel.act_star]

/-- 正確な位数より、軌道の `4·2^n` 個の頂点は互いに異なる。 -/
theorem directVertex_injective (n : ℕ) : Function.Injective (directVertex n) := by
  intro i j hij
  have he : (sequence n).kernel ^ i.val = (sequence n).kernel ^ j.val := by
    apply UnitKernel.ext
    simpa [directVertex, UnitKernel.act] using hij
  have hi : i.val < orderOf (sequence n).kernel := by rw [sequence_kernel_orderOf]; exact i.isLt
  have hj : j.val < orderOf (sequence n).kernel := by rw [sequence_kernel_orderOf]; exact j.isLt
  exact Fin.ext (pow_injOn_Iio_orderOf hi hj he)

/-- 直接生成した有限軌道の頂点集合は `4·2^n` 個の点からなる。 -/
theorem directVertex_ncard (n : ℕ) : (Set.range (directVertex n)).ncard = 4 * 2 ^ n := by
  rw [Set.ncard_range_of_injective (directVertex_injective n), Nat.card_fin]


/-- 直接軌道上で半周だけ先へ進む添字。 -/
def directVertexOpposite (n : ℕ) (j : Fin (4 * 2 ^ n)) : Fin (4 * 2 ^ n) :=
  ⟨(j.val + 2 ^ (n+1)) % (4 * 2 ^ n), Nat.mod_lt _ (by positivity)⟩

/-- 半周先の直接軌道の頂点は、元の頂点の各座標の符号を反転した点である。 -/
theorem directVertex_opposite (n : ℕ) (j : Fin (4 * 2 ^ n)) :
    directVertex n (directVertexOpposite n j) =
      ⟨-(directVertex n j).core, -(directVertex n j).beam⟩ := by
  unfold directVertex directVertexOpposite
  dsimp only
  have hmod : (sequence n).kernel ^ ((j.val + 2 ^ (n+1)) % (4 * 2 ^ n)) =
      (sequence n).kernel ^ (j.val + 2 ^ (n+1)) := by
    simpa only [sequence_kernel_orderOf] using (pow_mod_orderOf (sequence n).kernel (j.val + 2 ^ (n+1)))
  rw [hmod, pow_add, UnitKernel.mul_eq_star, UnitKernel.act_star]
  simp [UnitKernel.act, sequence_kernel_pow_half_val, Vec.star, Vec.one]

end QuadrantUnitKernel
end DkMath.CosmicFormula.Rotation.CF2D
