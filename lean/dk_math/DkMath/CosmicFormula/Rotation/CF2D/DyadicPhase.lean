/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.CosmicFormula.Rotation.CF2D.HalfKernelRefinement
import DkMath.CosmicFormula.Rotation.CF2D.HalfKernelRefinementGeometry

#print "file: DkMath.CosmicFormula.Rotation.CF2D.DyadicPhase"

/-!
# 二分核の有理位相

一周を 1 とし、第 n 段階の第 j 頂点に有理数 j/(4·2^n) を割り当てる。
位相が等しい二つの表示は、細かい方の段階で同じ添字を持つ。
核の平方関係により、その座標も一致する。
-/

namespace DkMath.CosmicFormula.Rotation.CF2D
namespace QuadrantUnitKernel

/-- 一周を 1 とした第 n 段階の有理位相。最後の頂点の位相は 1 未満。 -/
def dyadicPhase (n : ℕ) (j : Fin (4 * 2 ^ n)) : ℚ :=
  (j.val : ℚ) / ((4 * 2 ^ n : ℕ) : ℚ)

/-- 有理位相は一周の半開区間に属する。 -/
theorem dyadicPhase_mem_Ico (n : ℕ) (j : Fin (4 * 2 ^ n)) :
    dyadicPhase n j ∈ Set.Ico 0 1 := by
  have hp : (0 : ℚ) < ((4 * 2 ^ n : ℕ) : ℚ) := by positivity
  exact ⟨div_nonneg (by positivity) hp.le, (div_lt_one hp).2 (by exact_mod_cast j.isLt)⟩

/-- 一段細分化すると分子と分母がともに二倍になるので、偶数頂点の位相は変わらない。 -/
theorem dyadicPhase_even (n : ℕ) (j : Fin (4 * 2 ^ n)) :
    dyadicPhase (n + 1) (evenIndex n j) = dyadicPhase n j := by
  unfold dyadicPhase
  have hc := congrArg (fun k : ℕ => (k : ℚ)) (refinement_count n)
  rw [hc]
  simp only [evenIndex, Nat.cast_mul, Nat.cast_ofNat]
  field_simp

/-- 同じ段階では添字の大小と有理位相の大小が一致する。 -/
theorem dyadicPhase_strictMono (n : ℕ) : StrictMono (dyadicPhase n) := by
  intro i j h
  unfold dyadicPhase
  exact (div_lt_div_iff_of_pos_right (by positivity)).2 (by exact_mod_cast h)

/-- 奇数頂点の位相は、対応する旧頂点から半ステップ先にある。
最後の辺でもこの式は一周の半開区間内で成り立つ。 -/
theorem dyadicPhase_odd (n : ℕ) (j : Fin (4 * 2 ^ n)) :
    dyadicPhase (n + 1) (oddIndex n j) =
      dyadicPhase n j + 1 / ((4 * 2 ^ (n + 1) : ℕ) : ℚ) := by
  rw [← dyadicPhase_even n j, dyadicPhase, dyadicPhase]
  simp only [evenIndex, oddIndex, Nat.cast_add, Nat.cast_one]
  rw [add_div]

/-- 細分化を r 回行うと、同じ頂点の添字は 2^r 倍になる。 -/
theorem rawVertex_refine (n r j : ℕ) :
    rawVertex (n + r) (2 ^ r * j) = rawVertex n j := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [show 2 ^ (r + 1) * j = 2 * (2 ^ r * j) by ring]
    exact (rawVertex_even (n + r) (2 ^ r * j)).trans ih

private theorem phase_eq_vertex_of_add (n r : ℕ) (j : Fin (4 * 2 ^ n))
    (k : Fin (4 * 2 ^ (n + r))) (h : dyadicPhase n j = dyadicPhase (n + r) k) :
    directVertex n j = directVertex (n + r) k := by
  have hn : ((4 * 2 ^ n : ℕ) : ℚ) ≠ 0 := by positivity
  have hm : ((4 * 2 ^ (n + r) : ℕ) : ℚ) ≠ 0 := by positivity
  have hmul := (div_eq_div_iff hn hm).mp h
  have hd : 4 * 2 ^ (n + r) = (4 * 2 ^ n) * 2 ^ r := by rw [pow_add, mul_assoc]
  have hmul' : (j.val : ℚ) * (((4 * 2 ^ n : ℕ) : ℚ) * ((2 ^ r : ℕ) : ℚ)) =
      (k.val : ℚ) * ((4 * 2 ^ n : ℕ) : ℚ) := by
    simpa only [hd, Nat.cast_mul] using hmul
  have hk : ((2 ^ r * j.val : ℕ) : ℚ) = k.val := by
    apply mul_right_cancel₀ hn
    push_cast at hmul' ⊢
    linear_combination hmul'
  have hi : 2 ^ r * j.val = k.val := by exact_mod_cast hk
  rw [directVertex_eq_rawVertex, directVertex_eq_rawVertex, ← hi, rawVertex_refine]

/-- 同じ有理位相を表す頂点は、段階が異なっても同じ座標を持つ。 -/
theorem directVertex_eq_of_dyadicPhase_eq (n m : ℕ) (j : Fin (4 * 2 ^ n))
    (k : Fin (4 * 2 ^ m)) (h : dyadicPhase n j = dyadicPhase m k) :
    directVertex n j = directVertex m k := by
  rcases le_total n m with hnm | hmn
  · obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le hnm
    exact phase_eq_vertex_of_add n r j k h
  · obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le hmn
    exact (phase_eq_vertex_of_add m r k j h.symm).symm

/-- 有限二分軌道が実現する位相の集合。一周の代表元を取る。 -/
def DyadicPhase := {t : ℚ // ∃ (n : ℕ) (j : Fin (4 * 2 ^ n)), dyadicPhase n j = t}

/-- 有限軌道の添字を、段階によらない有理位相に移す。 -/
def DyadicPhase.ofIndex (n : ℕ) (j : Fin (4 * 2 ^ n)) : DyadicPhase :=
  ⟨dyadicPhase n j, ⟨n, j, rfl⟩⟩

/-- 位相から座標を取り出す。表示を選ぶが、下の補題で選択に依存しないことを示す。 -/
noncomputable def DyadicPhase.vertex (t : DyadicPhase) : Vec ℝ :=
  directVertex t.property.choose t.property.choose_spec.choose

/-- 任意の有限表示で位相の座標を計算できる。 -/
theorem DyadicPhase.vertex_of_index (n : ℕ) (j : Fin (4 * 2 ^ n)) :
    (DyadicPhase.ofIndex n j).vertex = directVertex n j := by
  let t : DyadicPhase := ⟨dyadicPhase n j, ⟨n, j, rfl⟩⟩
  exact directVertex_eq_of_dyadicPhase_eq _ n _ j t.property.choose_spec.choose_spec

/-- 内在的余弦は位相が表す単位核の第一座標。 -/
noncomputable def DyadicPhase.cfcos (t : DyadicPhase) : ℝ := t.vertex.core

/-- 内在的正弦は位相が表す単位核の第二座標。 -/
noncomputable def DyadicPhase.cfsin (t : DyadicPhase) : ℝ := t.vertex.beam

/-- 単位核の保存量から、二つの座標の二乗和は 1 である。 -/
theorem DyadicPhase.cfcos_sq_add_cfsin_sq (t : DyadicPhase) :
    t.cfcos ^ 2 + t.cfsin ^ 2 = 1 :=
  directVertex_q2 _ _

/-- 旧頂点、新しい奇数頂点、旧次頂点の順に並べると、隣接する二対の外積は正である。
有理位相から復元した座標に二分核の局所配置を移す。旧次頂点は末尾で先頭へ巡回する。 -/
theorem DyadicPhase.refinement_cross_pos (n : ℕ) (j : Fin (4 * 2 ^ n)) :
    let p := (ofIndex n j).vertex
    let w := (ofIndex (n + 1) (oddIndex n j)).vertex
    let q := (ofIndex n (directVertexNext n j)).vertex
    0 < refinementCross p w ∧ 0 < refinementCross w q := by
  simpa only [vertex_of_index] using refinement_vertex_cross_pos n j

end QuadrantUnitKernel
end DkMath.CosmicFormula.Rotation.CF2D
