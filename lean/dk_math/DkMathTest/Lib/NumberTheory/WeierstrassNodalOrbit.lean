/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.NumberTheory.WeierstrassNodalOrbit
import DkMathTest.Lib.NumberTheory.WeierstrassNodalVelu

#print "file: DkMathTest.Lib.NumberTheory.WeierstrassNodalOrbit"

/-! 実際の節点点群で、異なる素数位数の点を使って非衝突軌道を構成する。
標数2,3の37点軌道、および衝突条件の境界を確認する。 -/
namespace WeierstrassNodalOrbitTest
open WeierstrassCurve WeierstrassCurve.Affine
open DkMath.Lib.NumberTheory WeierstrassNodalOrbit EllipticNodalTorsion.NodalTorsion
open WeierstrassNodalVeluTest
noncomputable section
local instance {α : Type*} : DecidableEq α := Classical.decEq _
variable {k : Type*} [Field k] {m n : ℕ} [Fact m.Prime] [Fact n.Prime]

/-- 原始根から構成済みの同じ実点。 -/
def rootPoint {u : k} (hu : IsPrimitiveRoot u m) : (splitCurve k).toAffine.Point :=
  parameterPoint u (hu.isUnit (Fact.out : m.Prime).ne_zero).ne_zero (by
    intro h
    exact (Fact.out : m.Prime).ne_one (hu.unique (h ▸ (by simp : IsPrimitiveRoot (1 : k) 1))))

private theorem frame : Frame (splitCurve k) 0 0 0 := by
  constructor <;> norm_num [splitCurve]
private theorem separated : (0 : k) ≠ -(splitCurve k).a₁ - 0 := by norm_num [splitCurve]
private theorem root_tc {u : k} (hu : IsPrimitiveRoot u m) :
    tc (splitCurve k) 0 0 0 (rootPoint hu) = u := parameter_tc _ _ _

/-- 異なる位数の実点を用い、仮定だけでない非衝突の巡回座標和を確認する。 -/
theorem actual_orbit {u v : k} (hu : IsPrimitiveRoot u m) (hv : IsPrimitiveRoot v n)
    (hnd : ¬ m ∣ n) :
    ∑ j ∈ Finset.range n, (rootPoint hu + j • rootPoint hv).xc =
      (n : k) ^ 2 * (n • rootPoint hu).xc := by
  have hP : n • rootPoint hu ≠ 0 := by
    intro he
    have h := (nsmul_eq_zero_iff frame separated _).mp he
    rw [root_tc] at h
    exact hnd (hu.dvd_of_pow_eq_one n h)
  have hQ : IsPrimitiveRoot (tc (splitCurve k) 0 0 0 (rootPoint hv)) n := by rwa [root_tc]
  simpa only [mul_zero, sub_zero, zero_add] using translated_x_sum_nsmul frame separated _ _ hQ hP

/-- 構成済みの実核上では非衝突条件が破れ、有限座標公式の適用外となる。 -/
theorem actual_collision {v : k} (hv : IsPrimitiveRoot v n) :
    n • rootPoint hv = 0 ∧ rootPoint hv ∈ AddSubgroup.zmultiples (rootPoint hv) := by
  constructor
  · apply (nsmul_eq_zero_iff frame separated _).mpr
    rw [root_tc]
    exact hv.pow_eq_one
  · exact AddSubgroup.mem_zmultiples _

local instance : Fact (Nat.Prime 5) := ⟨by decide⟩
local instance : Fact (Nat.Prime 7) := ⟨by decide⟩
local instance : Fact (Nat.Prime 37) := ⟨by decide⟩

/-- 標数2で、5位数の実点を実37点核で平行移動する非空の例。 -/
theorem characteristic_two_actual_orbit :
    ∃ (u v : AlgebraicClosure (ZMod 2)) (hu : IsPrimitiveRoot u 5) (hv : IsPrimitiveRoot v 37),
      ∑ j ∈ Finset.range 37, (rootPoint hu + j • rootPoint hv).xc =
        (37 : AlgebraicClosure (ZMod 2)) ^ 2 * (37 • rootPoint hu).xc := by
  have : NeZero (5 : ZMod 2) := ⟨by decide⟩
  have : NeZero (37 : ZMod 2) := ⟨by decide⟩
  obtain ⟨u, hu⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (AlgebraicClosure (ZMod 2)) 5
  obtain ⟨v, hv⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (AlgebraicClosure (ZMod 2)) 37
  exact ⟨u, v, hu, hv, actual_orbit hu hv (by decide)⟩

/-- 標数3でも、7位数の実点を実37点核で平行移動できる。 -/
theorem characteristic_three_actual_orbit :
    ∃ (u v : AlgebraicClosure (ZMod 3)) (hu : IsPrimitiveRoot u 7) (hv : IsPrimitiveRoot v 37),
      ∑ j ∈ Finset.range 37, (rootPoint hu + j • rootPoint hv).xc =
        (37 : AlgebraicClosure (ZMod 3)) ^ 2 * (37 • rootPoint hu).xc := by
  have : NeZero (7 : ZMod 3) := ⟨by decide⟩
  have : NeZero (37 : ZMod 3) := ⟨by decide⟩
  obtain ⟨u, hu⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (AlgebraicClosure (ZMod 3)) 7
  obtain ⟨v, hv⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (AlgebraicClosure (ZMod 3)) 37
  exact ⟨u, v, hu, hv, actual_orbit hu hv (by decide)⟩

end
end WeierstrassNodalOrbitTest
