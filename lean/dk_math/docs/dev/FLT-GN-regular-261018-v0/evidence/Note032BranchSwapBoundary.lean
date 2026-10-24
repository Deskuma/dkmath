/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.RepresentationTheory.CofixedBranchSwap
import Mathlib.Algebra.Field.ZMod

#print "file: Note032BranchSwapBoundary"

/-! NOTE-032: 非自明な有限表現で、枝交換と標数のガードを確認する。 -/
namespace CofixedBranchSwapTest
open DkMath.Lib.RepresentationTheory LocalFixedCofixed

section Field
variable (k : Type*) [Field k]

/-- 第一座標軸を第二射影の核として取る。 -/
def axis : Submodule k (k × k) := LinearMap.ker (LinearMap.snd k k k)

/-- 軸の所属は第二座標が零であること。 -/
theorem mem_axis (v : k × k) : v ∈ axis k ↔ v.2 = 0 := Iff.rfl

/-- 実際のベクトル(0,1)は軸の外にある。 -/
theorem axis_ne_top : axis k ≠ ⊤ := by
  intro h
  have hm : ((0, 1) : k × k) ∈ axis k := h ▸ Submodule.mem_top
  exact one_ne_zero ((mem_axis k _).mp hm)

/-- 実際のベクトル(1,0)は非零の軸の元である。 -/
theorem axis_ne_bot : axis k ≠ ⊥ := by
  intro h
  have hm : ((1, 0) : k × k) ∈ axis k := (mem_axis k _).mpr rfl
  rw [h, Submodule.mem_bot] at hm
  exact one_ne_zero (congrArg Prod.fst hm)

/-- 有限二次元空間の非零な真部分空間として次元1を確認する。 -/
theorem axis_finrank : Module.finrank k (axis k) = 1 := by
  have hd : Module.finrank k (k × k) = 2 := by simp
  exact (proper_nonzero_iff_finrank_one hd _).mp ⟨axis_ne_bot k, axis_ne_top k⟩

/-- 加法群kによる実際の非自明なせん断表現。 -/
def rho : Representation k (Multiplicative k) (k × k) where
  toFun t := {
    toFun := fun v => (v.1 + t.toAdd * v.2, v.2)
    map_add' := by
      intro v w
      apply Prod.ext
      · dsimp; ring
      · rfl
    map_smul' := by
      intro c v
      apply Prod.ext
      · dsimp; ring
      · rfl }
  map_one' := by ext <;> simp
  map_mul' := by intro a b; ext <;> simp [Module.End.mul_apply, add_mul, add_comm]

/-- 商は第二座標なので全群で固定される。 -/
theorem rho_cofixed : IsCofixedOn (rho k) (axis k) := by
  intro g x
  change x.2 - x.2 = 0
  exact sub_self _

/-- せん断パラメータ1は(0,1)を動かす。 -/
theorem rho_nontrivial : ∃ τ ∈ (⊤ : Subgroup (Multiplicative k)), ∃ x, rho k τ x ≠ x := by
  refine ⟨Multiplicative.ofAdd 1, Subgroup.mem_top _, (0, 1), ?_⟩
  intro h
  have hh := congrArg Prod.fst h
  change 0 + 1 * 1 = (0 : k) at hh
  norm_num at hh

/-- 同じ軸が全局所変化量を吸収する。 -/
theorem rho_absorbs : CofixedOn (rho k) (axis k) ⊤ := fun g _ x => rho_cofixed k g x
end Field

local instance : Fact (Nat.Prime 2) := ⟨by decide⟩
local instance : Fact (Nat.Prime 3) := ⟨by decide⟩

/-- 標数2では恒等元すら枝交換条件を満たすが、Cofixed直線は存在する。
他の全条件は成立するため、2≠0のガードを除けない。 -/
theorem characteristic_two_boundary :
    axis (ZMod 2) ≠ ⊤ ∧
      CofixedOn (rho (ZMod 2)) (axis (ZMod 2)) ⊤ ∧
      (∃ τ ∈ (⊤ : Subgroup (Multiplicative (ZMod 2))), ∃ x, rho (ZMod 2) τ x ≠ x) ∧
      (∃ σ, ∀ x, x ∉ axis (ZMod 2) → rho (ZMod 2) σ x + x ∈ axis (ZMod 2)) ∧
      ∃ L : Submodule (ZMod 2) (ZMod 2 × ZMod 2), Module.finrank (ZMod 2) L = 1 ∧
        IsCofixedOn (rho (ZMod 2)) L := by
  refine ⟨axis_ne_top _, rho_absorbs _, rho_nontrivial _, ?_, axis _, axis_finrank _, rho_cofixed _⟩
  refine ⟨1, fun x _ => ?_⟩
  change x.2 + x.2 = 0
  calc x.2 + x.2 = (2 : ZMod 2) * x.2 := by ring
       _ = 0 := by rw [show (2 : ZMod 2) = 0 from rfl, zero_mul]

/-- 標数3の非自明せん断はCofixed直線を持つので、吸収と非自明性だけでは排除できない。
実際に枝交換条件が失敗することを、商の座標2≠0から確認する。 -/
theorem odd_shear_has_no_branch_swap :
    ¬ ∃ σ, ∀ x, x ∉ axis (ZMod 3) → rho (ZMod 3) σ x + x ∈ axis (ZMod 3) := by
  rintro ⟨σ, hσ⟩
  have hx : ((0, 1) : ZMod 3 × ZMod 3) ∉ axis (ZMod 3) := by
    rw [mem_axis]; decide
  have h := (mem_axis (ZMod 3) _).mp (hσ (0, 1) hx)
  change (1 : ZMod 3) + 1 = 0 at h
  exact (by decide : (1 : ZMod 3) + 1 ≠ 0) h

/-- 奇標数でもCofixedは実在する。枝交換の存在を一般論から作っていない。 -/
theorem odd_cofixed_line_exists :
    ∃ L : Submodule (ZMod 3) (ZMod 3 × ZMod 3), Module.finrank (ZMod 3) L = 1 ∧
      IsCofixedOn (rho (ZMod 3)) L := ⟨axis _, axis_finrank _, rho_cofixed _⟩

/-- M=⊤なら枝交換条件は空虚に成立する。真性を落としてはいけない。 -/
theorem top_absorber_boundary :
    CofixedOn (rho (ZMod 3)) ⊤ ⊤ ∧
      (∃ σ, ∀ x : ZMod 3 × ZMod 3, x ∉ (⊤ : Submodule (ZMod 3) _) →
        rho (ZMod 3) σ x + x ∈ (⊤ : Submodule (ZMod 3) _)) := by
  exact ⟨fun _ _ _ => Submodule.mem_top, 1, fun _ h => (h Submodule.mem_top).elim⟩

/-- mod4の条件だけからmod8の3側を選ぶことはできない。Sourceの存在例とは主張しない。 -/
theorem orientation_leaves_seven_branch : ∃ a : ℤ, (4 : ℤ) ∣ a + 1 ∧ a % 8 = 7 :=
  ⟨-1, by decide⟩

end CofixedBranchSwapTest
