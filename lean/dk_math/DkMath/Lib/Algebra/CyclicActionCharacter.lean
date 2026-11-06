/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.Algebra.Module.ZMod
import Mathlib.Algebra.Group.Units.Hom

#print "file: DkMath.Lib.Algebra.CyclicActionCharacter"

/-!
# 巡回加法群への実際の作用を単元値指標へ変換する

座標 e:ZMod N≃+G のもとで、作用の係数は e⁻¹(ρ(g)(e(1)))。
群作用の合成則から乗法性と可逆性を証明する。恒等作用は係数1と同値。
-/

namespace DkMath.Lib.Algebra.CyclicActionCharacter

noncomputable section
variable {Γ G : Type*} [Group Γ] [AddCommGroup G] {N : ℕ}
    (e : ZMod N ≃+ G) (ρ : Γ →* AddMonoid.End G)

/-- 実際の作用の座標上の係数。 -/
def coefficient (g : Γ) : ZMod N := e.symm (ρ g (e 1))

/-- ZMod の加法自己準同型は、1の像を掛ける写像そのもの。 -/
theorem coordinate_action (g : Γ) (x : G) :
    e.symm (ρ g x) = coefficient e ρ g * e.symm x := by
  let f : ZMod N →+ ZMod N := e.symm.toAddMonoidHom.comp ((ρ g).comp e.toAddMonoidHom)
  have h := (f.toZModLinearMap N).map_smul (e.symm x) (1 : ZMod N)
  change f (e.symm x * 1) = e.symm x * f 1 at h
  rw [mul_one] at h
  change e.symm (ρ g (e (e.symm x))) = e.symm x * coefficient e ρ g at h
  rw [e.apply_symm_apply] at h
  exact h.trans (mul_comm _ _)

/-- 合成される実際の作用の係数は乗法的。 -/
def coefficientHom : Γ →* ZMod N where
  toFun := coefficient e ρ
  map_one' := by simp [coefficient]
  map_mul' g h := by
    change e.symm (ρ (g * h) (e 1)) = _
    rw [map_mul]
    change e.symm (ρ g (ρ h (e 1))) = _
    exact coordinate_action e ρ g (ρ h (e 1))

/-- 群の逆元を写して可逆性を内部証明した、実際の単元値指標。 -/
def character : Γ →* (ZMod N)ˣ := (coefficientHom e ρ).toHomUnits

/-- 指標の値は同じ作用の係数である。 -/
theorem character_coe (g : Γ) : (character e ρ g : ZMod N) = coefficient e ρ g := rfl

/-- 指標が記述する、同じ群のすべての元への実際の作用。 -/
theorem action_eq_nsmul [NeZero N] (g : Γ) (x : G) :
    ρ g x = (character e ρ g : ZMod N).val • x := by
  apply e.symm.injective
  rw [coordinate_action, map_nsmul, nsmul_eq_mul, ZMod.natCast_zmod_val, character_coe]

/-- 任意の自然数の scalar 作用から、同じ指標の値を一意に復元する。 -/
theorem character_eq_natCast_of_action (g : Γ) (a : ℕ)
    (h : ∀ x : G, ρ g x = a • x) : (character e ρ g : ZMod N) = a := by
  rw [character_coe]
  change e.symm (ρ g (e 1)) = _
  have he := congrArg e.symm (h (e 1))
  simpa only [map_nsmul, AddEquiv.symm_apply_apply, nsmul_eq_mul, mul_one] using he

/-- 指標の値1は、すべての点の固定性と正確に同値。群の安定性とは異なる。 -/
theorem character_eq_one_iff (g : Γ) : character e ρ g = 1 ↔ ∀ x : G, ρ g x = x := by
  constructor
  · intro h x
    apply e.symm.injective
    rw [coordinate_action]
    have hc : coefficient e ρ g = 1 := congrArg Units.val h
    rw [hc, one_mul]
  · intro h
    apply Units.ext
    change coefficient e ρ g = 1
    simp only [coefficient, h, AddEquiv.symm_apply_apply]

/-- 座標の選び直しで指標は変わらない。実際の作用を記述する同じ scalar である。 -/
theorem character_independent [NeZero N] (e' : ZMod N ≃+ G) : character e ρ = character e' ρ := by
  apply MonoidHom.ext
  intro g
  apply Units.ext
  have h := character_eq_natCast_of_action e ρ g (character e' ρ g : ZMod N).val
    (action_eq_nsmul e' ρ g)
  simpa only [ZMod.natCast_zmod_val] using h

end
end DkMath.Lib.Algebra.CyclicActionCharacter
