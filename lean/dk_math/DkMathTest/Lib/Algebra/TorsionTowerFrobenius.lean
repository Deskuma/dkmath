/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.Algebra.TorsionTowerFrobenius
import DkMath.Lib.NumberTheory.EllipticTorsionTowerObstruction
import Mathlib.Algebra.Field.ZMod

namespace DkMathTest.Lib.Algebra.TorsionTowerFrobenius

open DkMath.Lib.Algebra.TorsionTowerFrobenius
open DkMath.Lib.NumberTheory.EllipticTorsionRepresentation

-- A genuine finite model of the characteristic relation with negative
-- coefficient ell+1-N = -2.  Both fixed-mod-K and the relation are checked.
example (y : ZMod 5) : 5 • y ∈ (⊥ : AddSubgroup (ZMod 5)) := by
  apply nsmul_mem_of_frobenius_relation (⊥ : AddSubgroup (ZMod 5))
    (AddMonoidHom.id (ZMod 5)) 5 5 2
  · intro x _
    simp only [AddMonoidHom.id_apply, sub_self, AddSubgroup.zero_mem]
  · have hall : ∀ x : ZMod 5, x + (2 : ℤ) • x = (2 + 1 - (5 : ℤ)) • x := by decide
    exact fun x _ => hall x
  · have hall : ∀ x : ZMod 5, 5 • x = 0 := by decide
    exact hall y

-- A nontrivial prime-to-3 scalar may be cancelled in a subgroup, with
-- Bezout coefficients in Z.  No division operation on the group is assumed.
example : (2 : ZMod 6) ∈ AddSubgroup.zmultiples (2 : ZMod 6) := by
  apply mem_of_coprime_nsmul (AddSubgroup.zmultiples (2 : ZMod 6))
    (by decide : Nat.Coprime 2 3) (by decide : 3 • (2 : ZMod 6) = 0)
  exact ⟨2, by decide⟩

#print axioms nsmul_mem_of_frobenius_relation
#print axioms prime_torsion_mem_of_scalar_absorbs
#print axioms false_of_rank_two_scalar_absorbs
#print axioms false_of_prime_torsion_tower_scalar_absorbs
#print axioms false_of_prime_torsion_tower_frobenius

end DkMathTest.Lib.Algebra.TorsionTowerFrobenius
