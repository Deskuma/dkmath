/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.Algebra.TorsionPreimageQuotient
import Mathlib.Algebra.Field.ZMod

namespace DkMathTest.Lib.Algebra.TorsionPreimageQuotient

open DkMath.Lib.Algebra.TorsionPreimageQuotient

abbrev G := ZMod 4 × ZMod 4

def horizontalTwo : AddSubgroup G :=
  ((nsmulAddMonoidHom 2 : ZMod 4 →+ ZMod 4).ker.comap
    (AddMonoidHom.fst (ZMod 4) (ZMod 4))) ⊓
    (AddMonoidHom.snd (ZMod 4) (ZMod 4)).ker

-- The vertical point is 2-torsion in the preimage but is outside K.
def verticalPoint : G := (0, 2)

private theorem vertical_kill : 2 • verticalPoint = 0 := by decide

private theorem vertical_not_mem : verticalPoint ∉ horizontalTwo := by
  change ¬ (2 • verticalPoint.1 = 0 ∧ verticalPoint.2 = 0)
  decide

private theorem vertical_mem_preimage : verticalPoint ∈ preimage 2 horizontalTwo := by
  change 2 • verticalPoint ∈ horizontalTwo
  rw [vertical_kill]
  exact horizontalTwo.zero_mem

private theorem horizontal_mem : ((2, 0) : G) ∈ horizontalTwo := by
  change 2 • (2 : ZMod 4) = 0 ∧ (0 : ZMod 4) = 0
  decide

noncomputable def verticalClass : Quotient 2 horizontalTwo :=
  quotientMap 2 horizontalTwo ⟨verticalPoint, vertical_mem_preimage⟩

example : verticalClass ≠ 0 := by
  intro hz
  have hk := (quotientMap_eq_zero_iff 2 horizontalTwo _).mp hz
  exact vertical_not_mem hk

example : verticalClass ∈ torsionImage 2 horizontalTwo := by
  exact (mem_torsionImage_iff 2 horizontalTwo _).mpr ⟨⟨verticalPoint, vertical_kill⟩, rfl⟩

-- The horizontal point lies in K and its quotient class is zero.
example : quotientMap 2 horizontalTwo
    ⟨((2, 0) : G), (le_preimage 2 horizontalTwo) horizontal_mem⟩ = 0 := by
  exact (quotientMap_eq_zero_iff 2 horizontalTwo _).mpr horizontal_mem

-- The preimage of the zero submodule is exactly the original K.
example : liftSubmodule 2 horizontalTwo ⊥ = horizontalTwo := by
  ext y
  rw [mem_liftSubmodule_iff]
  constructor
  · rintro ⟨hy, hv⟩
    exact (quotientMap_eq_zero_iff 2 horizontalTwo _).mp hv
  · intro hy
    exact ⟨horizontalTwo.nsmul_mem hy 2,
      (quotientMap_eq_zero_iff 2 horizontalTwo _).mpr hy⟩

-- Disjointness from the torsion image is essential: the lift of top contains
-- a new 2-torsion point, so the descent-to-K conclusion would be false there.
example : verticalPoint ∈ liftSubmodule 2 horizontalTwo ⊤ ∧
    2 • verticalPoint = 0 ∧ verticalPoint ∉ horizontalTwo := by
  exact ⟨(mem_liftSubmodule_iff 2 horizontalTwo ⊤ _).mpr ⟨vertical_mem_preimage, trivial⟩,
    vertical_kill, vertical_not_mem⟩

#print axioms card_quotient
#print axioms card_torsionImage_mul_card_kernel
#print axioms card_liftSubmodule
#print axioms torsion_mem_of_lift_disjoint
#print axioms representation_sub_nsmul_mem_torsionImage

end DkMathTest.Lib.Algebra.TorsionPreimageQuotient
