/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyCyclotomicExtensionCharacter

namespace DkMathTest.FLT.FreyCyclotomicExtensionCharacter

open DkMath.Lib.RepresentationTheory
open FixedLineExtension

-- The affine group of order 20, acting as [[1,b],[0,a]].
-- A diagonal subgroup has a stable complement, while the full group does not.
private abbrev F := ZMod 5
private abbrev V := F × F
local instance : Fact (Nat.Prime 5) := ⟨by decide⟩

private structure Aff where
  b : F
  a : Fˣ
  deriving DecidableEq, Fintype

@[ext] private theorem aff_ext {g h : Aff} (hb : g.b = h.b) (ha : g.a = h.a) : g = h := by
  cases g
  cases h
  cases hb
  cases ha
  rfl

private instance : Group Aff where
  one := ⟨0, 1⟩
  mul g h := ⟨h.b + g.b * (h.a : F), g.a * h.a⟩
  inv g := ⟨-g.b * (g.a⁻¹ : F), g.a⁻¹⟩
  mul_assoc g h k := by
    apply aff_ext
    · change k.b + (h.b + g.b * (h.a : F)) * (k.a : F) =
        (k.b + h.b * (k.a : F)) + g.b * ((h.a * k.a : Fˣ) : F)
      rw [Units.val_mul]
      ring
    · exact mul_assoc _ _ _
  one_mul g := by
    apply aff_ext
    · change g.b + 0 * (g.a : F) = g.b
      ring
    · exact one_mul _
  mul_one g := by
    apply aff_ext
    · change 0 + g.b * (1 : F) = g.b
      ring
    · exact mul_one _
  inv_mul_cancel g := by
    apply aff_ext
    · change g.b + (-g.b * (g.a⁻¹ : F)) * (g.a : F) = 0
      rw [mul_assoc, inv_mul_cancel₀ (Units.ne_zero g.a), mul_one, add_neg_cancel]
    · exact inv_mul_cancel _

private def chi : Aff →* Fˣ where
  toFun := Aff.a
  map_one' := rfl
  map_mul' _ _ := rfl

private def rho : Representation F Aff V where
  toFun g := {
    toFun v := (v.1 + g.b * v.2, (g.a : F) * v.2)
    map_add' v w := by ext <;> dsimp <;> ring
    map_smul' c v := by ext <;> dsimp <;> ring }
  map_one' := by
    apply LinearMap.ext
    intro v
    apply Prod.ext
    · change v.1 + 0 * v.2 = v.1
      ring
    · change 1 * v.2 = v.2
      ring
  map_mul' g h := by
    apply LinearMap.ext
    intro v
    apply Prod.ext
    · change v.1 + (h.b + g.b * (h.a : F)) * v.2 =
        (v.1 + h.b * v.2) + g.b * ((h.a : F) * v.2)
      ring
    · change ((g.a * h.a : Fˣ) : F) * v.2 = (g.a : F) * ((h.a : F) * v.2)
      rw [Units.val_mul, mul_assoc]

private def C : Submodule F V := LinearMap.ker (LinearMap.snd F F F)
private def D : Submodule F V := LinearMap.ker (LinearMap.fst F F F)

private theorem fixed : IsFixedOn rho C := by
  intro g v hv
  change v.2 = 0 at hv
  change (v.1 + g.b * v.2, (g.a : F) * v.2) = v
  ext <;> simp [hv]

private theorem quotient_character (g : Aff) (v : V) : rho g v - (chi g : F) • v ∈ C := by
  change (g.a : F) * v.2 - (chi g : F) * v.2 = 0
  exact sub_self _

private theorem axes_complement : IsCompl C D := by
  apply IsCompl.of_eq
  · rw [Submodule.eq_bot_iff]
    intro v hv
    change v.2 = 0 ∧ v.1 = 0 at hv
    exact Prod.ext hv.2 hv.1
  · rw [Submodule.eq_top_iff']
    intro v
    exact Submodule.mem_sup.mpr ⟨(v.1, 0), rfl, (0, v.2), rfl, by ext <;> simp⟩

private def shear : Aff := ⟨1, 1⟩
private def twoUnit : Fˣ := ⟨2, 3, by decide, by decide⟩
private def diagonalTwo : Aff := ⟨0, twoUnit⟩

example : Fintype.card Aff = 20 := by decide

-- The explicitly constructed eigenspace really is a complement for diag(1,2).
example : IsCompl C (LinearMap.ker
    (rho diagonalTwo - (2 : F) • (1 : Module.End F V))) := by
  exact isCompl_eigenKernel rho C chi fixed quotient_character
    (t := diagonalTwo) (by decide)

-- This tests a nontrivial character, not the degenerate chi=1 case.
example : ∃ g : Aff, (chi g : F) ≠ 1 := by
  refine ⟨diagonalTwo, ?_⟩
  decide

-- Every diagonal element preserves D; local splitting by itself does not imply global splitting.
example : IsCompl C D ∧ ∀ g : Aff, g.b = 0 → ∀ v ∈ D, rho g v ∈ D := by
  refine ⟨axes_complement, ?_⟩
  intro g hg v hv
  change v.1 = 0 at hv
  change v.1 + g.b * v.2 = 0
  rw [hv, hg, zero_mul, add_zero]

-- A shear lies in ker chi and acts nontrivially; the entire group admits no stable complement.
example : ¬ ∃ U : Submodule F V, IsCompl C U ∧ IsStable rho U := by
  rintro ⟨U, hCU, hU⟩
  have he := eq_one_of_complement rho C chi fixed quotient_character U hCU (hU shear) (by rfl)
  have h := congrArg (fun f : Module.End F V => (f (0, 1)).1) he
  exact (by decide : (1 : F) ≠ 0) h

-- The constructed character sees precisely this obstruction and surjects onto the fixed line.
example : Function.Surjective (deviationAt rho C chi fixed quotient_character ((0, 1) : V)) := by
  intro z
  refine ⟨⟨⟨z.toAdd.val.1, 1⟩, rfl⟩, ?_⟩
  apply Subtype.ext
  have hz : z.toAdd.val.2 = 0 := z.toAdd.property
  change (rho (⟨z.toAdd.val.1, 1⟩ : Aff)) ((0, 1) : V) - ((0, 1) : V) = z.toAdd.val
  apply Prod.ext <;> simp [rho, hz]

-- Actual scalar direction: conjugation by diag(1,2) multiplies the shear deviation by 2^-1.
example :
    (deviationAt rho C chi fixed quotient_character ((0, 1) : V)
      ⟨diagonalTwo * shear * diagonalTwo⁻¹,
        by
          change chi (diagonalTwo * shear * diagonalTwo⁻¹) = 1
          simp only [map_mul, map_inv, show chi shear = 1 from rfl, mul_one, mul_inv_cancel]⟩).toAdd.val = (3, 0) := by
  decide +kernel

#check DkMath.FLT.Frey.Source.residual_cyclic_extension_splits_iff_character_trivial
#check DkMath.FLT.Frey.Source.residual_cyclic_extension_nonsplit_has_surjective_character
#check DkMath.FLT.Frey.Source.residual_cyclic_tower_step_of_character_trivial

#print axioms FixedLineExtension.isCompl_eigenKernel
#print axioms FixedLineExtension.stable_complement_iff_kernel_trivial
#print axioms FixedLineExtension.deviationHom
#print axioms FixedLineExtension.deviation_conjugate
#print axioms FixedLineExtension.deviationAt
#print axioms FixedLineExtension.kernel_trivial_iff_deviationAt_trivial
#print axioms DkMath.FLT.Frey.Source.residualCyclicExtensionCharacter
#print axioms DkMath.FLT.Frey.Source.residual_cyclic_extension_character_at_p
#print axioms DkMath.FLT.Frey.Source.residual_cyclic_extension_character_conjugate
#print axioms DkMath.FLT.Frey.Source.residual_cyclic_extension_character_kernel_isOpen
#print axioms DkMath.FLT.Frey.Source.residual_cyclic_extension_character_range_card_le
#print axioms DkMath.FLT.Frey.Source.residual_cyclic_extension_character_inertia_away
#print axioms DkMath.FLT.Frey.Source.residual_cyclic_extension_splits_iff_character_trivial
#print axioms DkMath.FLT.Frey.Source.residual_cyclic_extension_nonsplit_has_surjective_character
#print axioms DkMath.FLT.Frey.Source.residual_cyclic_tower_step_of_character_trivial

end DkMathTest.FLT.FreyCyclotomicExtensionCharacter
