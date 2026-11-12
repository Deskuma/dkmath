/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyCyclotomicKummer
import Mathlib.FieldTheory.Finite.GaloisField

namespace DkMathTest.FLT.FreyCyclotomicKummer

open DkMath.Lib.NumberTheory CyclicKummer
noncomputable section

local instance : Fact (Nat.Prime 3) := ⟨by decide⟩

private theorem roots_two : (primitiveRoots 2 (ZMod 3)).Nonempty :=
  ⟨-1, (mem_primitiveRoots (by decide)).mpr (IsPrimitiveRoot.neg_one 3 (by decide))⟩

-- An actual extension F_9/F_3, including the even prime boundary, supplies its own radical.
example : Nonempty (Presentation 2 (ZMod 3) (GaloisField 3 2)) :=
  CyclicKummer.exists_presentation (GaloisField.finrank 3 (by decide)) roots_two

-- The constructed constant must be the unique nonsquare 2 in F_3, not merely nonzero.
example : ∃ P : Presentation 2 (ZMod 3) (GaloisField 3 2), P.constant = 2 := by
  obtain ⟨P⟩ := CyclicKummer.exists_presentation (M := GaloisField 3 2)
    (GaloisField.finrank 3 (by decide)) roots_two
  have h : ∀ b : ZMod 3, (∀ c : ZMod 3, c ^ 2 ≠ b) → b = 2 := by decide +kernel
  exact ⟨P, h P.constant (P.constant_not_pow (by decide))⟩

-- Nontrivial automorphisms of the actual degree-2 field move the chosen same radical.
example (P : Presentation 2 (ZMod 3) (GaloisField 3 2)) :
    ∃ σ : (GaloisField 3 2) ≃ₐ[ZMod 3] (GaloisField 3 2), σ P.radical ≠ P.radical := by
  let η : rootsOfUnity 2 (ZMod 3) := (IsPrimitiveRoot.neg_one 3 (by decide)).toRootsOfUnity
  have hη : η ≠ 1 := by
    intro h
    have he := congrArg (fun u : rootsOfUnity 2 (ZMod 3) => (u.val : ZMod 3)) h
    change (-1 : ZMod 3) = 1 at he
    exact (by decide : (-1 : ZMod 3) ≠ 1) he
  let e := P.autEquivRoots (GaloisField.finrank 3 (by decide)) roots_two
  refine ⟨e.symm η, fun h => hη ?_⟩
  have he := congrArg e ((P.aut_fix_radical_iff _).mp h)
  simpa only [e.apply_symm_apply, map_one] using he

-- A trivial extension cannot carry such an irreducible degree-2 presentation.
example : ¬ Nonempty (Presentation 2 (ZMod 3) (ZMod 3)) := by
  rintro ⟨P⟩
  exact P.constant_not_pow (by decide) P.radical P.radical_pow

-- The degree-1 case does exist, and its constant is a first power. The n != 1 guard matters.
example : ∃ P : Presentation 1 ℚ ℚ, ∃ b : ℚ, b ^ 1 = P.constant := by
  have hroots : (primitiveRoots 1 ℚ).Nonempty :=
    ⟨1, (mem_primitiveRoots (by decide)).mpr (IsPrimitiveRoot.one_right_iff.mpr rfl)⟩
  obtain ⟨P⟩ := CyclicKummer.exists_presentation (M := ℚ) (Module.finrank_self ℚ) hroots
  exact ⟨P, P.constant, pow_one _⟩

#print axioms CyclicKummer.exists_presentation
#print axioms Presentation.constant_not_pow
#print axioms Presentation.constant_ne_zero
#print axioms Presentation.radical_ne_zero
#print axioms Presentation.algHom_ext
#print axioms Presentation.aut_fix_radical_iff
#print axioms Presentation.isSplittingField
#print axioms Presentation.autEquivRoots
#print axioms Presentation.autEquivRoots_smul
#print axioms Presentation.autEquivRoots_ratio
#print axioms CyclotomicCharacterKummer.rootField_primitiveRoots
#print axioms CyclotomicCharacterKummer.exists_presentation
#print axioms CyclotomicCharacterKummer.character_eq_one_iff_fix_radical
#print axioms DkMath.FLT.Frey.Source.residual_nonsplit_has_kummer_presentation
#print axioms DkMath.FLT.Frey.Source.residual_character_eq_one_iff_fix_kummer_radical
#print axioms DkMath.FLT.Frey.Source.residual_kummer_radical_decomposition_fixed_at_p
#print axioms DkMath.FLT.Frey.Source.residual_kummer_radical_inertia_fixed_away

end
end DkMathTest.FLT.FreyCyclotomicKummer
