/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyCyclotomicCharacterField

namespace DkMathTest.FLT.FreyCyclotomicCharacterField

open DkMath.Lib.NumberTheory
open CyclotomicRootModule CyclotomicKernelField CyclotomicCharacterField

local instance : Fact (Nat.Prime 5) := ⟨by decide⟩

-- Actual cyclotomic field in the same closure: its degree is 4.
example {ζ : AlgebraicClosure ℚ} (hζ : IsPrimitiveRoot ζ 5) :
    Module.finrank ℚ (rootField ζ) = 4 := by
  simpa only [show 5 - 1 = 4 from rfl] using rootField_finrank hζ

-- Zero characters do not manufacture nontrivial degree-5 extensions.
example {ζ : AlgebraicClosure ℚ} (hζ : IsPrimitiveRoot ζ 5) :
    characterField (1 : (cyclotomicCharacter (K := ℚ) 5).ker →* Multiplicative (ZMod 5)) =
      rootField ζ := characterField_one_eq_rootField hζ

-- In particular that zero-character field has absolute degree 4, not 20.
example {ζ : AlgebraicClosure ℚ} (hζ : IsPrimitiveRoot ζ 5) :
    Module.finrank ℚ
      (characterField (1 : (cyclotomicCharacter (K := ℚ) 5).ker →* Multiplicative (ZMod 5))) ≠ 20 := by
  rw [characterField_one_eq_rootField hζ, rootField_finrank hζ]
  decide

-- Surjectivity onto a trivial codomain must give relative degree 1, not p.
example {ζ : AlgebraicClosure ℚ} (hζ : IsPrimitiveRoot ζ 5) :
    let ψ : (cyclotomicCharacter (K := ℚ) 5).ker →* Multiplicative PUnit := 1
    letI := extensionAlgebra ψ hζ
    Module.finrank (rootField ζ) (characterField ψ) = 1 := by
  let ψ : (cyclotomicCharacter (K := ℚ) 5).ker →* Multiplicative PUnit := 1
  have hopen : IsOpen (ψ.ker : Set (cyclotomicCharacter (K := ℚ) 5).ker) := by
    change IsOpen ((1 : (cyclotomicCharacter (K := ℚ) 5).ker →* Multiplicative PUnit).ker :
      Set (cyclotomicCharacter (K := ℚ) 5).ker)
    rw [MonoidHom.ker_one]
    exact isOpen_univ
  have hs : Function.Surjective ψ := fun z => ⟨1, Subsingleton.elim _ _⟩
  simpa only [Nat.card_unique] using relative_finrank ψ hζ hopen hs

-- The same kernel/field identification preserves both decomposition and inertia membership.
example {ζ : AlgebraicClosure ℚ} (hζ : IsPrimitiveRoot ζ 5)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (g : (cyclotomicCharacter (K := ℚ) 5).ker) :
    kernelEquiv hζ g ∈ ValuationInertia.inertiaSubgroupIn A (rootField ζ) ↔
      g.val ∈ ValuationInertia.inertiaSubgroupIn A ℚ := kernelEquiv_mem_inertia_iff hζ A g

-- The prime 2 boundary is handled by the general field API (index 1).
example : (letI : Fact (Nat.Prime 2) := ⟨by decide⟩;
    (cyclotomicCharacter (K := ℚ) 2).ker.index = 1) := by
  let : Fact (Nat.Prime 2) := ⟨by decide⟩
  exact kernel_index (p := 2)

#check DkMath.FLT.Frey.Source.residual_nonsplit_has_cyclotomic_cyclic_extension
#check DkMath.FLT.Frey.Source.residual_characterField_decomposition_fixed_at_p
#check DkMath.FLT.Frey.Source.residual_characterField_inertia_fixed_away

#print axioms CyclotomicKernelField.fixingSubgroup_eq_kernel
#print axioms CyclotomicKernelField.kernelEquiv_mem_inertia_iff
#print axioms CyclotomicKernelField.kernel_isOpen
#print axioms CyclotomicKernelField.rootField_isCyclotomic
#print axioms CyclotomicKernelField.rootField_finrank
#print axioms CyclotomicCharacterField.kernelInGalois_normal
#print axioms CyclotomicCharacterField.fixingSubgroup_characterField
#print axioms CyclotomicCharacterField.characterField_finrank
#print axioms CyclotomicCharacterField.relative_finrank
#print axioms CyclotomicCharacterField.relative_isGalois
#print axioms CyclotomicCharacterField.relative_isCyclic
#print axioms DkMath.FLT.Frey.Source.residual_nonsplit_has_cyclotomic_cyclic_extension
#print axioms DkMath.FLT.Frey.Source.residual_characterField_decomposition_fixed_at_p
#print axioms DkMath.FLT.Frey.Source.residual_characterField_inertia_fixed_away

end DkMathTest.FLT.FreyCyclotomicCharacterField
