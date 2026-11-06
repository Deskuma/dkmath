/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyCyclicTowerCharacter

#print "file: DkMathTest.FLT.FreyCyclicTowerCharacter"

namespace DkMathTest.FLT.FreyCyclicTowerCharacter

open DkMath.Lib.Algebra DkMath.Lib.NumberTheory
open DkMath.FLT.Frey EllipticTorsionRepresentation CyclotomicKernelField CyclotomicKummerWeight
open DkMath.Lib.RepresentationTheory
noncomputable section

-- A concrete faithful cyclic action. Stability does not mean fixed points.
private def scalarAction : (ZMod 5)ˣ →* AddMonoid.End (ZMod 5) where
  toFun u := AddMonoidHom.mulLeft (u : ZMod 5)
  map_one' := by
    apply AddMonoidHom.ext
    intro x
    exact one_mul x
  map_mul' u v := by
    apply AddMonoidHom.ext
    intro x
    change ((u * v : (ZMod 5)ˣ) : ZMod 5) * x = (u : ZMod 5) * ((v : ZMod 5) * x)
    rw [Units.val_mul, mul_assoc]

private theorem scalar_character (u : (ZMod 5)ˣ) :
    CyclicActionCharacter.character (AddEquiv.refl (ZMod 5)) scalarAction u = u := by
  apply Units.ext
  change (u : ZMod 5) * 1 = (u : ZMod 5)
  exact mul_one _

private def negCoordinates : ZMod 5 ≃+ ZMod 5 where
  toFun x := -x
  invFun x := -x
  left_inv x := neg_neg x
  right_inv x := neg_neg x
  map_add' x y := neg_add x y

example : (∀ x : ZMod 5, scalarAction (-1) x ∈ (⊤ : AddSubgroup (ZMod 5))) ∧
    CyclicActionCharacter.character (AddEquiv.refl (ZMod 5)) scalarAction (-1) ≠ 1 := by
  refine ⟨fun _ => trivial, ?_⟩
  rw [scalar_character]
  decide
example : scalarAction (-1) 1 ≠ (1 : ZMod 5) := by
  change (-1 : ZMod 5) * 1 ≠ 1
  decide
example : CyclicActionCharacter.character (AddEquiv.refl (ZMod 5)) scalarAction =
    CyclicActionCharacter.character negCoordinates scalarAction :=
  CyclicActionCharacter.character_independent _ _ _
example (u : (ZMod 5)ˣ) : CyclicActionCharacter.character negCoordinates scalarAction u = u := by
  rw [← CyclicActionCharacter.character_independent (AddEquiv.refl (ZMod 5)) scalarAction negCoordinates]
  exact scalar_character u

variable {p : ℕ} [Fact p.Prime] (S : Source p)
local instance : S.rationalCurve.IsElliptic := S.rationalCurve_isElliptic
variable (L : Submodule (ZMod p) S.ResidualSpace)
    (hline : Module.finrank (ZMod p) L = 1)
    (hcofixed : IsCofixedOn S.residualRepresentation L)

-- Individual-stage character facts need no hclass/hbad.
example {n : ℕ} (T : S.ResidualCyclicStage L n) :
    IsOpen (T.character.ker : Set (Field.absoluteGaloisGroup ℚ)) := T.character_kernel_isOpen
example {n : ℕ} (T : S.ResidualCyclicStage L n) (σ : Field.absoluteGaloisGroup ℚ) :
    Units.map (ZMod.castHom (dvd_pow_self p (by omega : n + 1 ≠ 0)) (ZMod p)).toMonoidHom
      (T.character σ) = CyclotomicRootModule.cyclotomicCharacter p σ :=
  T.character_mod_prime hline hcofixed σ

variable {ζ : AlgebraicClosure ℚ} (hζ : IsPrimitiveRoot ζ p) (hp5 : 5 ≤ p)
local instance : NumberField (rootField ζ) := rootField_numberField ζ
variable
    (hclass : ∀ a : CyclotomicClassVanishing.ClassModP (rootField ζ) p,
      (∀ γ : (rootField ζ) ≃ₐ[ℚ] (rootField ζ),
        CyclotomicClassVanishing.classModPAction p γ a =
          (baseCharacter hζ γ : ZMod p) ^ 2 • a) → a = 0)
    (hbad : ∀ (n : ℕ) (T : S.ResidualCyclicStage L n), S.ResonantAbsorptionAt T.carrier)
local notation "tower" => S.residualCyclicTower L hline hcofixed hζ hp5 hclass hbad

-- Check compatibility over TWO stages, with the SAME ambient action and residue map.
example (n : ℕ) (σ : Field.absoluteGaloisGroup ℚ) :
    Units.map (ZMod.castHom (pow_dvd_pow p (by omega : n + 1 ≤ (n + 2) + 1))
      (ZMod (p ^ (n + 1)))).toMonoidHom ((tower (n + 2)).character σ) = (tower n).character σ :=
  (tower n).character_compatible (tower (n + 2)) (by omega)
    (S.residualCyclicTower_monotone L hline hcofixed hζ hp5 hclass hbad (by omega)) σ

-- Fixed-point criterion does not prove that Frobenius has character value 1.
example (n : ℕ) (σ : Field.absoluteGaloisGroup ℚ) :
    (tower n).character σ = 1 ↔ ∀ x ∈ (tower n).carrier, pointAction S.rationalCurve σ x = x :=
  (tower n).character_eq_one_iff σ

#print axioms CyclicActionCharacter.character
#print axioms CyclicActionCharacter.action_eq_nsmul
#print axioms CyclicActionCharacter.character_eq_one_iff
#print axioms CyclicActionCharacter.character_independent
#print axioms Source.ResidualCyclicStage.character_spec
#print axioms Source.ResidualCyclicStage.character_eq_one_iff
#print axioms Source.ResidualCyclicStage.character_kernel_isOpen
#print axioms Source.ResidualCyclicStage.character_compatible
#print axioms Source.ResidualCyclicStage.character_mod_prime
#print axioms Source.ResidualCyclicStage.card_le_good_points_of_character_one
#print axioms Source.residualCyclicTowerCharacter_compatible

end
end DkMathTest.FLT.FreyCyclicTowerCharacter
