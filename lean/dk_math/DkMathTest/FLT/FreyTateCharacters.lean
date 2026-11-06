/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyTateCharactersModP

#print "file: DkMathTest.FLT.FreyTateCharacters"

namespace FreyTateCharactersTest
open DkMath.Lib.RepresentationTheory

/-- 非零の上右成分を持つ実際の群準同型。 -/
def exampleAction : (ZMod 25)ˣ →* Matrix (Fin 2) (Fin 2) (ZMod 25) where
  toFun u := !![(u : ZMod 25), 1 - (u : ZMod 25); 0, 1]
  map_one' := by ext i j; fin_cases i <;> fin_cases j <;> simp
  map_mul' u v := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
    all_goals ring

theorem exampleAction_lower (u : (ZMod 25)ˣ) : exampleAction u 1 0 = 0 := rfl

example (u : (ZMod 25)ˣ) : TriangularTwoCharacter.first exampleAction exampleAction_lower u = u := by
  apply Units.ext; rfl

example (u : (ZMod 25)ˣ) : TriangularTwoCharacter.second exampleAction exampleAction_lower u = 1 := by
  apply Units.ext; rfl

def six : (ZMod 25)ˣ := ⟨6, 21, by decide, by decide⟩

/-- 第二指標が1でも、上右成分は零とは限らない。 -/
example : exampleAction six 0 1 ≠ 0 := by
  change 1 - (6 : ZMod 25) ≠ 0
  decide

/-- mod 5 の1は mod 25 の自明性を意味しない。 -/
example : Units.map (ZMod.castHom (by decide : 5 ∣ 25) (ZMod 5)).toMonoidHom six = 1 ∧ six ≠ 1 := by
  constructor
  · apply Units.ext; decide
  · decide

end FreyTateCharactersTest

namespace FreyTateCharactersSourceTest
open DkMath.FLT.Frey DkMath.Lib.Algebra DkMath.Lib.NumberTheory DkMath.Lib.RepresentationTheory
open EllipticTorsionRepresentation PrimePowerTateSequence
noncomputable section
open CyclotomicKernelField CyclotomicKummerWeight
variable {p : ℕ} [Fact p.Prime] (S : Source p)
local instance : S.rationalCurve.IsElliptic := S.rationalCurve_isElliptic
variable (L : Submodule (ZMod p) S.ResidualSpace)
    (hline : Module.finrank (ZMod p) L = 1)
    (hcofixed : IsCofixedOn S.residualRepresentation L)
    {ζ : AlgebraicClosure ℚ} (hζ : IsPrimitiveRoot ζ p) (hp5 : 5 ≤ p)
local instance : NumberField (rootField ζ) := rootField_numberField ζ
variable
    (hclass : ∀ a : CyclotomicClassVanishing.ClassModP (rootField ζ) p,
      (∀ γ : (rootField ζ) ≃ₐ[ℚ] (rootField ζ),
        CyclotomicClassVanishing.classModPAction p γ a =
          (baseCharacter hζ γ : ZMod p) ^ 2 • a) → a = 0)
    (hbad : ∀ (n : ℕ) (T : S.ResidualCyclicStage L n), S.ResonantAbsorptionAt T.carrier)
local notation "d" => S.residualTateSecondCharacter L hline hcofixed hζ hp5 hclass hbad
local notation "chi" => S.residualPadicTowerCharacter L hline hcofixed hζ hp5 hclass hbad
local notation "mat" => S.residualTateActionMatrix L hline hcofixed hζ hp5 hclass hbad

/-- 実際の第二単元値指標は逆 Galois 元で逆元を返す。 -/
example (σ : Field.absoluteGaloisGroup ℚ) : d σ * d σ⁻¹ = 1 := by simp

/-- 非対角の積公式を逆元と合成すると実際の零成分へ戻る。 -/
example (σ : Field.absoluteGaloisGroup ℚ) :
    (chi σ : ℤ_[p]) * mat σ⁻¹ 0 1 + mat σ 0 1 * (d σ⁻¹ : ℤ_[p]) = 0 := by
  rw [← S.residualTate_offDiagonal_mul L hline hcofixed hζ hp5 hclass hbad]
  simp [Source.residualTateActionMatrix]

/-- 元の Cofixed 条件を使った、同じ第二指標の有限剰余。 -/
example (σ : Field.absoluteGaloisGroup ℚ) :
    Units.map (Source.tateResidueModP (p := p)).toMonoidHom (d σ) = 1 :=
  S.residualTateSecondCharacter_mod_prime L hline hcofixed hζ hp5 hclass hbad σ

end
end FreyTateCharactersSourceTest

#print axioms DkMath.Lib.RepresentationTheory.TriangularTwoCharacter.second
#print axioms DkMath.Lib.RepresentationTheory.TriangularTwoCharacter.offDiagonal_mul
#print axioms DkMath.Lib.RepresentationTheory.TriangularTwoCharacter.determinant
#print axioms DkMath.Lib.Algebra.PadicCharacterLimit.continuous_of_reduction_kernels
#print axioms DkMath.FLT.Frey.Source.residualTateMatrixRepresentation
#print axioms DkMath.FLT.Frey.Source.residualTateMatrix_first_character
#print axioms DkMath.FLT.Frey.Source.residualTateSecondCharacter
#print axioms DkMath.FLT.Frey.Source.residualTateSecond_coordinate
#print axioms DkMath.FLT.Frey.Source.residualTateSecondCharacter_finite_kernel
#print axioms DkMath.FLT.Frey.Source.residualTateSecondCharacter_finite_kernel_isOpen
#print axioms DkMath.FLT.Frey.Source.residualTateSecondCharacter_continuous
#print axioms DkMath.FLT.Frey.Source.residualTate_offDiagonal_mul
#print axioms DkMath.FLT.Frey.Source.residualTate_determinant
#print axioms DkMath.FLT.Frey.Source.residualTateSecondCharacter_mod_prime
#print axioms DkMath.FLT.Frey.Source.residualTate_determinant_mod_prime
