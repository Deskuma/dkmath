/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyCyclotomicClassVanishing

#print "file: DkMathTest.FLT.FreyCyclotomicClassVanishing"

namespace DkMathTest.FLT.FreyCyclotomicClassVanishing

open DkMath.Lib.Algebra FiniteEigenTorsionBridge
open DkMath.Lib.NumberTheory CyclotomicRootModule CyclotomicKernelField
open CyclotomicKummerEquivariance CyclotomicClassVanishing
set_option backward.isDefEq.respectTransparency false
noncomputable section

local instance : Fact (Nat.Prime 3) := ⟨by decide⟩

-- The natural map really kills a nonzero p-torsion element in Z/p².
example : (3 : ZMod 9) ≠ 0 ∧ 3 • (3 : ZMod 9) = 0 ∧
    ((3 : ZMod 9) : ModQuotient 3 (ZMod 9)) = 0 := by
  refine ⟨by decide +kernel, by decide +kernel, ?_⟩
  exact (QuotientAddGroup.eq_zero_iff _).mpr ⟨1, by decide +kernel⟩

-- The Fitting kernel lemma applies to an actual finite endomorphism, not a quotient injection.
example (x : ZMod 9) (hp : 3 • x = 0) (hf : 2 • x = 0) : x = 0 := by
  apply torsion_kernel_eq_zero 3 (nsmulAddMonoidHom 2) _ x hp hf
  intro a ha
  obtain ⟨b, hb⟩ := ha
  refine ⟨2 • b - a, ?_⟩
  change 3 • b = 2 • a at hb
  calc
    3 • (2 • b - a) = 2 • (3 • b) - 3 • a := by rw [nsmul_sub, smul_comm 3 2 b]
    _ = 2 • (2 • a) - 3 • a := by rw [hb]
    _ = a := by simp only [succ_nsmul, zero_nsmul]; abel

private abbrev Γ := (ZMod 3)ˣ
private def trivialAction : Γ →* (ZMod 9 ≃ₗ[ℤ] ZMod 9) := 1
private def character : Γ →* (ZMod 3)ˣ := MonoidHom.id _

private theorem trivial_quotient (g : Γ) (v : ModQuotient 3 (ZMod 9)) :
    quotientAction 3 trivialAction g v = v := by
  refine Quotient.inductionOn v (fun a => ?_)
  rfl

-- The nontrivial character has zero eigenspace on this actual mod-3 quotient.
private theorem quotient_eigen_zero (v : ModQuotient 3 (ZMod 9))
    (h : ∀ g : Γ, quotientAction 3 trivialAction g v = (character g : ZMod 3) • v) : v = 0 := by
  have hh := h (-1)
  rw [trivial_quotient] at hh
  change v = (-1 : ZMod 3) • v at hh
  rw [neg_one_smul] at hh
  have htwo : (2 : ZMod 3) • v = 0 := by
    calc
      (2 : ZMod 3) • v = v + v := by
        rw [show (2 : ZMod 3) = 1 + 1 from rfl, add_smul, one_smul]
      _ = v + -v := congrArg (v + ·) hh
      _ = 0 := add_neg_cancel v
  exact ((ZMod.isUnit_iff_coprime 2 3).mpr (by decide)).smul_eq_zero.mp htwo

-- The bridge transports this vanishing to actual 3-torsion in Z/9, without a natural injection.
example (x : ZMod 9) (hp : 3 • x = 0)
    (he : ∀ g : Γ, trivialAction g x = (character g : ZMod 3).val • x) : x = 0 := by
  apply torsion_eigen_eq_zero trivialAction character _ quotient_eigen_zero x hp he
  rw [ZMod.card_units_eq_totient, ZMod.isUnit_iff_coprime]
  decide +kernel

-- The integer lift of the weighted sum need not vanish on the original group.
example : liftedWeightedSum trivialAction character (1 : ZMod 9) = 3 := by
  decide +kernel

private def ζ₃ : AlgebraicClosure ℚ :=
  (HasEnoughRootsOfUnity.exists_primitiveRoot (AlgebraicClosure ℚ) 3).choose
private theorem hζ₃ : IsPrimitiveRoot ζ₃ 3 :=
  (HasEnoughRootsOfUnity.exists_primitiveRoot (AlgebraicClosure ℚ) 3).choose_spec
local instance : NumberField (rootField ζ₃) := rootField_numberField ζ₃

-- The actual root-field Galois order and its invertibility are supplied internally.
example : Nat.card ((rootField ζ₃) ≃ₐ[ℚ] (rootField ζ₃)) = 2 ∧
    IsUnit (Fintype.card ((rootField ζ₃) ≃ₐ[ℚ] (rootField ζ₃)) : ZMod 3) :=
  ⟨root_galois_card hζ₃, root_galois_card_isUnit hζ₃⟩

example : Finite (ClassModP (rootField ζ₃) 3) := inferInstance

-- The quotient action is the descent of the same actual class-group action, on the same class.
example (γ : (rootField ζ₃) ≃ₐ[ℚ] (rootField ζ₃))
    (c : ClassGroup (NumberField.RingOfIntegers (rootField ζ₃))) :
    classModPAction 3 γ (Additive.ofMul c : ClassModP (rootField ζ₃) 3) =
      (Additive.ofMul (classGroupAction γ c) : ClassModP (rootField ζ₃) 3) := rfl

#print axioms torsion_kernel_eq_zero
#print axioms weightedSum_eigen
#print axioms liftedWeightedSum_quotient
#print axioms liftedWeightedSum_torsion
#print axioms torsion_eigen_eq_zero
#print axioms classTorsion_eq_one_of_quotient_eigen_vanishing
#print axioms root_galois_card
#print axioms root_galois_card_isUnit
#print axioms classImage_eq_one_of_quotient_weight_square_vanishing
#print axioms DkMath.FLT.Frey.Source.residual_kummer_classImage_eq_one_of_quotient_vanishing
#print axioms DkMath.FLT.Frey.Source.residual_kummer_unit_weight_square_of_quotient_vanishing

end
end DkMathTest.FLT.FreyCyclotomicClassVanishing
