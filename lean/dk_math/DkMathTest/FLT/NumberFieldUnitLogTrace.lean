/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.NumberTheory.NumberFieldUnitLogTrace
import DkMath.Lib.NumberTheory.CyclotomicOmegaSquareUnitRank
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed

#print "file: DkMathTest.FLT.NumberFieldUnitLogTrace"

namespace DkMathTest.FLT.NumberFieldUnitLogTrace

open DkMath.Lib.NumberTheory
open NumberFieldUnitGaloisTrace NumberFieldUnitLogTrace NumberFieldUnitPowerDimension
open CyclotomicKernelField CyclotomicKummerWeight CyclotomicOmegaSquareProjector
open CyclotomicOmegaSquareUnitRank KummerSelmerExact
open NumberField NumberField.Units
open scoped NumberField
noncomputable section

-- Matrix trace of actual coordinate permutations: fixed points, not permutation order.
example : LinearMap.trace ℝ (InfinitePlace ℚ → ℝ)
    (LinearMap.funLeft ℝ ℝ (fun w => w)) = Nat.card (InfinitePlace ℚ) := by
  rw [trace_funLeft]
  exact_mod_cast Nat.card_congr (Equiv.subtypeUnivEquiv (fun _ => rfl))

-- A permutation of three coordinates has trace 1 if it fixes only the third coordinate.
example : LinearMap.trace ℝ (Fin 3 → ℝ)
    (LinearMap.funLeft ℝ ℝ (Equiv.swap (0 : Fin 3) 1)) = 1 := by
  rw [LinearMap.trace_eq_matrix_trace ℝ (Pi.basisFun ℝ (Fin 3))]
  norm_num [Matrix.trace, Matrix.diag, LinearMap.toMatrix_apply, LinearMap.funLeft_apply,
    Pi.basisFun_apply, Pi.basisFun_repr, Pi.single_apply, Fin.sum_univ_succ, Equiv.swap_apply_def]
  decide

namespace Five

local instance : Fact (Nat.Prime 5) := ⟨by decide⟩
private def ζ : AlgebraicClosure ℚ :=
  (HasEnoughRootsOfUnity.exists_primitiveRoot (AlgebraicClosure ℚ) 5).choose
private theorem hζ : IsPrimitiveRoot ζ 5 :=
  (HasEnoughRootsOfUnity.exists_primitiveRoot (AlgebraicClosure ℚ) 5).choose_spec
local instance : NumberField (rootField ζ) := rootField_numberField ζ

private def two : (ZMod 5)ˣ := Units.mk0 2 (by decide)

-- Actual nontrivial Galois element acts by its character on ALL fifth roots in O_F.
example (x : 𝓞 (rootField ζ)) (hx : x ^ 5 = 1) :
    (CyclotomicKummerEquivariance.integerAut ((characterEquiv hζ).symm two)).integers x = x ^ 2 :=
  integerAut_on_pth_roots hζ two x hx

-- The actual weighted logarithm commutes with that same nontrivial global action.
example (u : (𝓞 (rootField ζ))ˣ) :
    logFull (rootField ζ) (Additive.ofMul (unitsMap (rootField ζ) ((characterEquiv hζ).symm two) u)) =
      permL (rootField ζ) ((characterEquiv hζ).symm two) (logFull (rootField ζ) (Additive.ofMul u)) :=
  logFull_unitsMap (rootField ζ) ((characterEquiv hζ).symm two) u

-- Integer free trace and mod-5 total trace refer to the SAME field and automorphism.
example : LinearMap.trace ℤ _ (quotMapLin (rootField ζ) ((characterEquiv hζ).symm two)) =
    (Nat.card {w : InfinitePlace (rootField ζ) // (characterEquiv hζ).symm two • w = w} : ℤ) - 1 :=
  trace_quotMap_eq (rootField ζ) ((characterEquiv hζ).symm two)

example : LinearMap.trace (ZMod 5) _ (unitAction (p := 5) ((characterEquiv hζ).symm two)) =
    2 + (Nat.card {w : InfinitePlace (rootField ζ) // (characterEquiv hζ).symm two • w = w} : ZMod 5) - 1 :=
  trace_unitAction_eq_character_add_fixedPlaces hζ two

-- Identity total trace uses the proved actual quotient dimension 2.
example : LinearMap.trace (ZMod 5) _ (unitAction (p := 5) (1 : (rootField ζ) ≃ₐ[ℚ] (rootField ζ))) = 2 := by
  rw [map_one]
  change LinearMap.trace (ZMod 5) _ LinearMap.id = 2
  rw [LinearMap.trace_id, root_unitClass_finrank hζ (by decide)]
  norm_num

end Five

#print axioms unitsMap_torsion_le
#print axioms quotMap_mk
#print axioms freeUnitAction
#print axioms trace_vMap
#print axioms logFull_eq_zero_iff
#print axioms logQuot_quotMap
#print axioms trace_funLeft
#print axioms trace_quotMap_eq
#print axioms trace_vMap_eq_exponent_add_fixedPlaces
#print axioms integerAut_on_pth_roots
#print axioms trace_unitAction_eq_character_add_fixedPlaces

end
end DkMathTest.FLT.NumberFieldUnitLogTrace
