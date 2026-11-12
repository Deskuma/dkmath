/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyCyclotomicUnitSplit
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed

#print "file: DkMathTest.FLT.CyclotomicUnitClosure"

namespace DkMathTest.FLT.CyclotomicUnitClosure

open DkMath.Lib.NumberTheory
open CyclotomicInfinitePlaceFixed CyclotomicOmegaSquareTrace
open CyclotomicKernelField CyclotomicKummerWeight CyclotomicOmegaSquareProjector
open CyclotomicPrimaryUnitSpace KummerSelmerExact NumberField
open scoped NumberField
noncomputable section

namespace Five

local instance : Fact (Nat.Prime 5) := ⟨by decide⟩
private def ζ : AlgebraicClosure ℚ :=
  (HasEnoughRootsOfUnity.exists_primitiveRoot (AlgebraicClosure ℚ) 5).choose
private theorem hζ : IsPrimitiveRoot ζ 5 :=
  (HasEnoughRootsOfUnity.exists_primitiveRoot (AlgebraicClosure ℚ) 5).choose_spec
local instance : NumberField (rootField ζ) := rootField_numberField ζ
private def two : (ZMod 5)ˣ := Units.mk0 2 (by decide)
private def three : (ZMod 5)ˣ := Units.mk0 3 (by decide)

-- Galois inverse is kept explicit: inverse character of 2 is 3, not 2.
example : ((characterEquiv hζ).symm two).symm (baseRoot ζ) = baseRoot ζ ^ 3 := by
  have he : two⁻¹ = three := inv_eq_of_mul_eq_one_right (by decide)
  have h := symm_symm_apply_zeta hζ two
  rw [he, show (three : ZMod 5).val = 3 from by decide] at h
  exact h

example : Nat.card {w : InfinitePlace (rootField ζ) // (characterEquiv hζ).symm 1 • w = w} = 2 := by
  simpa using card_fixedPlaces_prime hζ (by decide) 1
example : Nat.card {w : InfinitePlace (rootField ζ) // (characterEquiv hζ).symm (-1) • w = w} = 2 := by
  simpa using card_fixedPlaces_prime hζ (by decide) (-1)
example : Nat.card {w : InfinitePlace (rootField ζ) // (characterEquiv hζ).symm two • w = w} = 0 := by
  rw [card_fixedPlaces_prime hζ (by decide)]
  have hn : ¬ (two = 1 ∨ two = -1) := by decide
  simp only [hn, ite_false]
example (w : InfinitePlace (rootField ζ)) : (characterEquiv hζ).symm two • w ≠ w := by
  intro hw
  have hn : ¬ (two = 1 ∨ two = -1) := by decide
  exact hn ((smul_infinitePlace_eq_self_iff hζ (by decide) two w).mp hw)

-- Same actual action: fixed ALL complex places at -1 does not mean trace equals dimension.
example : LinearMap.trace (ZMod 5) _ (unitAction (p := 5) ((characterEquiv hζ).symm (-1))) = 0 := by
  rw [trace_unitAction hζ (by decide)]
  norm_num
example : LinearMap.trace (ZMod 5) _ (unitAction (p := 5) ((characterEquiv hζ).symm two)) = 1 := by
  rw [trace_unitAction hζ (by decide)]
  have hn : ¬ (two = 1 ∨ two = -1) := by decide
  simp only [hn, ite_false, add_zero]
  decide

-- These conclusions no longer take trace/rank/unit-vanishing hypotheses.
example : LinearMap.trace (ZMod 5) _ (omegaSquareProjector hζ) = 1 :=
  trace_omegaSquareProjector hζ (by decide)
example : Module.finrank (ZMod 5) (weightSquareSpace hζ) = 1 :=
  weightSquareSpace_finrank_eq_one hζ (by decide)
example : primaryWeightSquareSpace hζ = ⊥ := primaryWeightSquareSpace_eq_bot hζ (by decide)
example (u : (𝓞 (rootField ζ))ˣ)
    (hu : Additive.ofMul (u : UnitClass (𝓞 (rootField ζ)) 5) ∈ primaryWeightSquareSpace hζ) :
    ∃ a : (𝓞 (rootField ζ))ˣ, a ^ 5 = u := exists_global_unit_pow_of_primary hζ (by decide) u hu

end Five

namespace Seven

local instance : Fact (Nat.Prime 7) := ⟨by decide⟩
private def ζ : AlgebraicClosure ℚ :=
  (HasEnoughRootsOfUnity.exists_primitiveRoot (AlgebraicClosure ℚ) 7).choose
private theorem hζ : IsPrimitiveRoot ζ 7 :=
  (HasEnoughRootsOfUnity.exists_primitiveRoot (AlgebraicClosure ℚ) 7).choose_spec
local instance : NumberField (rootField ζ) := rootField_numberField ζ

example : Nat.card {w : InfinitePlace (rootField ζ) // (characterEquiv hζ).symm (-1) • w = w} = 3 := by
  simpa using card_fixedPlaces_prime hζ (by decide) (-1)
example : LinearMap.trace (ZMod 7) _ (omegaSquareProjector hζ) = 1 :=
  trace_omegaSquareProjector hζ (by decide)
example : Module.finrank (ZMod 7) (weightSquareSpace hζ) = 1 :=
  weightSquareSpace_finrank_eq_one hζ (by decide)
example : primaryWeightSquareSpace hζ = ⊥ := primaryWeightSquareSpace_eq_bot hζ (by decide)

end Seven

#print axioms symm_symm_apply_zeta
#print axioms smul_infinitePlace_eq_self_iff
#print axioms card_fixedPlaces_prime
#print axioms sum_inv_sq_mul_sub_one
#print axioms sum_inv_sq_mul_indicator
#print axioms trace_unitAction
#print axioms omegaSquareProjector_eq_units_sum
#print axioms trace_omegaSquareProjector
#print axioms weightSquareSpace_finrank_eq_one
#print axioms primaryWeightSquareSpace_eq_bot
#print axioms exists_global_unit_pow_of_primary
#print axioms DkMath.FLT.Frey.Source.residual_cyclic_extension_has_stable_complement_of_class_vanishing

end
end DkMathTest.FLT.CyclotomicUnitClosure
