/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.NumberTheory.CyclotomicOmegaSquareUnitRank
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed

#print "file: DkMathTest.FLT.CyclotomicOmegaSquareUnitRank"

namespace DkMathTest.FLT.CyclotomicOmegaSquareUnitRank

open DkMath.Lib.NumberTheory
open NumberFieldUnitPowerDimension CyclotomicOmegaSquareUnitRank
open CyclotomicKernelField CyclotomicKummerWeight CyclotomicPrimaryUnitSpace
open CyclotomicOmegaSquareProjector KummerSelmerExact
open scoped NumberField
noncomputable section

-- Finite generation comes from Dirichlet for every number field and every exponent,
-- including exponent 0 (ZMod 0 is Z), with no cyclotomic or trace hypothesis.
example : Module.Finite (ZMod 0) (Additive (UnitClass (𝓞 ℚ) 0)) := inferInstance
example : Module.Finite (ZMod 3) (Additive (UnitClass (𝓞 ℚ) 3)) := inferInstance

namespace Five

local instance : Fact (Nat.Prime 5) := ⟨by decide⟩
private def ζ : AlgebraicClosure ℚ :=
  (HasEnoughRootsOfUnity.exists_primitiveRoot (AlgebraicClosure ℚ) 5).choose
private theorem hζ : IsPrimitiveRoot ζ 5 :=
  (HasEnoughRootsOfUnity.exists_primitiveRoot (AlgebraicClosure ℚ) 5).choose_spec
local instance : NumberField (rootField ζ) := rootField_numberField ζ

-- Exact dimension of the actual quotient, not only a cardinality or congruence.
example : Module.finrank (ZMod 5) (Additive (UnitClass (𝓞 (rootField ζ)) 5)) = 2 :=
  root_unitClass_finrank hζ (by decide)

-- Finite-dimensionality is supplied internally before using the actual nonzero eigenvector.
example : 1 ≤ Module.finrank (ZMod 5) (weightSquareSpace hζ) ∧
    Module.finrank (ZMod 5) (weightSquareSpace hζ) ≤ 2 :=
  ⟨weightSquareSpace_finrank_pos hζ (by decide), weightSquareSpace_finrank_le hζ (by decide)⟩

example : LinearMap.trace (ZMod 5) _ (omegaSquareProjector hζ) =
    (Module.finrank (ZMod 5) (weightSquareSpace hζ) : ZMod 5) :=
  trace_omegaSquareProjector_eq_finrank hζ

-- This implication RETAINS the missing arithmetic trace computation as an input.
example (htrace : LinearMap.trace (ZMod 5) _ (omegaSquareProjector hζ) = 1) :
    primaryWeightSquareSpace hζ = ⊥ := primaryWeightSquareSpace_eq_bot_of_trace hζ (by decide) htrace

end Five

namespace Seven

local instance : Fact (Nat.Prime 7) := ⟨by decide⟩
private def ζ : AlgebraicClosure ℚ :=
  (HasEnoughRootsOfUnity.exists_primitiveRoot (AlgebraicClosure ℚ) 7).choose
private theorem hζ : IsPrimitiveRoot ζ 7 :=
  (HasEnoughRootsOfUnity.exists_primitiveRoot (AlgebraicClosure ℚ) 7).choose_spec
local instance : NumberField (rootField ζ) := rootField_numberField ζ

example : Module.finrank (ZMod 7) (Additive (UnitClass (𝓞 (rootField ζ)) 7)) = 3 :=
  root_unitClass_finrank hζ (by decide)

example : 0 < Module.finrank (ZMod 7) (weightSquareSpace hζ) ∧
    Module.finrank (ZMod 7) (weightSquareSpace hζ) < 7 :=
  ⟨weightSquareSpace_finrank_pos hζ (by decide), weightSquareSpace_finrank_lt_prime hζ (by decide)⟩

example : LinearMap.trace (ZMod 7) _ (omegaSquareProjector hζ) = 1 ↔
    Module.finrank (ZMod 7) (weightSquareSpace hζ) = 1 :=
  trace_eq_one_iff_finrank_eq_one hζ (by decide)

end Seven

-- A cast equality alone cannot determine a natural dimension: 1 and 6 coincide mod 5.
example : (6 : ZMod 5) = 1 ∧ (6 : ℕ) ≠ 1 := ⟨by decide, by decide⟩

#print axioms unitClassFinite
#print axioms exists_unitClass_basis
#print axioms finrank_unitClass
#print axioms finrank_unitClass_cyclotomic
#print axioms unitClass_finite
#print axioms weightSquareSpace_finite
#print axioms root_unitClass_finrank
#print axioms weightSquareSpace_finrank_pos
#print axioms weightSquareSpace_finrank_lt_prime
#print axioms trace_omegaSquareProjector_eq_finrank
#print axioms weightSquareSpace_finrank_eq_one_of_trace
#print axioms trace_eq_one_iff_finrank_eq_one
#print axioms primaryWeightSquareSpace_eq_bot_of_trace

end
end DkMathTest.FLT.CyclotomicOmegaSquareUnitRank
