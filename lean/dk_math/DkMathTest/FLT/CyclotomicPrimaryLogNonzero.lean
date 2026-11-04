/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyCyclotomicPrimaryLogSplit
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed

#print "file: DkMathTest.FLT.CyclotomicPrimaryLogNonzero"

namespace DkMathTest.FLT.CyclotomicPrimaryLogNonzero

open DkMath.Lib.NumberTheory
open CyclotomicOmegaSquareProjector CyclotomicPrimaryLogNonzero
open CyclotomicPrimaryLog CyclotomicPrimaryUnitSpace CyclotomicKernelField
open CyclotomicKummerWeight KummerSelmerExact
open scoped NumberField
noncomputable section

namespace Five

local instance : Fact (Nat.Prime 5) := ⟨by decide⟩
private def ζ : AlgebraicClosure ℚ :=
  (HasEnoughRootsOfUnity.exists_primitiveRoot (AlgebraicClosure ℚ) 5).choose
private theorem hζ : IsPrimitiveRoot ζ 5 :=
  (HasEnoughRootsOfUnity.exists_primitiveRoot (AlgebraicClosure ℚ) 5).choose_spec
local instance : NumberField (rootField ζ) := rootField_numberField ζ
local instance : IsCyclotomicExtension {5} ℚ (rootField ζ) := rootField_isCyclotomic hζ

-- Actual root field and its Galois group, without replacing the specified primitive root.
example : Nat.card ((rootField ζ) ≃ₐ[ℚ] (rootField ζ)) = 4 :=
  CyclotomicClassVanishing.root_galois_card hζ

example (d : (ZMod 5)ˣ) :
    (characterEquiv hζ).symm d (baseRoot ζ) = baseRoot ζ ^ (d : ZMod 5).val :=
  characterEquiv_symm_root hζ d

-- Actual global unit class: eigenmembership and idempotence of the SAME projection.
example : (projectedCyclotomicUnit hζ (by decide) : Additive (UnitClass (𝓞 (rootField ζ)) 5)) ∈
    weightSquareSpace hζ := (projectedCyclotomicUnit hζ (by decide)).property

example : omegaSquareProjector hζ (projectedCyclotomicUnit hζ (by decide)) =
    projectedCyclotomicUnit hζ (by decide) :=
  omegaSquareProjector_eq_self hζ _ (projectedCyclotomicUnit hζ (by decide)).property

-- Check the normalization at p=5: -1/8=3 in the actual cubic quotient.
example : primaryLog (baseRoot_primitive hζ) (by decide) (projectedCyclotomicUnit hζ (by decide)) =
    3 * parameter (baseRoot_primitive hζ) ^ 2 := by
  have hh : half (baseRoot_primitive hζ) (by decide) = (3 : ResidueCube (baseRoot_primitive hζ)) := by
    rw [half, show (2 : ZMod 5)⁻¹ = 3 from inv_eq_of_mul_eq_one_left (by decide), map_ofNat]
  rw [primaryLog_projectedCyclotomicUnit, hh]
  have h5 := natCast_eq_zero (baseRoot_primitive hζ) (by decide)
  linear_combination (-6 * parameter (baseRoot_primitive hζ) ^ 2) * h5

-- This time it IS a projected global unit and its actual log is nonzero.
example : primaryLog (baseRoot_primitive hζ) (by decide) (projectedCyclotomicUnit hζ (by decide)) ≠ 0 :=
  primaryLog_projectedCyclotomicUnit_ne_zero hζ (by decide)

example : projectedCyclotomicUnit hζ (by decide) ≠ 0 :=
  projectedCyclotomicUnit_ne_zero hζ (by decide)

-- Therefore the original global unit is not a fifth power in the integer unit group.
example : ¬ ∃ u : (𝓞 (rootField ζ))ˣ, u ^ 5 = cyclotomicUnit (baseRoot_primitive hζ) (by decide) := by
  rintro ⟨u, hu⟩
  apply projectedCyclotomicUnit_ne_zero hζ (by decide)
  apply Subtype.ext
  change omegaSquareProjector hζ (Additive.ofMul
    (cyclotomicUnit (baseRoot_primitive hζ) (by decide) : UnitClass (𝓞 (rootField ζ)) 5)) = 0
  have hc : (cyclotomicUnit (baseRoot_primitive hζ) (by decide) : UnitClass (𝓞 (rootField ζ)) 5) = 1 :=
    (QuotientGroup.eq_one_iff _).mpr ⟨u, hu⟩
  rw [hc]
  exact map_zero _

end Five

namespace Seven

local instance : Fact (Nat.Prime 7) := ⟨by decide⟩
private def ζ : AlgebraicClosure ℚ :=
  (HasEnoughRootsOfUnity.exists_primitiveRoot (AlgebraicClosure ℚ) 7).choose
private theorem hζ : IsPrimitiveRoot ζ 7 :=
  (HasEnoughRootsOfUnity.exists_primitiveRoot (AlgebraicClosure ℚ) 7).choose_spec
local instance : NumberField (rootField ζ) := rootField_numberField ζ
local instance : IsCyclotomicExtension {7} ℚ (rootField ζ) := rootField_isCyclotomic hζ

-- A second prime checks the general construction beyond the minimal p=5 case.
example : primaryLog (baseRoot_primitive hζ) (by decide) (projectedCyclotomicUnit hζ (by decide)) ≠ 0 :=
  primaryLog_projectedCyclotomicUnit_ne_zero hζ (by decide)

example : weightSquareSpace hζ ≠ ⊥ := weightSquareSpace_ne_bot hζ (by decide)

end Seven

#print axioms omegaSquareProjector_mem
#print axioms omegaSquareProjector_eq_self
#print axioms omegaSquareProjector_idempotent
#print axioms omegaSquareProjector_range
#print axioms characterEquiv
#print axioms characterEquiv_symm_root
#print axioms unitLog_conjugate
#print axioms e2_sum
#print axioms primaryLog_projectedCyclotomicUnit
#print axioms primaryLog_projectedCyclotomicUnit_ne_zero
#print axioms projectedCyclotomicUnit_ne_zero
#print axioms weightSquareSpace_ne_bot
#print axioms primaryWeightSquareSpace_eq_bot_of_rank_one
#print axioms DkMath.FLT.Frey.Source.residual_cyclic_extension_has_stable_complement_of_unit_rank_one

end
end DkMathTest.FLT.CyclotomicPrimaryLogNonzero
