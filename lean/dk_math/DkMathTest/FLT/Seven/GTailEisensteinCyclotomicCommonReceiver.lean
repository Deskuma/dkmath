/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Seven.GTailEisensteinCyclotomicCommonReceiver

#print "file: DkMathTest.FLT.Seven.GTailEisensteinCyclotomicCommonReceiver"

namespace DkMathTest.FLT.Seven.GTailEisensteinCyclotomicCommonReceiver

open DkMath.FLT.Seven DkMath.Lib.NumberTheory DkMath.NumberTheory.TraceOneQuadratic
open DkMath.FLT.Seven.GTailCommonReceiver

local instance : Fact (Nat.Prime 43) := ⟨by decide⟩
local notation "R" => SevenCyclotomicDegreeSixInt.Ring
local notation "P37" => eisensteinResidueIdeal (37 : ZMod 43) (by decide)
local notation "P7" => eisensteinResidueIdeal (7 : ZMod 43) (by decide)
local notation "K0" => sixRootKernel (11 : ZMod 43) (by decide) (by decide) (by decide) 0
local notation "α43" => gtailSevenNormCoord 1166 1857
local notation "F0" => gtailCyclotomicFactor 1858 1165 (0 : Fin 6)

example : TraceOneInt (-1) →+* Carrier := fromEisenstein
example : R →+* Carrier := fromCyclotomic
example : Function.Injective fromEisenstein := fromEisenstein_injective
example : Function.Injective fromCyclotomic := fromCyclotomic_injective
example : fromEisenstein (tau (-1)) = (QuadraticAlgebra.omega : Carrier) := fromEisenstein_tau
example : (QuadraticAlgebra.omega : Carrier) ^ 2 - QuadraticAlgebra.omega + 1 = 0 := omega_relation
example : fromCyclotomic SevenCyclotomicDegreeSixInt.zeta =
    algebraMap R Carrier SevenCyclotomicDegreeSixInt.zeta := fromCyclotomic_zeta
example (n : ℤ) : fromEisenstein (n : TraceOneInt (-1)) = fromCyclotomic (n : R) := scalar_images_eq n
example (x y : TraceOneInt (-1)) : fromEisenstein (x * y) = fromEisenstein x * fromEisenstein y :=
  map_mul _ _ _
example (x y : R) : fromCyclotomic (x + y) = fromCyclotomic x + fromCyclotomic y := map_add _ _ _
example : eval43.comp fromEisenstein = eisensteinResidueRingHom (37 : ZMod 43) (by decide) :=
  eval43_comp_eisenstein
example : eval43.comp fromCyclotomic =
    evalCyclotomicFromSeventhRoot (11 : ZMod 43) (by decide) (by decide) (by decide) :=
  eval43_comp_cyclotomic
example : eval43 (fromEisenstein (tau (-1))) = 37 := eval43_tau
example : eval43 (fromCyclotomic SevenCyclotomicDegreeSixInt.zeta) = 11 := eval43_zeta
example (n : ℤ) : eval43 (fromEisenstein (n : TraceOneInt (-1))) = (n : ZMod 43) ∧
    eval43 (fromCyclotomic (n : R)) = (n : ZMod 43) := eval43_scalar n
example : Ideal.comap fromEisenstein M43 = P37 := M43_comap_eisenstein
example : Ideal.comap fromCyclotomic M43 =
    seventhRootKernel (11 : ZMod 43) (by decide) (by decide) (by decide) := M43_comap_cyclotomic
example : Ideal.comap fromCyclotomic M43 = K0 := M43_comap_cyclotomic_slot_zero
example : Function.Surjective eval43 := eval43_surjective
example : M43.IsMaximal := M43_isMaximal
example : M43.IsPrime := M43_isPrime

-- Distinct generator residues still distinguish the two embedded generators.
example : fromEisenstein (tau (-1)) ≠ fromCyclotomic SevenCyclotomicDegreeSixInt.zeta := by
  intro h
  have hx := congrArg eval43 h
  rw [eval43_tau, eval43_zeta] at hx
  exact (by decide : (37 : ZMod 43) ≠ 11) hx

private theorem eroot : gtailSevenResidueRoot 43 1166 1857 = 37 := by
  dsimp [gtailSevenResidueRoot]
  apply (div_eq_iff (by decide : (1857 : ZMod 43) ≠ 0)).mpr
  decide
private theorem rroot : gtailSevenTailRatio 43 1858 1165 = 11 := by
  dsimp [gtailSevenTailRatio]
  apply (div_eq_iff (by decide : (1858 : ZMod 43) ≠ 0)).mpr
  decide
private theorem alpha_mem : α43 ∈ P37 := by
  have h := gtailSevenNormCoord_mem_residueIdeal (q := 43) (a := 1166) (b := 1857)
    (by decide) (by decide)
  simpa only [eroot] using h
private theorem factor_square : F0 ∈ K0 ^ 2 := by
  have h := (gtailCyclotomicFactor_mem_square_iff (q := 43) 1858 1165
    (by decide) (by decide) (by decide) (0 : Fin 6)).mpr (by decide)
  simpa only [rroot, show sixInverseSlot (0 : Fin 6) = 0 from rfl] using h
private theorem factor_mem : F0 ∈ K0 :=
  (Ideal.pow_le_self (by decide : 2 ≠ 0)) factor_square

example : α43 ∈ P37 := alpha_mem
example : (α43 : TraceOneInt (-1)) ^ 2 ∈ P37 * P37 ∧
    (α43 : TraceOneInt (-1)) ^ 2 ∉ P7 ∧ (α43 : TraceOneInt (-1)) ^ 2 ∉ eisensteinScalarIdeal 43 := by
  have h := gtailSevenNormCoord_split_square_address (q := 43) (a := 1166) (b := 1857)
    (by decide) (by decide) (by decide)
  simpa only [eroot, show 1 - (37 : ZMod 43) = 7 by decide] using h
example : F0 ∈ K0 ^ 2 := factor_square

-- Use the actual commuting triangles, rather than unrelated polynomial evaluations.
example : eval43 (fromEisenstein α43) = 0 := by
  have h := DFunLike.congr_fun eval43_comp_eisenstein α43
  exact h.trans ((RingHom.mem_ker).mp alpha_mem)
example : eval43 (fromCyclotomic F0) = 0 := by
  have h := DFunLike.congr_fun eval43_comp_cyclotomic F0
  have hm : F0 ∈ seventhRootKernel (11 : ZMod 43) (by decide) (by decide) (by decide) := by
    simpa only [sixRootKernel, sixSlotRoot, Fin.val_zero, zero_add, pow_one] using factor_mem
  exact h.trans ((RingHom.mem_ker).mp hm)
example : fromEisenstein α43 ∈ M43 := by
  change α43 ∈ Ideal.comap fromEisenstein M43
  rw [M43_comap_eisenstein]
  exact alpha_mem
example : fromCyclotomic F0 ∈ M43 := by
  change F0 ∈ Ideal.comap fromCyclotomic M43
  rw [M43_comap_cyclotomic_slot_zero]
  exact factor_mem

-- Two actual elements of the same maximal kernel are still different in C.
example : fromEisenstein α43 ≠ fromCyclotomic F0 := by
  intro h
  have hh : ((1857 : ℤ) : R) = 0 := by
    simpa [fromEisenstein, fromCyclotomic, QuadraticAlgebra.algebraMap_eq,
      gtailSevenNormCoord_eq] using congrArg (fun x : Carrier => x.im) h
  have he := congrArg (evalCyclotomicFromSeventhRoot (11 : ZMod 43)
    (by decide) (by decide) (by decide)) hh
  exact (by decide : ((1857 : ℤ) : ZMod 43) ≠ 0)
    (by simpa only [map_intCast, map_zero] using he)

-- Common receiving maps coexist with the previously proved impossibility of direct maps.
example : ¬ Nonempty (TraceOneInt (-1) →+* R) := not_nonempty_eisenstein_to_seven_cyclotomic
example : ¬ Nonempty (R →+* TraceOneInt (-1)) := not_nonempty_seven_cyclotomic_to_eisenstein
example : ∀ x : ZMod 29, x ^ 2 - x + 1 ≠ 0 := no_eisenstein_root_zmod29
example : ∀ x : ZMod 13, 1 + x + x ^ 2 + x ^ 3 + x ^ 4 + x ^ 5 + x ^ 6 ≠ 0 :=
  no_seven_geom_root_zmod13
example : ¬ Fermat7Equation 1166 1857 1858 := by unfold Fermat7Equation; decide
-- The old cubic norm coordinate still inhabits the discriminant-minus-seven ring.
example (z y : ℤ) : TraceOneInt (-2) := cyclotomicSevenToTraceOne z y
example : discr (-1) = -3 ∧ discr (-2) = -7 := by decide

#check QuadraticAlgebra.algebraMap_injective
#check QuadraticAlgebra.re_mul
#check QuadraticAlgebra.im_mul
#check QuadraticAlgebra.lift
#check Ideal.mem_comap
#check RingHom.mem_ker
#check Ideal.ext

#print axioms DkMath.FLT.Seven.GTailCommonReceiver.Carrier
#print axioms DkMath.FLT.Seven.GTailCommonReceiver.fromCyclotomic
#print axioms DkMath.FLT.Seven.GTailCommonReceiver.fromEisenstein
#print axioms DkMath.FLT.Seven.GTailCommonReceiver.fromEisenstein_tau
#print axioms DkMath.FLT.Seven.GTailCommonReceiver.fromEisenstein_intCast
#print axioms DkMath.FLT.Seven.GTailCommonReceiver.fromCyclotomic_zeta
#print axioms DkMath.FLT.Seven.GTailCommonReceiver.scalar_images_eq
#print axioms DkMath.FLT.Seven.GTailCommonReceiver.omega_relation
#print axioms DkMath.FLT.Seven.GTailCommonReceiver.fromCyclotomic_injective
#print axioms DkMath.FLT.Seven.GTailCommonReceiver.fromEisenstein_injective
#print axioms DkMath.FLT.Seven.GTailCommonReceiver.eval43
#print axioms DkMath.FLT.Seven.GTailCommonReceiver.eval43_comp_cyclotomic
#print axioms DkMath.FLT.Seven.GTailCommonReceiver.eval43_comp_eisenstein
#print axioms DkMath.FLT.Seven.GTailCommonReceiver.eval43_zeta
#print axioms DkMath.FLT.Seven.GTailCommonReceiver.eval43_tau
#print axioms DkMath.FLT.Seven.GTailCommonReceiver.eval43_scalar
#print axioms DkMath.FLT.Seven.GTailCommonReceiver.M43
#print axioms DkMath.FLT.Seven.GTailCommonReceiver.M43_comap_eisenstein
#print axioms DkMath.FLT.Seven.GTailCommonReceiver.M43_comap_cyclotomic
#print axioms DkMath.FLT.Seven.GTailCommonReceiver.M43_comap_cyclotomic_slot_zero
#print axioms DkMath.FLT.Seven.GTailCommonReceiver.eval43_surjective
#print axioms DkMath.FLT.Seven.GTailCommonReceiver.M43_isMaximal
#print axioms DkMath.FLT.Seven.GTailCommonReceiver.M43_isPrime

end DkMathTest.FLT.Seven.GTailEisensteinCyclotomicCommonReceiver
