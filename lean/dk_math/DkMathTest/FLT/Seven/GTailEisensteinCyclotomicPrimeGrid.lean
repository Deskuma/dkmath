/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Seven.GTailEisensteinCyclotomicPrimeGrid

#print "file: DkMathTest.FLT.Seven.GTailEisensteinCyclotomicPrimeGrid"

namespace DkMathTest.FLT.Seven.GTailEisensteinCyclotomicPrimeGrid

open DkMath.FLT.Seven DkMath.Lib.NumberTheory DkMath.NumberTheory.TraceOneQuadratic
open DkMath.FLT.Seven.GTailCommonReceiver DkMath.FLT.Seven.GTailPrimeGrid

local instance : Fact (Nat.Prime 43) := ⟨by decide⟩

example : eisenstein43Root 0 = 37 ∧ eisenstein43Root 1 = 7 := by decide
example : (List.finRange 6).map seven43Root = [11, 35, 41, 21, 16, 4] := by decide
example : Function.Injective eisenstein43Root := eisenstein43Root_injective
example : Function.Injective seven43Root := seven43Root_injective
example (e : Fin 2) : eisenstein43Root e ^ 2 - eisenstein43Root e + 1 = 0 :=
  eisenstein43Root_relation e
example (j : Fin 6) : seven43Root j ^ 7 = 1 ∧ seven43Root j ≠ 0 ∧ seven43Root j ≠ 1 :=
  ⟨seven43Root_pow_seven j, seven43Root_ne_zero j, seven43Root_ne_one j⟩
example (e : Fin 2) (j : Fin 6) : Carrier →+* ZMod 43 := evGrid e j
example (e : Fin 2) (j : Fin 6) : (evGrid e j).comp fromEisenstein =
    eisensteinResidueRingHom (eisenstein43Root e) (eisenstein43Root_relation e) :=
  evGrid_comp_eisenstein e j
example (e : Fin 2) (j : Fin 6) : (evGrid e j).comp fromCyclotomic = evR43 j :=
  evGrid_comp_cyclotomic e j
example (e : Fin 2) (j : Fin 6) : evGrid e j (fromEisenstein (tau (-1))) = eisenstein43Root e :=
  evGrid_tau e j
example (e : Fin 2) (j : Fin 6) (n : ℤ) :
    evGrid e j (fromCyclotomic (n : SevenCyclotomicDegreeSixInt.Ring)) = (n : ZMod 43) :=
  (evGrid_scalar e j n).2
example (e : Fin 2) (j : Fin 6) : Function.Surjective (evGrid e j) := evGrid_surjective e j
example : ∀ x : Fin 2 × Fin 6, (M x.1 x.2).IsMaximal := fun x => M_isMaximal x.1 x.2
example : ∀ x : Fin 2 × Fin 6, (M x.1 x.2).IsPrime := fun x => M_isPrime x.1 x.2
example : Function.Injective (fun x : Fin 2 × Fin 6 => M x.1 x.2) := M_injective
example (x y : Fin 2 × Fin 6) (h : x ≠ y) : M x.1 x.2 ≠ M y.1 y.2 :=
  fun he => h (M_injective he)
example : Fintype.card (Fin 2 × Fin 6) = 12 := by decide
example (e : Fin 2) (j k : Fin 6) :
    Ideal.comap fromEisenstein (M e j) = Ideal.comap fromEisenstein (M e k) :=
  M_comap_eisenstein_column e j k
example (e f : Fin 2) (j : Fin 6) :
    Ideal.comap fromCyclotomic (M e j) = Ideal.comap fromCyclotomic (M f j) :=
  M_comap_cyclotomic_row e f j
example : evGrid 0 0 = eval43 := evGrid_zero_zero
example : M 0 0 = M43 := M_zero_zero
example : Ideal.map fromEisenstein (eisensteinResidueIdeal (37 : ZMod 43) (by decide)) < M 0 0 :=
  map_eisenstein_lt_zero_zero
example : Ideal.map fromCyclotomic
    (sixRootKernel (11 : ZMod 43) (by decide) (by decide) (by decide) 0) < M 0 0 :=
  map_cyclotomic_lt_zero_zero
example (e : Fin 2) (j : Fin 6) :
    fromEisenstein (gtailSevenNormCoord 1166 1857) ∈ M e j ↔ e = 0 := normCoord_mem_iff e j
example (e : Fin 2) (j : Fin 6) :
    fromCyclotomic (gtailCyclotomicFactor 1858 1165 0) ∈ M e j ↔ j = 0 := factor_mem_iff e j
example (e : Fin 2) (j : Fin 6) :
    (fromEisenstein (gtailSevenNormCoord 1166 1857) ∈ M e j ∧
      fromCyclotomic (gtailCyclotomicFactor 1858 1165 0) ∈ M e j) ↔ e = 0 ∧ j = 0 := by
  rw [normCoord_mem_iff, factor_mem_iff]
example : fromEisenstein (gtailSevenNormCoord 1166 1857) ∉ M 1 0 := by
  rw [normCoord_mem_iff]
  decide
example : fromCyclotomic (gtailCyclotomicFactor 1858 1165 0) ∉ M 0 1 := by
  rw [factor_mem_iff]
  decide
example : ¬ Fermat7Equation 1166 1857 1858 := by
  unfold Fermat7Equation
  decide
example : fromEisenstein (gtailSevenNormCoord 1166 1857) ≠
    fromCyclotomic (gtailCyclotomicFactor 1858 1165 0) := by
  intro h
  have hh : ((1857 : ℤ) : SevenCyclotomicDegreeSixInt.Ring) = 0 := by
    simpa [fromEisenstein, fromCyclotomic, QuadraticAlgebra.algebraMap_eq, gtailSevenNormCoord_eq]
      using congrArg (fun x : Carrier => x.im) h
  have he := congrArg (evR43 0) hh
  exact (by decide : ((1857 : ℤ) : ZMod 43) ≠ 0)
    (by simpa only [map_intCast, map_zero] using he)

#print axioms DkMath.FLT.Seven.GTailPrimeGrid.eisenstein43Root
#print axioms DkMath.FLT.Seven.GTailPrimeGrid.seven43Root
#print axioms DkMath.FLT.Seven.GTailPrimeGrid.eisenstein43Root_relation
#print axioms DkMath.FLT.Seven.GTailPrimeGrid.eisenstein43Root_injective
#print axioms DkMath.FLT.Seven.GTailPrimeGrid.seven43Root_pow_seven
#print axioms DkMath.FLT.Seven.GTailPrimeGrid.seven43Root_ne_zero
#print axioms DkMath.FLT.Seven.GTailPrimeGrid.seven43Root_ne_one
#print axioms DkMath.FLT.Seven.GTailPrimeGrid.seven43Root_injective
#print axioms DkMath.FLT.Seven.GTailPrimeGrid.evR43
#print axioms DkMath.FLT.Seven.GTailPrimeGrid.evGrid
#print axioms DkMath.FLT.Seven.GTailPrimeGrid.evGrid_comp_cyclotomic
#print axioms DkMath.FLT.Seven.GTailPrimeGrid.evGrid_comp_eisenstein
#print axioms DkMath.FLT.Seven.GTailPrimeGrid.evGrid_tau
#print axioms DkMath.FLT.Seven.GTailPrimeGrid.evGrid_zeta
#print axioms DkMath.FLT.Seven.GTailPrimeGrid.evGrid_scalar
#print axioms DkMath.FLT.Seven.GTailPrimeGrid.M
#print axioms DkMath.FLT.Seven.GTailPrimeGrid.evGrid_surjective
#print axioms DkMath.FLT.Seven.GTailPrimeGrid.M_isMaximal
#print axioms DkMath.FLT.Seven.GTailPrimeGrid.M_isPrime
#print axioms DkMath.FLT.Seven.GTailPrimeGrid.M_comap_eisenstein
#print axioms DkMath.FLT.Seven.GTailPrimeGrid.M_comap_cyclotomic
#print axioms DkMath.FLT.Seven.GTailPrimeGrid.evGrid_zero_zero
#print axioms DkMath.FLT.Seven.GTailPrimeGrid.M_zero_zero
#print axioms DkMath.FLT.Seven.GTailPrimeGrid.M_comap_eisenstein_column
#print axioms DkMath.FLT.Seven.GTailPrimeGrid.M_comap_cyclotomic_row
#print axioms DkMath.FLT.Seven.GTailPrimeGrid.M_injective
#print axioms DkMath.FLT.Seven.GTailPrimeGrid.map_eisenstein_le
#print axioms DkMath.FLT.Seven.GTailPrimeGrid.map_cyclotomic_le
#print axioms DkMath.FLT.Seven.GTailPrimeGrid.map_cyclotomic_lt_zero_zero
#print axioms DkMath.FLT.Seven.GTailPrimeGrid.map_eisenstein_lt_zero_zero
#print axioms DkMath.FLT.Seven.GTailPrimeGrid.normCoord_mem_iff
#print axioms DkMath.FLT.Seven.GTailPrimeGrid.factor_mem_iff

end DkMathTest.FLT.Seven.GTailEisensteinCyclotomicPrimeGrid
