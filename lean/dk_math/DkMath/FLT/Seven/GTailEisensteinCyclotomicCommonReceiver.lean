/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Seven.GTailEisensteinCyclotomicNoDirectHom

#print "file: DkMath.FLT.Seven.GTailEisensteinCyclotomicCommonReceiver"

namespace DkMath.FLT.Seven.GTailCommonReceiver

open DkMath.NumberTheory.TraceOneQuadratic DkMath.Lib.NumberTheory

/-- A quadratic receiving algebra over the actual degree-six ring, with ω²=-1+ω. -/
abbrev Carrier := QuadraticAlgebra SevenCyclotomicDegreeSixInt.Ring (-1) 1

/-- The canonical coefficient-ring inclusion. -/
def fromCyclotomic : SevenCyclotomicDegreeSixInt.Ring →+* Carrier :=
  algebraMap _ _

/-- The Eisenstein inclusion uses signed integer coordinates and the correct quadratic law. -/
def fromEisenstein : TraceOneInt (-1) →+* Carrier where
  toFun x := ⟨(x.fst : SevenCyclotomicDegreeSixInt.Ring), (x.snd : SevenCyclotomicDegreeSixInt.Ring)⟩
  map_zero' := by ext <;> simp
  map_one' := by
    apply QuadraticAlgebra.ext <;> simp [QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]
  map_add' x y := by ext <;> simp
  map_mul' x y := by ext <;> simp

/-- The quadratic source generator becomes the new receiving generator. -/
theorem fromEisenstein_tau : fromEisenstein (tau (-1)) = (QuadraticAlgebra.omega : Carrier) := rfl

/-- Integer scalars are preserved by the actual Eisenstein RingHom. -/
theorem fromEisenstein_intCast (n : ℤ) : fromEisenstein (n : TraceOneInt (-1)) = (n : Carrier) :=
  map_intCast _ _

/-- The coefficient generator is embedded by the canonical algebra map. -/
theorem fromCyclotomic_zeta : fromCyclotomic SevenCyclotomicDegreeSixInt.zeta =
    algebraMap SevenCyclotomicDegreeSixInt.Ring Carrier SevenCyclotomicDegreeSixInt.zeta := rfl

/-- Both integral sources agree on integer scalars, not on arbitrary elements. -/
theorem scalar_images_eq (n : ℤ) : fromEisenstein (n : TraceOneInt (-1)) =
    fromCyclotomic (n : SevenCyclotomicDegreeSixInt.Ring) := by
  simp only [map_intCast]

/-- The new generator has the discriminant-minus-three relation inside the receiver. -/
theorem omega_relation : (QuadraticAlgebra.omega : Carrier) ^ 2 - QuadraticAlgebra.omega + 1 = 0 := by
  apply QuadraticAlgebra.ext <;> simp [pow_two, QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]

/-- The coefficient inclusion is injective by the actual quadratic coordinate chart. -/
theorem fromCyclotomic_injective : Function.Injective fromCyclotomic :=
  QuadraticAlgebra.algebraMap_injective

private theorem intCast_cyclotomic_injective :
    Function.Injective (fun n : ℤ => (n : SevenCyclotomicDegreeSixInt.Ring)) := by
  intro n m h
  simpa using congrArg (fun z : SevenCyclotomicDegreeSixInt.Ring => z.re.fst) h

/-- The Eisenstein map is injective, using scalar injectivity in the actual degree-six ring. -/
theorem fromEisenstein_injective : Function.Injective fromEisenstein := by
  intro x y h
  apply traceOne_ext
  · exact intCast_cyclotomic_injective (congrArg QuadraticAlgebra.re h)
  · exact intCast_cyclotomic_injective (congrArg QuadraticAlgebra.im h)

local instance : Fact (Nat.Prime 43) := ⟨by decide⟩

private def residueR43 : SevenCyclotomicDegreeSixInt.Ring →+* ZMod 43 :=
  evalCyclotomicFromSeventhRoot (11 : ZMod 43) (by decide) (by decide) (by decide)

/-- A common residue evaluation with separately supplied Eisenstein and cyclotomic roots. -/
def eval43 : Carrier →+* ZMod 43 where
  toFun x := residueR43 x.re + 37 * residueR43 x.im
  map_zero' := by simp
  map_one' := by simp [QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]
  map_add' x y := by simp only [QuadraticAlgebra.re_add, QuadraticAlgebra.im_add, map_add]; ring
  map_mul' x y := by
    simp only [QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul, map_add, map_mul, map_neg, map_one]
    have ht : (37 : ZMod 43) ^ 2 - 37 + 1 = 0 := by decide
    linear_combination -(residueR43 x.im * residueR43 y.im) * ht

/-- The common evaluation restricts to the original degree-six residue RingHom. -/
theorem eval43_comp_cyclotomic : eval43.comp fromCyclotomic =
    evalCyclotomicFromSeventhRoot (11 : ZMod 43) (by decide) (by decide) (by decide) := by
  ext x
  simp [eval43, fromCyclotomic, QuadraticAlgebra.algebraMap_eq, residueR43]

/-- The other restriction is the original Eisenstein residue RingHom. -/
theorem eval43_comp_eisenstein : eval43.comp fromEisenstein =
    eisensteinResidueRingHom (37 : ZMod 43) (by decide) := by
  ext x
  simp [eval43, fromEisenstein, eisensteinResidueRingHom, eisensteinResidueEval, mul_comm]

/-- The shared evaluation sees the coefficient cyclotomic generator at eleven. -/
theorem eval43_zeta : eval43 (fromCyclotomic SevenCyclotomicDegreeSixInt.zeta) = 11 := by
  have h := DFunLike.congr_fun eval43_comp_cyclotomic SevenCyclotomicDegreeSixInt.zeta
  exact h.trans (evalCyclotomicFromSeventhRoot_zeta _ _ _ _)

/-- The new independent quadratic generator has residue thirty-seven. -/
theorem eval43_tau : eval43 (fromEisenstein (tau (-1))) = 37 := by
  have h := DFunLike.congr_fun eval43_comp_eisenstein (tau (-1))
  exact h.trans (eisensteinResidueRingHom_tau _ _)

/-- Both source scalar embeddings have the same canonical residue. -/
theorem eval43_scalar (n : ℤ) : eval43 (fromEisenstein (n : TraceOneInt (-1))) = (n : ZMod 43) ∧
    eval43 (fromCyclotomic (n : SevenCyclotomicDegreeSixInt.Ring)) = (n : ZMod 43) := by
  simp only [map_intCast, and_self]

/-- The common residue kernel is an actual ideal of the third receiving ring. -/
def M43 : Ideal Carrier := RingHom.ker eval43

/-- Contraction to E returns its original typed Eisenstein residue ideal. -/
theorem M43_comap_eisenstein : Ideal.comap fromEisenstein M43 =
    eisensteinResidueIdeal (37 : ZMod 43) (by decide) := by
  ext x
  change (eval43.comp fromEisenstein) x = 0 ↔
    eisensteinResidueRingHom (37 : ZMod 43) (by decide) x = 0
  rw [eval43_comp_eisenstein]

/-- Contraction to R returns its original typed seventh-root kernel. -/
theorem M43_comap_cyclotomic : Ideal.comap fromCyclotomic M43 =
    seventhRootKernel (11 : ZMod 43) (by decide) (by decide) (by decide) := by
  ext x
  change (eval43.comp fromCyclotomic) x = 0 ↔
    evalCyclotomicFromSeventhRoot (11 : ZMod 43) (by decide) (by decide) (by decide) x = 0
  rw [eval43_comp_cyclotomic]

/-- The same R contraction has the existing slot-zero presentation. -/
theorem M43_comap_cyclotomic_slot_zero : Ideal.comap fromCyclotomic M43 =
    sixRootKernel (11 : ZMod 43) (by decide) (by decide) (by decide) 0 := by
  rw [M43_comap_cyclotomic]
  simp only [sixRootKernel, sixSlotRoot, Fin.val_zero, zero_add, pow_one]

/-- The coefficient restriction already makes the common evaluation surjective. -/
theorem eval43_surjective : Function.Surjective eval43 := by
  intro z
  obtain ⟨x, hx⟩ := evalCyclotomicFromSeventhRoot_surjective
    (11 : ZMod 43) (by decide) (by decide) (by decide) z
  exact ⟨fromCyclotomic x, (DFunLike.congr_fun eval43_comp_cyclotomic x).trans hx⟩

/-- The common kernel is maximal, by its actual prime-field residue quotient. -/
theorem M43_isMaximal : M43.IsMaximal :=
  RingHom.ker_isMaximal_of_surjective _ eval43_surjective

/-- In particular, the common kernel is prime. -/
theorem M43_isPrime : M43.IsPrime := M43_isMaximal.isPrime

end DkMath.FLT.Seven.GTailCommonReceiver
