/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Kummer.SevenPrimaryNormBridge

open DkMath.FLT.Seven DkMath.FLT.Kummer.SevenPrimaryNorm

namespace DkMathTest.FLT.Kummer.SevenPrimaryNorm

abbrev R := SevenCyclotomicDegreeSixInt.Ring

-- Nontrivial kernel of the relative norm: equality of norms cannot identify elements.
example : relativeNorm SevenCyclotomicDegreeSixInt.zeta = 1 := by
  simp [relativeNorm, QuadraticAlgebra.norm_def, SevenCyclotomicDegreeSixInt.zeta]

example : ¬ Function.Injective relativeNorm := by
  intro h
  apply SevenCyclotomicDegreeSixInt.zeta_ne_one
  apply h
  change QuadraticAlgebra.norm SevenCyclotomicDegreeSixInt.zeta = QuadraticAlgebra.norm (1 : R)
  rw [QuadraticAlgebra.norm_one]
  simp [QuadraticAlgebra.norm_def, SevenCyclotomicDegreeSixInt.zeta]

-- The integer congruence is a real restriction on units, not an automatic hypothesis.
example (n : ℤ) : ¬ (7 : R) ∣ SevenCyclotomicDegreeSixInt.zeta - (n : R) := by
  rintro ⟨w, hw⟩
  have hi : (1 : SevenRealCubicInt) = 7 * w.im := by
    simpa [SevenCyclotomicDegreeSixInt.zeta, show (7 : R) = ⟨7, 0⟩ from rfl]
      using congrArg QuadraticAlgebra.im hw
  have hf : (1 : ℤ) = 7 * w.im.fst := by
    simpa [show (7 : SevenRealCubicInt) = ⟨7, 0, 0⟩ from rfl]
      using congrArg SevenRealCubicInt.fst hi
  omega

example (u : Rˣ) (h : ∃ n : ℤ, (7 : R) ∣ (u : R) - (n : R)) :
    ∃ v : SevenRealCubicIntˣ, Units.map relativeNorm u = v ^ 7 :=
  relativeNorm_primary_unit_seventh u h

example (u : Rˣ) (h : ∃ n : ℤ, (7 : R) ∣ (u : R) - (n : R)) :
    ∃ v : SevenRealCubicIntˣ,
      (u : R) * star (u : R) = SevenCyclotomicDegreeSixInt.ofReal (v : SevenRealCubicInt) ^ 7 :=
  primary_unit_mul_conjugate u h

-- Only the elementary degree arithmetic is checked here; this does not prove unit ranks.
example : ([3, 5, 7, 11, 13].map Nat.totient) = [2, 4, 6, 10, 12] := by decide
example : ([3, 5, 7, 11, 13].map (fun p => (p - 1) / 2)) = [1, 2, 3, 5, 6] := by decide
example : ([3, 5, 7, 11, 13].map (fun p => (p - 3) / 2)) = [0, 1, 2, 4, 5] := by decide

#print axioms GN_primary_unit_relativeNorm_seventh
#print axioms realCubic_primary_unit_log_zero
#print axioms realCubic_primary_unit_seventh
#print axioms relativeNorm_congruent_integer
#print axioms relativeNorm_primary_unit_seventh
#print axioms primary_unit_mul_conjugate

run_cmd do
  for n in #[``realCubic_primary_unit_log_zero, ``realCubic_primary_unit_seventh,
      ``relativeNorm, ``relativeNorm_congruent_integer,
      ``relativeNorm_primary_unit_seventh, ``primary_unit_mul_conjugate,
      ``integralEquiv, ``integralEquiv_generator, ``integralRelativeNorm,
      ``integralEquiv_congruent_integer, ``integralRelativeNorm_primary_unit_seventh,
      ``GN_primary_unit_relativeNorm_seventh] do
    for ax in ← Lean.collectAxioms n do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom {ax} in {n}"

end DkMathTest.FLT.Kummer.SevenPrimaryNorm
