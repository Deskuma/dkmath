/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Kummer.GNFirstCase

open scoped NumberField
open DkMath.CosmicFormula DkMath.Lib.NumberTheory DkMath.FLT.Kummer

-- The gap-congruence adapter also works at p=2 for an actual Pythagorean triple.
example : ((3 + 4 : ℤ) : ZMod 2) = (5 : ZMod 2) := by
  exact flt_gap_mod_prime (p := 2) (a := 3) (b := 4) (c := 5) (by norm_num)

example : IsCoprime (3 + 4 : ℤ) (2 : ℤ) := by
  exact gap_isCoprime_prime_of_flt_equation (p := 2) (c := 5) (by norm_num) (by norm_num)

-- A genuinely ramified cubic phase factor has exactly one ramified divisor.
example {K : Type*} [Field K] [NumberField K]
    [Fact (Nat.Prime 3)] [IsCyclotomicExtension {3} ℚ K]
    {ζ : K} (hζ : IsPrimitiveRoot ζ 3) :
    ∃ β : 𝓞 K, (3 : 𝓞 K) + (1 - hζ.toInteger) * 1 = (hζ.toInteger - 1) * β ∧
      ¬ hζ.toInteger - 1 ∣ β := by
  simpa using exists_ramified_phase_quotient_of_dvd_gap hζ (by decide)
    (x := 3) (u := 1) (by norm_num) (by norm_num) (i := 1) (by decide) (by decide)

-- The opposite side of the branch criterion: 3 does not divide gap 2.
example {K : Type*} [Field K] [NumberField K]
    [Fact (Nat.Prime 3)] [IsCyclotomicExtension {3} ℚ K]
    {ζ : K} (hζ : IsPrimitiveRoot ζ 3) :
    ¬ hζ.toInteger - 1 ∣ (2 : 𝓞 K) + (1 - hζ.toInteger ^ 2) * (-1) := by
  have hn : ¬ (3 : ℤ) ∣ 2 := by norm_num
  simpa using (not_congr (ramified_dvd_integral_phaseFactor_iff hζ 2 (-1) 2)).mpr hn

-- The exact-one layer needs the odd-prime boundary: at p=2 it can fail.
example : (-1 - 1 : ℤ) ^ 2 ∣ (2 : ℤ) + (1 - (-1 : ℤ) ^ 1) * 1 := by
  norm_num

#print axioms DkMath.FLT.Kummer.GN_kummer_structure_of_first_case
#print axioms DkMath.FLT.Kummer.exists_GN_eq_pow_of_first_case
#print axioms DkMath.Lib.NumberTheory.ramifiedIdeal_pow_eq_prime_span
#print axioms DkMath.Lib.NumberTheory.exists_ramified_phase_quotient_of_dvd_gap

run_cmd do
  let names := #[
    ``DkMath.FLT.Kummer.flt_gap_mod_prime,
    ``DkMath.FLT.Kummer.gap_isCoprime_prime_of_flt_equation,
    ``DkMath.FLT.Kummer.GN_kummer_structure_of_first_case,
    ``DkMath.FLT.Kummer.exists_GN_eq_pow_of_kummerFactor_eq_unit_mul_pow,
    ``DkMath.FLT.Kummer.exists_GN_eq_pow_of_first_case,
    ``DkMath.Lib.NumberTheory.sub_one_dvd_phaseFactor_iff_gap,
    ``DkMath.Lib.NumberTheory.ramified_pow_dvd_GTail,
    ``DkMath.Lib.NumberTheory.ramifiedIdeal_pow_eq_prime_span,
    ``DkMath.Lib.NumberTheory.ramified_dvd_integral_phaseFactor_iff,
    ``DkMath.Lib.NumberTheory.prime_dvd_integral_GTail_of_dvd_gap,
    ``DkMath.Lib.NumberTheory.ramified_square_not_dvd_phaseFactor,
    ``DkMath.Lib.NumberTheory.exists_ramified_phase_quotient_of_dvd_gap]
  for name in names do
    let axioms ← Lean.collectAxioms name
    for ax in axioms do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom {ax} in {name}"
