/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Kummer.GNRamified

#print "file: DkMathTest.FLT.Kummer.GNRamified"

/-!
Nonvacuous checks of the ideal allocation kernel, independent of an FLT
counterexample. The generic kernel includes p=2 when exact stripping is supplied.
The integer/cyclotomic orchestration theorem retains its p>=3 boundary.
-/

open scoped NumberField
open scoped BigOperators
open DkMath.CosmicFormula DkMath.Lib.NumberTheory

-- 8 * GN₂(8,5) = 12². The chosen factor is 18 = (-2)*(-9).
-- Its stripped ideal is a square, even though the original factor has a ramifier.
example : ∃ I : Ideal ℤ, I ≠ ⊥ ∧ Ideal.span ({-9} : Set ℤ) = I ^ 2 := by
  have hζ : IsPrimitiveRoot (-1 : ℤ) 2 := IsPrimitiveRoot.neg_one 0 (by decide)
  exact exists_ideal_pow_of_stripped_phaseFactor Nat.prime_two hζ
    (by norm_num [Int.prime_iff_natAbs_prime])
    (x := 8) (u := 5) (c := 12) (β := -9)
    (by norm_num [Int.isCoprime_iff_gcd_eq_one]) (by norm_num)
    (by norm_num [GTail, Finset.sum_range_succ]) (i := 1) (by decide)
    (by norm_num) (by norm_num)

-- Actual odd-prime data: x=3, u=1 has no Fermat-equation assumption.
-- The stripped first cubic phase is coprime to the second original phase.
example {K : Type*} [Field K] [NumberField K]
    [Fact (Nat.Prime 3)] [IsCyclotomicExtension {3} ℚ K]
    {ζ : K} (hζ : IsPrimitiveRoot ζ 3) :
    ∃ β : 𝓞 K,
      (3 : 𝓞 K) + (1 - hζ.toInteger) * 1 = (hζ.toInteger - 1) * β ∧
      IsCoprime (Ideal.span ({β} : Set (𝓞 K)))
        (Ideal.span ({(3 : 𝓞 K) + (1 - hζ.toInteger ^ 2) * 1} : Set (𝓞 K))) := by
  obtain ⟨β, hstrip, hβ⟩ := exists_ramified_phase_quotient_of_dvd_gap hζ (by decide)
    (x := 3) (u := 1) (by norm_num) (by norm_num) (i := 1) (by decide) (by decide)
  have hstrip' : (3 : 𝓞 K) + (1 - hζ.toInteger ^ 1) * 1 = (hζ.toInteger - 1) * β := by
    simpa using hstrip
  have hprime := hζ.zeta_sub_one_prime'
  have hmax : (Ideal.span ({hζ.toInteger - 1} : Set (𝓞 K))).IsMaximal :=
    (Ideal.isPrime_span_singleton_of_prime hprime).isMaximal (by
      intro h
      exact hprime.ne_zero (Ideal.span_singleton_eq_bot.mp h))
  refine ⟨β, by simpa only [pow_one] using hstrip', ?_⟩
  exact stripped_phase_span_isCoprime_other Nat.prime_three hζ.toInteger_isPrimitiveRoot
    (x := (3 : 𝓞 K)) (u := 1) ⟨0, 1, by simp⟩ hmax (i := 1) (j := 2)
    (by decide) (by decide) (by decide) hstrip' hβ

-- The ramifier must remain in the complementary ideal product.
-- For the concrete square example, it is coprime to the stripped factor.
example : IsCoprime (Ideal.span ({-9} : Set ℤ)) (Ideal.span ({-2} : Set ℤ)) := by
  have hprime : Prime (-2 : ℤ) := by norm_num [Int.prime_iff_natAbs_prime]
  apply stripped_span_isCoprime_ramifier
  · exact (Ideal.isPrime_span_singleton_of_prime hprime).isMaximal (by
      intro h
      exact hprime.ne_zero (Ideal.span_singleton_eq_bot.mp h))
  · norm_num

-- The whole nontrivial product retains exactly its explicit ramifier ideal.
example : Ideal.span ({GTail 2 1 (8 : ℤ) 5} : Set ℤ) =
    Ideal.span ({-2} : Set ℤ) * Ideal.span ({3} : Set ℤ) ^ 2 := by
  have hζ : IsPrimitiveRoot (-1 : ℤ) 2 := IsPrimitiveRoot.neg_one 0 (by decide)
  have h := span_GTail_eq_ramifier_pow_mul_roots_pow (by decide : 0 < 2) hζ 8 5
    (fun _ => Ideal.span ({3} : Set ℤ)) (by
      intro i hi
      have hi1 : i = 1 := by
        have hn := (Finset.mem_erase.mp hi).1
        have hl := Finset.mem_range.mp (Finset.mem_erase.mp hi).2
        omega
      subst i
      norm_num [Ideal.span_singleton_pow, Ideal.span_singleton_mul_span_singleton,
        Ideal.span_singleton_neg])
  simpa using h

#print axioms DkMath.Lib.NumberTheory.exists_ideal_pow_of_stripped_phaseFactor
#print axioms DkMath.Lib.NumberTheory.exists_ramified_phase_ideal_pow
#print axioms DkMath.FLT.Kummer.GN_ideal_pow_of_ramified_case
#print axioms DkMath.FLT.Kummer.GN_kummer_structure_of_ramified_case
#print axioms DkMath.Lib.NumberTheory.exists_ramified_GTail_ideal_pow

run_cmd do
  let names := #[
    ``DkMath.Lib.NumberTheory.stripped_span_isCoprime_ramifier,
    ``DkMath.Lib.NumberTheory.stripped_phase_span_isCoprime_other,
    ``DkMath.Lib.NumberTheory.exists_ideal_pow_of_stripped_phaseFactor,
    ``DkMath.Lib.NumberTheory.exists_ramified_phase_ideal_pow,
    ``DkMath.Lib.NumberTheory.span_GTail_eq_ramifier_pow_mul_roots_pow,
    ``DkMath.Lib.NumberTheory.exists_ramified_ideal_power_family,
    ``DkMath.Lib.NumberTheory.exists_ramified_GTail_ideal_pow,
    ``DkMath.FLT.Kummer.prime_dvd_gap_of_dvd_right_of_flt_equation,
    ``DkMath.FLT.Kummer.GN_ideal_pow_of_ramified_case,
    ``DkMath.FLT.Kummer.GN_kummer_structure_of_ramified_case]
  for name in names do
    let axioms ← Lean.collectAxioms name
    for ax in axioms do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom {ax} in {name}"
