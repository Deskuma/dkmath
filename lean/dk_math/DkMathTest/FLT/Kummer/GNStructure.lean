/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Kummer.GNStructure

/-! Boundary and nonvacuous arithmetic checks for the GN to ideal bridge. -/

open scoped NumberField
open DkMath.CosmicFormula DkMath.Lib.NumberTheory DkMath.FLT.Kummer

-- Zero gap: cancellation at an evaluated x would incorrectly exclude this case.
example {K : Type*} [Field K] [NumberField K]
    [Fact (Nat.Prime 3)] [IsCyclotomicExtension {3} ℚ K]
    {ζ : K} (hζ : IsPrimitiveRoot ζ 3) :
    Algebra.norm ℤ ((1 - hζ.toInteger) * (2 : 𝓞 K)) = 12 := by
  have h := integral_norm_phaseFactor_eq_GTail hζ 0 2
  norm_num [GTail, Finset.sum_range_succ] at h ⊢
  exact h

-- The research note's cubic norm example, valid in any cubic-root cyclotomic field.
example {K : Type*} [Field K] [NumberField K]
    [Fact (Nat.Prime 3)] [IsCyclotomicExtension {3} ℚ K]
    {ζ : K} (hζ : IsPrimitiveRoot ζ 3) :
    Algebra.norm ℤ ((3 : 𝓞 K) - hζ.toInteger) = 13 := by
  have h := integral_norm_phaseFactor_eq_GTail hζ 2 1
  norm_num [GTail, Finset.sum_range_succ] at h
  convert h using 1
  congr 1
  ring

-- Signed coordinates, including a negative parameter, are essential to the FLT adapter.
example : (2 + 3 : ℤ) * GN 3 (2 + 3) (-3) = 35 := by
  rw [signed_GN_identity (by decide)]
  norm_num

-- A real instance of the ideal extraction theorem: 9 * GN₂(9,8) = 15².
-- Both factors 9 and 25 are squares; no hypothetical FLT counterexample is used.
example : ∃ (I : Ideal ℤ) (ε γ : ℤ), I ≠ ⊥ ∧
    Ideal.span ({25} : Set ℤ) = I ^ 2 ∧ IsUnit ε ∧
    Ideal.span ({γ} : Set ℤ) = I ∧ 25 = ε * γ ^ 2 := by
  have hζ : IsPrimitiveRoot (-1 : ℤ) 2 := by
    exact IsPrimitiveRoot.neg_one 0 (by decide)
  have h := GN_kummer_structure_of_unramified (R := ℤ) Nat.prime_two hζ
    (x := 9) (u := 8) (c := 15) (by norm_num)
    (by norm_num [GTail, Finset.sum_range_succ])
    (by norm_num [Int.isCoprime_iff_gcd_eq_one])
    (by norm_num [Int.isCoprime_iff_gcd_eq_one])
    (classGroupPTorsionFreeAt_of_isPrincipalIdealRing 2) (i := 1) (by decide)
  norm_num at h ⊢
  exact h

-- The higher-tail ideal identity includes the zero cut.
example (x u : ℤ) : Ideal.span ({(x + u) ^ 3} : Set ℤ) =
    Ideal.span ({GTail 3 0 x u} : Set ℤ) := by
  simpa using span_tail_remainder 3 0 x u (by decide)

#print axioms DkMath.Lib.NumberTheory.norm_phaseFactor_eq_GTail
#print axioms DkMath.Lib.NumberTheory.integral_norm_phaseFactor_eq_GTail
#print axioms DkMath.Lib.NumberTheory.span_tail_remainder
#print axioms DkMath.Lib.NumberTheory.span_GTail_eq_prod_phase_span
#print axioms DkMath.Lib.NumberTheory.common_prime_contains_ramified
#print axioms DkMath.Lib.NumberTheory.phase_spans_pairwise_isCoprime
#print axioms DkMath.Lib.NumberTheory.GN_kummer_structure_of_unramified
#print axioms DkMath.FLT.Kummer.GN_kummer_structure_of_regular

-- Fail the build if a new bridge starts depending on an admitted theorem or
-- an axiom outside Lean's usual classical kernel foundations.
run_cmd do
  let names := #[
    ``DkMath.Lib.NumberTheory.norm_phaseFactor_eq_GTail,
    ``DkMath.Lib.NumberTheory.integral_norm_phaseFactor_eq_GTail,
    ``DkMath.Lib.NumberTheory.span_tail_remainder,
    ``DkMath.Lib.NumberTheory.span_GTail_eq_prod_phase_span,
    ``DkMath.Lib.NumberTheory.common_prime_contains_ramified,
    ``DkMath.Lib.NumberTheory.phase_spans_pairwise_isCoprime,
    ``DkMath.Lib.NumberTheory.GN_kummer_structure_of_unramified,
    ``DkMath.FLT.Kummer.GN_kummer_structure_of_regular]
  for name in names do
    let axioms ← Lean.collectAxioms name
    for ax in axioms do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom {ax} in {name}"
