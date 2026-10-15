import DkMath.NumberTheory.AKSBridge

open DkMath.NumberTheory DkMath.CosmicFormula

-- Coefficient normalization retains the actual polynomial, including p = 2.
example (n : ℕ) : primeGNUnitStepCorrection 3 n = n ^ 2 + n := by
  simp [primeGNUnitStepCorrection, Finset.sum_range_succ]

example (n : ℕ) : primeGNUnitStepCorrection 2 n = n := by
  simp [primeGNUnitStepCorrection]

example : primeGNAccumulatedCorrection 3 4 = 20 := by decide

example : 4 ^ 3 = 4 + 3 * primeGNAccumulatedCorrection 3 4 :=
  prime_pow_eq_self_add_mul_GN_correction Nat.prime_three 4

example (p : ℕ) : primeGNAccumulatedCorrection p 0 = 0 := by
  simp [primeGNAccumulatedCorrection]

example (u : ℕ) : (∑ n ∈ Finset.range u, GN 1 1 n) = u := by
  exact (sum_GN_unit_steps_eq_pow (Nat.zero_lt_succ 0) u).trans (pow_one u)

example (u : ℕ) : u ^ 3 ≡ u [MOD 3] :=
  prime_pow_modEq_self_via_GN Nat.prime_three

example (u : ZMod 3) : u ^ 3 = u :=
  prime_zmod_gap_compress_via_GN Nat.prime_three u

-- Composite degrees do not have the prime unit-step property.
example : ¬ GN 4 (1 : ℕ) 1 ≡ 1 [MOD 4] := by decide

run_cmd do
  for name in #[
    ``GN_unit_step_eq_one_add_innerBeam,
    ``prime_innerBeam_eq_mul_GN_correction,
    ``prime_GN_unit_step_eq_one_add_mul_correction,
    ``prime_GN_unit_step_modEq_one,
    ``sum_GN_unit_steps_eq_pow,
    ``prime_pow_eq_self_add_mul_GN_correction,
    ``prime_pow_modEq_self_via_GN,
    ``prime_zmod_gap_compress_via_GN] do
    for ax in ← Lean.collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom {ax} in {name}"
