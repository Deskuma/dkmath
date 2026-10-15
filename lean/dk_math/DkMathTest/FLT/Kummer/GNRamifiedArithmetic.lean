/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Kummer.GNRamifiedArithmetic

open scoped NumberField
open DkMath.CosmicFormula DkMath.Lib.NumberTheory DkMath.FLT.Kummer

-- Signed coordinates and x=0 are admitted by the arithmetic congruence.
example : GTail 3 1 (-3 : ℤ) (-1) ≡ 3 [ZMOD (3 : ℤ) ^ 2] := by
  simpa using integral_GN_modEq_head_mod_prime_sq Nat.prime_three (by decide)
    (x := -3) (u := -1) (by norm_num)

example : ∃ M : ℤ, GTail 3 1 3 (-1) = 3 + 9 * M := by
  simpa using integral_GN_eq_head_add_prime_sq_mul Nat.prime_three (by decide)
    (x := 3) (u := -1) (by norm_num)

example : padicValInt 3 (GTail 3 1 (0 : ℤ) (-1)) = 1 := by
  exact padicValInt_GN_eq_one_of_dvd_gap (by decide) (by norm_num) (by norm_num)

example : padicValInt 5 (GTail 5 1 (-10 : ℤ) 3) = 1 := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  exact padicValInt_GN_eq_one_of_dvd_gap (by decide) (by norm_num) (by norm_num)

-- Both odd-prime and parameter-unit hypotheses are mathematically necessary.
example : (2 : ℤ) ^ 2 ∣ GTail 2 1 (2 : ℤ) 1 := by decide
example : (3 : ℤ) ^ 2 ∣ GTail 3 1 (3 : ℤ) 3 := by decide

-- Without c≠0, the desired balance becomes 0+1=3*0 under the valuation convention.
example : (0 : ℤ) * GTail 3 1 (0 : ℤ) 1 = 0 ^ 3 ∧
    padicValInt 3 (0 : ℤ) + 1 ≠ 3 * padicValInt 3 (0 : ℤ) := by decide

-- A genuine norm calculation with α=λ, ε=γ=1; no hypothetical FLT solution.
example {K : Type*} [Field K] [NumberField K]
    [Fact (Nat.Prime 3)] [IsCyclotomicExtension {3} ℚ K]
    {ζ : K} (hζ : IsPrimitiveRoot ζ 3) :
    Algebra.norm ℤ (hζ.toInteger - 1) = (3 : ℤ) :=
  integral_norm_ramifier_eq_prime hζ (by decide)

example {K : Type*} [Field K] [NumberField K]
    [Fact (Nat.Prime 3)] [IsCyclotomicExtension {3} ℚ K]
    {ζ : K} (hζ : IsPrimitiveRoot ζ 3) :
    ∃ t : ℤ, GTail 3 1 (0 : ℤ) (-1) = 3 * t ^ 3 := by
  exact exists_integral_GTail_eq_prime_mul_pow_of_ramified_factor hζ (by decide)
    (ε := 1) (γ := 1) isUnit_one (by simp)

-- Extension preserves the actual ideal roots, not only their existence.
example {K : Type*} [Field K] [NumberField K]
    {p : ℕ} [Fact p.Prime] [IsCyclotomicExtension {p} ℚ K]
    {ζ : K} {hζ : IsPrimitiveRoot ζ p} {x u c : ℤ}
    (P : RamifiedIdealPowerPacket hζ x u c)
    (hreg : Nat.Coprime p (Fintype.card (ClassGroup (𝓞 K)))) :
    ∃ Q : RamifiedPrincipalPowerPacket hζ x u c,
      Q.toRamifiedIdealPowerPacket = P ∧ Q.idealRoot = P.idealRoot := by
  obtain ⟨Q, hQ⟩ := P.exists_principal_extension hreg
  exact ⟨Q, hQ, congrArg RamifiedIdealPowerPacket.idealRoot hQ⟩

#print axioms DkMath.Lib.NumberTheory.nonempty_ramifiedIdealPowerPacket
#print axioms DkMath.Lib.NumberTheory.RamifiedIdealPowerPacket.exists_principal_extension
#print axioms DkMath.FLT.Kummer.exists_GN_eq_prime_mul_pow_of_ramified_case

run_cmd do
  for name in #[
    ``integral_norm_ramifier_eq_prime,
    ``integral_GN_eq_head_add_prime_sq_mul,
    ``integral_GN_modEq_head_mod_prime_sq,
    ``integral_GN_prime_dvd_and_not_sq,
    ``padicValInt_GN_eq_one_of_dvd_gap,
    ``padicValInt_gap_add_one_eq_prime_mul,
    ``RamifiedIdealPowerPacket.rootProduct_ne_bot,
    ``nonempty_ramifiedIdealPowerPacket,
    ``RamifiedIdealPowerPacket.exists_principal_extension,
    ``exists_integral_GTail_eq_prime_mul_pow_of_ramified_factor,
    ``RamifiedPrincipalPowerPacket.exists_integral_root,
    ``padicValInt_gap_add_one_of_ramified_case,
    ``padicValInt_gap_of_ramified_case,
    ``nonempty_GN_ramified_packet_of_flt_equation,
    ``exists_GN_eq_prime_mul_pow_of_ramified_case] do
    for ax in ← Lean.collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom {ax} in {name}"
