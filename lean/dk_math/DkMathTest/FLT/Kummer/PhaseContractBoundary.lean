/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Kummer.RegularPrimeContract

#print "file: DkMathTest.FLT.Kummer.PhaseContractBoundary"

/-!
NOTE-002 の固定契約を、古典的な具体供給を import しない環境で検査する。
供給証明は任意の引数として受け取り、一般終端まで接続できることを確認する。
新しい GN 供給証明を得たという主張はしない。
-/

namespace PhaseContractBoundaryTest

open DkMath.Lib.NumberTheory DkMath.FLT.Kummer
open scoped NumberField

-- Detect an accidental concrete import, rather than only checking theorem types.
run_cmd do
  let env ← Lean.getEnv
  for n in #[
    `DkMath.Lib.NumberTheory.RegularKummer.unit_inv_conj_is_root_of_unity,
    `DkMath.FLT.Kummer.CaseIConjugation.packet_of_factor,
    `DkMath.FLT.Kummer.CaseIConjugation.classical_factor_packet_provider,
    `DkMath.FLT.Kummer.classical_solution_packet_provider,
    `DkMath.FLT.Kummer.regular_kummer_unit_power_criterion,
    `DkMath.FLT.Kummer.regular_prime_conditions,
    `DkMath.Lib.NumberTheory.CyclotomicElevenPID.eleven_pid,
    `DkMath.Lib.NumberTheory.CyclotomicThirteenPID.thirteen_pid] do
    if env.contains n then throwError "Concrete provider leaked into contract consumer: {n}"
  Lean.logInfo "PASS: abstract contract consumer imports no listed classical/concrete providers."

-- Freeze the weakest field assumptions and arbitrary integer modulus of the library contract.
example {p : ℕ} {K : Type*} [Field K] [CharZero K]
    [IsCyclotomicExtension {p} ℚ K] (hp : p.Prime) {ζ : 𝓞 K}
    (hζ : IsPrimitiveRoot ζ p) (f : Fin p → ℤ) (m : ℤ) :
    (m : 𝓞 K) ∣ ∑ i, f i • ζ ^ (i : ℕ) ↔ ∀ i j, m ∣ f i - f j :=
  phase_sum_dvd_iff hp hζ f m

-- Freeze the four original Packet fields, including collision-sensitive adjacency.
example {p : ℕ} {K : Type*} [Field K] (ζ : 𝓞 K) (a b : ℤ)
    (i j : Fin p) (hadj : Int.ModEq p (j : ℤ) ((i : ℤ) - 1))
    (hdiv : (p : 𝓞 K) ∣ (a : 𝓞 K) + b * ζ - a * ζ ^ (i : ℕ) - b * ζ ^ (j : ℕ)) :
    CaseIConjugation.Packet (p := p) ζ a b :=
  ⟨i, j, hadj, hdiv⟩

-- Freeze all five Conditions fields. No step, base case or FLT conclusion is supplied.
example {R : Type*} [CommRing R] [IsDomain R] {p : ℕ} [Fact p.Prime]
    (P : RamifiedPhasePacket R p) (ho : Odd p) (hp3 : 3 ≤ p)
    (hram : (p : R) ∣ P.lambda ^ (p - 1))
    (hfree : classGroupPTorsionFreeAt R p) (hu : KummerUnitPowerCriterion R p) :
    RegularDescent.Conditions P := ⟨ho, hp3, hram, hfree, hu⟩

section Replaceable
variable {p : ℕ} [hp : Fact p.Prime] {K : Type*} [Field K] [NumberField K]
  [IsCyclotomicExtension {p} ℚ K] {ζ : K} (hζ : IsPrimitiveRoot ζ p) (hp5 : 5 ≤ p)

example (hreg : Nat.Coprime p (Fintype.card (ClassGroup (𝓞 K))))
    (factor : CaseIConjugation.FactorPacketProvider (p := p) hζ.toInteger) :
    CaseIConjugation.SolutionPacketProvider (p := p) hζ.toInteger :=
  solution_packet_provider_using hζ hp5 hreg factor

-- These consumers require no particular class-number proof or conjugation implementation.
example (ho : Odd p)
    (source : CaseIConjugation.SolutionPacketProvider (p := p) hζ.toInteger)
    (C : RegularDescent.Conditions (cyclotomicRamifiedPhase hζ ho)) :
    FermatLastTheoremWith ℤ p :=
  fermatLastTheoremWith_int_of_phase_contracts hζ hp5 ho source C

example (ho : Odd p)
    (source : CaseIConjugation.SolutionPacketProvider (p := p) hζ.toInteger)
    (C : RegularDescent.Conditions (cyclotomicRamifiedPhase hζ ho)) :
    FermatLastTheoremFor p :=
  fermatLastTheoremFor_of_phase_contracts hζ hp5 ho source C
end Replaceable

-- Nonzero assumptions cannot be removed from the integer statement.
example {p : ℕ} (hp : 0 < p) : ¬ (∀ a b c : ℤ, a ^ p + b ^ p ≠ c ^ p) := by
  intro h
  exact h 0 1 1 (by simp [zero_pow hp.ne'])

end PhaseContractBoundaryTest
