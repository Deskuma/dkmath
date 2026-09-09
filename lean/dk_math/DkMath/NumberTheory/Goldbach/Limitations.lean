/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/
import DkMath.NumberTheory.Goldbach.Capacity
import DkMath.NumberTheory.Goldbach.PrimeWorld
import DkMath.NumberTheory.Goldbach.Signature
import DkMath.NumberTheory.Goldbach.Conservation

#print "file: DkMath.NumberTheory.Goldbach.Limitations"

/-!
# Kernel-checked limitations of stronger proposed shortcuts

These are counterexamples to specific intermediate assertions, not to
Goldbach. At target `12`, incidence is already too large for the naive strict
union bound even though `5+7` is a solution. Endpoint equality invalidates a
raw sieve at target `4`, and proper-divisor exceptions destroy periodicity.
Finally, the same degree-two signature occurs at both prime and composite
targets. None of these examples rules out a different structural proof.
-/

namespace DkMath.NumberTheory

/-- At center six the true cover has four seats, while incidence counts five. -/
theorem goldbach_six_capacity_values :
    (goldbachCoveredSeats 6 (goldbachSmallPrimes 6)).card = 4 ∧
      goldbachIncidence 6 (goldbachSmallPrimes 6) = 5 ∧
      (goldbachSurvivors 6 (goldbachSmallPrimes 6)).card = 1 := by
  decide +kernel

/-- The naive strict total-incidence hypothesis is false as a universal assertion. -/
theorem goldbach_not_universal_strict_incidence :
    ¬ (∀ n : ℕ, 2 ≤ n → goldbachIncidence n (goldbachSmallPrimes n) < n - 1) := by
  intro h
  have hb := h 6 (by omega)
  have he := goldbach_six_capacity_values.2.1
  omega

/-- The exact capacity theorem still closes target twelve, despite incidence overcounting. -/
theorem goldbach_pair_six : GoldbachPairAt 6 := by
  apply (goldbachPairAt_iff_covered_card_lt 6).mpr
  rw [goldbach_six_capacity_values.1]
  omega

/-- At target four the correct interval survivor is the equal pair `2+2`. -/
theorem goldbach_two_survivors : goldbachSurvivors 2 (goldbachSmallPrimes 2) = {0} := by
  decide +kernel

/-- A raw sieve would incorrectly delete the only admissible seat at target four. -/
theorem goldbach_two_raw_interval_empty :
    (goldbachOffsets 2).filter (GoldbachResidueSurvives 2 (goldbachSmallPrimes 2)) = ∅ := by
  decide +kernel

/-- Endpoint-corrected obstruction is not periodic, even when both offsets are admissible. -/
theorem goldbach_proper_obstruction_not_periodic :
    4 ∈ goldbachOffsets 10 ∧ 7 ∈ goldbachOffsets 10 ∧
      GoldbachProperObstructed 10 3 4 ∧ ¬ GoldbachProperObstructed 10 3 (4 + 3) := by
  decide

/-- A nonempty degree-two signature can belong to a composite target. -/
theorem goldbach_signature_does_not_certify_prime :
    2 ∈ goldbachGNSignature 9 ∧ ¬ Nat.Prime 9 := by
  exact ⟨goldbach_two_mem_odd_signature (k := 4) (by omega), by decide⟩

/-- A prime left endpoint with a degree-two signature can reflect to a composite endpoint. -/
theorem goldbach_no_automatic_signature_transport :
    Nat.Prime (6 - 3) ∧ 2 ∈ goldbachGNSignature (6 - 3) ∧ ¬ Nat.Prime (6 + 3) := by
  exact ⟨by decide, goldbach_two_mem_odd_signature (k := 1) (by omega), by decide⟩

/-- The existing PCK old-world branch actually admits a composite endpoint. -/
theorem goldbach_pck_allows_composite_old_branch :
    StructuralArithmetic.PrimeScaleGeneratedBy (Primitive.primeScalesUpTo 3) 6 ∧
      ¬ Nat.Prime 6 := by
  refine ⟨⟨by decide, ?_⟩, by decide⟩
  intro q hq hd
  have hdiv : q ∣ 2 * 3 := hd
  rcases hq.dvd_mul.mp hdiv with htwo | hthree
  · have he : q = 2 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp htwo
    subst q
    exact Primitive.mem_primeScalesUpTo.mpr ⟨Nat.prime_two, by omega⟩
  · have hp3 : Nat.Prime 3 := by decide
    have he : q = 3 := (Nat.prime_dvd_prime_iff_eq hq hp3).mp hthree
    subst q
    exact Primitive.mem_primeScalesUpTo.mpr ⟨hp3, le_rfl⟩

end DkMath.NumberTheory
