/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/
import DkMath.NumberTheory.Goldbach

#print "file: DkMathTest.NumberTheory.GoldbachGNFiber"

/-!
# Goldbach GN fiber regressions and axiom audit

Finite checks exercise endpoint equality, the inclusive square-root cutoff,
CRT cardinality, refinement, overlap, and the full finite decision procedure.
The bounded range certificate is not a proof of the universal conjecture.
All computational proofs use kernel reduction, not native decision oracles.
-/

namespace DkMathTest.NumberTheory.GoldbachGNFiber

open DkMath.NumberTheory

/-- The equal pair at target four survives the exact endpoint exceptions. -/
example : GoldbachGNFiberAt 2 := by decide +kernel

/-- A pair containing the cutoff prime three must remain available at target ten. -/
example : 2 ∈ goldbachSurvivors 5 (goldbachSmallPrimes 5) := by decide +kernel

/-- A square endpoint must be caught even when its prime factor is exactly at the cutoff. -/
example : 11 ∈ goldbachOffsets 14 ∧ 5 ∈ goldbachSmallPrimes 14 ∧
    GoldbachProperObstructed 14 5 11 := by
  decide +kernel

/-- The forbidden classes coalesce for a divisor of the center and for parity. -/
example : (goldbachForbiddenResidues 6 3).card = 1 ∧
    (goldbachForbiddenResidues 5 3).card = 2 ∧
    (goldbachForbiddenResidues 5 2).card = 1 := by decide +kernel

/-- The paired 30-wheel retains the exact CRT product count. -/
example : (goldbachPairedPHZ30 15).card = 8 := by decide +kernel

/-- Empty-world CRT has its single canonical residue. -/
example : goldbachPrimeWorldResidues 7 ∅ = {0} := by decide +kernel

/-- Adding a prime deletes precisely the seats with a new proper obstruction. -/
example : goldbachSurvivors 6 {2} = {1, 3} ∧
    goldbachSurvivors 6 {2, 3} = {1} := by decide +kernel

/-- Centers zero and one have no prime pair. -/
example : ¬ GoldbachPairAt 0 ∧ ¬ GoldbachPairAt 1 := by decide +kernel

/-- Kernel-checked bounded verification for even targets four through two hundred. -/
theorem goldbach_centers_two_through_one_hundred :
    ∀ n ∈ Finset.range 101, 2 ≤ n → GoldbachPairAt n := by
  decide +kernel

#print axioms goldbach_centers_two_through_one_hundred
#print axioms goldbachPairAt_iff_gnFiberAt
#print axioms goldbach_failure_iff_finite_cover
#print axioms goldbach_card_primeWorld
#print axioms goldbach_primeWorld_nonempty
#print axioms goldbach_blocked_card_le_residue_capacity
#print axioms goldbach_paired_primitive_dichotomy
#print axioms goldbach_signature_constraints
#print axioms goldbach_not_universal_strict_incidence
#print axioms strongGoldbach_iff_capacityEscape
#print axioms strongGoldbach_of_capacityEscape

end DkMathTest.NumberTheory.GoldbachGNFiber
