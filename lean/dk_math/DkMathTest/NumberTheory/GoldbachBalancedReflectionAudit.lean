/-
Copyright (c) 2026 DkMath contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: DkMath contributors.
-/

import DkMath.NumberTheory.Goldbach

#print "file: DkMathTest.NumberTheory.GoldbachBalancedReflectionAudit"

/-!
# Balanced reflection window audit

The examples exercise the finite window restriction, orientation-independent
Cross-Gap canonicalization, anchor-local survival, and the conditional local
Goldbach bridge.  They do not assert a universal survivor provider.
-/

namespace DkMathTest.NumberTheory.GoldbachBalancedReflectionAudit

open DkMath.NumberTheory
open DkMath.NumberTheory.GoldbachCrossGapExchange
open DkMath.NumberTheory.GoldbachCrossGapEscape
open DkMath.NumberTheory.Primitive
open scoped BigOperators

/-- The central window is an exact filter of the admissible offset fiber. -/
example :
    goldbachBalancedOffsets 15 8 = Finset.range 9 := by
  rw [goldbachBalancedOffsets_eq_range]
  decide +kernel

example : (goldbachBalancedOffsets 15 8).card = 9 := by
  simp [card_goldbachBalancedOffsets]

/-- Every reflection pair with offset at most fourteen preserves target thirty. -/
example : ∀ t : ℕ, t ≤ 14 →
    reflectionLeft 15 t + reflectionRight 15 t = 30 := by
  intro t ht
  exact reflection_endpoints_add (by omega)

/-- The prime balanced offsets reproduce `13+17`, `11+19`, and `7+23`. -/
example :
    2 ∈ goldbachBalancedOffsets 15 8 ∧
      4 ∈ goldbachBalancedOffsets 15 8 ∧
      8 ∈ goldbachBalancedOffsets 15 8 ∧
      reflectionLeft 15 2 + reflectionRight 15 2 = 30 ∧
      reflectionLeft 15 4 + reflectionRight 15 4 = 30 ∧
      reflectionLeft 15 8 + reflectionRight 15 8 = 30 ∧
      Nat.Prime (reflectionLeft 15 2) ∧ Nat.Prime (reflectionRight 15 2) ∧
      Nat.Prime (reflectionLeft 15 4) ∧ Nat.Prime (reflectionRight 15 4) ∧
      Nat.Prime (reflectionLeft 15 8) ∧ Nat.Prime (reflectionRight 15 8) := by
  norm_num [goldbachBalancedOffsets, goldbachOffsets, reflectionLeft,
    reflectionRight]

/-- The endpoint-one reflection is not a Goldbach prime pair. -/
example :
    reflectionLeft 15 14 = 1 ∧ reflectionRight 15 14 = 29 ∧
      reflectionLeft 15 14 + reflectionRight 15 14 = 30 ∧
      ¬ Nat.Prime (reflectionLeft 15 14) := by
  norm_num [reflectionLeft, reflectionRight]

/-- The minimum reflection is a fixed point at target two, but not prime. -/
example :
    reflectionLeft 1 0 = 1 ∧ reflectionRight 1 0 = 1 ∧
      reflectionLeft 1 0 + reflectionRight 1 0 = 2 ∧
      ¬ Nat.Prime (reflectionLeft 1 0) := by
  norm_num [reflectionLeft, reflectionRight]

theorem auditCrossGapFiber :
    CrossGapEvenFiberAt 3 1 2 1 1 2 1 := by
  decide +kernel

/-- Cross-Gap labels are projected to sorted reflection endpoints. -/
example :
    crossGapReflectionOffset 3 1 2 1 1 2 1 = 0 ∧
      crossGapReflectionOffset 3 1 2 1 1 2 1 ∈
        goldbachBalancedOffsets 3 0 := by
  constructor <;> decide +kernel

example :
    reflectionLeft 3 (crossGapReflectionOffset 3 1 2 1 1 2 1) =
        min (crossLeft 1 2 1 1 2 1) (crossRight 1 2 1 1 2 1) ∧
      reflectionRight 3 (crossGapReflectionOffset 3 1 2 1 1 2 1) =
        max (crossLeft 1 2 1 1 2 1) (crossRight 1 2 1 1 2 1) := by
  exact crossGapReflectionOffset_endpoints auditCrossGapFiber

/-- Window conservation is replayed for the concrete local finite world. -/
example :
    (goldbachWindowSurvivors 3 0 (primeScalesUpTo 2)).card +
        (goldbachWindowCoveredSeats 3 0 (primeScalesUpTo 2)).card =
      (goldbachBalancedOffsets 3 0).card := by
  exact goldbachWindow_survivors_add_covered 3 0 (primeScalesUpTo 2)

example :
    (goldbachWindowSurvivors 3 0 (primeScalesUpTo 2)).card +
        (goldbachWindowCoveredSeats 3 0 (primeScalesUpTo 2)).card = 1 := by
  decide +kernel

/-- The width-local block capacity uses `w / r + 1`, not the full-fiber width. -/
example :
    (goldbachWindowBlockedSeats 15 8 2).card ≤
      (if 2 ∣ 2 * 15 then 1 else 2) * (8 / 2 + 1) := by
  exact goldbachWindow_blocked_card_le_residue_capacity 15 8 2

/-- The target-30 window has six covered seats and nine incidences. -/
example :
    (goldbachWindowCoveredSeats 15 8 (primeScalesUpTo 5)).card = 6 ∧
      goldbachWindowIncidence 15 8 (primeScalesUpTo 5) = 9 ∧
      goldbachWindowOverlapExcess 15 8 (primeScalesUpTo 5) = 3 := by
  decide +kernel

example :
    (∑ r ∈ primeScalesUpTo 5,
      (if r ∣ 2 * 15 then 1 else 2) * (8 / r + 1)) = 10 ∧
      ¬ (10 < (goldbachBalancedOffsets 15 8).card) ∧
      10 < (goldbachBalancedOffsets 15 8).card +
        goldbachWindowOverlapExcess 15 8 (primeScalesUpTo 5) := by
  decide +kernel

/-- Exact incidence conservation is replayed on the target-30 finite window. -/
example :
    (goldbachWindowSurvivors 15 8 (primeScalesUpTo 5)).card +
        goldbachWindowIncidence 15 8 (primeScalesUpTo 5) =
      (goldbachBalancedOffsets 15 8).card +
        goldbachWindowOverlapExcess 15 8 (primeScalesUpTo 5) := by
  exact goldbachWindowIncidenceConservation 15 8 (primeScalesUpTo 5)

example :
    (goldbachWindowSurvivors 15 8 (primeScalesUpTo 5)).Nonempty := by
  apply goldbachWindowSurvivor_of_residue_capacity_of_overlap_lower
    (S := primeScalesUpTo 5) (e := 3)
  · decide +kernel
  · decide +kernel

/-- A surviving seat enters the `P=2` shell and closes to Goldbach. -/
example : GoldbachPairAt 3 := by
  apply goldbachPairAt_of_goldbachWindowSurvivor
    (n := 3) (w := 0) (P := 2) (t := 0)
  all_goals decide +kernel

/-- The strict window-cover shortfall is a conditional provider interface. -/
example : GoldbachPairAt 3 := by
  apply goldbachPairAt_of_goldbachWindow_cover_shortfall
    (n := 3) (w := 0) (P := 2)
  all_goals decide +kernel

end DkMathTest.NumberTheory.GoldbachBalancedReflectionAudit

#print axioms DkMath.NumberTheory.goldbachWindow_survivors_add_covered
#print axioms DkMath.NumberTheory.crossGapReflectionOffset_min_max
#print axioms DkMath.NumberTheory.prime_pair_of_goldbachWindowSurvivor
#print axioms DkMath.NumberTheory.goldbachPairAt_of_goldbachWindow_cover_shortfall
#print axioms DkMath.NumberTheory.goldbachWindow_blocked_card_le_residue_capacity
#print axioms DkMath.NumberTheory.goldbachWindowIncidence_eq_covered_add_overlapExcess
#print axioms DkMath.NumberTheory.goldbachWindowIncidenceConservation
#print axioms DkMath.NumberTheory.goldbachWindowSurvivor_of_incidence_le_of_overlap_le
