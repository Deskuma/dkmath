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

/-- The local Pascal firewall at support size three. -/
example :
    Nat.choose 3 2 = 3 ∧ Nat.choose 3 3 = 1 ∧ 3 - 1 = 2 ∧
      ¬ (Nat.choose 3 2 ≤ 3 - 1) ∧
      Nat.choose 3 2 ≤ (3 - 1) + Nat.choose 3 3 := by
  decide +kernel

/-- At support size four, pair-minus-triple is a strict lower bound. -/
example :
    Nat.choose 4 2 = 6 ∧ Nat.choose 4 3 = 4 ∧ 4 - 1 = 3 ∧
      Nat.choose 4 2 - Nat.choose 4 3 = 2 ∧
      Nat.choose 4 2 - Nat.choose 4 3 ≤ 4 - 1 := by
  decide +kernel

/-- The target-30 window has pair overlap three and no triple overlap. -/
example :
    goldbachWindowPairOverlapCount 15 8 (primeScalesUpTo 5) = 3 ∧
      goldbachWindowTripleOverlapCount 15 8 (primeScalesUpTo 5) = 0 ∧
      goldbachWindowPairOverlapCount 15 8 (primeScalesUpTo 5) -
          goldbachWindowTripleOverlapCount 15 8 (primeScalesUpTo 5) = 3 ∧
      goldbachWindowPairOverlapCount 15 8 (primeScalesUpTo 5) -
          goldbachWindowTripleOverlapCount 15 8 (primeScalesUpTo 5) =
        goldbachWindowOverlapExcess 15 8 (primeScalesUpTo 5) := by
  decide +kernel

/-- The pair-minus-triple budget supplies the conditional target-30 endpoint. -/
example : GoldbachPairAt 15 := by
  apply goldbachPairAt_of_goldbachWindow_residue_capacity_of_pairMinusTriple_budget
    (n := 15) (w := 8) (P := 5)
  all_goals decide +kernel

/-- The canonical target-30 left witnesses are exactly the three unordered
prime pairs from the `P=5` world. -/
example :
    goldbachLeftPairWitness 15 2 3 = 3 ∧
      goldbachLeftPairWitness 15 2 5 = 5 ∧
      goldbachLeftPairWitness 15 3 5 = 0 ∧
      goldbachWindowPairLower 15 8 (primeScalesUpTo 5) = 3 := by
  decide +kernel

example :
    goldbachWindowPairLower 15 8 (primeScalesUpTo 5) ≤
      goldbachWindowPairOverlapCount 15 8 (primeScalesUpTo 5) := by
  apply goldbachWindowPairLower_le_pairOverlap
    (S := primeScalesUpTo 5) (P := 5)
  · exact knownPrimeScales_primeScalesUpTo 5
  · intro r hr
    exact (mem_primeScalesUpTo.mp hr).2
  · decide +kernel
  · decide +kernel

example :
    goldbachWindowPairLower 15 8 (primeScalesUpTo 5) =
        goldbachWindowPairOverlapCount 15 8 (primeScalesUpTo 5) ∧
    goldbachTripleCRTUpperSum 15 8 (primeScalesUpTo 5) =
        goldbachWindowTripleOverlapCount 15 8 (primeScalesUpTo 5) := by
  decide +kernel

/-- The center-aligned target world collapses every local signed class. -/
example : GoldbachCenterAlignedWorld 15 (primeScalesUpTo 5) := by
  rw [show primeScalesUpTo 5 = ({2, 3, 5} : Finset ℕ) by decide +kernel]
  intro r hr
  simp only [Finset.mem_insert, Finset.mem_singleton] at hr
  rcases hr with rfl | rfl | rfl
  all_goals norm_num

example :
    goldbachTripleWitness 15 2 3 5 = 15 ∧
      goldbachTripleCRTUpperSum 15 8 (primeScalesUpTo 5) = 0 := by
  decide +kernel

example :
    goldbachTripleWitness 15 2 3 5 > 8 ∧
      goldbachTripleCRTUpper 15 8 2 3 5 = 0 := by
  decide +kernel

example :
    (∑ r ∈ primeScalesUpTo 5,
      (if r ∣ 2 * 15 then 1 else 2) * (8 / r + 1)) = 10 ∧
      goldbachWindowPairLower 15 8 (primeScalesUpTo 5) = 3 ∧
      goldbachTripleCRTUpperSum 15 8 (primeScalesUpTo 5) = 0 ∧
      10 < (goldbachBalancedOffsets 15 8).card +
        (goldbachWindowPairLower 15 8 (primeScalesUpTo 5) -
          goldbachTripleCRTUpperSum 15 8 (primeScalesUpTo 5)) := by
  decide +kernel

/-! ## CGE-007 signed residue regression -/

/-- Coincident local signs are represented once in the canonical family. -/
example :
    signedPairResidues 15 2 3 = ({3} : Finset ℕ) ∧
      signedPairResidues 15 2 5 = ({5} : Finset ℕ) ∧
      signedPairResidues 15 3 5 = ({0} : Finset ℕ) ∧
      signedTripleResidues 15 2 3 5 = ({15} : Finset ℕ) := by
  decide +kernel

example :
    signedTripleResidues 15 2 3 5 =
      ({goldbachTripleWitness 15 2 3 5} : Finset ℕ) := by
  apply signedTripleResidues_center_aligned_eq_singleton
  all_goals norm_num

example :
    goldbachSignedPairCRTSum 15 8 (primeScalesUpTo 5) = 3 ∧
      goldbachSignedTripleCRTSum 15 8 (primeScalesUpTo 5) = 0 := by
  decide +kernel

example :
    ¬ GoldbachCenterAlignedWorld 50 (primeScalesUpTo 7) := by
  intro hcenter
  have h := hcenter 3 (by decide +kernel)
  norm_num at h

/-- The mixed-sign target is an exact finite accounting regression. -/
example :
    (goldbachBalancedOffsets 50 10).card = 11 ∧
      goldbachWindowPairOverlapCount 50 10 (primeScalesUpTo 7) = 12 ∧
      goldbachWindowTripleOverlapCount 50 10 (primeScalesUpTo 7) = 2 ∧
      goldbachWindowPairOverlapCount 50 10 (primeScalesUpTo 7) -
          goldbachWindowTripleOverlapCount 50 10 (primeScalesUpTo 7) = 10 := by
  decide +kernel

example :
    (∑ r ∈ primeScalesUpTo 7,
      (if r ∣ 2 * 50 then 1 else 2) * (10 / r + 1)) = 21 ∧
      ¬ (21 < (goldbachBalancedOffsets 50 10).card +
        (goldbachWindowPairOverlapCount 50 10 (primeScalesUpTo 7) -
          goldbachWindowTripleOverlapCount 50 10 (primeScalesUpTo 7))) := by
  decide +kernel

example :
    (goldbachSignedPairCRTSum 50 10 (primeScalesUpTo 7) = 12) ∧
      (goldbachSignedTripleCRTSum 50 10 (primeScalesUpTo 7) = 2) := by
  decide +kernel

example :
    (∀ t ∈ goldbachBalancedOffsets 15 8, ∀ r ∈ primeScalesUpTo 5,
      ((t : ZMod r) ∈ goldbachForbiddenResidues 15 r ↔
        r ∈ goldbachObstructionSupportIn 15 t (primeScalesUpTo 5))) := by
  intro t ht r hr
  refine goldbach_signed_pair_raw_iff_support
    (n := 15) (w := 8) (S := primeScalesUpTo 5) (P := 5)
      (t := t) (r := r) ?_ ?_ ?_ ht hr
  · exact knownPrimeScales_primeScalesUpTo 5
  · intro s hs
    exact (mem_primeScalesUpTo.mp hs).2
  · decide +kernel

/-! ## CGE-008 exact signed / Pascal identification -/

example :
    goldbachSignedPairCRTCount 15 8 2 3 =
      (goldbachWindowPairSupportSeats 15 8 (primeScalesUpTo 5) 2 3).card := by
  apply goldbachSignedPairCRTCount_eq_pairSupportSeats_card
    (n := 15) (w := 8) (P := 5) (p := 2) (q := 3)
  · decide +kernel
  · exact knownPrimeScales_primeScalesUpTo 5
  · intro r hr
    exact (mem_primeScalesUpTo.mp hr).2
  · decide +kernel
  · decide +kernel

example :
    goldbachSignedTripleCRTCount 15 8 2 3 5 =
      (goldbachWindowTripleSupportSeats 15 8 (primeScalesUpTo 5) 2 3 5).card := by
  apply goldbachSignedTripleCRTCount_eq_tripleSupportSeats_card
    (n := 15) (w := 8) (P := 5) (p := 2) (q := 3) (r := 5)
  · decide +kernel
  · exact knownPrimeScales_primeScalesUpTo 5
  · intro s hs
    exact (mem_primeScalesUpTo.mp hs).2
  · decide +kernel
  · decide +kernel

example :
    goldbachSignedPairCRTSum 15 8 (primeScalesUpTo 5) =
      goldbachWindowPairOverlapCount 15 8 (primeScalesUpTo 5) ∧
    goldbachSignedTripleCRTSum 15 8 (primeScalesUpTo 5) =
      goldbachWindowTripleOverlapCount 15 8 (primeScalesUpTo 5) := by
  constructor
  · apply goldbachSignedPairCRTSum_eq_windowPairOverlapCount
      (n := 15) (w := 8) (P := 5)
    · decide +kernel
    · exact knownPrimeScales_primeScalesUpTo 5
    · intro r hr
      exact (mem_primeScalesUpTo.mp hr).2
    · decide +kernel
  · apply goldbachSignedTripleCRTSum_eq_windowTripleOverlapCount
      (n := 15) (w := 8) (P := 5)
    · decide +kernel
    · exact knownPrimeScales_primeScalesUpTo 5
    · intro r hr
      exact (mem_primeScalesUpTo.mp hr).2
    · decide +kernel

example :
    goldbachSignedPairCRTSum 50 10 (primeScalesUpTo 7) = 12 ∧
      goldbachSignedTripleCRTSum 50 10 (primeScalesUpTo 7) = 2 ∧
      goldbachWindowPairOverlapCount 50 10 (primeScalesUpTo 7) = 12 ∧
      goldbachWindowTripleOverlapCount 50 10 (primeScalesUpTo 7) = 2 := by
  have hp := knownPrimeScales_primeScalesUpTo 7
  have hb : ∀ ⦃r : ℕ⦄, r ∈ primeScalesUpTo 7 → r ≤ 7 := by
    intro r hr
    exact (mem_primeScalesUpTo.mp hr).2
  have ha : 7 < 50 - 10 := by decide
  have hpair := goldbachSignedPairCRTSum_eq_windowPairOverlapCount
    (n := 50) (w := 10) (P := 7) (S := primeScalesUpTo 7)
    (by decide) hp hb ha
  have htriple := goldbachSignedTripleCRTSum_eq_windowTripleOverlapCount
    (n := 50) (w := 10) (P := 7) (S := primeScalesUpTo 7)
    (by decide) hp hb ha
  exact ⟨by decide +kernel, by decide +kernel,
    hpair ▸ rfl, htriple ▸ rfl⟩

example :
    (goldbachWindowSurvivors 15 8 (primeScalesUpTo 5)).Nonempty := by
  apply goldbachWindowSurvivor_of_residue_capacity_of_signed_crt_budget_exact
    (n := 15) (w := 8) (P := 5) (S := primeScalesUpTo 5)
  · decide +kernel
  · exact knownPrimeScales_primeScalesUpTo 5
  · intro r hr
    exact (mem_primeScalesUpTo.mp hr).2
  · decide +kernel
  · decide +kernel

/-- The signed counts feed the existing Pascal provider only with explicit
comparison hypotheses; the target-30 comparisons are kernel-checked here. -/
example :
    (goldbachWindowSurvivors 15 8 (primeScalesUpTo 5)).Nonempty := by
  apply goldbachWindowSurvivor_of_signed_crt_budget (C := 10)
  · decide +kernel
  · decide +kernel
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

/-! ## CGE-009 exact single-prime incidence regression -/

/-- The target-30 single-prime sum is the exact window incidence nine. -/
example :
    goldbachSignedSingleCRTSum 15 8 (primeScalesUpTo 5) = 9 ∧
      goldbachWindowIncidence 15 8 (primeScalesUpTo 5) = 9 ∧
      goldbachSignedPairCRTSum 15 8 (primeScalesUpTo 5) = 3 ∧
      goldbachSignedTripleCRTSum 15 8 (primeScalesUpTo 5) = 0 ∧
      (goldbachBalancedOffsets 15 8).card = 9 ∧
      9 < 9 + (3 - 0) := by
  decide +kernel

example :
    goldbachSignedSingleCRTCount 15 8 2 = 4 ∧
      goldbachSignedSingleCRTCount 15 8 3 = 3 ∧
      goldbachSignedSingleCRTCount 15 8 5 = 2 := by
  decide +kernel

example :
    goldbachSignedSingleCRTSum 50 10 (primeScalesUpTo 7) = 19 ∧
      goldbachWindowIncidence 50 10 (primeScalesUpTo 7) = 19 ∧
      goldbachSignedSingleCRTCount 50 10 2 = 6 ∧
      goldbachSignedSingleCRTCount 50 10 3 = 7 ∧
      goldbachSignedSingleCRTCount 50 10 5 = 3 ∧
      goldbachSignedSingleCRTCount 50 10 7 = 3 := by
  decide +kernel

example :
    19 < (goldbachBalancedOffsets 50 10).card +
      (goldbachSignedPairCRTSum 50 10 (primeScalesUpTo 7) -
        goldbachSignedTripleCRTSum 50 10 (primeScalesUpTo 7)) ∧
    19 < 21 := by
  decide +kernel

example :
    (goldbachWindowSurvivors 15 8 (primeScalesUpTo 5)).Nonempty := by
  apply goldbachWindowSurvivor_of_exact_signed_crt_budget
    (n := 15) (w := 8) (P := 5) (S := primeScalesUpTo 5)
  · decide +kernel
  · exact knownPrimeScales_primeScalesUpTo 5
  · intro r hr
    exact (mem_primeScalesUpTo.mp hr).2
  · decide +kernel
  · decide +kernel

example : GoldbachPairAt 15 := by
  apply goldbachPairAt_of_exact_signed_crt_budget
    (n := 15) (w := 8) (P := 5)
  all_goals decide +kernel

example : GoldbachPairAt 50 := by
  apply goldbachPairAt_of_exact_signed_crt_budget
    (n := 50) (w := 10) (P := 7)
  all_goals decide +kernel

/-! ## CGE-010 bounded quadruple regression -/

example :
    (goldbachObstructionSupportIn 22 0 (primeScalesUpTo 7)).card = 1 ∧
      (goldbachObstructionSupportIn 22 1 (primeScalesUpTo 7)).card = 2 ∧
      (goldbachObstructionSupportIn 22 2 (primeScalesUpTo 7)).card = 3 ∧
      (goldbachObstructionSupportIn 22 3 (primeScalesUpTo 7)).card = 1 ∧
      (goldbachObstructionSupportIn 22 4 (primeScalesUpTo 7)).card = 2 ∧
      (goldbachObstructionSupportIn 22 5 (primeScalesUpTo 7)).card = 1 ∧
      (goldbachObstructionSupportIn 22 6 (primeScalesUpTo 7)).card = 2 ∧
      (goldbachObstructionSupportIn 22 7 (primeScalesUpTo 7)).card = 2 ∧
      (goldbachObstructionSupportIn 22 8 (primeScalesUpTo 7)).card = 4 ∧
      (goldbachObstructionSupportIn 22 9 (primeScalesUpTo 7)).card = 0 := by
  decide +kernel

example :
    (goldbachBalancedOffsets 22 9).card = 10 ∧
      goldbachWindowIncidence 22 9 (primeScalesUpTo 7) = 18 ∧
      goldbachWindowPairOverlapCount 22 9 (primeScalesUpTo 7) = 13 ∧
      goldbachWindowTripleOverlapCount 22 9 (primeScalesUpTo 7) = 5 ∧
      goldbachWindowQuadrupleOverlapCount 22 9 (primeScalesUpTo 7) = 1 ∧
      goldbachWindowOverlapExcess 22 9 (primeScalesUpTo 7) = 9 ∧
      goldbachSignedQuadrupleCRTSum 22 9 (primeScalesUpTo 7) = 1 := by
  decide +kernel

example :
    ¬ (18 < 10 + (13 - 5)) ∧
      18 < 10 + ((13 - 5) + 1) := by
  decide +kernel

example :
    Nat.choose 5 2 = 10 ∧ Nat.choose 5 3 = 10 ∧
      Nat.choose 5 4 = 5 ∧ 5 - 1 = 4 ∧
      10 - 10 + 5 = 5 ∧ 5 ≠ 4 := by
  decide +kernel

example : (goldbachWindowSurvivors 22 9 (primeScalesUpTo 7)).Nonempty := by
  apply goldbachWindowSurvivor_of_exact_signed_crt_quadruple_budget
    (n := 22) (w := 9) (P := 7) (S := primeScalesUpTo 7)
  · decide +kernel
  · exact knownPrimeScales_primeScalesUpTo 7
  · intro r hr
    exact (mem_primeScalesUpTo.mp hr).2
  · decide +kernel
  · intro t ht
    exact goldbach_support_card_le_four_of_world_card_le_four
      (n := 22) (w := 9) (S := primeScalesUpTo 7) (by decide +kernel) t ht
  · decide +kernel

example : GoldbachPairAt 22 := by
  apply goldbachPairAt_of_exact_signed_crt_quadruple_budget
    (n := 22) (w := 9) (P := 7)
  all_goals decide +kernel

/-! ## CGE-011 full parity-tail regressions -/

example :
    goldbachWindowEvenTailMass 15 8 (primeScalesUpTo 5) = 3 ∧
      goldbachWindowOddTailMass 15 8 (primeScalesUpTo 5) = 0 ∧
      goldbachWindowEvenTailMass 15 8 (primeScalesUpTo 5) =
        goldbachWindowOverlapExcess 15 8 (primeScalesUpTo 5) +
          goldbachWindowOddTailMass 15 8 (primeScalesUpTo 5) := by
  decide +kernel

example :
    goldbachWindowIncidence 50 10 (primeScalesUpTo 7) = 19 ∧
      goldbachWindowEvenTailMass 50 10 (primeScalesUpTo 7) = 12 ∧
      goldbachWindowOddTailMass 50 10 (primeScalesUpTo 7) = 2 ∧
      19 + 2 < 11 + 12 := by
  decide +kernel

example :
    goldbachWindowIncidence 22 9 (primeScalesUpTo 7) = 18 ∧
      goldbachWindowEvenTailMass 22 9 (primeScalesUpTo 7) = 14 ∧
      goldbachWindowOddTailMass 22 9 (primeScalesUpTo 7) = 5 ∧
      14 = 9 + 5 ∧ 13 + 1 = 14 := by
  decide +kernel

example :
    Nat.choose 5 2 = 10 ∧ Nat.choose 5 3 = 10 ∧
      Nat.choose 5 4 = 5 ∧ Nat.choose 5 5 = 1 ∧
      10 + 5 = 15 ∧ 10 + 1 = 11 ∧
      15 = 5 - 1 + 11 ∧ 10 - 10 + 5 = 5 := by
  decide +kernel

example :
    (goldbachObstructionSupportIn 68 0 (primeScalesUpTo 11)).card = 1 ∧
      (goldbachObstructionSupportIn 68 1 (primeScalesUpTo 11)).card = 1 ∧
      (goldbachObstructionSupportIn 68 2 (primeScalesUpTo 11)).card = 5 ∧
      (goldbachObstructionSupportIn 68 3 (primeScalesUpTo 11)).card = 1 ∧
      (goldbachObstructionSupportIn 68 4 (primeScalesUpTo 11)).card = 2 ∧
      (goldbachObstructionSupportIn 68 5 (primeScalesUpTo 11)).card = 2 ∧
      (goldbachObstructionSupportIn 68 6 (primeScalesUpTo 11)).card = 1 ∧
      (goldbachObstructionSupportIn 68 7 (primeScalesUpTo 11)).card = 2 ∧
      (goldbachObstructionSupportIn 68 8 (primeScalesUpTo 11)).card = 3 ∧
      (goldbachObstructionSupportIn 68 9 (primeScalesUpTo 11)).card = 2 ∧
      (goldbachObstructionSupportIn 68 10 (primeScalesUpTo 11)).card = 2 ∧
      (goldbachObstructionSupportIn 68 11 (primeScalesUpTo 11)).card = 1 ∧
      (goldbachObstructionSupportIn 68 12 (primeScalesUpTo 11)).card = 3 ∧
      (goldbachObstructionSupportIn 68 13 (primeScalesUpTo 11)).card = 3 ∧
      (goldbachObstructionSupportIn 68 14 (primeScalesUpTo 11)).card = 2 ∧
      (goldbachObstructionSupportIn 68 15 (primeScalesUpTo 11)).card = 0 := by
  decide +kernel

example :
    (goldbachBalancedOffsets 68 15).card = 16 ∧
      goldbachWindowIncidence 68 15 (primeScalesUpTo 11) = 31 ∧
      (goldbachWindowCoveredSeats 68 15 (primeScalesUpTo 11)).card = 15 ∧
      goldbachWindowPairOverlapCount 68 15 (primeScalesUpTo 11) = 25 ∧
      goldbachWindowTripleOverlapCount 68 15 (primeScalesUpTo 11) = 13 ∧
      goldbachWindowQuadrupleOverlapCount 68 15 (primeScalesUpTo 11) = 5 ∧
      goldbachWindowJOverlapCount 68 15 (primeScalesUpTo 11) 5 = 1 ∧
      goldbachWindowEvenTailMass 68 15 (primeScalesUpTo 11) = 30 ∧
      goldbachWindowOddTailMass 68 15 (primeScalesUpTo 11) = 14 ∧
      goldbachWindowOverlapExcess 68 15 (primeScalesUpTo 11) = 16 := by
  decide +kernel

example :
    goldbachSignedJCRTSum 68 15 (primeScalesUpTo 11) 5 = 1 ∧
      goldbachWindowJOverlapCount 68 15 (primeScalesUpTo 11) 5 = 1 := by
  decide +kernel

example :
    goldbachSignedEvenTailCRTSum 68 15 (primeScalesUpTo 11) = 30 ∧
      goldbachSignedOddTailCRTSum 68 15 (primeScalesUpTo 11) = 14 := by
  have he := goldbachSignedEvenTailCRTSum_eq_windowEvenTailMass
    (n := 68) (w := 15) (P := 11) (S := primeScalesUpTo 11)
    (by decide +kernel) (knownPrimeScales_primeScalesUpTo 11)
    (fun {_} hr => (mem_primeScalesUpTo.mp hr).2) (by decide +kernel)
  have ho := goldbachSignedOddTailCRTSum_eq_windowOddTailMass
    (n := 68) (w := 15) (P := 11) (S := primeScalesUpTo 11)
    (by decide +kernel) (knownPrimeScales_primeScalesUpTo 11)
    (fun {_} hr => (mem_primeScalesUpTo.mp hr).2) (by decide +kernel)
  rw [he, ho]
  decide +kernel

example :
    (goldbachWindowSurvivors 68 15 (primeScalesUpTo 11)).Nonempty ↔
      goldbachSignedSingleCRTSum 68 15 (primeScalesUpTo 11) +
          goldbachSignedOddTailCRTSum 68 15 (primeScalesUpTo 11) <
        (goldbachBalancedOffsets 68 15).card +
          goldbachSignedEvenTailCRTSum 68 15 (primeScalesUpTo 11) := by
  exact goldbachWindowSurvivors_nonempty_iff_exact_signed_parity_budget
    (n := 68) (w := 15) (P := 11) (S := primeScalesUpTo 11)
    (by decide +kernel) (knownPrimeScales_primeScalesUpTo 11)
    (fun {_} hr => (mem_primeScalesUpTo.mp hr).2) (by decide +kernel)

example : GoldbachPairAt 68 := by
  apply goldbachPairAt_of_exact_signed_parity_budget
    (n := 68) (w := 15) (P := 11)
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
#print axioms DkMath.NumberTheory.choose_two_le_sub_one_add_choose_three
#print axioms DkMath.NumberTheory.goldbachWindowPairOverlapCount_le_overlap_add_triple
#print axioms DkMath.NumberTheory.goldbachWindowPairOverlap_sub_triple_le_overlap
#print axioms DkMath.NumberTheory.goldbachPairAt_of_goldbachWindow_residue_capacity_of_pairMinusTriple_budget
#print axioms DkMath.NumberTheory.goldbachLeftPairWitness_dvd_left
#print axioms DkMath.NumberTheory.goldbachTripleWitness_dvd_left
#print axioms DkMath.NumberTheory.goldbachCenterAlignedWorld_forbiddenResidues
#print axioms DkMath.NumberTheory.goldbachTripleWitness_center_aligned_progression
#print axioms DkMath.NumberTheory.signedPairResidues_card_le_four
#print axioms DkMath.NumberTheory.signedTripleResidues_card_le_eight
#print axioms DkMath.NumberTheory.goldbachProgressionSeats_card
#print axioms DkMath.NumberTheory.goldbach_signed_pair_raw_iff_support
#print axioms DkMath.NumberTheory.goldbachWindowSurvivor_of_signed_crt_budget
#print axioms DkMath.NumberTheory.mem_goldbachProgressionSeats_iff_balanced_modEq
#print axioms DkMath.NumberTheory.goldbachSignedPairCRTCount_eq_pairSupportSeats_card
#print axioms DkMath.NumberTheory.goldbachSignedTripleCRTCount_eq_tripleSupportSeats_card
#print axioms DkMath.NumberTheory.signedSingleResidues_card_eq_forbidden
#print axioms DkMath.NumberTheory.goldbachSignedSingleCRTCount_eq_windowBlockedSeats_card
#print axioms DkMath.NumberTheory.goldbachSignedSingleCRTSum_eq_windowIncidence
#print axioms DkMath.NumberTheory.goldbachWindowSurvivor_of_exact_signed_crt_budget
#print axioms DkMath.NumberTheory.goldbachPairAt_of_exact_signed_crt_budget
#print axioms DkMath.NumberTheory.goldbachSignedPairCRTSum_eq_windowPairOverlapCount
#print axioms DkMath.NumberTheory.goldbachSignedTripleCRTSum_eq_windowTripleOverlapCount
#print axioms DkMath.NumberTheory.choose_sub_one_eq_pair_sub_triple_add_quadruple_of_le_four
#print axioms DkMath.NumberTheory.goldbachWindowLocalOverlapExcess_eq_pair_sub_triple_add_quadruple
#print axioms DkMath.NumberTheory.goldbachWindowOverlapExcess_eq_pair_sub_triple_add_quadruple
#print axioms DkMath.NumberTheory.goldbachSignedQuadrupleCRTCount_eq_supportSeats_card
#print axioms DkMath.NumberTheory.goldbachSignedQuadrupleCRTSum_eq_windowQuadrupleOverlapCount
#print axioms DkMath.NumberTheory.goldbachWindowSurvivor_of_exact_signed_crt_quadruple_budget
#print axioms DkMath.NumberTheory.goldbachPairAt_of_exact_signed_crt_quadruple_budget
#print axioms DkMath.NumberTheory.goldbachWindowSurvivor_of_signed_crt_budget_exact
#print axioms DkMath.NumberTheory.goldbachWindowSurvivor_of_residue_capacity_of_signed_crt_budget_exact
#print axioms DkMath.NumberTheory.signedTripleResidues_target_eq_existing_witness
#print axioms DkMath.NumberTheory.signedTripleResidues_center_aligned_eq_singleton
#print axioms DkMath.NumberTheory.goldbachSignedSubsetCRTCount_eq_supportSeats_card
#print axioms DkMath.NumberTheory.goldbachSignedJCRTSum_eq_windowJOverlapCount
#print axioms DkMath.NumberTheory.goldbachWindowLocalEvenTailMass_eq_overlapExcess_add_oddTail
#print axioms DkMath.NumberTheory.goldbachSignedEvenTailCRTSum_eq_windowEvenTailMass
#print axioms DkMath.NumberTheory.goldbachSignedOddTailCRTSum_eq_windowOddTailMass
#print axioms DkMath.NumberTheory.goldbachWindowSurvivors_nonempty_iff_exact_signed_parity_budget
#print axioms DkMath.NumberTheory.goldbachPairAt_of_exact_signed_parity_budget
