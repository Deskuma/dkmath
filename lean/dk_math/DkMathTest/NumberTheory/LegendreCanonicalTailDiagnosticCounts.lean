/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMathTest.NumberTheory.LegendreCanonicalTailCalibration

#print "file: DkMathTest.NumberTheory.LegendreCanonicalTailDiagnosticCounts"

namespace DkMathTest.LegendreCanonicalTailDiagnostics
open DkMath.NumberTheory.Legendre DkMathTest.LegendreCanonicalTailCalibration
open DkMathTest.LegendreBlockLocalization
open scoped BigOperators

set_option maxRecDepth 100000
-- Diagnostic rows and long explicit prime inventories need a larger synthesis budget.
set_option synthInstance.maxSize 1024

/-- Sorted explicit prime labels; the Nodup proof avoids recomputing insertion deduplication per seat. -/
def diagnosticActivePrimes (n : ℕ) : Finset ℕ :=
  if n = 47 then ⟨([3,5,7,11,13,17,19,23,29,31,37,41,43] : List ℕ), by decide⟩ else
  if n = 97 then ⟨([3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71,73,79,83,89] : List ℕ), by decide⟩ else
  if n = 127 then ⟨([3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71,73,79,83,89,97,101,103,107,109,113] : List ℕ), by decide⟩ else
  if n = 211 then ⟨([3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71,73,79,83,89,97,101,103,107,109,113,127,131,137,139,149,151,157,163,167,173,179,181,191,193,197,199] : List ℕ), by decide⟩ else
  if n = 503 then ⟨([3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71,73,79,83,89,97,101,103,107,109,113,127,131,137,139,149,151,157,163,167,173,179,181,191,193,197,199,211,223,227,229,233,239,241,251,257,263,269,271,277,281,283,293,307,311,313,317,331,337,347,349,353,359,367,373,379,383,389,397,401,409,419,421,431,433,439,443,449,457,461,463,467,479,487,491,499] : List ℕ), by decide⟩ else
  if n = 1009 then ⟨([3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71,73,79,83,89,97,101,103,107,109,113,127,131,137,139,149,151,157,163,167,173,179,181,191,193,197,199,211,223,227,229,233,239,241,251,257,263,269,271,277,281,283,293,307,311,313,317,331,337,347,349,353,359,367,373,379,383,389,397,401,409,419,421,431,433,439,443,449,457,461,463,467,479,487,491,499,503,509,521,523,541,547,557,563,569,571,577,587,593,599,601,607,613,617,619,631,641,643,647,653,659,661,673,677,683,691,701,709,719,727,733,739,743,751,757,761,769,773,787,797,809,811,821,823,827,829,839,853,857,859,863,877,881,883,887,907,911,919,929,937,941,947,953,967,971,977,983,991,997] : List ℕ), by decide⟩ else
  if n = 1013 then ⟨([3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71,73,79,83,89,97,101,103,107,109,113,127,131,137,139,149,151,157,163,167,173,179,181,191,193,197,199,211,223,227,229,233,239,241,251,257,263,269,271,277,281,283,293,307,311,313,317,331,337,347,349,353,359,367,373,379,383,389,397,401,409,419,421,431,433,439,443,449,457,461,463,467,479,487,491,499,503,509,521,523,541,547,557,563,569,571,577,587,593,599,601,607,613,617,619,631,641,643,647,653,659,661,673,677,683,691,701,709,719,727,733,739,743,751,757,761,769,773,787,797,809,811,821,823,827,829,839,853,857,859,863,877,881,883,887,907,911,919,929,937,941,947,953,967,971,977,983,991,997,1009] : List ℕ), by decide⟩ else
  ∅


def excessData : Finset (ℕ × ℕ) := {(47,21),(97,51),(127,67),(211,139),(503,392),(1009,845),(1013,856)}

def tailData : Finset (ℕ × ℕ × ℕ × ℕ × ℕ) := {
  (47,3,12,9,30),(47,5,16,5,24),(47,7,20,1,21),(47,11,21,0,20),
  (97,3,29,22,64),(97,5,39,12,51),(97,7,46,5,44),(97,11,49,2,39),
  (127,3,42,25,84),(127,5,53,14,67),(127,7,58,9,58),(127,11,60,7,52),
  (211,3,78,61,140),(211,5,105,34,112),(211,7,120,19,96),(211,11,124,15,88),
  (503,3,222,170,334),(503,5,300,92,267),(503,7,336,56,229),(503,11,344,48,208),
  (1009,3,460,385,672),(1009,5,608,237,537),(1009,7,684,161,460),(1009,11,711,134,419),
  (1013,3,461,395,674),(1013,5,620,236,539),(1013,7,699,157,462),(1013,11,748,108,421)}

set_option maxHeartbeats 5000000 in
-- Check complete active prime inventories once, before any seat diagnostics.
theorem prime_inventory_checked : ∀ t ∈ rootData,
    squareAnchorOddActivePrimes t.1 = diagnosticActivePrimes t.1 := by
  simp_rw [oddActive_eq_filter_range]
  decide +kernel

/-- Full E diagnostic normal form; its values are derived from smaller coverage counts. -/
def diagnosticExcess (n : ℕ) : ℕ :=
  ∑ r ∈ (Finset.Icc 1 (2 * n)).filter (fun r => Nat.Coprime n r ∧ (n ^ 2 + r) % 2 = 1),
    (((diagnosticActivePrimes n).filter (fun q => q ∣ n ^ 2 + r)).card - 1)

/-- Explicit finite avoidance at the four diagnostic cutoffs. -/
def diagnosticRoughSeats (n P : ℕ) : Finset ℕ :=
  ((Finset.Icc 1 (2 * n)).filter (fun r => Nat.Coprime n r ∧ (n ^ 2 + r) % 2 = 1)).filter
    (fun r => ∀ a ∈ ({3,5,7,11}:Finset ℕ).filter (fun a => a ≤ P), ¬a ∣ n ^ 2 + r)

/-- Covered cutoff11 rough seats are counted by a bounded existential, without all-label multiplicity evaluation. -/
def diagnosticCoveredEleven (n : ℕ) : Finset ℕ :=
  (diagnosticRoughSeats n 11).filter
    (fun r => ∃ q ∈ diagnosticActivePrimes n, q ∣ n ^ 2 + r)

def coveredElevenData : Finset (ℕ × ℕ) :=
  {(47,7),(97,17),(127,29),(211,46),(503,127),(1009,268),(1013,274)}

set_option maxHeartbeats 20000000 in
-- Evaluate only whether each rough seat has a supported label, not its full support card.
theorem covered_eleven_checked : ∀ c ∈ coveredElevenData,
    (diagnosticCoveredEleven c.1).card = c.2 := by
  decide +kernel

/-- Pure numeric row matching supplies E=head11+roughI11-roughCovered11. -/
theorem diagnostic_excess_inputs : ∀ e ∈ excessData, ∃ t ∈ rootData, t.1=e.1 ∧
    ∃ r ∈ roughData, r.1=e.1 ∧ ∃ c ∈ coveredElevenData, c.1=e.1 ∧
      e.2 = t.2.2.2.1 + t.2.2.2.2.1 + t.2.2.2.2.2.1 + t.2.2.2.2.2.2 + r.2.2 - c.2 := by
  decide +kernel

set_option maxHeartbeats 12000000 in
-- Candidate coprimality, parity and four finite small-label avoidance filters.
theorem diagnostic_rough_seats_checked : ∀ t ∈ tailData,
    (diagnosticRoughSeats t.1 t.2.1).card = t.2.2.2.2 := by
  decide +kernel

theorem tail_tables_consistent : ∀ v ∈ tailData, ∃ t ∈ rootData, t.1=v.1 ∧ ∃ e ∈ excessData,
    e.1=v.1 ∧ e.2=v.2.2.1 + v.2.2.2.1 ∧
    ((v.2.1=3 ∧ v.2.2.1=t.2.2.2.1) ∨
     (v.2.1=5 ∧ v.2.2.1=t.2.2.2.1 + t.2.2.2.2.1) ∨
     (v.2.1=7 ∧ v.2.2.1=t.2.2.2.1 + t.2.2.2.2.1 + t.2.2.2.2.2.1) ∨
     (v.2.1=11 ∧ v.2.2.1=t.2.2.2.1 + t.2.2.2.2.1 + t.2.2.2.2.2.1 + t.2.2.2.2.2.2)) := by
  decide +kernel

end DkMathTest.LegendreCanonicalTailDiagnostics
