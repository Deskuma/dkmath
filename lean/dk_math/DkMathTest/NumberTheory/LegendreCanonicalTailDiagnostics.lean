/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMathTest.NumberTheory.LegendreCanonicalTailDiagnosticCounts

#print "file: DkMathTest.NumberTheory.LegendreCanonicalTailDiagnostics"

namespace DkMathTest.LegendreCanonicalTailDiagnostics
open DkMath.NumberTheory.Legendre DkMathTest.LegendreCanonicalTailCalibration
open DkMathTest.LegendreBlockLocalization
open scoped BigOperators

set_option maxRecDepth 100000
-- Diagnostic rows and long explicit prime inventories need a larger synthesis budget.
set_option synthInstance.maxSize 1024

/-- This support normal form is used only in this separate diagnostic module. -/
theorem diagnostic_support_eq {n r : ℕ} (h : squareAnchorOddActivePrimes n = diagnosticActivePrimes n) :
    paritySafeActiveSupport n r = (diagnosticActivePrimes n).filter (fun q => q ∣ n ^ 2 + r) := by
  classical
  ext q
  simp only [mem_paritySafeActiveSupport_iff_dvd,Finset.mem_filter,h]

theorem excess_eq_diagnostic : ∀ t ∈ rootData, paritySafeSupportExcess t.1 = diagnosticExcess t.1 := by
  intro t ht
  unfold paritySafeSupportExcess diagnosticExcess
  rw [candidate_eq_filter_Icc]
  apply Finset.sum_congr rfl
  intro r hr
  rw [diagnostic_support_eq (prime_inventory_checked t ht)]

/-- Exact bridge from the production rough-covered filter to the finite diagnostic selector. -/
theorem rough_covered_eq_diagnostic : ∀ t ∈ rootData,
    (canonicalRoughCandidates t.1 11).filter (fun r => (paritySafeActiveSupport t.1 r).Nonempty) =
      diagnosticCoveredEleven t.1 := by
  classical
  intro t ht
  obtain ⟨hp,hlarge,_,_⟩ := caps_checked t ht
  have he : canonicalRoughCandidates t.1 11 = diagnosticRoughSeats t.1 11 := by
    ext r
    simp only [canonicalRoughCandidates,diagnosticRoughSeats,candidate_eq_filter_Icc,Finset.mem_filter]
    apply and_congr_right
    intro _
    simpa only [Finset.mem_filter] using
      (roughCriterion_smallCutoff (P := 11) (r := r) hp hlarge (by decide))
  unfold diagnosticCoveredEleven
  rw [he]
  apply Finset.filter_congr
  intro r hr
  rw [diagnostic_support_eq (prime_inventory_checked t ht)]
  simp only [Finset.nonempty_def,Finset.mem_filter]

/-- Actual E is recovered from exact head/rough-wave identities and the smaller coverage diagnostic. -/
theorem actual_excess_checked : ∀ e ∈ excessData, paritySafeSupportExcess e.1 = e.2 := by
  intro e he
  obtain ⟨t,ht,hn,r,hr,hrn,c,hc,hcn,hsum⟩ := diagnostic_excess_inputs e he
  obtain ⟨hp,hlarge,_,_⟩ := caps_checked t ht
  have hhead := (head_charges_checked t ht).2.2.2
  rw [hn] at hhead
  obtain ⟨_,_,_,hi,_⟩ := rough_floor_counts_checked r hr
  have hI : (∑ q ∈ squareAnchorOddActivePrimes e.1,
      (canonicalRoughWave e.1 11 q).card) = r.2.2 := by
    rw [roughWave_eleven_sum_eq_count (hn ▸ hp) (hn ▸ hlarge)]
    simpa only [hrn] using hi
  have hC : ((canonicalRoughCandidates e.1 11).filter
      (fun r => (paritySafeActiveSupport e.1 r).Nonempty)).card = c.2 := by
    have hEq := rough_covered_eq_diagnostic t ht
    rw [hn] at hEq
    rw [hEq]
    simpa only [hcn] using covered_eleven_checked c hc
  have hrough := roughWave_sum_eq_covered_add_tail e.1 11
  rw [hI,hC] at hrough
  have hpart := supportExcess_eq_head_add_tail e.1 11
  rw [hhead] at hpart
  omega

/-- The finite full-support normal form has this value, proved without directly evaluating it. -/
theorem diagnostic_excess_checked : ∀ e ∈ excessData, diagnosticExcess e.1 = e.2 := by
  intro e he
  obtain ⟨t,ht,hn,_⟩ := diagnostic_excess_inputs e he
  have H : paritySafeSupportExcess e.1 = diagnosticExcess e.1 := by
    simpa only [hn] using excess_eq_diagnostic t ht
  rw [← H]
  exact actual_excess_checked e he

/-- Actual tail cards after3/5/7/11, never used by the structural prime endpoints. -/
theorem actual_tail_cards_checked : ∀ v ∈ tailData,
    (canonicalRootTail v.1 v.2.1).card = v.2.2.2.1 := by
  intro v hv
  obtain ⟨t,ht,hn,e,he,hen,heSum,hcases⟩ := tail_tables_consistent v hv
  have hdiag : diagnosticExcess v.1 = e.2 := by
    simpa only [hen] using diagnostic_excess_checked e he
  have hnorm : paritySafeSupportExcess v.1 = diagnosticExcess v.1 := by
    simpa only [hn] using excess_eq_diagnostic t ht
  have hheads := head_charges_checked t ht
  have hhead : (canonicalRootHead v.1 v.2.1).card = v.2.2.1 := by
    rw [← hn]
    rcases hcases with ⟨hP,hV⟩ | ⟨hP,hV⟩ | ⟨hP,hV⟩ | ⟨hP,hV⟩
    · rw [hP,hheads.1]; exact hV.symm
    · rw [hP,hheads.2.1]; exact hV.symm
    · rw [hP,hheads.2.2.1]; exact hV.symm
    · rw [hP,hheads.2.2.2]; exact hV.symm
  have hpart := supportExcess_eq_head_add_tail v.1 v.2.1
  rw [hnorm,hdiag,hhead] at hpart
  omega

/-- Actual rough seat cards at all cutoffs, obtained by explicit finite avoidance. -/
theorem actual_rough_seat_cards_checked : ∀ v ∈ tailData,
    (canonicalRoughCandidates v.1 v.2.1).card = v.2.2.2.2 := by
  intro v hv
  obtain ⟨t,ht,hn,e,he,hen,heSum,hcases⟩ := tail_tables_consistent v hv
  obtain ⟨hp,hlarge,_,_⟩ := caps_checked t ht
  have hP : v.2.1 ∈ ({3,5,7,11}:Finset ℕ) := by
    rcases hcases with ⟨hP,_⟩ | ⟨hP,_⟩ | ⟨hP,_⟩ | ⟨hP,_⟩ <;> simp [hP]
  have hEq : canonicalRoughCandidates v.1 v.2.1 = diagnosticRoughSeats v.1 v.2.1 := by
    unfold diagnosticRoughSeats canonicalRoughCandidates
    rw [candidate_eq_filter_Icc]
    congr 1
    funext r
    apply propext
    exact roughCriterion_smallCutoff (hn ▸ hp) (hn ▸ hlarge) hP
  rw [hEq]
  exact diagnostic_rough_seats_checked v hv

end DkMathTest.LegendreCanonicalTailDiagnostics
