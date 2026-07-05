/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Collatz.PetalBridge.PressureAdjacentDiagnosis

#print "file: DkMath.Collatz.PetalBridge.PressureDiagnosticDecomposition"

namespace DkMath.Collatz

/-
Bounded diagnostic decomposition helpers for explicit witness lists.

This module is a refactor-only split from `PressureAdjacentDiagnosis`.  It
keeps the bounded length-two, length-three, and length-four helper theorems
separate from the core diagnostic carriers and constructors.  Nothing here
adds arbitrary-list coverage, maximality, uniqueness, canonical selection,
enumeration, union accounting, overlap repair, aggregation, or Collatz
convergence.
-/

/--
In a two-element explicit witness list, the only adjacent-pair address is the
head pair.

This is a two-element normal form only.  It does not choose a canonical pair in
longer lists and does not enumerate diagnostics.
-/
theorem SourcePressureLocalIslandWitnessAdjacentPairInList.two_iff_head
    {n : OddNat} {k r : ℕ}
    {W1 W2 A B : SourcePressureLocalIslandWitness n k r} :
    SourcePressureLocalIslandWitnessAdjacentPairInList [W1, W2] A B ↔
      A = W1 ∧ B = W2 := by
  constructor
  · intro h
    rcases h with hhead | htail
    · exact hhead
    · exact False.elim
        (SourcePressureLocalIslandWitnessAdjacentPairInList.singleton_false htail)
  · rintro ⟨rfl, rfl⟩
    exact SourcePressureLocalIslandWitnessAdjacentPairInList.head

/-- Extract the head-pair equality from a two-element adjacent-pair address. -/
theorem SourcePressureLocalIslandWitnessAdjacentPairInList.two_eq
    {n : OddNat} {k r : ℕ}
    {W1 W2 A B : SourcePressureLocalIslandWitness n k r}
    (h : SourcePressureLocalIslandWitnessAdjacentPairInList [W1, W2] A B) :
    A = W1 ∧ B = W2 :=
  SourcePressureLocalIslandWitnessAdjacentPairInList.two_iff_head.mp h

/--
In a three-element explicit witness list, an adjacent-pair address is either
the head pair or an adjacent-pair address in the two-element tail.

This is a bounded three-element decomposition only.  It does not enumerate
diagnostics in arbitrary lists.
-/
theorem SourcePressureLocalIslandWitnessAdjacentPairInList.three_head_or_tail
    {n : OddNat} {k r : ℕ}
    {W1 W2 W3 A B : SourcePressureLocalIslandWitness n k r}
    (h : SourcePressureLocalIslandWitnessAdjacentPairInList [W1, W2, W3] A B) :
    (A = W1 ∧ B = W2) ∨
      SourcePressureLocalIslandWitnessAdjacentPairInList [W2, W3] A B :=
  h

/--
In a four-element explicit witness list, an adjacent-pair address is either
the head pair or an adjacent-pair address in the three-element tail.

This is a bounded four-element decomposition only.  It does not enumerate
diagnostics in arbitrary lists.
-/
theorem SourcePressureLocalIslandWitnessAdjacentPairInList.four_head_or_tail
    {n : OddNat} {k r : ℕ}
    {W1 W2 W3 W4 A B : SourcePressureLocalIslandWitness n k r}
    (h : SourcePressureLocalIslandWitnessAdjacentPairInList [W1, W2, W3, W4] A B) :
    (A = W1 ∧ B = W2) ∨
      SourcePressureLocalIslandWitnessAdjacentPairInList [W2, W3, W4] A B :=
  h

set_option linter.style.longLine false in
/--
Build the bundled diagnostic directly from a reversed two-witness list.

For `[W1, W2]`, the only adjacent-pair address is the head pair `W1, W2`.
Thus a witness that `W2` is before `W1` gives the recovered pair-local
accounted family immediately.
-/
theorem SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic.of_two_reversed
    {n : OddNat} {k r : ℕ}
    {W1 W2 : SourcePressureLocalIslandWitness n k r}
    (hrev : SourcePressureLocalIslandWitnessBefore W2 W1) :
    SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic
      [W1, W2] :=
  SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic.of_pair
    SourcePressureLocalIslandWitnessAdjacentPairInList.head
    hrev
    (sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair_sum_le_neg_two
      W1 W2 hrev)
    (sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair_sum_neg
      W1 W2 hrev)
    (sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair_length
      W1 W2 hrev)

set_option linter.style.longLine false in
/--
Extract the reversed-before witness and the bundled pair-local facts from a
two-element diagnostic.

This is a two-element explicit-list normal form only.  It does not choose a
canonical diagnostic in longer lists.
-/
theorem SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic.exists_reversed_of_two
    {n : OddNat} {k r : ℕ}
    {W1 W2 : SourcePressureLocalIslandWitness n k r}
    (h :
      SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic
        [W1, W2]) :
    ∃ hrev : SourcePressureLocalIslandWitnessBefore W2 W1,
      let F :=
        sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair
          W1 W2 hrev
      (((F.items).map
        (fun I => SourcePressureIntervalNetDrop n k r I.start I.len)).sum ≤ -2) ∧
        (((F.items).map
          (fun I => SourcePressureIntervalNetDrop n k r I.start I.len)).sum < 0) ∧
        F.items.length = 2 := by
  rcases h.exists_pair with ⟨A, B, hin, hrev, hbudget, hneg, hlen⟩
  rcases SourcePressureLocalIslandWitnessAdjacentPairInList.two_eq hin with
    ⟨rfl, rfl⟩
  exact ⟨hrev, hbudget, hneg, hlen⟩

set_option linter.style.longLine false in
/--
Two-element normal form for the bundled diagnostic carrier.

The equivalence is only for the explicit two-witness list `[W1, W2]`.  It does
not assert uniqueness or canonical selection for arbitrary lists.
-/
theorem SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic.two_iff
    {n : OddNat} {k r : ℕ}
    {W1 W2 : SourcePressureLocalIslandWitness n k r} :
    SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic
      [W1, W2] ↔
    ∃ hrev : SourcePressureLocalIslandWitnessBefore W2 W1,
      let F :=
        sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair
          W1 W2 hrev
      (((F.items).map
        (fun I => SourcePressureIntervalNetDrop n k r I.start I.len)).sum ≤ -2) ∧
        (((F.items).map
          (fun I => SourcePressureIntervalNetDrop n k r I.start I.len)).sum < 0) ∧
        F.items.length = 2 := by
  constructor
  · exact
      SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic.exists_reversed_of_two
  · rintro ⟨hrev, _hbudget, _hneg, _hlen⟩
    exact
      SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic.of_two_reversed
        hrev

set_option linter.style.longLine false in
/--
Three-element bounded decomposition for the bundled diagnostic carrier.

A diagnostic on `[W1, W2, W3]` is either carried by the head pair `W1, W2`,
or it is already a diagnostic on the two-element tail `[W2, W3]`.
This theorem only decomposes the explicit three-element list; it does not
enumerate diagnostics in arbitrary lists.
-/
theorem SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic.three_head_or_tail
    {n : OddNat} {k r : ℕ}
    {W1 W2 W3 : SourcePressureLocalIslandWitness n k r}
    (h :
      SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic
        [W1, W2, W3]) :
    (∃ hrev : SourcePressureLocalIslandWitnessBefore W2 W1,
      let F :=
        sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair
          W1 W2 hrev
      (((F.items).map
        (fun I => SourcePressureIntervalNetDrop n k r I.start I.len)).sum ≤ -2) ∧
        (((F.items).map
          (fun I => SourcePressureIntervalNetDrop n k r I.start I.len)).sum < 0) ∧
        F.items.length = 2)
    ∨
      SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic
        [W2, W3] := by
  rcases h.exists_pair with ⟨A, B, hin, hrev, hbudget, hneg, hlen⟩
  rcases SourcePressureLocalIslandWitnessAdjacentPairInList.three_head_or_tail
      hin with hhead | htail
  · rcases hhead with ⟨rfl, rfl⟩
    exact Or.inl ⟨hrev, hbudget, hneg, hlen⟩
  · exact Or.inr
      (SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic.of_pair
        htail hrev hbudget hneg hlen)

set_option linter.style.longLine false in
/--
Iff form of the three-element diagnostic decomposition.

The reverse direction either builds the head-pair diagnostic from the reversed
witness and lifts it through the tail API, or lifts an existing tail diagnostic.
-/
theorem SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic.three_iff_head_or_tail
    {n : OddNat} {k r : ℕ}
    {W1 W2 W3 : SourcePressureLocalIslandWitness n k r} :
    SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic
      [W1, W2, W3] ↔
    ((∃ hrev : SourcePressureLocalIslandWitnessBefore W2 W1,
      let F :=
        sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair
          W1 W2 hrev
      (((F.items).map
        (fun I => SourcePressureIntervalNetDrop n k r I.start I.len)).sum ≤ -2) ∧
        (((F.items).map
          (fun I => SourcePressureIntervalNetDrop n k r I.start I.len)).sum < 0) ∧
        F.items.length = 2)
    ∨
      SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic
        [W2, W3]) := by
  constructor
  · exact
      SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic.three_head_or_tail
  · intro h
    rcases h with hhead | htail
    · rcases hhead with ⟨hrev, _hbudget, _hneg, _hlen⟩
      exact
        SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic.of_pair
          SourcePressureLocalIslandWitnessAdjacentPairInList.head
          hrev
          (sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair_sum_le_neg_two
            W1 W2 hrev)
          (sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair_sum_neg
            W1 W2 hrev)
          (sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair_length
            W1 W2 hrev)
    · exact
        SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic.of_tail
          htail

set_option linter.style.longLine false in
/--
Four-element bounded decomposition for the bundled diagnostic carrier.

A diagnostic on `[W1, W2, W3, W4]` is either carried by the head pair `W1, W2`,
or it is already a diagnostic on the three-element tail `[W2, W3, W4]`.
This theorem only decomposes the explicit four-element list; it does not
enumerate diagnostics in arbitrary lists.
-/
theorem SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic.four_head_or_tail
    {n : OddNat} {k r : ℕ}
    {W1 W2 W3 W4 : SourcePressureLocalIslandWitness n k r}
    (h :
      SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic
        [W1, W2, W3, W4]) :
    (∃ hrev : SourcePressureLocalIslandWitnessBefore W2 W1,
      let F :=
        sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair
          W1 W2 hrev
      (((F.items).map
        (fun I => SourcePressureIntervalNetDrop n k r I.start I.len)).sum ≤ -2) ∧
        (((F.items).map
          (fun I => SourcePressureIntervalNetDrop n k r I.start I.len)).sum < 0) ∧
        F.items.length = 2)
    ∨
      SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic
        [W2, W3, W4] := by
  rcases h.exists_pair with ⟨A, B, hin, hrev, hbudget, hneg, hlen⟩
  rcases SourcePressureLocalIslandWitnessAdjacentPairInList.four_head_or_tail
      hin with hhead | htail
  · rcases hhead with ⟨rfl, rfl⟩
    exact Or.inl ⟨hrev, hbudget, hneg, hlen⟩
  · exact Or.inr
      (SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic.of_pair
        htail hrev hbudget hneg hlen)

set_option linter.style.longLine false in
/--
Iff form of the four-element diagnostic decomposition.

The reverse direction either builds the head-pair diagnostic directly from the
reversed witness, or lifts an existing tail diagnostic.  This is still bounded
to `[W1, W2, W3, W4]`.
-/
theorem SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic.four_iff_head_or_tail
    {n : OddNat} {k r : ℕ}
    {W1 W2 W3 W4 : SourcePressureLocalIslandWitness n k r} :
    SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic
      [W1, W2, W3, W4] ↔
    ((∃ hrev : SourcePressureLocalIslandWitnessBefore W2 W1,
      let F :=
        sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair
          W1 W2 hrev
      (((F.items).map
        (fun I => SourcePressureIntervalNetDrop n k r I.start I.len)).sum ≤ -2) ∧
        (((F.items).map
          (fun I => SourcePressureIntervalNetDrop n k r I.start I.len)).sum < 0) ∧
        F.items.length = 2)
    ∨
      SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic
        [W2, W3, W4]) := by
  constructor
  · exact
      SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic.four_head_or_tail
  · intro h
    rcases h with hhead | htail
    · rcases hhead with ⟨hrev, _hbudget, _hneg, _hlen⟩
      exact
        SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic.of_pair
          SourcePressureLocalIslandWitnessAdjacentPairInList.head
          hrev
          (sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair_sum_le_neg_two
            W1 W2 hrev)
          (sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair_sum_neg
            W1 W2 hrev)
          (sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair_length
            W1 W2 hrev)
    · exact
        SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic.of_tail
          htail

set_option linter.style.longLine false in
/--
Two-element consumer form: failure plus named no-adjacent-overlap yields the
reversed-before witness for the only adjacent pair.

This is only the `[W1, W2]` normal form.  It does not select a canonical pair in
longer lists.
-/
theorem
    sourcePressureLocalIslandWitnessList_failure_two_exists_reversed_of_noAdjacentOverlap
    {n : OddNat} {k r : ℕ}
    {W1 W2 : SourcePressureLocalIslandWitness n k r}
    (h :
      SourcePressureLocalIslandWitnessListHasSortedBeforeFailure [W1, W2])
    (hno :
      SourcePressureLocalIslandWitnessListHasNoAdjacentOverlapObstruction [W1, W2]) :
    ∃ hrev : SourcePressureLocalIslandWitnessBefore W2 W1,
      let F :=
        sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair
          W1 W2 hrev
      (((F.items).map
        (fun I => SourcePressureIntervalNetDrop n k r I.start I.len)).sum ≤ -2) ∧
        (((F.items).map
          (fun I => SourcePressureIntervalNetDrop n k r I.start I.len)).sum < 0) ∧
        F.items.length = 2 :=
  (sourcePressureLocalIslandWitnessList_failure_hasRecoveredAdjacentAccountedFamilyDiagnostic_of_noAdjacentOverlap
    h hno).exists_reversed_of_two

set_option linter.style.longLine false in
/--
Three-element consumer form: failure plus named no-adjacent-overlap yields
either the head-pair recovered branch or a diagnostic on the two-element tail.

This is still a bounded decomposition for `[W1, W2, W3]`; it does not enumerate
or aggregate diagnostics in longer lists.
-/
theorem
    sourcePressureLocalIslandWitnessList_failure_three_diagnostic_head_or_tail_of_noAdjacentOverlap
    {n : OddNat} {k r : ℕ}
    {W1 W2 W3 : SourcePressureLocalIslandWitness n k r}
    (h :
      SourcePressureLocalIslandWitnessListHasSortedBeforeFailure [W1, W2, W3])
    (hno :
      SourcePressureLocalIslandWitnessListHasNoAdjacentOverlapObstruction
        [W1, W2, W3]) :
    (∃ hrev : SourcePressureLocalIslandWitnessBefore W2 W1,
      let F :=
        sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair
          W1 W2 hrev
      (((F.items).map
        (fun I => SourcePressureIntervalNetDrop n k r I.start I.len)).sum ≤ -2) ∧
        (((F.items).map
          (fun I => SourcePressureIntervalNetDrop n k r I.start I.len)).sum < 0) ∧
        F.items.length = 2)
    ∨
      SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic
        [W2, W3] :=
  (sourcePressureLocalIslandWitnessList_failure_hasRecoveredAdjacentAccountedFamilyDiagnostic_of_noAdjacentOverlap
    h hno).three_head_or_tail

set_option linter.style.longLine false in
/--
Four-element consumer form: failure plus named no-adjacent-overlap yields
either the head-pair recovered branch or a diagnostic on the three-element tail.

This remains a bounded decomposition for `[W1, W2, W3, W4]`; it does not
enumerate or aggregate diagnostics in longer lists.
-/
theorem
    sourcePressureLocalIslandWitnessList_failure_four_diagnostic_head_or_tail_of_noAdjacentOverlap
    {n : OddNat} {k r : ℕ}
    {W1 W2 W3 W4 : SourcePressureLocalIslandWitness n k r}
    (h :
      SourcePressureLocalIslandWitnessListHasSortedBeforeFailure
        [W1, W2, W3, W4])
    (hno :
      SourcePressureLocalIslandWitnessListHasNoAdjacentOverlapObstruction
        [W1, W2, W3, W4]) :
    (∃ hrev : SourcePressureLocalIslandWitnessBefore W2 W1,
      let F :=
        sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair
          W1 W2 hrev
      (((F.items).map
        (fun I => SourcePressureIntervalNetDrop n k r I.start I.len)).sum ≤ -2) ∧
        (((F.items).map
          (fun I => SourcePressureIntervalNetDrop n k r I.start I.len)).sum < 0) ∧
        F.items.length = 2)
    ∨
      SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic
        [W2, W3, W4] :=
  (sourcePressureLocalIslandWitnessList_failure_hasRecoveredAdjacentAccountedFamilyDiagnostic_of_noAdjacentOverlap
    h hno).four_head_or_tail

end DkMath.Collatz
