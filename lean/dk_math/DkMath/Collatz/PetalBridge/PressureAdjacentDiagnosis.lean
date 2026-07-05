/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Collatz.PetalBridge.PressureLocalWitnessObstruction

#print "file: DkMath.Collatz.PetalBridge.PressureAdjacentDiagnosis"

namespace DkMath.Collatz

/-
Adjacent-diagnosis surface for explicit local-island witness lists.

This module is the first refactor split from `PressureAccounting`.  It keeps
the mathematical contract unchanged: recovered budgets remain attached to the
adjacent pair that produced them, and overlap remains an adjacent obstruction
on the enclosing list.  Nothing here claims maximality, uniqueness, coverage,
prefix behavior, union accounting, sorting, or Collatz convergence.
-/

/--
Carrier predicate for a local adjacent-pair diagnosis inside an enclosing list.

The recovered branch is always pair-local for `A, B`.  The overlap branch is an
adjacent-overlap obstruction on the enclosing list `L`.  This carrier is only a
return-type abbreviation for bounded diagnosis theorems; it does not perform
sorting, merging, coverage, or union accounting.
-/
def SourcePressureLocalIslandWitnessAdjacentDiagnosis
    {n : OddNat} {k r : ℕ}
    (L : List (SourcePressureLocalIslandWitness n k r))
    (A B : SourcePressureLocalIslandWitness n k r) : Prop :=
  (∃ hrev : SourcePressureLocalIslandWitnessBefore B A,
    (((sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair
      A B hrev).items).map
      (fun I => SourcePressureIntervalNetDrop n k r I.start I.len)).sum ≤ -2)
  ∨ SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction L

/-- Constructor for the pair-local recovered branch of adjacent diagnosis. -/
theorem SourcePressureLocalIslandWitnessAdjacentDiagnosis.recovered
    {n : OddNat} {k r : ℕ}
    {L : List (SourcePressureLocalIslandWitness n k r)}
    {A B : SourcePressureLocalIslandWitness n k r}
    (hrev : SourcePressureLocalIslandWitnessBefore B A)
    (hbudget :
      (((sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair
        A B hrev).items).map
        (fun I => SourcePressureIntervalNetDrop n k r I.start I.len)).sum ≤ -2) :
    SourcePressureLocalIslandWitnessAdjacentDiagnosis L A B :=
  Or.inl ⟨hrev, hbudget⟩

/-- Constructor for the enclosing-list overlap branch of adjacent diagnosis. -/
theorem SourcePressureLocalIslandWitnessAdjacentDiagnosis.overlap
    {n : OddNat} {k r : ℕ}
    {L : List (SourcePressureLocalIslandWitness n k r)}
    {A B : SourcePressureLocalIslandWitness n k r}
    (hobs : SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction L) :
    SourcePressureLocalIslandWitnessAdjacentDiagnosis L A B :=
  Or.inr hobs

/-- Eliminate an adjacent diagnosis by handling its two stored branches. -/
theorem SourcePressureLocalIslandWitnessAdjacentDiagnosis.elim
    {n : OddNat} {k r : ℕ}
    {L : List (SourcePressureLocalIslandWitness n k r)}
    {A B : SourcePressureLocalIslandWitness n k r}
    {P : Prop}
    (hdiag : SourcePressureLocalIslandWitnessAdjacentDiagnosis L A B)
    (hrecovered :
      (∃ hrev : SourcePressureLocalIslandWitnessBefore B A,
        (((sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair
          A B hrev).items).map
          (fun I => SourcePressureIntervalNetDrop n k r I.start I.len)).sum ≤ -2) → P)
    (hoverlap : SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction L → P) :
    P := by
  rcases hdiag with hrec | hobs
  · exact hrecovered hrec
  · exact hoverlap hobs

/--
Forget the obstruction-specific part of an adjacent diagnosis.

The recovered branch remains pair-local; the overlap branch is weakened to
ordinary sorted-before failure for the enclosing list.
-/
theorem SourcePressureLocalIslandWitnessAdjacentDiagnosis.recovered_or_listFailure
    {n : OddNat} {k r : ℕ}
    {L : List (SourcePressureLocalIslandWitness n k r)}
    {A B : SourcePressureLocalIslandWitness n k r}
    (hdiag : SourcePressureLocalIslandWitnessAdjacentDiagnosis L A B) :
    (∃ hrev : SourcePressureLocalIslandWitnessBefore B A,
      (((sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair
        A B hrev).items).map
        (fun I => SourcePressureIntervalNetDrop n k r I.start I.len)).sum ≤ -2)
    ∨ SourcePressureLocalIslandWitnessListHasSortedBeforeFailure L := by
  rcases hdiag with hrec | hobs
  · exact Or.inl hrec
  · exact Or.inr
      (SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction.hasSortedBeforeFailure
        hobs)

/--
Length-three diagnosis with the nested branches packed into the adjacent
diagnosis carrier.

This is still bounded to `[W1, W2, W3]`.  The carrier keeps recovered budgets
attached to the adjacent pair that produced them.
-/
theorem sourcePressureLocalIslandWitnessList_failure_threeDiagnosis_carrier
    {n : OddNat} {k r : ℕ}
    {W1 W2 W3 : SourcePressureLocalIslandWitness n k r}
    (h1pos :
      0 < (sourcePressureIntervalPulseAddress_of_localIslandWitness W1).len)
    (h2pos :
      0 < (sourcePressureIntervalPulseAddress_of_localIslandWitness W2).len)
    (h3pos :
      0 < (sourcePressureIntervalPulseAddress_of_localIslandWitness W3).len)
    (h :
      SourcePressureLocalIslandWitnessListHasSortedBeforeFailure [W1, W2, W3]) :
    SourcePressureLocalIslandWitnessAdjacentDiagnosis [W1, W2, W3] W1 W2 ∨
      SourcePressureLocalIslandWitnessAdjacentDiagnosis [W1, W2, W3] W2 W3 := by
  rcases sourcePressureLocalIslandWitnessList_failure_threeDiagnosis
      h1pos h2pos h3pos h with hhead | htail
  · rcases hhead with hrecovered | hobs
    · exact Or.inl (Or.inl hrecovered)
    · exact Or.inl
        (SourcePressureLocalIslandWitnessAdjacentDiagnosis.overlap hobs)
  · rcases htail with hrecovered | hobs
    · exact Or.inr (Or.inl hrecovered)
    · exact Or.inr
        (SourcePressureLocalIslandWitnessAdjacentDiagnosis.overlap hobs)

/--
Lift an adjacent diagnosis on a tail list through a newly supplied head.

Recovered evidence is unchanged and remains attached to the same adjacent pair
`A, B`.  Only overlap evidence is transported to the larger enclosing list.
-/
theorem SourcePressureLocalIslandWitnessAdjacentDiagnosis.lift_tail
    {n : OddNat} {k r : ℕ}
    {W1 W2 : SourcePressureLocalIslandWitness n k r}
    {rest : List (SourcePressureLocalIslandWitness n k r)}
    {A B : SourcePressureLocalIslandWitness n k r}
    (hdiag :
      SourcePressureLocalIslandWitnessAdjacentDiagnosis (W2 :: rest) A B) :
    SourcePressureLocalIslandWitnessAdjacentDiagnosis (W1 :: W2 :: rest) A B := by
  rcases hdiag with hrecovered | hobs
  · exact Or.inl hrecovered
  · exact Or.inr
      (SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction.of_tail
        hobs)

/--
Bounded diagnosis for a four-witness sorted-before failure.

The result is one adjacent diagnosis for one of the three adjacent pairs:
`W1,W2`, `W2,W3`, or `W3,W4`.  Recovered budgets remain attached to the pair
that produced them, and overlap evidence stays an obstruction on the enclosing
four-witness list.
-/
theorem sourcePressureLocalIslandWitnessList_failure_fourDiagnosis_carrier
    {n : OddNat} {k r : ℕ}
    {W1 W2 W3 W4 : SourcePressureLocalIslandWitness n k r}
    (h1pos :
      0 < (sourcePressureIntervalPulseAddress_of_localIslandWitness W1).len)
    (h2pos :
      0 < (sourcePressureIntervalPulseAddress_of_localIslandWitness W2).len)
    (h3pos :
      0 < (sourcePressureIntervalPulseAddress_of_localIslandWitness W3).len)
    (h4pos :
      0 < (sourcePressureIntervalPulseAddress_of_localIslandWitness W4).len)
    (h :
      SourcePressureLocalIslandWitnessListHasSortedBeforeFailure
        [W1, W2, W3, W4]) :
    SourcePressureLocalIslandWitnessAdjacentDiagnosis [W1, W2, W3, W4] W1 W2 ∨
      SourcePressureLocalIslandWitnessAdjacentDiagnosis [W1, W2, W3, W4] W2 W3 ∨
        SourcePressureLocalIslandWitnessAdjacentDiagnosis [W1, W2, W3, W4] W3 W4 := by
  rcases sourcePressureLocalIslandWitnessList_failure_oneStepDiagnosis
      h1pos h2pos h with hhead | htail
  · rcases hhead with hrecovered | hobs
    · exact Or.inl (Or.inl hrecovered)
    · exact Or.inl
        (SourcePressureLocalIslandWitnessAdjacentDiagnosis.overlap hobs)
  · rcases sourcePressureLocalIslandWitnessList_failure_threeDiagnosis_carrier
        h2pos h3pos h4pos htail with htailHead | htailTail
    · exact Or.inr (Or.inl
        (SourcePressureLocalIslandWitnessAdjacentDiagnosis.lift_tail
          htailHead))
    · exact Or.inr (Or.inr
        (SourcePressureLocalIslandWitnessAdjacentDiagnosis.lift_tail
          htailTail))

/--
An ordered adjacent pair occurring in an explicitly supplied witness list.

This predicate recognizes neighboring entries only.  It does not express
arbitrary pair membership, does not sort the list, and does not claim that the
recognized pair is unique or maximal.  It is a small address layer for bounded
diagnosis theorems, so later consumers can say "some adjacent pair in this
list carries the local diagnosis" without introducing a recursive classifier.
-/
def SourcePressureLocalIslandWitnessAdjacentPairInList
    {n : OddNat} {k r : ℕ} :
    List (SourcePressureLocalIslandWitness n k r) →
      SourcePressureLocalIslandWitness n k r →
      SourcePressureLocalIslandWitness n k r →
      Prop
  | [], _, _ => False
  | [_], _, _ => False
  | W1 :: W2 :: rest, A, B =>
      (A = W1 ∧ B = W2) ∨
        SourcePressureLocalIslandWitnessAdjacentPairInList
          (W2 :: rest) A B

/-- The head pair of a list with at least two witnesses is adjacent in that list. -/
theorem SourcePressureLocalIslandWitnessAdjacentPairInList.head
    {n : OddNat} {k r : ℕ}
    {W1 W2 : SourcePressureLocalIslandWitness n k r}
    {rest : List (SourcePressureLocalIslandWitness n k r)} :
    SourcePressureLocalIslandWitnessAdjacentPairInList
      (W1 :: W2 :: rest) W1 W2 :=
  Or.inl ⟨rfl, rfl⟩

/--
An adjacent pair in the tail remains an adjacent pair after adding a new head.
-/
theorem SourcePressureLocalIslandWitnessAdjacentPairInList.tail
    {n : OddNat} {k r : ℕ}
    {W1 W2 A B : SourcePressureLocalIslandWitness n k r}
    {rest : List (SourcePressureLocalIslandWitness n k r)}
    (h :
      SourcePressureLocalIslandWitnessAdjacentPairInList
        (W2 :: rest) A B) :
    SourcePressureLocalIslandWitnessAdjacentPairInList
      (W1 :: W2 :: rest) A B :=
  Or.inr h

/-- Decompose an adjacent-pair address in a nontrivial cons list. -/
theorem SourcePressureLocalIslandWitnessAdjacentPairInList.head_or_tail
    {n : OddNat} {k r : ℕ}
    {W1 W2 A B : SourcePressureLocalIslandWitness n k r}
    {rest : List (SourcePressureLocalIslandWitness n k r)}
    (h :
      SourcePressureLocalIslandWitnessAdjacentPairInList
        (W1 :: W2 :: rest) A B) :
    (A = W1 ∧ B = W2) ∨
      SourcePressureLocalIslandWitnessAdjacentPairInList
        (W2 :: rest) A B :=
  h

/-- Adjacent-pair address in a cons list is exactly head-pair or tail-pair. -/
theorem SourcePressureLocalIslandWitnessAdjacentPairInList.cons_iff_head_or_tail
    {n : OddNat} {k r : ℕ}
    {W1 W2 A B : SourcePressureLocalIslandWitness n k r}
    {rest : List (SourcePressureLocalIslandWitness n k r)} :
    SourcePressureLocalIslandWitnessAdjacentPairInList
      (W1 :: W2 :: rest) A B ↔
    (A = W1 ∧ B = W2) ∨
      SourcePressureLocalIslandWitnessAdjacentPairInList
        (W2 :: rest) A B :=
  Iff.rfl

/-- There is no adjacent pair in the empty witness list. -/
theorem SourcePressureLocalIslandWitnessAdjacentPairInList.nil_false
    {n : OddNat} {k r : ℕ}
    {A B : SourcePressureLocalIslandWitness n k r} :
    ¬ SourcePressureLocalIslandWitnessAdjacentPairInList
      ([] : List (SourcePressureLocalIslandWitness n k r)) A B := by
  intro h
  exact h

/-- There is no adjacent pair in a singleton witness list. -/
theorem SourcePressureLocalIslandWitnessAdjacentPairInList.singleton_false
    {n : OddNat} {k r : ℕ}
    {W A B : SourcePressureLocalIslandWitness n k r} :
    ¬ SourcePressureLocalIslandWitnessAdjacentPairInList [W] A B := by
  intro h
  exact h

/--
A list-level carrier for "some adjacent pair in this explicit list has an
adjacent diagnosis".

The diagnosis is still local to the pair `A, B`.  In particular, recovered
budget evidence remains attached to the adjacent pair that produced it, while
overlap evidence remains an obstruction on the enclosing list.
-/
def SourcePressureLocalIslandWitnessListHasAdjacentDiagnosis
    {n : OddNat} {k r : ℕ}
    (L : List (SourcePressureLocalIslandWitness n k r)) : Prop :=
  ∃ A B,
    SourcePressureLocalIslandWitnessAdjacentPairInList L A B ∧
      SourcePressureLocalIslandWitnessAdjacentDiagnosis L A B

/-- Package an adjacent-pair address and its diagnosis into the list-level carrier. -/
theorem SourcePressureLocalIslandWitnessListHasAdjacentDiagnosis.of_adjacent
    {n : OddNat} {k r : ℕ}
    {L : List (SourcePressureLocalIslandWitness n k r)}
    {A B : SourcePressureLocalIslandWitness n k r}
    (hin :
      SourcePressureLocalIslandWitnessAdjacentPairInList L A B)
    (hdiag :
      SourcePressureLocalIslandWitnessAdjacentDiagnosis L A B) :
    SourcePressureLocalIslandWitnessListHasAdjacentDiagnosis L :=
  ⟨A, B, hin, hdiag⟩

/-- Eliminate a list-level adjacent diagnosis by exposing its addressed pair. -/
theorem SourcePressureLocalIslandWitnessListHasAdjacentDiagnosis.elim
    {n : OddNat} {k r : ℕ}
    {L : List (SourcePressureLocalIslandWitness n k r)}
    {P : Prop}
    (h : SourcePressureLocalIslandWitnessListHasAdjacentDiagnosis L)
    (hp :
      ∀ A B,
        SourcePressureLocalIslandWitnessAdjacentPairInList L A B →
        SourcePressureLocalIslandWitnessAdjacentDiagnosis L A B →
        P) :
    P := by
  rcases h with ⟨A, B, hin, hdiag⟩
  exact hp A B hin hdiag

/-- Build a list-level adjacent diagnosis from a diagnosis on the head pair. -/
theorem SourcePressureLocalIslandWitnessListHasAdjacentDiagnosis.of_head
    {n : OddNat} {k r : ℕ}
    {W1 W2 : SourcePressureLocalIslandWitness n k r}
    {rest : List (SourcePressureLocalIslandWitness n k r)}
    (hdiag :
      SourcePressureLocalIslandWitnessAdjacentDiagnosis
        (W1 :: W2 :: rest) W1 W2) :
    SourcePressureLocalIslandWitnessListHasAdjacentDiagnosis
      (W1 :: W2 :: rest) :=
  SourcePressureLocalIslandWitnessListHasAdjacentDiagnosis.of_adjacent
    SourcePressureLocalIslandWitnessAdjacentPairInList.head hdiag

/--
Propagate a list-level adjacent diagnosis through a new head.

This only transports the address and the enclosing-list obstruction branch.
Recovered budget evidence remains attached to the same adjacent pair.
-/
theorem SourcePressureLocalIslandWitnessListHasAdjacentDiagnosis.of_tail
    {n : OddNat} {k r : ℕ}
    {W1 W2 : SourcePressureLocalIslandWitness n k r}
    {rest : List (SourcePressureLocalIslandWitness n k r)}
    (h :
      SourcePressureLocalIslandWitnessListHasAdjacentDiagnosis
        (W2 :: rest)) :
    SourcePressureLocalIslandWitnessListHasAdjacentDiagnosis
      (W1 :: W2 :: rest) := by
  rcases h with ⟨A, B, hin, hdiag⟩
  exact SourcePressureLocalIslandWitnessListHasAdjacentDiagnosis.of_adjacent
    (SourcePressureLocalIslandWitnessAdjacentPairInList.tail hin)
    (SourcePressureLocalIslandWitnessAdjacentDiagnosis.lift_tail hdiag)

/--
Two-step tail propagation for bounded address plumbing.

This is deliberately not a general recursive classifier; it is only a named
composition of `of_tail` for small explicit lists.
-/
theorem SourcePressureLocalIslandWitnessListHasAdjacentDiagnosis.of_tail_tail
    {n : OddNat} {k r : ℕ}
    {W1 W2 W3 : SourcePressureLocalIslandWitness n k r}
    {rest : List (SourcePressureLocalIslandWitness n k r)}
    (h :
      SourcePressureLocalIslandWitnessListHasAdjacentDiagnosis
        (W3 :: rest)) :
    SourcePressureLocalIslandWitnessListHasAdjacentDiagnosis
      (W1 :: W2 :: W3 :: rest) :=
  SourcePressureLocalIslandWitnessListHasAdjacentDiagnosis.of_tail
    (SourcePressureLocalIslandWitnessListHasAdjacentDiagnosis.of_tail h)

/--
Three-step tail propagation for bounded address plumbing.

This helper keeps the current API bounded and explicit; it does not inspect or
classify an arbitrary witness list.
-/
theorem SourcePressureLocalIslandWitnessListHasAdjacentDiagnosis.of_tail_tail_tail
    {n : OddNat} {k r : ℕ}
    {W1 W2 W3 W4 : SourcePressureLocalIslandWitness n k r}
    {rest : List (SourcePressureLocalIslandWitness n k r)}
    (h :
      SourcePressureLocalIslandWitnessListHasAdjacentDiagnosis
        (W4 :: rest)) :
    SourcePressureLocalIslandWitnessListHasAdjacentDiagnosis
      (W1 :: W2 :: W3 :: W4 :: rest) :=
  SourcePressureLocalIslandWitnessListHasAdjacentDiagnosis.of_tail
    (SourcePressureLocalIslandWitnessListHasAdjacentDiagnosis.of_tail_tail h)

/--
Project a list-level adjacent diagnosis to either pair-local recovered budget
evidence or ordinary sorted-before failure of the enclosing list.
-/
theorem SourcePressureLocalIslandWitnessListHasAdjacentDiagnosis.exists_recovered_or_listFailure
    {n : OddNat} {k r : ℕ}
    {L : List (SourcePressureLocalIslandWitness n k r)}
    (h : SourcePressureLocalIslandWitnessListHasAdjacentDiagnosis L) :
    ∃ A B,
      SourcePressureLocalIslandWitnessAdjacentPairInList L A B ∧
        ((∃ hrev : SourcePressureLocalIslandWitnessBefore B A,
          (((sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair
            A B hrev).items).map
            (fun I => SourcePressureIntervalNetDrop n k r I.start I.len)).sum ≤ -2)
        ∨ SourcePressureLocalIslandWitnessListHasSortedBeforeFailure L) := by
  rcases h with ⟨A, B, hin, hdiag⟩
  exact ⟨A, B, hin,
    SourcePressureLocalIslandWitnessAdjacentDiagnosis.recovered_or_listFailure hdiag⟩

/--
Project a list-level adjacent diagnosis without weakening the overlap branch.

The recovered alternative remains explicitly tied to the addressed adjacent
pair `A, B`.  The other alternative is still the sharp adjacent-overlap
obstruction on the enclosing list `L`; it is not merged into ordinary failure
and no interval union accounting is introduced.
-/
theorem SourcePressureLocalIslandWitnessListHasAdjacentDiagnosis.exists_recovered_or_overlap
    {n : OddNat} {k r : ℕ}
    {L : List (SourcePressureLocalIslandWitness n k r)}
    (h : SourcePressureLocalIslandWitnessListHasAdjacentDiagnosis L) :
    (∃ A B,
      SourcePressureLocalIslandWitnessAdjacentPairInList L A B ∧
        ∃ hrev : SourcePressureLocalIslandWitnessBefore B A,
          (((sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair
            A B hrev).items).map
            (fun I => SourcePressureIntervalNetDrop n k r I.start I.len)).sum ≤ -2)
    ∨ SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction L := by
  rcases h with ⟨A, B, hin, hdiag⟩
  rcases hdiag with hrecovered | hobs
  · exact Or.inl ⟨A, B, hin, hrecovered⟩
  · exact Or.inr hobs

/-- The empty witness list cannot carry a list-level adjacent diagnosis. -/
theorem SourcePressureLocalIslandWitnessListHasAdjacentDiagnosis.nil_false
    {n : OddNat} {k r : ℕ} :
    ¬ SourcePressureLocalIslandWitnessListHasAdjacentDiagnosis
      ([] : List (SourcePressureLocalIslandWitness n k r)) := by
  rintro ⟨A, B, hin, _⟩
  exact SourcePressureLocalIslandWitnessAdjacentPairInList.nil_false hin

/-- A singleton witness list cannot carry a list-level adjacent diagnosis. -/
theorem SourcePressureLocalIslandWitnessListHasAdjacentDiagnosis.singleton_false
    {n : OddNat} {k r : ℕ}
    {W : SourcePressureLocalIslandWitness n k r} :
    ¬ SourcePressureLocalIslandWitnessListHasAdjacentDiagnosis [W] := by
  rintro ⟨A, B, hin, _⟩
  exact SourcePressureLocalIslandWitnessAdjacentPairInList.singleton_false hin

/--
Any sorted-before failure in an explicitly supplied witness list has a
list-level adjacent diagnosis, assuming the converted witness addresses have
positive length.

The proof only peels the explicit list until the existing one-step diagnosis
finds either the head pair or a tail failure.  It does not sort the list, choose
a canonical first diagnosis, enumerate all diagnoses, merge intervals, or claim
that the list covers all local islands.
-/
theorem
    sourcePressureLocalIslandWitnessList_failure_hasAdjacentDiagnosis_of_forall_len_pos
    {n : OddNat} {k r : ℕ}
    {L : List (SourcePressureLocalIslandWitness n k r)}
    (hpos :
      ∀ W ∈ L,
        0 < (sourcePressureIntervalPulseAddress_of_localIslandWitness W).len)
    (h :
      SourcePressureLocalIslandWitnessListHasSortedBeforeFailure L) :
    SourcePressureLocalIslandWitnessListHasAdjacentDiagnosis L := by
  induction L with
  | nil =>
      exact False.elim
        (SourcePressureLocalIslandWitnessListHasSortedBeforeFailure_nil_false h)
  | cons W1 tail ih =>
      cases tail with
      | nil =>
          exact False.elim
            (SourcePressureLocalIslandWitnessListHasSortedBeforeFailure_singleton_false
              h)
      | cons W2 rest =>
          have h1pos :
              0 < (sourcePressureIntervalPulseAddress_of_localIslandWitness W1).len :=
            hpos W1 (by simp)
          have h2pos :
              0 < (sourcePressureIntervalPulseAddress_of_localIslandWitness W2).len :=
            hpos W2 (by simp)
          rcases sourcePressureLocalIslandWitnessList_failure_oneStepDiagnosis
              h1pos h2pos h with hhead | htail
          · exact SourcePressureLocalIslandWitnessListHasAdjacentDiagnosis.of_head
              hhead
          · have htailpos :
                ∀ W ∈ W2 :: rest,
                  0 <
                    (sourcePressureIntervalPulseAddress_of_localIslandWitness
                      W).len := by
              intro W hW
              exact hpos W (List.mem_cons_of_mem W1 hW)
            exact SourcePressureLocalIslandWitnessListHasAdjacentDiagnosis.of_tail
              (ih htailpos htail)

/--
Any sorted-before failure in an explicitly supplied witness list has a
list-level adjacent diagnosis.

This is the clean public form of the previous theorem.  The positivity
hypothesis is discharged by the local witness-address length lemma.  The result
is still only local to the supplied explicit list: it is not a sorting
algorithm, not a coverage theorem, and not a union-accounting statement.
-/
theorem sourcePressureLocalIslandWitnessList_failure_hasAdjacentDiagnosis
    {n : OddNat} {k r : ℕ}
    {L : List (SourcePressureLocalIslandWitness n k r)}
    (h :
      SourcePressureLocalIslandWitnessListHasSortedBeforeFailure L) :
    SourcePressureLocalIslandWitnessListHasAdjacentDiagnosis L :=
  sourcePressureLocalIslandWitnessList_failure_hasAdjacentDiagnosis_of_forall_len_pos
    (by
      intro W _hW
      exact sourcePressureIntervalPulseAddress_of_localIslandWitness_len_pos W)
    h

/--
Project an explicit-list sorted-before failure to the two consumer-facing
branches: either some adjacent pair has a pair-local recovered budget, or the
enclosing explicit list has an adjacent overlap obstruction.

This is the sharp projection of the general adjacent-diagnosis theorem.  It
does not select a canonical first diagnosis, enumerate all diagnosed pairs,
repair overlap, or perform any union accounting.
-/
theorem sourcePressureLocalIslandWitnessList_failure_exists_recovered_or_overlap
    {n : OddNat} {k r : ℕ}
    {L : List (SourcePressureLocalIslandWitness n k r)}
    (h :
      SourcePressureLocalIslandWitnessListHasSortedBeforeFailure L) :
    (∃ A B,
      SourcePressureLocalIslandWitnessAdjacentPairInList L A B ∧
        ∃ hrev : SourcePressureLocalIslandWitnessBefore B A,
          (((sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair
            A B hrev).items).map
            (fun I => SourcePressureIntervalNetDrop n k r I.start I.len)).sum ≤ -2)
    ∨ SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction L :=
  SourcePressureLocalIslandWitnessListHasAdjacentDiagnosis.exists_recovered_or_overlap
    (sourcePressureLocalIslandWitnessList_failure_hasAdjacentDiagnosis h)

/--
If a failed explicit witness list has no adjacent overlap obstruction, then
some adjacent pair in that same list carries a pair-local recovered budget.

The conclusion remains pair-local.  The theorem only removes the overlap branch
from `sourcePressureLocalIslandWitnessList_failure_exists_recovered_or_overlap`;
it does not sort the list or claim that all failures are recovered globally.
-/
theorem sourcePressureLocalIslandWitnessList_failure_exists_recovered_of_no_overlap
    {n : OddNat} {k r : ℕ}
    {L : List (SourcePressureLocalIslandWitness n k r)}
    (h :
      SourcePressureLocalIslandWitnessListHasSortedBeforeFailure L)
    (hno :
      ¬ SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction L) :
    ∃ A B,
      SourcePressureLocalIslandWitnessAdjacentPairInList L A B ∧
        ∃ hrev : SourcePressureLocalIslandWitnessBefore B A,
          (((sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair
            A B hrev).items).map
            (fun I => SourcePressureIntervalNetDrop n k r I.start I.len)).sum ≤ -2 := by
  rcases sourcePressureLocalIslandWitnessList_failure_exists_recovered_or_overlap h
      with hrec | hobs
  · exact hrec
  · exact False.elim (hno hobs)

/--
Length-three sorted-before failure yields a list-level adjacent diagnosis.

This is only a wrapper over the bounded three-witness carrier: it records that
the diagnosed pair is one of the adjacent pairs already present in the supplied
list, without adding a general list classifier.
-/
theorem sourcePressureLocalIslandWitnessList_failure_three_hasAdjacentDiagnosis
    {n : OddNat} {k r : ℕ}
    {W1 W2 W3 : SourcePressureLocalIslandWitness n k r}
    (h1pos :
      0 < (sourcePressureIntervalPulseAddress_of_localIslandWitness W1).len)
    (h2pos :
      0 < (sourcePressureIntervalPulseAddress_of_localIslandWitness W2).len)
    (h3pos :
      0 < (sourcePressureIntervalPulseAddress_of_localIslandWitness W3).len)
    (h :
      SourcePressureLocalIslandWitnessListHasSortedBeforeFailure [W1, W2, W3]) :
    SourcePressureLocalIslandWitnessListHasAdjacentDiagnosis [W1, W2, W3] := by
  rcases sourcePressureLocalIslandWitnessList_failure_threeDiagnosis_carrier
      h1pos h2pos h3pos h with h12 | h23
  · exact SourcePressureLocalIslandWitnessListHasAdjacentDiagnosis.of_adjacent
      SourcePressureLocalIslandWitnessAdjacentPairInList.head h12
  · exact SourcePressureLocalIslandWitnessListHasAdjacentDiagnosis.of_adjacent
      (SourcePressureLocalIslandWitnessAdjacentPairInList.tail
        SourcePressureLocalIslandWitnessAdjacentPairInList.head) h23

/--
Length-four sorted-before failure yields a list-level adjacent diagnosis.

The result exposes only that one adjacent pair in the explicit four-witness
list has a local diagnosis.  It intentionally avoids coverage, maximality,
union accounting, or a recursive failure classifier.
-/
theorem sourcePressureLocalIslandWitnessList_failure_four_hasAdjacentDiagnosis
    {n : OddNat} {k r : ℕ}
    {W1 W2 W3 W4 : SourcePressureLocalIslandWitness n k r}
    (h1pos :
      0 < (sourcePressureIntervalPulseAddress_of_localIslandWitness W1).len)
    (h2pos :
      0 < (sourcePressureIntervalPulseAddress_of_localIslandWitness W2).len)
    (h3pos :
      0 < (sourcePressureIntervalPulseAddress_of_localIslandWitness W3).len)
    (h4pos :
      0 < (sourcePressureIntervalPulseAddress_of_localIslandWitness W4).len)
    (h :
      SourcePressureLocalIslandWitnessListHasSortedBeforeFailure
        [W1, W2, W3, W4]) :
    SourcePressureLocalIslandWitnessListHasAdjacentDiagnosis [W1, W2, W3, W4] := by
  rcases sourcePressureLocalIslandWitnessList_failure_fourDiagnosis_carrier
      h1pos h2pos h3pos h4pos h with h12 | htail
  · exact SourcePressureLocalIslandWitnessListHasAdjacentDiagnosis.of_adjacent
      SourcePressureLocalIslandWitnessAdjacentPairInList.head h12
  · rcases htail with h23 | h34
    · exact SourcePressureLocalIslandWitnessListHasAdjacentDiagnosis.of_adjacent
        (SourcePressureLocalIslandWitnessAdjacentPairInList.tail
          SourcePressureLocalIslandWitnessAdjacentPairInList.head) h23
    · exact SourcePressureLocalIslandWitnessListHasAdjacentDiagnosis.of_adjacent
        (SourcePressureLocalIslandWitnessAdjacentPairInList.tail
          (SourcePressureLocalIslandWitnessAdjacentPairInList.tail
            SourcePressureLocalIslandWitnessAdjacentPairInList.head)) h34

/--
Length-five sorted-before failure yields a list-level adjacent diagnosis.

This is a bounded wrapper: it peels the head pair once, then delegates the tail
case to the existing four-witness wrapper and lifts that diagnosis back to the
full list.  It is not a general recursive classifier.
-/
theorem sourcePressureLocalIslandWitnessList_failure_five_hasAdjacentDiagnosis
    {n : OddNat} {k r : ℕ}
    {W1 W2 W3 W4 W5 : SourcePressureLocalIslandWitness n k r}
    (h1pos :
      0 < (sourcePressureIntervalPulseAddress_of_localIslandWitness W1).len)
    (h2pos :
      0 < (sourcePressureIntervalPulseAddress_of_localIslandWitness W2).len)
    (h3pos :
      0 < (sourcePressureIntervalPulseAddress_of_localIslandWitness W3).len)
    (h4pos :
      0 < (sourcePressureIntervalPulseAddress_of_localIslandWitness W4).len)
    (h5pos :
      0 < (sourcePressureIntervalPulseAddress_of_localIslandWitness W5).len)
    (h :
      SourcePressureLocalIslandWitnessListHasSortedBeforeFailure
        [W1, W2, W3, W4, W5]) :
    SourcePressureLocalIslandWitnessListHasAdjacentDiagnosis
      [W1, W2, W3, W4, W5] := by
  rcases sourcePressureLocalIslandWitnessList_failure_oneStepDiagnosis
      h1pos h2pos h with hhead | htail
  · exact SourcePressureLocalIslandWitnessListHasAdjacentDiagnosis.of_head hhead
  · exact SourcePressureLocalIslandWitnessListHasAdjacentDiagnosis.of_tail
      (sourcePressureLocalIslandWitnessList_failure_four_hasAdjacentDiagnosis
        h2pos h3pos h4pos h5pos htail)

end DkMath.Collatz
