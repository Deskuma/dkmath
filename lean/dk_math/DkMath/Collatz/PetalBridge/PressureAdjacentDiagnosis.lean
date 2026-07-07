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
The left witness of an addressed adjacent pair is a member of the addressed
list.

This is a pure address projection for
`SourcePressureLocalIslandWitnessAdjacentPairInList`.  It does not inspect the
pair diagnosis, does not choose a canonical pair, and does not claim coverage
of all witnesses in the list.
-/
theorem sourcePressureLocalIslandWitnessAdjacentPairInList_left_mem
    {n : OddNat} {k r : ℕ}
    {L : List (SourcePressureLocalIslandWitness n k r)}
    {A B : SourcePressureLocalIslandWitness n k r}
    (hin : SourcePressureLocalIslandWitnessAdjacentPairInList L A B) :
    A ∈ L := by
  induction L generalizing A B with
  | nil =>
      exact False.elim hin
  | cons W1 rest ih =>
      cases rest with
      | nil =>
          exact False.elim hin
      | cons W2 rest =>
          rcases hin with hhead | htail
          · rcases hhead with ⟨hA, _hB⟩
            simp [hA]
          · exact List.mem_cons_of_mem W1 (ih htail)

/--
The right witness of an addressed adjacent pair is a member of the addressed
list.

This is the right-side companion to
`sourcePressureLocalIslandWitnessAdjacentPairInList_left_mem`.  It is still
only an address projection; it does not make the adjacent pair canonical and
does not aggregate diagnostics.
-/
theorem sourcePressureLocalIslandWitnessAdjacentPairInList_right_mem
    {n : OddNat} {k r : ℕ}
    {L : List (SourcePressureLocalIslandWitness n k r)}
    {A B : SourcePressureLocalIslandWitness n k r}
    (hin : SourcePressureLocalIslandWitnessAdjacentPairInList L A B) :
    B ∈ L := by
  induction L generalizing A B with
  | nil =>
      exact False.elim hin
  | cons W1 rest ih =>
      cases rest with
      | nil =>
          exact False.elim hin
      | cons W2 rest =>
          rcases hin with hhead | htail
          · rcases hhead with ⟨_hA, hB⟩
            simp [hB]
          · exact List.mem_cons_of_mem W1 (ih htail)

/--
An adjacent-overlap obstruction exposes one addressed neighboring pair and its
pair-local overlap obstruction.

This is the cp230 lower-layer overlap projection.  It follows the same
recursive address structure as
`SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction`: the head
case returns the head pair, while the tail case lifts the tail address through
the newly supplied head.  It does not import Beam vocabulary, repair the
overlap, choose a canonical pair among several possibilities, or claim list
coverage.
-/
theorem exists_adjacentPairInList_pairOverlapObstruction_of_overlapObstruction
    {n : OddNat} {k r : ℕ}
    {L : List (SourcePressureLocalIslandWitness n k r)}
    (hobs :
      SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction L) :
    ∃ A B,
      SourcePressureLocalIslandWitnessAdjacentPairInList L A B ∧
        SourcePressureLocalIslandWitnessPairOverlapObstruction A B := by
  induction L with
  | nil =>
      exact False.elim hobs
  | cons W1 rest ih =>
      cases rest with
      | nil =>
          exact False.elim hobs
      | cons W2 rest =>
          rcases hobs with hhead | htail
          · exact
              ⟨W1, W2,
                SourcePressureLocalIslandWitnessAdjacentPairInList.head,
                hhead⟩
          · rcases ih htail with ⟨A, B, hin, hobspair⟩
            exact
              ⟨A, B,
                SourcePressureLocalIslandWitnessAdjacentPairInList.tail hin,
                hobspair⟩

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

/--
Named no-adjacent-overlap condition for an explicitly supplied witness list.

This is deliberately only a readability wrapper around the negation of the
existing adjacent-overlap obstruction predicate.  It does not say that the list
is globally overlap-free, canonical, maximal, sorted, complete, or repaired; it
only says that this explicit list has no neighboring overlap obstruction in
the sense already defined by
`SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction`.
-/
def SourcePressureLocalIslandWitnessListHasNoAdjacentOverlapObstruction
    {n : OddNat} {k r : ℕ}
    (L : List (SourcePressureLocalIslandWitness n k r)) : Prop :=
  ¬ SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction L

/-- Project the named no-adjacent-overlap wrapper back to the raw negation. -/
theorem SourcePressureLocalIslandWitnessListHasNoAdjacentOverlapObstruction.not_obstruction
    {n : OddNat} {k r : ℕ}
    {L : List (SourcePressureLocalIslandWitness n k r)}
    (hno :
      SourcePressureLocalIslandWitnessListHasNoAdjacentOverlapObstruction L) :
    ¬ SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction L :=
  hno

/-- Construct the named no-adjacent-overlap wrapper from the raw negation. -/
theorem SourcePressureLocalIslandWitnessListHasNoAdjacentOverlapObstruction.of_not
    {n : OddNat} {k r : ℕ}
    {L : List (SourcePressureLocalIslandWitness n k r)}
    (hno :
      ¬ SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction L) :
    SourcePressureLocalIslandWitnessListHasNoAdjacentOverlapObstruction L :=
  hno

/-- Empty explicit witness lists have no adjacent-overlap obstruction. -/
theorem SourcePressureLocalIslandWitnessListHasNoAdjacentOverlapObstruction.nil
    {n : OddNat} {k r : ℕ} :
    SourcePressureLocalIslandWitnessListHasNoAdjacentOverlapObstruction
      ([] : List (SourcePressureLocalIslandWitness n k r)) := by
  intro h
  exact h

/-- Singleton explicit witness lists have no adjacent-overlap obstruction. -/
theorem SourcePressureLocalIslandWitnessListHasNoAdjacentOverlapObstruction.singleton
    {n : OddNat} {k r : ℕ}
    {W : SourcePressureLocalIslandWitness n k r} :
    SourcePressureLocalIslandWitnessListHasNoAdjacentOverlapObstruction [W] := by
  intro h
  exact h

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
Named no-adjacent-overlap version of the recovered-pair projection.

This is the consumer-facing form for callers that track the no-overlap branch
with the explicit wrapper introduced above.  The conclusion is unchanged from
`sourcePressureLocalIslandWitnessList_failure_exists_recovered_of_no_overlap`:
one adjacent pair in the supplied list carries a pair-local recovered budget.
No global overlap-free construction, list coverage, union accounting, or
Collatz convergence is introduced here.
-/
theorem sourcePressureLocalIslandWitnessList_failure_exists_recovered_of_noAdjacentOverlap
    {n : OddNat} {k r : ℕ}
    {L : List (SourcePressureLocalIslandWitness n k r)}
    (h :
      SourcePressureLocalIslandWitnessListHasSortedBeforeFailure L)
    (hno :
      SourcePressureLocalIslandWitnessListHasNoAdjacentOverlapObstruction L) :
    ∃ A B,
      SourcePressureLocalIslandWitnessAdjacentPairInList L A B ∧
        ∃ hrev : SourcePressureLocalIslandWitnessBefore B A,
          (((sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair
            A B hrev).items).map
            (fun I => SourcePressureIntervalNetDrop n k r I.start I.len)).sum ≤ -2 :=
  sourcePressureLocalIslandWitnessList_failure_exists_recovered_of_no_overlap
    h hno.not_obstruction

/--
Carrier saying that an explicit witness list contains one adjacent pair whose
reversed order yields a pair-local accounted interval family with budget
`≤ -2`.

This is only a named package for the existing recovered branch.  The accounted
family is exactly
`sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair A B hrev`
for one adjacent pair `A, B` already occurring in the supplied list.  It does
not aggregate multiple recovered pairs, merge intervals, perform union
accounting, or claim coverage of all local islands.
-/
def SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamily
    {n : OddNat} {k r : ℕ}
    (L : List (SourcePressureLocalIslandWitness n k r)) : Prop :=
  ∃ A B,
    SourcePressureLocalIslandWitnessAdjacentPairInList L A B ∧
      ∃ hrev : SourcePressureLocalIslandWitnessBefore B A,
        (((sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair
          A B hrev).items).map
          (fun I => SourcePressureIntervalNetDrop n k r I.start I.len)).sum ≤ -2

/-- Build the recovered accounted-family carrier from explicit adjacent-pair evidence. -/
theorem SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamily.of_pair
    {n : OddNat} {k r : ℕ}
    {L : List (SourcePressureLocalIslandWitness n k r)}
    {A B : SourcePressureLocalIslandWitness n k r}
    (hin :
      SourcePressureLocalIslandWitnessAdjacentPairInList L A B)
    (hrev : SourcePressureLocalIslandWitnessBefore B A)
    (hbudget :
      (((sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair
        A B hrev).items).map
        (fun I => SourcePressureIntervalNetDrop n k r I.start I.len)).sum ≤ -2) :
    SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamily L :=
  ⟨A, B, hin, hrev, hbudget⟩

/-- Project the carrier back to the underlying recovered adjacent pair. -/
theorem SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamily.exists_pair
    {n : OddNat} {k r : ℕ}
    {L : List (SourcePressureLocalIslandWitness n k r)}
    (h :
      SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamily L) :
    ∃ A B,
      SourcePressureLocalIslandWitnessAdjacentPairInList L A B ∧
        ∃ hrev : SourcePressureLocalIslandWitnessBefore B A,
          (((sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair
            A B hrev).items).map
            (fun I => SourcePressureIntervalNetDrop n k r I.start I.len)).sum ≤ -2 :=
  h

set_option linter.style.longLine false in
/--
Bundled consumer-facing diagnostic for one recovered adjacent accounted family.

This carrier intentionally stores redundant local facts about the same
recovered reversed-pair family:

* the pair occurs adjacently in the explicit witness list;
* the pair is reversed with respect to the `Before` relation;
* the associated pair-local accounted family has budget `≤ -2`;
* the same listed budget is strictly negative;
* the family has exactly two listed accounted intervals.

The redundancy is deliberate.  Downstream callers often need the operational
`< 0` and `items.length = 2` facts without reproving them from the lower-level
carrier.  This definition is still a one-pair diagnostic.  It does not list all
diagnoses, aggregate multiple recovered pairs, form interval unions, claim
coverage, or repair overlaps.
-/
def SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic
    {n : OddNat} {k r : ℕ}
    (L : List (SourcePressureLocalIslandWitness n k r)) : Prop :=
  ∃ A B,
    SourcePressureLocalIslandWitnessAdjacentPairInList L A B ∧
      ∃ hrev : SourcePressureLocalIslandWitnessBefore B A,
        let F :=
          sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair
            A B hrev
        (((F.items).map
          (fun I => SourcePressureIntervalNetDrop n k r I.start I.len)).sum ≤ -2) ∧
          (((F.items).map
            (fun I => SourcePressureIntervalNetDrop n k r I.start I.len)).sum < 0) ∧
          F.items.length = 2

set_option linter.style.longLine false in
/--
Build the bundled diagnostic from explicit pair-local evidence.

This constructor only packages one recovered adjacent pair and its associated
reversed-pair accounted family.
-/
theorem SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic.of_pair
    {n : OddNat} {k r : ℕ}
    {L : List (SourcePressureLocalIslandWitness n k r)}
    {A B : SourcePressureLocalIslandWitness n k r}
    (hin :
      SourcePressureLocalIslandWitnessAdjacentPairInList L A B)
    (hrev : SourcePressureLocalIslandWitnessBefore B A)
    (hbudget :
      let F :=
        sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair
          A B hrev
      ((F.items).map
        (fun I => SourcePressureIntervalNetDrop n k r I.start I.len)).sum ≤ -2)
    (hneg :
      let F :=
        sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair
          A B hrev
      ((F.items).map
        (fun I => SourcePressureIntervalNetDrop n k r I.start I.len)).sum < 0)
    (hlen :
      let F :=
        sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair
          A B hrev
      F.items.length = 2) :
    SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic L :=
  ⟨A, B, hin, hrev, hbudget, hneg, hlen⟩

set_option linter.style.longLine false in
/--
Upgrade the lower-level recovered accounted-family carrier to the bundled
diagnostic carrier.

The strict negativity and length-two facts come from the existing reversed-pair
accounted-family theorems, so no list-wide accounting principle is introduced.
-/
theorem
    SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamily.toDiagnostic
    {n : OddNat} {k r : ℕ}
    {L : List (SourcePressureLocalIslandWitness n k r)}
    (h :
      SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamily L) :
    SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic L := by
  rcases h.exists_pair with ⟨A, B, hin, hrev, hbudget⟩
  exact
    SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic.of_pair
      hin hrev hbudget
      (sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair_sum_neg
        A B hrev)
      (sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair_length
        A B hrev)

set_option linter.style.longLine false in
/--
Forget the extra diagnostic fields and recover the lower-level carrier.

This is useful when a caller has the bundled diagnostic but an older theorem
expects only the recovered accounted-family carrier.
-/
theorem
    SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic.toRecoveredAdjacentAccountedFamily
    {n : OddNat} {k r : ℕ}
    {L : List (SourcePressureLocalIslandWitness n k r)}
    (h :
      SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic L) :
    SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamily L := by
  rcases h with ⟨A, B, hin, hrev, hbudget, _hneg, _hlen⟩
  exact
    SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamily.of_pair
      hin hrev hbudget

set_option linter.style.longLine false in
/--
Project the underlying adjacent recovered pair from the bundled diagnostic.

This is a convenience projection only; it does not assert uniqueness or
enumerate every possible diagnostic in the list.
-/
theorem
    SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic.exists_pair
    {n : OddNat} {k r : ℕ}
    {L : List (SourcePressureLocalIslandWitness n k r)}
    (h :
      SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic L) :
    ∃ A B,
      SourcePressureLocalIslandWitnessAdjacentPairInList L A B ∧
        ∃ hrev : SourcePressureLocalIslandWitnessBefore B A,
          let F :=
            sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair
              A B hrev
          (((F.items).map
            (fun I => SourcePressureIntervalNetDrop n k r I.start I.len)).sum ≤ -2) ∧
            (((F.items).map
            (fun I => SourcePressureIntervalNetDrop n k r I.start I.len)).sum < 0) ∧
            F.items.length = 2 :=
  h

set_option linter.style.longLine false in
/--
Project strict negativity from the bundled diagnostic.

This is the same pair-local family stored in the diagnostic; the theorem only
forgets the additional `≤ -2` and length fields.
-/
theorem
    SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic.exists_accountedFamily_sum_neg
    {n : OddNat} {k r : ℕ}
    {L : List (SourcePressureLocalIslandWitness n k r)}
    (h :
      SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic L) :
    ∃ A B,
      SourcePressureLocalIslandWitnessAdjacentPairInList L A B ∧
        ∃ hrev : SourcePressureLocalIslandWitnessBefore B A,
          let F :=
            sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair
              A B hrev
          ((F.items).map
            (fun I => SourcePressureIntervalNetDrop n k r I.start I.len)).sum < 0 := by
  rcases h.exists_pair with ⟨A, B, hin, hrev, _hbudget, hneg, _hlen⟩
  exact ⟨A, B, hin, hrev, hneg⟩

set_option linter.style.longLine false in
/--
Project length-two structure from the bundled diagnostic.

This remains about the explicit accounted family associated with one recovered
adjacent pair.
-/
theorem
    SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic.exists_accountedFamily_length_two
    {n : OddNat} {k r : ℕ}
    {L : List (SourcePressureLocalIslandWitness n k r)}
    (h :
      SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic L) :
    ∃ A B,
      SourcePressureLocalIslandWitnessAdjacentPairInList L A B ∧
        ∃ hrev : SourcePressureLocalIslandWitnessBefore B A,
          let F :=
            sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair
              A B hrev
          F.items.length = 2 := by
  rcases h.exists_pair with ⟨A, B, hin, hrev, _hbudget, _hneg, hlen⟩
  exact ⟨A, B, hin, hrev, hlen⟩

/--
The empty explicit witness list cannot carry a recovered accounted-family
diagnostic, because it contains no adjacent pair address.
-/
theorem SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic.nil_false
    {n : OddNat} {k r : ℕ} :
    ¬ SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic
      ([] : List (SourcePressureLocalIslandWitness n k r)) := by
  rintro ⟨A, B, hin, _⟩
  exact SourcePressureLocalIslandWitnessAdjacentPairInList.nil_false hin

set_option linter.style.longLine false in
/--
A singleton explicit witness list cannot carry a recovered accounted-family
diagnostic, because it contains no adjacent pair address.
-/
theorem SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic.singleton_false
    {n : OddNat} {k r : ℕ}
    {W : SourcePressureLocalIslandWitness n k r} :
    ¬ SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic [W] := by
  rintro ⟨A, B, hin, _⟩
  exact SourcePressureLocalIslandWitnessAdjacentPairInList.singleton_false hin

set_option linter.style.longLine false in
/--
Lift a recovered accounted-family diagnostic through a newly supplied head.

The recovered family, reversed-before witness, and all budget facts are
unchanged.  Only the adjacent-pair address is transported from the tail list to
the larger enclosing list.
-/
theorem SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic.of_tail
    {n : OddNat} {k r : ℕ}
    {W1 W2 : SourcePressureLocalIslandWitness n k r}
    {rest : List (SourcePressureLocalIslandWitness n k r)}
    (h :
      SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic
        (W2 :: rest)) :
    SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic
      (W1 :: W2 :: rest) := by
  rcases h.exists_pair with ⟨A, B, hin, hrev, hbudget, hneg, hlen⟩
  exact
    SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic.of_pair
      (SourcePressureLocalIslandWitnessAdjacentPairInList.tail hin)
      hrev hbudget hneg hlen

set_option linter.style.longLine false in
/--
Two-step bounded tail lift for a recovered accounted-family diagnostic.

This is just a small composition helper; it still transports one existing
pair-local diagnostic and does not scan the list.
-/
theorem SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic.of_tail_tail
    {n : OddNat} {k r : ℕ}
    {W1 W2 W3 : SourcePressureLocalIslandWitness n k r}
    {rest : List (SourcePressureLocalIslandWitness n k r)}
    (h :
      SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic
        (W3 :: rest)) :
    SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic
      (W1 :: W2 :: W3 :: rest) :=
  SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic.of_tail
    (SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic.of_tail
      h)

set_option linter.style.longLine false in
/--
Three-step bounded tail lift for a recovered accounted-family diagnostic.

This mirrors the older adjacent-diagnosis convenience API while staying
bounded and pair-local.
-/
theorem SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic.of_tail_tail_tail
    {n : OddNat} {k r : ℕ}
    {W1 W2 W3 W4 : SourcePressureLocalIslandWitness n k r}
    {rest : List (SourcePressureLocalIslandWitness n k r)}
    (h :
      SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic
        (W4 :: rest)) :
    SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic
      (W1 :: W2 :: W3 :: W4 :: rest) :=
  SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic.of_tail
    (SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic.of_tail_tail
      h)

/--
Expose the actual pair-local accounted interval family object stored by the
recovered adjacent-family carrier.

The `let F := ...` form is deliberately consumer-facing: downstream code can
see the `SourcePressureAccountedIntervalFamily` object and then use `F.items`.
This is still definitionally the same pair-local recovered branch as
`exists_pair`; no new list-wide family or aggregation is introduced.
-/
theorem
    SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamily.exists_accountedFamily
    {n : OddNat} {k r : ℕ}
    {L : List (SourcePressureLocalIslandWitness n k r)}
    (h :
      SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamily L) :
    ∃ A B,
      SourcePressureLocalIslandWitnessAdjacentPairInList L A B ∧
        ∃ hrev : SourcePressureLocalIslandWitnessBefore B A,
          let F :=
            sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair
              A B hrev
          ((F.items).map
            (fun I => SourcePressureIntervalNetDrop n k r I.start I.len)).sum ≤ -2 := by
  rcases h.exists_pair with ⟨A, B, hin, hrev, hbudget⟩
  exact ⟨A, B, hin, hrev, hbudget⟩

set_option linter.style.longLine false in
/--
Expose strict negativity for the recovered pair-local accounted family.

This projection uses the existing reversed-pair family theorem rather than
deriving negativity from the stored `≤ -2` budget.  The result is still about
one adjacent recovered pair only.
-/
theorem
    SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamily.exists_accountedFamily_sum_neg
    {n : OddNat} {k r : ℕ}
    {L : List (SourcePressureLocalIslandWitness n k r)}
    (h :
      SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamily L) :
    ∃ A B,
      SourcePressureLocalIslandWitnessAdjacentPairInList L A B ∧
        ∃ hrev : SourcePressureLocalIslandWitnessBefore B A,
          let F :=
            sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair
              A B hrev
          ((F.items).map
            (fun I => SourcePressureIntervalNetDrop n k r I.start I.len)).sum < 0 := by
  rcases h.exists_pair with ⟨A, B, hin, hrev, _hbudget⟩
  exact ⟨A, B, hin, hrev,
    sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair_sum_neg
      A B hrev⟩

set_option linter.style.longLine false in
/--
Expose the length of the recovered pair-local accounted family.

The recovered family is built from a reversed adjacent pair, so its explicit
`items` list has length `2`.  This is a pair-local structural fact, not a
statement about the length of the enclosing witness list.
-/
theorem
    SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamily.exists_accountedFamily_length_two
    {n : OddNat} {k r : ℕ}
    {L : List (SourcePressureLocalIslandWitness n k r)}
    (h :
      SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamily L) :
    ∃ A B,
      SourcePressureLocalIslandWitnessAdjacentPairInList L A B ∧
        ∃ hrev : SourcePressureLocalIslandWitnessBefore B A,
          let F :=
            sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair
              A B hrev
          F.items.length = 2 := by
  rcases h.exists_pair with ⟨A, B, hin, hrev, _hbudget⟩
  exact ⟨A, B, hin, hrev,
    sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair_length
      A B hrev⟩

/--
Empty explicit witness lists cannot contain a recovered adjacent accounted
family, because they contain no adjacent pair.
-/
theorem SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamily.nil_false
    {n : OddNat} {k r : ℕ} :
    ¬ SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamily
      ([] : List (SourcePressureLocalIslandWitness n k r)) := by
  rintro ⟨A, B, hin, _⟩
  exact SourcePressureLocalIslandWitnessAdjacentPairInList.nil_false hin

/--
Singleton explicit witness lists cannot contain a recovered adjacent accounted
family, because they contain no adjacent pair.
-/
theorem SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamily.singleton_false
    {n : OddNat} {k r : ℕ}
    {W : SourcePressureLocalIslandWitness n k r} :
    ¬ SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamily [W] := by
  rintro ⟨A, B, hin, _⟩
  exact SourcePressureLocalIslandWitnessAdjacentPairInList.singleton_false hin

set_option linter.style.longLine false in
/--
A failed explicit witness list with no adjacent overlap obstruction contains a
recovered adjacent pair packaged as one pair-local accounted interval family.

This is still only a one-pair statement.  It reuses the recovered pair obtained
from the no-adjacent-overlap projection and does not add list-level union
accounting or aggregation.
-/
theorem
    sourcePressureLocalIslandWitnessList_failure_hasRecoveredAdjacentAccountedFamily_of_noAdjacentOverlap
    {n : OddNat} {k r : ℕ}
    {L : List (SourcePressureLocalIslandWitness n k r)}
    (h :
      SourcePressureLocalIslandWitnessListHasSortedBeforeFailure L)
    (hno :
      SourcePressureLocalIslandWitnessListHasNoAdjacentOverlapObstruction L) :
    SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamily L := by
  rcases sourcePressureLocalIslandWitnessList_failure_exists_recovered_of_noAdjacentOverlap
      h hno with ⟨A, B, hin, hrev, hbudget⟩
  exact
    SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamily.of_pair
      hin hrev hbudget

set_option linter.style.longLine false in
/--
Raw-negation version of the recovered accounted-family carrier theorem.

This keeps compatibility with callers that still store the no-overlap branch as
`¬ SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction L`.
-/
theorem
    sourcePressureLocalIslandWitnessList_failure_hasRecoveredAdjacentAccountedFamily_of_no_overlap
    {n : OddNat} {k r : ℕ}
    {L : List (SourcePressureLocalIslandWitness n k r)}
    (h :
      SourcePressureLocalIslandWitnessListHasSortedBeforeFailure L)
    (hno :
      ¬ SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction L) :
    SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamily L :=
  sourcePressureLocalIslandWitnessList_failure_hasRecoveredAdjacentAccountedFamily_of_noAdjacentOverlap
    h
    (SourcePressureLocalIslandWitnessListHasNoAdjacentOverlapObstruction.of_not
      hno)

set_option linter.style.longLine false in
/--
Failure plus named no-adjacent-overlap, packaged as the bundled pair-local
diagnostic carrier.

This is the consumer-facing form of the recovered branch.  It bundles the
adjacent pair, reversed-before witness, budget `≤ -2`, strict negativity, and
length-two structure for one recovered family only.
-/
theorem
    sourcePressureLocalIslandWitnessList_failure_hasRecoveredAdjacentAccountedFamilyDiagnostic_of_noAdjacentOverlap
    {n : OddNat} {k r : ℕ}
    {L : List (SourcePressureLocalIslandWitness n k r)}
    (h :
      SourcePressureLocalIslandWitnessListHasSortedBeforeFailure L)
    (hno :
      SourcePressureLocalIslandWitnessListHasNoAdjacentOverlapObstruction L) :
    SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic L :=
  (sourcePressureLocalIslandWitnessList_failure_hasRecoveredAdjacentAccountedFamily_of_noAdjacentOverlap
    h hno).toDiagnostic

set_option linter.style.longLine false in
/--
Raw-negation version of the bundled diagnostic consumer theorem.

This keeps the compatibility path for callers that still represent the
no-adjacent-overlap branch as a raw negation.
-/
theorem
    sourcePressureLocalIslandWitnessList_failure_hasRecoveredAdjacentAccountedFamilyDiagnostic_of_no_overlap
    {n : OddNat} {k r : ℕ}
    {L : List (SourcePressureLocalIslandWitness n k r)}
    (h :
      SourcePressureLocalIslandWitnessListHasSortedBeforeFailure L)
    (hno :
      ¬ SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction L) :
    SourcePressureLocalIslandWitnessListHasRecoveredAdjacentAccountedFamilyDiagnostic L :=
  (sourcePressureLocalIslandWitnessList_failure_hasRecoveredAdjacentAccountedFamily_of_no_overlap
    h hno).toDiagnostic

set_option linter.style.longLine false in
/--
Failure plus named no-adjacent-overlap, projected directly to the pair-local
accounted interval family object.

This theorem only exposes the same recovered family already provided by the
carrier theorem.  The family is still produced from one adjacent recovered pair;
there is no list-wide union family and no aggregation over multiple pairs.
-/
theorem
    sourcePressureLocalIslandWitnessList_failure_exists_accountedFamily_of_noAdjacentOverlap
    {n : OddNat} {k r : ℕ}
    {L : List (SourcePressureLocalIslandWitness n k r)}
    (h :
      SourcePressureLocalIslandWitnessListHasSortedBeforeFailure L)
    (hno :
      SourcePressureLocalIslandWitnessListHasNoAdjacentOverlapObstruction L) :
    ∃ A B,
      SourcePressureLocalIslandWitnessAdjacentPairInList L A B ∧
        ∃ hrev : SourcePressureLocalIslandWitnessBefore B A,
          let F :=
            sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair
              A B hrev
          ((F.items).map
            (fun I => SourcePressureIntervalNetDrop n k r I.start I.len)).sum ≤ -2 :=
  (sourcePressureLocalIslandWitnessList_failure_hasRecoveredAdjacentAccountedFamily_of_noAdjacentOverlap
    h hno).exists_accountedFamily

set_option linter.style.longLine false in
/--
Raw-negation version of the direct accounted-family projection.

This is a compatibility wrapper for callers that still store no-overlap as the
raw negation of the adjacent-overlap obstruction predicate.
-/
theorem
    sourcePressureLocalIslandWitnessList_failure_exists_accountedFamily_of_no_overlap
    {n : OddNat} {k r : ℕ}
    {L : List (SourcePressureLocalIslandWitness n k r)}
    (h :
      SourcePressureLocalIslandWitnessListHasSortedBeforeFailure L)
    (hno :
      ¬ SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction L) :
    ∃ A B,
      SourcePressureLocalIslandWitnessAdjacentPairInList L A B ∧
        ∃ hrev : SourcePressureLocalIslandWitnessBefore B A,
          let F :=
            sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair
              A B hrev
          ((F.items).map
            (fun I => SourcePressureIntervalNetDrop n k r I.start I.len)).sum ≤ -2 :=
  (sourcePressureLocalIslandWitnessList_failure_hasRecoveredAdjacentAccountedFamily_of_no_overlap
    h hno).exists_accountedFamily

set_option linter.style.longLine false in
/--
Failure plus named no-adjacent-overlap, projected to a pair-local recovered
accounted family with strictly negative listed cost.

This is a direct consumer wrapper over the carrier-level strict-negativity
projection.  It does not combine multiple families.
-/
theorem
    sourcePressureLocalIslandWitnessList_failure_exists_accountedFamily_sum_neg_of_noAdjacentOverlap
    {n : OddNat} {k r : ℕ}
    {L : List (SourcePressureLocalIslandWitness n k r)}
    (h :
      SourcePressureLocalIslandWitnessListHasSortedBeforeFailure L)
    (hno :
      SourcePressureLocalIslandWitnessListHasNoAdjacentOverlapObstruction L) :
    ∃ A B,
      SourcePressureLocalIslandWitnessAdjacentPairInList L A B ∧
        ∃ hrev : SourcePressureLocalIslandWitnessBefore B A,
          let F :=
            sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair
              A B hrev
          ((F.items).map
            (fun I => SourcePressureIntervalNetDrop n k r I.start I.len)).sum < 0 :=
  (sourcePressureLocalIslandWitnessList_failure_hasRecoveredAdjacentAccountedFamily_of_noAdjacentOverlap
    h hno).exists_accountedFamily_sum_neg

set_option linter.style.longLine false in
/--
Raw-negation version of the strict-negative accounted-family projection.

This keeps compatibility with callers that have not yet switched to the named
no-adjacent-overlap predicate.
-/
theorem
    sourcePressureLocalIslandWitnessList_failure_exists_accountedFamily_sum_neg_of_no_overlap
    {n : OddNat} {k r : ℕ}
    {L : List (SourcePressureLocalIslandWitness n k r)}
    (h :
      SourcePressureLocalIslandWitnessListHasSortedBeforeFailure L)
    (hno :
      ¬ SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction L) :
    ∃ A B,
      SourcePressureLocalIslandWitnessAdjacentPairInList L A B ∧
        ∃ hrev : SourcePressureLocalIslandWitnessBefore B A,
          let F :=
            sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair
              A B hrev
          ((F.items).map
            (fun I => SourcePressureIntervalNetDrop n k r I.start I.len)).sum < 0 :=
  (sourcePressureLocalIslandWitnessList_failure_hasRecoveredAdjacentAccountedFamily_of_no_overlap
    h hno).exists_accountedFamily_sum_neg

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
