import DkMath.Collatz.PetalBridge.PressureAccounting

#print "file: DkMath.Collatz.PetalBridge.PressureLocalWitnessObstruction"

namespace DkMath.Collatz

/-
Local-witness obstruction and pair/list diagnostics.

This module is a downstream refactor split from `PressureAccounting`.
It keeps the witness-level before/overlap vocabulary and the bounded pair/list
diagnosis theorems close to the obstruction predicates they use.

The semantic guardrail is unchanged: these theorems are local to explicitly
supplied witnesses and adjacent pairs.  They do not assert coverage of all local
islands, do not sort arbitrary lists, do not merge overlapping intervals, and do
not prove Collatz convergence.
-/

/--
The interval-pulse address obtained from one explicit local-island witness has
positive length.

This is the witness-facing wrapper around
`SourcePressureIntervalPulseAddress.len_pos`.  It is intentionally local to the
supplied witness and does not say anything about a complete list of islands.
-/
theorem sourcePressureIntervalPulseAddress_of_localIslandWitness_len_pos
    {n : OddNat} {k r : ℕ}
    (W : SourcePressureLocalIslandWitness n k r) :
    0 < (sourcePressureIntervalPulseAddress_of_localIslandWitness W).len :=
  SourcePressureIntervalPulseAddress.len_pos
    (sourcePressureIntervalPulseAddress_of_localIslandWitness W)

/--
Ordered non-overlap for two explicit local-island witnesses.

This is defined by converting both witnesses to interval-pulse addresses and
using the address-level before predicate.
-/
def SourcePressureLocalIslandWitnessBefore
    {n : OddNat} {k r : ℕ}
    (W1 W2 : SourcePressureLocalIslandWitness n k r) : Prop :=
  SourcePressureIntervalPulseAddressBefore
    (sourcePressureIntervalPulseAddress_of_localIslandWitness W1)
    (sourcePressureIntervalPulseAddress_of_localIslandWitness W2)

/--
Overlap predicate for two explicit local-island witnesses.

This is only the address-level overlap of the intervals obtained from the
supplied witnesses.  It is not a coverage, maximality, or union-accounting
claim, and it is not derivable from one failed `before` relation alone.
-/
def SourcePressureLocalIslandWitnessOverlap
    {n : OddNat} {k r : ℕ}
    (W1 W2 : SourcePressureLocalIslandWitness n k r) : Prop :=
  SourcePressureIntervalPulseAddressOverlap
    (sourcePressureIntervalPulseAddress_of_localIslandWitness W1)
    (sourcePressureIntervalPulseAddress_of_localIslandWitness W2)

/-- Witness-level overlap is symmetric. -/
theorem SourcePressureLocalIslandWitnessOverlap.symm
    {n : OddNat} {k r : ℕ}
    {W1 W2 : SourcePressureLocalIslandWitness n k r}
    (h : SourcePressureLocalIslandWitnessOverlap W1 W2) :
    SourcePressureLocalIslandWitnessOverlap W2 W1 :=
  SourcePressureIntervalPulseAddressOverlap.symm h

/-- A witness-level before relation excludes witness-level overlap. -/
theorem SourcePressureLocalIslandWitnessOverlap.not_of_before
    {n : OddNat} {k r : ℕ}
    {W1 W2 : SourcePressureLocalIslandWitness n k r}
    (hbefore : SourcePressureLocalIslandWitnessBefore W1 W2) :
    ¬ SourcePressureLocalIslandWitnessOverlap W1 W2 :=
  SourcePressureIntervalPulseAddressOverlap.not_of_before hbefore

/-- A reverse witness-level before relation also excludes witness-level overlap. -/
theorem SourcePressureLocalIslandWitnessOverlap.not_of_reverseBefore
    {n : OddNat} {k r : ℕ}
    {W1 W2 : SourcePressureLocalIslandWitness n k r}
    (hbefore : SourcePressureLocalIslandWitnessBefore W2 W1) :
    ¬ SourcePressureLocalIslandWitnessOverlap W1 W2 :=
  SourcePressureIntervalPulseAddressOverlap.not_of_reverseBefore hbefore

/-- Witness overlap excludes the forward before relation. -/
theorem SourcePressureLocalIslandWitnessOverlap.not_before
    {n : OddNat} {k r : ℕ}
    {W1 W2 : SourcePressureLocalIslandWitness n k r}
    (h : SourcePressureLocalIslandWitnessOverlap W1 W2) :
    ¬ SourcePressureLocalIslandWitnessBefore W1 W2 := by
  intro hbefore
  exact SourcePressureLocalIslandWitnessOverlap.not_of_before hbefore h

/-- Witness overlap excludes the reverse before relation. -/
theorem SourcePressureLocalIslandWitnessOverlap.not_reverseBefore
    {n : OddNat} {k r : ℕ}
    {W1 W2 : SourcePressureLocalIslandWitness n k r}
    (h : SourcePressureLocalIslandWitnessOverlap W1 W2) :
    ¬ SourcePressureLocalIslandWitnessBefore W2 W1 := by
  intro hbefore
  exact SourcePressureLocalIslandWitnessOverlap.not_of_reverseBefore hbefore h

/--
Two local-island witness intervals overlap once both ordered directions are
ruled out.

The length-positivity hypotheses are kept explicit because this wrapper only
uses the converted address intervals.  The theorem remains local to the two
supplied witnesses.
-/
theorem SourcePressureLocalIslandWitnessOverlap.of_not_before_not_reverseBefore
    {n : OddNat} {k r : ℕ}
    {W1 W2 : SourcePressureLocalIslandWitness n k r}
    (h1pos :
      0 < (sourcePressureIntervalPulseAddress_of_localIslandWitness W1).len)
    (h2pos :
      0 < (sourcePressureIntervalPulseAddress_of_localIslandWitness W2).len)
    (hnot12 : ¬ SourcePressureLocalIslandWitnessBefore W1 W2)
    (hnot21 : ¬ SourcePressureLocalIslandWitnessBefore W2 W1) :
    SourcePressureLocalIslandWitnessOverlap W1 W2 :=
  SourcePressureIntervalPulseAddressOverlap.of_not_before_not_reverseBefore
    h1pos h2pos hnot12 hnot21

/-- Local trichotomy for two explicit local-island witnesses. -/
theorem SourcePressureLocalIslandWitnessOverlap.before_or_reverseBefore_or_overlap
    {n : OddNat} {k r : ℕ}
    {W1 W2 : SourcePressureLocalIslandWitness n k r}
    (h1pos :
      0 < (sourcePressureIntervalPulseAddress_of_localIslandWitness W1).len)
    (h2pos :
      0 < (sourcePressureIntervalPulseAddress_of_localIslandWitness W2).len) :
    SourcePressureLocalIslandWitnessBefore W1 W2 ∨
      SourcePressureLocalIslandWitnessBefore W2 W1 ∨
        SourcePressureLocalIslandWitnessOverlap W1 W2 :=
  SourcePressureIntervalPulseAddressOverlap.before_or_reverseBefore_or_overlap
    h1pos h2pos

/--
Failure-reason split for a failed witness-level before relation.

This is the local diagnostic form: the failed pair order is either explained by
the reverse order, or the converted witness intervals overlap.  It still does
not enumerate all local islands or create a union-accounting statement.
-/
theorem SourcePressureLocalIslandWitnessOverlap.reverseBefore_or_overlap_of_not_before
    {n : OddNat} {k r : ℕ}
    {W1 W2 : SourcePressureLocalIslandWitness n k r}
    (h1pos :
      0 < (sourcePressureIntervalPulseAddress_of_localIslandWitness W1).len)
    (h2pos :
      0 < (sourcePressureIntervalPulseAddress_of_localIslandWitness W2).len)
    (hnot12 : ¬ SourcePressureLocalIslandWitnessBefore W1 W2) :
    SourcePressureLocalIslandWitnessBefore W2 W1 ∨
      SourcePressureLocalIslandWitnessOverlap W1 W2 :=
  SourcePressureIntervalPulseAddressOverlap.reverseBefore_or_overlap_of_not_before
    h1pos h2pos hnot12

theorem sourcePressureLocalIslandWitnessBefore_iff_addressBefore
    {n : OddNat} {k r : ℕ}
    {W1 W2 : SourcePressureLocalIslandWitness n k r} :
    SourcePressureLocalIslandWitnessBefore W1 W2 ↔
      SourcePressureIntervalPulseAddressBefore
        (sourcePressureIntervalPulseAddress_of_localIslandWitness W1)
        (sourcePressureIntervalPulseAddress_of_localIslandWitness W2) := by
  rfl

/--
A two-witness list is sorted exactly when the first converted address lies
before the second.
-/
theorem sourcePressureLocalIslandWitnessListSortedBefore_pair_iff
    {n : OddNat} {k r : ℕ}
    {W1 W2 : SourcePressureLocalIslandWitness n k r} :
    SourcePressureLocalIslandWitnessListSortedBefore [W1, W2] ↔
      SourcePressureLocalIslandWitnessBefore W1 W2 := by
  change
    SourcePressureIntervalPulseAddressListSortedBefore
      [sourcePressureIntervalPulseAddress_of_localIslandWitness W1,
        sourcePressureIntervalPulseAddress_of_localIslandWitness W2] ↔
      SourcePressureLocalIslandWitnessBefore W1 W2
  rw [sourcePressureIntervalPulseAddressListSortedBefore_pair_iff]
  rfl

/--
A two-witness list has a sorted-before failure exactly when the first converted
address is not before the second.

This is only an order failure.  It is not overlap evidence without additional
hypotheses.
-/
theorem sourcePressureLocalIslandWitnessListHasSortedBeforeFailure_pair_iff
    {n : OddNat} {k r : ℕ}
    {W1 W2 : SourcePressureLocalIslandWitness n k r} :
    SourcePressureLocalIslandWitnessListHasSortedBeforeFailure [W1, W2] ↔
      ¬ SourcePressureLocalIslandWitnessBefore W1 W2 := by
  change
    SourcePressureIntervalPulseAddressListHasSortedBeforeFailure
      [sourcePressureIntervalPulseAddress_of_localIslandWitness W1,
        sourcePressureIntervalPulseAddress_of_localIslandWitness W2] ↔
      ¬ SourcePressureLocalIslandWitnessBefore W1 W2
  rw [sourcePressureIntervalPulseAddressListHasSortedBeforeFailure_pair_iff]
  rfl

/--
Failure-facing constructor for an explicit local-island witness pair.

This theorem records only sorted-before order failure.  It deliberately does
not conclude interval overlap.  The failure may be caused by reversed order.
-/
theorem sourcePressureLocalIslandWitnessPair_hasSortedBeforeFailure_of_not_before
    {n : OddNat} {k r : ℕ}
    {W1 W2 : SourcePressureLocalIslandWitness n k r}
    (hfail : ¬ SourcePressureLocalIslandWitnessBefore W1 W2) :
    SourcePressureLocalIslandWitnessListHasSortedBeforeFailure [W1, W2] :=
  sourcePressureLocalIslandWitnessListHasSortedBeforeFailure_pair_iff.2 hfail

/--
If the first explicit local-island witness is before the second, the pair has
no sorted-before failure.
-/
theorem sourcePressureLocalIslandWitnessPair_no_failure_of_before
    {n : OddNat} {k r : ℕ}
    {W1 W2 : SourcePressureLocalIslandWitness n k r}
    (hbefore : SourcePressureLocalIslandWitnessBefore W1 W2) :
    ¬ SourcePressureLocalIslandWitnessListHasSortedBeforeFailure [W1, W2] := by
  rw [sourcePressureLocalIslandWitnessListHasSortedBeforeFailure_pair_iff]
  exact not_not_intro hbefore

/--
Head constructor for adjacent sorted-before failure in a witness list.

This exposes the first recursive branch of the failure predicate.  It is only
an order-failure constructor for the explicit list.
-/
theorem SourcePressureLocalIslandWitnessListHasSortedBeforeFailure.cons_of_head_not_before
    {n : OddNat} {k r : ℕ}
    {W1 W2 : SourcePressureLocalIslandWitness n k r}
    {rest : List (SourcePressureLocalIslandWitness n k r)}
    (hnot : ¬ SourcePressureLocalIslandWitnessBefore W1 W2) :
    SourcePressureLocalIslandWitnessListHasSortedBeforeFailure
      (W1 :: W2 :: rest) := by
  change (¬ SourcePressureLocalIslandWitnessBefore W1 W2) ∨
    SourcePressureLocalIslandWitnessListHasSortedBeforeFailure (W2 :: rest)
  exact Or.inl hnot

/--
Tail constructor for adjacent sorted-before failure in a witness list.

This exposes the second recursive branch of the failure predicate.  It does
not classify the tail; it only carries an already supplied tail failure.
-/
theorem SourcePressureLocalIslandWitnessListHasSortedBeforeFailure.cons_of_tail
    {n : OddNat} {k r : ℕ}
    {W1 W2 : SourcePressureLocalIslandWitness n k r}
    {rest : List (SourcePressureLocalIslandWitness n k r)}
    (htail :
      SourcePressureLocalIslandWitnessListHasSortedBeforeFailure
        (W2 :: rest)) :
    SourcePressureLocalIslandWitnessListHasSortedBeforeFailure
      (W1 :: W2 :: rest) := by
  simpa [SourcePressureLocalIslandWitnessListHasSortedBeforeFailure,
    sourcePressureIntervalPulseAddressFamily_of_localIslandWitnessList,
    sourcePressureIntervalPulseAddress_of_localIslandWitness,
    SourcePressureIntervalPulseAddressFamilyHasSortedBeforeFailure,
    SourcePressureIntervalPulseAddressListHasSortedBeforeFailure,
    sourcePressureAccountedIntervalList_of_intervalPulseAddressList,
    sourcePressureAccountedInterval_of_intervalPulseAddress,
    SourcePressureAccountedIntervalListHasSortedBeforeFailure] using
    (Or.inr htail)

/-- Case-split constructor for head-or-tail sorted-before failure. -/
theorem SourcePressureLocalIslandWitnessListHasSortedBeforeFailure.cons_of_head_or_tail
    {n : OddNat} {k r : ℕ}
    {W1 W2 : SourcePressureLocalIslandWitness n k r}
    {rest : List (SourcePressureLocalIslandWitness n k r)}
    (h :
      (¬ SourcePressureLocalIslandWitnessBefore W1 W2) ∨
        SourcePressureLocalIslandWitnessListHasSortedBeforeFailure
          (W2 :: rest)) :
    SourcePressureLocalIslandWitnessListHasSortedBeforeFailure
      (W1 :: W2 :: rest) := by
  rcases h with hhead | htail
  · exact
      SourcePressureLocalIslandWitnessListHasSortedBeforeFailure.cons_of_head_not_before
        hhead
  · exact SourcePressureLocalIslandWitnessListHasSortedBeforeFailure.cons_of_tail
      htail

/--
Decompose an adjacent sorted-before failure at a nontrivial witness list into
the head pair or the tail.

This is the inverse of the head/tail constructors.  It peels exactly one
recursive layer and does not classify or repair the resulting branch.
-/
theorem SourcePressureLocalIslandWitnessListHasSortedBeforeFailure.head_or_tail
    {n : OddNat} {k r : ℕ}
    {W1 W2 : SourcePressureLocalIslandWitness n k r}
    {rest : List (SourcePressureLocalIslandWitness n k r)}
    (h :
      SourcePressureLocalIslandWitnessListHasSortedBeforeFailure
        (W1 :: W2 :: rest)) :
    (¬ SourcePressureLocalIslandWitnessBefore W1 W2) ∨
      SourcePressureLocalIslandWitnessListHasSortedBeforeFailure
      (W2 :: rest) := by
  change (¬ SourcePressureLocalIslandWitnessBefore W1 W2) ∨
    SourcePressureLocalIslandWitnessListHasSortedBeforeFailure (W2 :: rest) at h
  exact h

/-- Iff form of one-layer sorted-before failure decomposition. -/
theorem SourcePressureLocalIslandWitnessListHasSortedBeforeFailure.cons_iff_head_or_tail
    {n : OddNat} {k r : ℕ}
    {W1 W2 : SourcePressureLocalIslandWitness n k r}
    {rest : List (SourcePressureLocalIslandWitness n k r)} :
    SourcePressureLocalIslandWitnessListHasSortedBeforeFailure
        (W1 :: W2 :: rest) ↔
      (¬ SourcePressureLocalIslandWitnessBefore W1 W2) ∨
        SourcePressureLocalIslandWitnessListHasSortedBeforeFailure
          (W2 :: rest) :=
  ⟨SourcePressureLocalIslandWitnessListHasSortedBeforeFailure.head_or_tail,
    SourcePressureLocalIslandWitnessListHasSortedBeforeFailure.cons_of_head_or_tail⟩

/--
Every explicit local-island witness pair is either sorted or carries a
sorted-before failure.

This is still only a two-witness statement about the supplied pair.  It does
not enumerate all local islands and does not introduce coverage or maximality.
-/
theorem sourcePressureLocalIslandWitnessPair_sorted_or_failure
    {n : OddNat} {k r : ℕ}
    (W1 W2 : SourcePressureLocalIslandWitness n k r) :
    SourcePressureLocalIslandWitnessListSortedBefore [W1, W2] ∨
      SourcePressureLocalIslandWitnessListHasSortedBeforeFailure [W1, W2] :=
  sourcePressureLocalIslandWitnessList_sorted_or_failure [W1, W2]

/--
Refine a two-witness sorted-before failure into its local reason.

For a pair, failure of `[W1, W2]` means `W1` is not before `W2`.  With positive
converted lengths, the reason is either that the pair is reversed, or that the
two converted witness intervals overlap.  This theorem deliberately stops
there: it does not merge intervals or create a union-accounting family.
-/
theorem sourcePressureLocalIslandWitnessPair_failure_reverseBefore_or_overlap
    {n : OddNat} {k r : ℕ}
    {W1 W2 : SourcePressureLocalIslandWitness n k r}
    (h1pos :
      0 < (sourcePressureIntervalPulseAddress_of_localIslandWitness W1).len)
    (h2pos :
      0 < (sourcePressureIntervalPulseAddress_of_localIslandWitness W2).len)
    (hfail :
      SourcePressureLocalIslandWitnessListHasSortedBeforeFailure [W1, W2]) :
    SourcePressureLocalIslandWitnessBefore W2 W1 ∨
      SourcePressureLocalIslandWitnessOverlap W1 W2 := by
  have hnot12 :
      ¬ SourcePressureLocalIslandWitnessBefore W1 W2 :=
    sourcePressureLocalIslandWitnessListHasSortedBeforeFailure_pair_iff.1 hfail
  exact
    SourcePressureLocalIslandWitnessOverlap.reverseBefore_or_overlap_of_not_before
      h1pos h2pos hnot12

/--
First-class obstruction predicate for the overlap branch of a failed witness
pair.

This packages exactly two local facts: `[W1, W2]` has sorted-before failure and
the converted witness intervals overlap.  It does not merge intervals, produce
coverage, or recover a union-accounting family.
-/
def SourcePressureLocalIslandWitnessPairOverlapObstruction
    {n : OddNat} {k r : ℕ}
    (W1 W2 : SourcePressureLocalIslandWitness n k r) : Prop :=
  SourcePressureLocalIslandWitnessListHasSortedBeforeFailure [W1, W2] ∧
    SourcePressureLocalIslandWitnessOverlap W1 W2

/-- Constructor for the explicit overlap-obstruction predicate. -/
theorem SourcePressureLocalIslandWitnessPairOverlapObstruction.mk_of_failure_overlap
    {n : OddNat} {k r : ℕ}
    {W1 W2 : SourcePressureLocalIslandWitness n k r}
    (hfail : SourcePressureLocalIslandWitnessListHasSortedBeforeFailure [W1, W2])
    (hoverlap : SourcePressureLocalIslandWitnessOverlap W1 W2) :
    SourcePressureLocalIslandWitnessPairOverlapObstruction W1 W2 :=
  ⟨hfail, hoverlap⟩

/-- Extract the sorted-before failure from an overlap obstruction. -/
theorem SourcePressureLocalIslandWitnessPairOverlapObstruction.failure
    {n : OddNat} {k r : ℕ}
    {W1 W2 : SourcePressureLocalIslandWitness n k r}
    (h : SourcePressureLocalIslandWitnessPairOverlapObstruction W1 W2) :
    SourcePressureLocalIslandWitnessListHasSortedBeforeFailure [W1, W2] :=
  h.1

/-- Extract the witness overlap from an overlap obstruction. -/
theorem SourcePressureLocalIslandWitnessPairOverlapObstruction.overlap
    {n : OddNat} {k r : ℕ}
    {W1 W2 : SourcePressureLocalIslandWitness n k r}
    (h : SourcePressureLocalIslandWitnessPairOverlapObstruction W1 W2) :
    SourcePressureLocalIslandWitnessOverlap W1 W2 :=
  h.2

/-- An overlap obstruction still blocks the original order. -/
theorem SourcePressureLocalIslandWitnessPairOverlapObstruction.not_before
    {n : OddNat} {k r : ℕ}
    {W1 W2 : SourcePressureLocalIslandWitness n k r}
    (h : SourcePressureLocalIslandWitnessPairOverlapObstruction W1 W2) :
    ¬ SourcePressureLocalIslandWitnessBefore W1 W2 :=
  SourcePressureLocalIslandWitnessOverlap.not_before h.overlap

/-- An overlap obstruction also blocks the swapped order. -/
theorem SourcePressureLocalIslandWitnessPairOverlapObstruction.not_reverseBefore
    {n : OddNat} {k r : ℕ}
    {W1 W2 : SourcePressureLocalIslandWitness n k r}
    (h : SourcePressureLocalIslandWitnessPairOverlapObstruction W1 W2) :
    ¬ SourcePressureLocalIslandWitnessBefore W2 W1 :=
  SourcePressureLocalIslandWitnessOverlap.not_reverseBefore h.overlap

/--
An overlap obstruction cannot be repaired merely by swapping the two witnesses.

This is the key diagnostic distinction from the reverse branch: reverse order
is recoverable by swapping, but overlap is not.
-/
theorem SourcePressureLocalIslandWitnessPairOverlapObstruction.not_recoverable_by_swap
    {n : OddNat} {k r : ℕ}
    {W1 W2 : SourcePressureLocalIslandWitness n k r}
    (hobs : SourcePressureLocalIslandWitnessPairOverlapObstruction W1 W2) :
    ¬ SourcePressureLocalIslandWitnessListSortedBefore [W2, W1] := by
  intro hsorted
  have hrev : SourcePressureLocalIslandWitnessBefore W2 W1 :=
    sourcePressureLocalIslandWitnessListSortedBefore_pair_iff.1 hsorted
  exact SourcePressureLocalIslandWitnessOverlap.not_reverseBefore hobs.overlap hrev

/--
The swapped two-witness list also has a sorted-before failure under overlap.

Overlap blocks both directions, so the obstruction is independent of which
side of the pair is inspected first.  This is still only a two-witness local
diagnostic and does not merge the overlapping intervals.
-/
theorem SourcePressureLocalIslandWitnessPairOverlapObstruction.swap_failure
    {n : OddNat} {k r : ℕ}
    {W1 W2 : SourcePressureLocalIslandWitness n k r}
    (hobs : SourcePressureLocalIslandWitnessPairOverlapObstruction W1 W2) :
    SourcePressureLocalIslandWitnessListHasSortedBeforeFailure [W2, W1] :=
  sourcePressureLocalIslandWitnessListHasSortedBeforeFailure_pair_iff.2
    hobs.not_reverseBefore

/-- An overlap obstruction makes the original pair list not sorted. -/
theorem SourcePressureLocalIslandWitnessPairOverlapObstruction.not_sorted
    {n : OddNat} {k r : ℕ}
    {W1 W2 : SourcePressureLocalIslandWitness n k r}
    (hobs : SourcePressureLocalIslandWitnessPairOverlapObstruction W1 W2) :
    ¬ SourcePressureLocalIslandWitnessListSortedBefore [W1, W2] := by
  intro hsorted
  have hbefore : SourcePressureLocalIslandWitnessBefore W1 W2 :=
    sourcePressureLocalIslandWitnessListSortedBefore_pair_iff.1 hsorted
  exact hobs.not_before hbefore

/-- An overlap obstruction makes the swapped pair list not sorted. -/
theorem SourcePressureLocalIslandWitnessPairOverlapObstruction.not_sorted_swap
    {n : OddNat} {k r : ℕ}
    {W1 W2 : SourcePressureLocalIslandWitness n k r}
    (hobs : SourcePressureLocalIslandWitnessPairOverlapObstruction W1 W2) :
    ¬ SourcePressureLocalIslandWitnessListSortedBefore [W2, W1] :=
  hobs.not_recoverable_by_swap

/--
Overlap obstruction is symmetric in the two supplied witnesses.

This packages the swapped failure together with symmetric overlap.  It still
does not choose a repaired order, merged interval, or union-accounting family.
-/
theorem SourcePressureLocalIslandWitnessPairOverlapObstruction.symm
    {n : OddNat} {k r : ℕ}
    {W1 W2 : SourcePressureLocalIslandWitness n k r}
    (hobs : SourcePressureLocalIslandWitnessPairOverlapObstruction W1 W2) :
    SourcePressureLocalIslandWitnessPairOverlapObstruction W2 W1 :=
  ⟨hobs.swap_failure, SourcePressureLocalIslandWitnessOverlap.symm hobs.overlap⟩

/-- Symmetric iff form for the local overlap-obstruction predicate. -/
theorem SourcePressureLocalIslandWitnessPairOverlapObstruction.symm_iff
    {n : OddNat} {k r : ℕ}
    {W1 W2 : SourcePressureLocalIslandWitness n k r} :
    SourcePressureLocalIslandWitnessPairOverlapObstruction W1 W2 ↔
      SourcePressureLocalIslandWitnessPairOverlapObstruction W2 W1 :=
  ⟨SourcePressureLocalIslandWitnessPairOverlapObstruction.symm,
    SourcePressureLocalIslandWitnessPairOverlapObstruction.symm⟩

/--
Adjacent overlap obstruction for an explicit local-island witness list.

This predicate intentionally looks only at neighboring witness pairs.  It does
not quantify over arbitrary pairs in the list, does not construct an overlap
cluster, and does not merge or split intervals for union accounting.
-/
def SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction
    {n : OddNat} {k r : ℕ} :
    List (SourcePressureLocalIslandWitness n k r) → Prop
  | [] => False
  | [_] => False
  | W1 :: W2 :: rest =>
      SourcePressureLocalIslandWitnessPairOverlapObstruction W1 W2 ∨
        SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction
          (W2 :: rest)

/-- A two-witness list has adjacent overlap obstruction exactly at that pair. -/
theorem SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction_pair_iff
    {n : OddNat} {k r : ℕ}
    {W1 W2 : SourcePressureLocalIslandWitness n k r} :
    SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction [W1, W2] ↔
      SourcePressureLocalIslandWitnessPairOverlapObstruction W1 W2 := by
  simp [SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction]

/-- Head constructor for adjacent overlap obstruction. -/
theorem SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction.cons_of_head
    {n : OddNat} {k r : ℕ}
    {W1 W2 : SourcePressureLocalIslandWitness n k r}
    {rest : List (SourcePressureLocalIslandWitness n k r)}
    (hobs : SourcePressureLocalIslandWitnessPairOverlapObstruction W1 W2) :
    SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction
      (W1 :: W2 :: rest) :=
  Or.inl hobs

/-- Tail constructor for adjacent overlap obstruction. -/
theorem SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction.cons_of_tail
    {n : OddNat} {k r : ℕ}
    {W1 W2 : SourcePressureLocalIslandWitness n k r}
    {rest : List (SourcePressureLocalIslandWitness n k r)}
    (htail :
      SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction
        (W2 :: rest)) :
    SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction
      (W1 :: W2 :: rest) :=
  Or.inr htail

/-- Readable alias for propagating adjacent overlap obstruction from the tail. -/
theorem SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction.of_tail
    {n : OddNat} {k r : ℕ}
    {W1 W2 : SourcePressureLocalIslandWitness n k r}
    {rest : List (SourcePressureLocalIslandWitness n k r)}
    (htail :
      SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction
        (W2 :: rest)) :
    SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction
      (W1 :: W2 :: rest) :=
  SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction.cons_of_tail
    htail

/-- Adjacent overlap obstruction for a pair is symmetric. -/
theorem SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction_pair_symm
    {n : OddNat} {k r : ℕ}
    {W1 W2 : SourcePressureLocalIslandWitness n k r}
    (h :
      SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction
        [W1, W2]) :
    SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction
      [W2, W1] := by
  rw [SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction_pair_iff]
  exact
    SourcePressureLocalIslandWitnessPairOverlapObstruction.symm
      (SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction_pair_iff.1 h)

/--
Adjacent overlap obstruction implies ordinary adjacent sorted-before failure.

The proof follows the explicit neighboring-pair recursion.  It does not turn
overlap into a repaired family and does not construct any merged interval.
-/
theorem SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction.hasSortedBeforeFailure
    {n : OddNat} {k r : ℕ}
    {L : List (SourcePressureLocalIslandWitness n k r)}
    (hobs :
      SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction L) :
    SourcePressureLocalIslandWitnessListHasSortedBeforeFailure L := by
  induction L with
  | nil =>
      exact False.elim hobs
  | cons W1 L ih =>
      cases L with
      | nil =>
          exact False.elim hobs
      | cons W2 rest =>
          rcases hobs with hhead | htail
          · change (¬ SourcePressureLocalIslandWitnessBefore W1 W2) ∨
              SourcePressureLocalIslandWitnessListHasSortedBeforeFailure (W2 :: rest)
            exact Or.inl hhead.not_before
          · have htailFailure :
                SourcePressureLocalIslandWitnessListHasSortedBeforeFailure
                  (W2 :: rest) :=
              ih htail
            simpa [SourcePressureLocalIslandWitnessListHasSortedBeforeFailure,
              sourcePressureIntervalPulseAddressFamily_of_localIslandWitnessList,
              SourcePressureIntervalPulseAddressFamilyHasSortedBeforeFailure,
              SourcePressureIntervalPulseAddressListHasSortedBeforeFailure,
              sourcePressureAccountedIntervalList_of_intervalPulseAddressList,
              SourcePressureAccountedIntervalListHasSortedBeforeFailure] using
              (Or.inr htailFailure)

/-- Pair specialization of adjacent obstruction implying sorted-before failure. -/
theorem
    SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction_pair_hasSortedBeforeFailure
    {n : OddNat} {k r : ℕ}
    {W1 W2 : SourcePressureLocalIslandWitness n k r}
    (hobs :
      SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction
        [W1, W2]) :
    SourcePressureLocalIslandWitnessListHasSortedBeforeFailure [W1, W2] :=
  SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction.hasSortedBeforeFailure
    hobs

/--
Tail adjacent-overlap obstruction gives sorted-before failure for the full
explicit list.

This is only propagation through a new head.  It does not inspect or repair the
tail obstruction.
-/
theorem
    SourcePressureLocalIslandWitnessListHasSortedBeforeFailure.of_tailAdjacentOverlapObstruction
    {n : OddNat} {k r : ℕ}
    {W1 W2 : SourcePressureLocalIslandWitness n k r}
    {rest : List (SourcePressureLocalIslandWitness n k r)}
    (htail :
      SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction
        (W2 :: rest)) :
    SourcePressureLocalIslandWitnessListHasSortedBeforeFailure
      (W1 :: W2 :: rest) :=
  SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction.hasSortedBeforeFailure
    (SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction.of_tail
      htail)

/--
Reverse-recovery helper for a pair whose failure reason is merely reversed
order.

If `W2` is before `W1`, then the swapped two-witness list is sorted.  This is
not an overlap theorem and not a global reordering theorem; it only recovers
the explicit two-element list.
-/
theorem sourcePressureLocalIslandWitnessPair_sorted_swap_of_reverseBefore
    {n : OddNat} {k r : ℕ}
    {W1 W2 : SourcePressureLocalIslandWitness n k r}
    (hrev : SourcePressureLocalIslandWitnessBefore W2 W1) :
    SourcePressureLocalIslandWitnessListSortedBefore [W2, W1] :=
  sourcePressureLocalIslandWitnessListSortedBefore_pair_iff.2 hrev

/--
Raw-argument version of the pair sorted-before failure constructor.

This packages the two supplied local-island facts as explicit witnesses.  As
above, the result is only order obstruction, not overlap evidence.
-/
theorem sourcePressureLocalIsland_pair_hasSortedBeforeFailure_of_not_before
    (n : OddNat) (k r j1 j2 : ℕ)
    (h1 : SourcePressureLocalIsland n k r j1)
    (h2 : SourcePressureLocalIsland n k r j2)
    (hfail :
      ¬ SourcePressureLocalIslandWitnessBefore
        (⟨j1, h1⟩ : SourcePressureLocalIslandWitness n k r)
        (⟨j2, h2⟩ : SourcePressureLocalIslandWitness n k r)) :
    SourcePressureLocalIslandWitnessListHasSortedBeforeFailure
      [(⟨j1, h1⟩ : SourcePressureLocalIslandWitness n k r),
       (⟨j2, h2⟩ : SourcePressureLocalIslandWitness n k r)] :=
  sourcePressureLocalIslandWitnessPair_hasSortedBeforeFailure_of_not_before hfail

/--
Raw-argument no-failure wrapper for an explicitly ordered local-island pair.
-/
theorem sourcePressureLocalIsland_pair_no_failure_of_before
    (n : OddNat) (k r j1 j2 : ℕ)
    (h1 : SourcePressureLocalIsland n k r j1)
    (h2 : SourcePressureLocalIsland n k r j2)
    (hbefore :
      SourcePressureLocalIslandWitnessBefore
        (⟨j1, h1⟩ : SourcePressureLocalIslandWitness n k r)
        (⟨j2, h2⟩ : SourcePressureLocalIslandWitness n k r)) :
    ¬ SourcePressureLocalIslandWitnessListHasSortedBeforeFailure
      [(⟨j1, h1⟩ : SourcePressureLocalIslandWitness n k r),
       (⟨j2, h2⟩ : SourcePressureLocalIslandWitness n k r)] :=
  sourcePressureLocalIslandWitnessPair_no_failure_of_before hbefore

/--
Accounted interval family generated by two explicitly sorted local-island
witnesses.

The `hbefore` hypothesis is just the supplied order relation.  No coverage,
maximality, or uniqueness is inferred.
-/
def sourcePressureAccountedIntervalFamily_of_sortedLocalIslandWitnessPair
    {n : OddNat} {k r : ℕ}
    (W1 W2 : SourcePressureLocalIslandWitness n k r)
    (hbefore : SourcePressureLocalIslandWitnessBefore W1 W2) :
    SourcePressureAccountedIntervalFamily n k r :=
  sourcePressureAccountedIntervalFamily_of_sortedLocalIslandWitnessList
    [W1, W2]
    (sourcePressureLocalIslandWitnessListSortedBefore_pair_iff.2 hbefore)

@[simp]
theorem sourcePressureAccountedIntervalFamily_of_sortedLocalIslandWitnessPair_length
    {n : OddNat} {k r : ℕ}
    (W1 W2 : SourcePressureLocalIslandWitness n k r)
    (hbefore : SourcePressureLocalIslandWitnessBefore W1 W2) :
    (sourcePressureAccountedIntervalFamily_of_sortedLocalIslandWitnessPair
      W1 W2 hbefore).items.length = 2 := by
  simp [sourcePressureAccountedIntervalFamily_of_sortedLocalIslandWitnessPair]

/--
The sorted two-witness family contains exactly the two directly converted
accounted intervals.
-/
theorem sourcePressureAccountedIntervalFamily_of_sortedLocalIslandWitnessPair_items
    {n : OddNat} {k r : ℕ}
    (W1 W2 : SourcePressureLocalIslandWitness n k r)
    (hbefore : SourcePressureLocalIslandWitnessBefore W1 W2) :
    (sourcePressureAccountedIntervalFamily_of_sortedLocalIslandWitnessPair
      W1 W2 hbefore).items =
      [sourcePressureAccountedInterval_of_intervalPulseAddress
        (sourcePressureIntervalPulseAddress_of_localIslandWitness W1),
       sourcePressureAccountedInterval_of_intervalPulseAddress
        (sourcePressureIntervalPulseAddress_of_localIslandWitness W2)] := by
  rfl

/--
The listed cost of a sorted two-witness family is at most `-2`.
-/
theorem sourcePressureAccountedIntervalFamily_of_sortedLocalIslandWitnessPair_sum_le_neg_two
    {n : OddNat} {k r : ℕ}
    (W1 W2 : SourcePressureLocalIslandWitness n k r)
    (hbefore : SourcePressureLocalIslandWitnessBefore W1 W2) :
    (((sourcePressureAccountedIntervalFamily_of_sortedLocalIslandWitnessPair
      W1 W2 hbefore).items).map
      (fun A => SourcePressureIntervalNetDrop n k r A.start A.len)).sum ≤ -2 := by
  simpa [sourcePressureAccountedIntervalFamily_of_sortedLocalIslandWitnessPair]
    using
      sourcePressureAccountedIntervalFamily_of_sortedLocalIslandWitnessList_sum_le_neg_length
        [W1, W2]
        (sourcePressureLocalIslandWitnessListSortedBefore_pair_iff.2 hbefore)

/-- The sorted two-witness family has strictly negative listed cost. -/
theorem sourcePressureAccountedIntervalFamily_of_sortedLocalIslandWitnessPair_sum_neg
    {n : OddNat} {k r : ℕ}
    (W1 W2 : SourcePressureLocalIslandWitness n k r)
    (hbefore : SourcePressureLocalIslandWitnessBefore W1 W2) :
    (((sourcePressureAccountedIntervalFamily_of_sortedLocalIslandWitnessPair
      W1 W2 hbefore).items).map
      (fun A => SourcePressureIntervalNetDrop n k r A.start A.len)).sum < 0 := by
  simpa [sourcePressureAccountedIntervalFamily_of_sortedLocalIslandWitnessPair]
    using
      sourcePressureAccountedIntervalFamily_of_sortedLocalIslandWitnessList_sum_neg_of_nonempty
        (sourcePressureLocalIslandWitnessListSortedBefore_pair_iff.2 hbefore)
        (by simp)

/--
Recovered accounted interval family for a reversed local-island witness pair.

This is only a two-witness local recovery by swapping the supplied pair.  It is
not a global sorting algorithm, not a maximal family construction, and not a
union-accounting theorem.
-/
def sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair
    {n : OddNat} {k r : ℕ}
    (W1 W2 : SourcePressureLocalIslandWitness n k r)
    (hrev : SourcePressureLocalIslandWitnessBefore W2 W1) :
    SourcePressureAccountedIntervalFamily n k r :=
  sourcePressureAccountedIntervalFamily_of_sortedLocalIslandWitnessPair
    W2 W1 hrev

@[simp]
theorem sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair_length
    {n : OddNat} {k r : ℕ}
    (W1 W2 : SourcePressureLocalIslandWitness n k r)
    (hrev : SourcePressureLocalIslandWitnessBefore W2 W1) :
    (sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair
      W1 W2 hrev).items.length = 2 := by
  simp [sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair]

/--
The recovered reversed pair lists the converted intervals in swapped order.
-/
theorem sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair_items
    {n : OddNat} {k r : ℕ}
    (W1 W2 : SourcePressureLocalIslandWitness n k r)
    (hrev : SourcePressureLocalIslandWitnessBefore W2 W1) :
    (sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair
      W1 W2 hrev).items =
      [sourcePressureAccountedInterval_of_intervalPulseAddress
        (sourcePressureIntervalPulseAddress_of_localIslandWitness W2),
       sourcePressureAccountedInterval_of_intervalPulseAddress
        (sourcePressureIntervalPulseAddress_of_localIslandWitness W1)] := by
  rfl

/- The recovered reversed-pair budget is just the sorted pair budget after swap. -/
theorem sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair_sum_le_neg_two
    {n : OddNat} {k r : ℕ}
    (W1 W2 : SourcePressureLocalIslandWitness n k r)
    (hrev : SourcePressureLocalIslandWitnessBefore W2 W1) :
    (((sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair
      W1 W2 hrev).items).map
      (fun A => SourcePressureIntervalNetDrop n k r A.start A.len)).sum ≤ -2 :=
  sourcePressureAccountedIntervalFamily_of_sortedLocalIslandWitnessPair_sum_le_neg_two
    W2 W1 hrev

/-- The recovered reversed-pair family has strictly negative listed cost. -/
theorem sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair_sum_neg
    {n : OddNat} {k r : ℕ}
    (W1 W2 : SourcePressureLocalIslandWitness n k r)
    (hrev : SourcePressureLocalIslandWitnessBefore W2 W1) :
    (((sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair
      W1 W2 hrev).items).map
      (fun A => SourcePressureIntervalNetDrop n k r A.start A.len)).sum < 0 :=
  sourcePressureAccountedIntervalFamily_of_sortedLocalIslandWitnessPair_sum_neg
    W2 W1 hrev

/--
Failure-use wrapper: if `[W1, W2]` failed because the witnesses are reversed,
the swapped recovered family still has the two-interval `≤ -2` budget.

The failure hypothesis is intentionally not used by the proof.  It documents
the branch in which this theorem is meant to be applied.
-/
theorem sourcePressureLocalIslandWitnessPair_failure_reversed_sum_le_neg_two
    {n : OddNat} {k r : ℕ}
    {W1 W2 : SourcePressureLocalIslandWitness n k r}
    (_hfail : SourcePressureLocalIslandWitnessListHasSortedBeforeFailure [W1, W2])
    (hrev : SourcePressureLocalIslandWitnessBefore W2 W1) :
    (((sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair
      W1 W2 hrev).items).map
      (fun A => SourcePressureIntervalNetDrop n k r A.start A.len)).sum ≤ -2 :=
  sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair_sum_le_neg_two
    W1 W2 hrev

/--
Failure-use wrapper: the reversed recovered family has strictly negative
listed cost.
-/
theorem sourcePressureLocalIslandWitnessPair_failure_reversed_sum_neg
    {n : OddNat} {k r : ℕ}
    {W1 W2 : SourcePressureLocalIslandWitness n k r}
    (_hfail : SourcePressureLocalIslandWitnessListHasSortedBeforeFailure [W1, W2])
    (hrev : SourcePressureLocalIslandWitnessBefore W2 W1) :
    (((sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair
      W1 W2 hrev).items).map
      (fun A => SourcePressureIntervalNetDrop n k r A.start A.len)).sum < 0 :=
  sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair_sum_neg
    W1 W2 hrev

/--
Recovered-or-overlap split for a failed two-witness order.

If the pair failure is a reversed-order failure, the swapped recovered family
has the two-interval budget.  Otherwise the obstruction is overlap.  This is
still a local two-witness theorem: it does not merge overlapping intervals and
does not produce union accounting.
-/
theorem sourcePressureLocalIslandWitnessPair_failure_recovered_or_overlap
    {n : OddNat} {k r : ℕ}
    {W1 W2 : SourcePressureLocalIslandWitness n k r}
    (h1pos :
      0 < (sourcePressureIntervalPulseAddress_of_localIslandWitness W1).len)
    (h2pos :
      0 < (sourcePressureIntervalPulseAddress_of_localIslandWitness W2).len)
    (hfail : SourcePressureLocalIslandWitnessListHasSortedBeforeFailure [W1, W2]) :
    (∃ hrev : SourcePressureLocalIslandWitnessBefore W2 W1,
      (((sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair
        W1 W2 hrev).items).map
        (fun A => SourcePressureIntervalNetDrop n k r A.start A.len)).sum ≤ -2)
    ∨ SourcePressureLocalIslandWitnessOverlap W1 W2 := by
  rcases sourcePressureLocalIslandWitnessPair_failure_reverseBefore_or_overlap
      h1pos h2pos hfail with hrev | hoverlap
  · exact Or.inl
      ⟨hrev,
        sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair_sum_le_neg_two
          W1 W2 hrev⟩
  · exact Or.inr hoverlap

/--
Recovered-or-obstruction split for a failed two-witness order.

The left branch is the recovered reversed-order budget.  The right branch is a
first-class overlap obstruction, keeping the overlap branch explicit and
unmerged.
-/
theorem sourcePressureLocalIslandWitnessPair_failure_recovered_or_overlapObstruction
    {n : OddNat} {k r : ℕ}
    {W1 W2 : SourcePressureLocalIslandWitness n k r}
    (h1pos :
      0 < (sourcePressureIntervalPulseAddress_of_localIslandWitness W1).len)
    (h2pos :
      0 < (sourcePressureIntervalPulseAddress_of_localIslandWitness W2).len)
    (hfail : SourcePressureLocalIslandWitnessListHasSortedBeforeFailure [W1, W2]) :
    (∃ hrev : SourcePressureLocalIslandWitnessBefore W2 W1,
      (((sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair
        W1 W2 hrev).items).map
        (fun A => SourcePressureIntervalNetDrop n k r A.start A.len)).sum ≤ -2)
    ∨ SourcePressureLocalIslandWitnessPairOverlapObstruction W1 W2 := by
  rcases sourcePressureLocalIslandWitnessPair_failure_recovered_or_overlap
      h1pos h2pos hfail with hrecovered | hoverlap
  · exact Or.inl hrecovered
  · exact Or.inr
      (SourcePressureLocalIslandWitnessPairOverlapObstruction.mk_of_failure_overlap
        hfail hoverlap)

/--
Head-pair view of the recovered-or-overlap-obstruction split.

This is only a naming bridge for callers that are processing the first adjacent
pair of a witness list.  The theorem itself remains pair-local and does not
inspect or sort a tail list.
-/
theorem
    sourcePressureLocalIslandWitnessList_headPair_failure_recovered_or_overlapObstruction
    {n : OddNat} {k r : ℕ}
    {W1 W2 : SourcePressureLocalIslandWitness n k r}
    (h1pos :
      0 < (sourcePressureIntervalPulseAddress_of_localIslandWitness W1).len)
    (h2pos :
      0 < (sourcePressureIntervalPulseAddress_of_localIslandWitness W2).len)
    (hfail : SourcePressureLocalIslandWitnessListHasSortedBeforeFailure [W1, W2]) :
    (∃ hrev : SourcePressureLocalIslandWitnessBefore W2 W1,
      (((sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair
        W1 W2 hrev).items).map
        (fun A => SourcePressureIntervalNetDrop n k r A.start A.len)).sum ≤ -2)
    ∨ SourcePressureLocalIslandWitnessPairOverlapObstruction W1 W2 :=
  sourcePressureLocalIslandWitnessPair_failure_recovered_or_overlapObstruction
    h1pos h2pos hfail

/--
Embed a head-pair overlap obstruction into the adjacent-list obstruction
predicate.

The tail is merely carried by the explicit list.  No non-adjacent pair search,
cluster construction, or interval merge is introduced.
-/
theorem
    SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction.of_headPairObstruction
    {n : OddNat} {k r : ℕ}
    {W1 W2 : SourcePressureLocalIslandWitness n k r}
    {rest : List (SourcePressureLocalIslandWitness n k r)}
    (hobs : SourcePressureLocalIslandWitnessPairOverlapObstruction W1 W2) :
    SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction
      (W1 :: W2 :: rest) :=
  SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction.cons_of_head
    hobs

/--
A head-pair overlap obstruction gives a sorted-before failure for the explicit
list whose first two witnesses form that obstructed pair.

This uses only the adjacent obstruction wrapper; it does not repair or merge
the overlap branch.
-/
theorem SourcePressureLocalIslandWitnessListHasSortedBeforeFailure.of_headPairOverlapObstruction
    {n : OddNat} {k r : ℕ}
    {W1 W2 : SourcePressureLocalIslandWitness n k r}
    {rest : List (SourcePressureLocalIslandWitness n k r)}
    (hobs : SourcePressureLocalIslandWitnessPairOverlapObstruction W1 W2) :
    SourcePressureLocalIslandWitnessListHasSortedBeforeFailure
      (W1 :: W2 :: rest) :=
  SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction.hasSortedBeforeFailure
    (SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction.of_headPairObstruction
      hobs)

/--
Head-pair list-facing split: a failed first adjacent pair is either recovered
by swapping that pair, or it embeds as an adjacent overlap obstruction in the
explicit list.

This does not classify failures deeper in the list and does not perform
list-wide sorting.
-/
theorem
    sourcePressureLocalIslandWitnessList_headPair_failure_recovered_or_adjacentOverlapObstruction
    {n : OddNat} {k r : ℕ}
    {W1 W2 : SourcePressureLocalIslandWitness n k r}
    {rest : List (SourcePressureLocalIslandWitness n k r)}
    (h1pos :
      0 < (sourcePressureIntervalPulseAddress_of_localIslandWitness W1).len)
    (h2pos :
      0 < (sourcePressureIntervalPulseAddress_of_localIslandWitness W2).len)
    (hfail : SourcePressureLocalIslandWitnessListHasSortedBeforeFailure [W1, W2]) :
    (∃ hrev : SourcePressureLocalIslandWitnessBefore W2 W1,
      (((sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair
        W1 W2 hrev).items).map
        (fun A => SourcePressureIntervalNetDrop n k r A.start A.len)).sum ≤ -2)
    ∨ SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction
        (W1 :: W2 :: rest) := by
  rcases
      sourcePressureLocalIslandWitnessList_headPair_failure_recovered_or_overlapObstruction
        h1pos h2pos hfail with hrecovered | hobs
  · exact Or.inl hrecovered
  · exact Or.inr
      (SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction.of_headPairObstruction
        hobs)

/--
Head not-before diagnosis for an explicit witness list.

The head order failure is first packaged as the two-witness sorted-before
failure, then passed to the head-pair recovered-or-obstruction split.
-/
theorem
    sourcePressureLocalIslandWitnessList_headNotBefore_recovered_or_adjacentOverlapObstruction
    {n : OddNat} {k r : ℕ}
    {W1 W2 : SourcePressureLocalIslandWitness n k r}
    {rest : List (SourcePressureLocalIslandWitness n k r)}
    (h1pos :
      0 < (sourcePressureIntervalPulseAddress_of_localIslandWitness W1).len)
    (h2pos :
      0 < (sourcePressureIntervalPulseAddress_of_localIslandWitness W2).len)
    (hnot : ¬ SourcePressureLocalIslandWitnessBefore W1 W2) :
    (∃ hrev : SourcePressureLocalIslandWitnessBefore W2 W1,
      (((sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair
        W1 W2 hrev).items).map
        (fun A => SourcePressureIntervalNetDrop n k r A.start A.len)).sum ≤ -2)
    ∨ SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction
        (W1 :: W2 :: rest) :=
  sourcePressureLocalIslandWitnessList_headPair_failure_recovered_or_adjacentOverlapObstruction
    h1pos h2pos
    (sourcePressureLocalIslandWitnessListHasSortedBeforeFailure_pair_iff.2
      hnot)

/--
One-step diagnosis for a nontrivial witness-list sorted-before failure.

The theorem peels one recursive layer.  A head failure is diagnosed by the
pair-level recovered-or-adjacent-obstruction split; a tail failure is returned
as a tail branch.  It is not a recursive algorithm.
-/
theorem sourcePressureLocalIslandWitnessList_failure_oneStepDiagnosis
    {n : OddNat} {k r : ℕ}
    {W1 W2 : SourcePressureLocalIslandWitness n k r}
    {rest : List (SourcePressureLocalIslandWitness n k r)}
    (h1pos :
      0 < (sourcePressureIntervalPulseAddress_of_localIslandWitness W1).len)
    (h2pos :
      0 < (sourcePressureIntervalPulseAddress_of_localIslandWitness W2).len)
    (h :
      SourcePressureLocalIslandWitnessListHasSortedBeforeFailure
        (W1 :: W2 :: rest)) :
    ((∃ hrev : SourcePressureLocalIslandWitnessBefore W2 W1,
      (((sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair
        W1 W2 hrev).items).map
        (fun A => SourcePressureIntervalNetDrop n k r A.start A.len)).sum ≤ -2)
      ∨ SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction
          (W1 :: W2 :: rest))
    ∨ SourcePressureLocalIslandWitnessListHasSortedBeforeFailure
        (W2 :: rest) := by
  rcases SourcePressureLocalIslandWitnessListHasSortedBeforeFailure.head_or_tail h
      with hhead | htail
  · exact Or.inl
      (sourcePressureLocalIslandWitnessList_headNotBefore_recovered_or_adjacentOverlapObstruction
        h1pos h2pos hhead)
  · exact Or.inr htail

/--
Tail-facing alias for one-step diagnosis.

The recovered branch is still the reversed budget for the tail head pair
`W2, W3`; this theorem only chooses names that make the tail role explicit.
-/
theorem sourcePressureLocalIslandWitnessList_tail_failure_oneStepDiagnosis
    {n : OddNat} {k r : ℕ}
    {W2 W3 : SourcePressureLocalIslandWitness n k r}
    {rest : List (SourcePressureLocalIslandWitness n k r)}
    (h2pos :
      0 < (sourcePressureIntervalPulseAddress_of_localIslandWitness W2).len)
    (h3pos :
      0 < (sourcePressureIntervalPulseAddress_of_localIslandWitness W3).len)
    (htail :
      SourcePressureLocalIslandWitnessListHasSortedBeforeFailure
        (W2 :: W3 :: rest)) :
    ((∃ hrev : SourcePressureLocalIslandWitnessBefore W3 W2,
      (((sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair
        W2 W3 hrev).items).map
        (fun A => SourcePressureIntervalNetDrop n k r A.start A.len)).sum ≤ -2)
      ∨ SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction
          (W2 :: W3 :: rest))
    ∨ SourcePressureLocalIslandWitnessListHasSortedBeforeFailure
        (W3 :: rest) :=
  sourcePressureLocalIslandWitnessList_failure_oneStepDiagnosis
    h2pos h3pos htail

/--
Lift an adjacent-overlap obstruction in the tail under a newly supplied head.

This is only propagation of the obstruction predicate.  It does not merge
intervals, repair overlap, or create a full-list recovered budget.
-/
theorem sourcePressureLocalIslandWitnessList_tailDiagnosis_overlap_lift
    {n : OddNat} {k r : ℕ}
    {W1 W2 W3 : SourcePressureLocalIslandWitness n k r}
    {rest : List (SourcePressureLocalIslandWitness n k r)}
    (hobs :
      SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction
        (W2 :: W3 :: rest)) :
    SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction
      (W1 :: W2 :: W3 :: rest) :=
  SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction.of_tail
    hobs

/--
Weakly view a tail one-step diagnosis under a new head.

The left recovered branch remains the recovered budget for the tail pair
`W2, W3`.  The new head can only carry the tail overlap obstruction forward;
it does not turn a tail-pair recovery into accounting for the full list.
-/
theorem sourcePressureLocalIslandWitnessList_tailFailure_oneStepDiagnosis_under_cons
    {n : OddNat} {k r : ℕ}
    {W1 W2 W3 : SourcePressureLocalIslandWitness n k r}
    {rest : List (SourcePressureLocalIslandWitness n k r)}
    (h2pos :
      0 < (sourcePressureIntervalPulseAddress_of_localIslandWitness W2).len)
    (h3pos :
      0 < (sourcePressureIntervalPulseAddress_of_localIslandWitness W3).len)
    (htail :
      SourcePressureLocalIslandWitnessListHasSortedBeforeFailure
        (W2 :: W3 :: rest)) :
    ((∃ hrev : SourcePressureLocalIslandWitnessBefore W3 W2,
      (((sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair
        W2 W3 hrev).items).map
        (fun A => SourcePressureIntervalNetDrop n k r A.start A.len)).sum ≤ -2)
      ∨ SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction
          (W1 :: W2 :: W3 :: rest))
    ∨ SourcePressureLocalIslandWitnessListHasSortedBeforeFailure
        (W3 :: rest) := by
  rcases sourcePressureLocalIslandWitnessList_tail_failure_oneStepDiagnosis
      h2pos h3pos htail with htailDiag | hdeep
  · rcases htailDiag with hrecovered | hobs
    · exact Or.inl (Or.inl hrecovered)
    · exact Or.inl (Or.inr
        (sourcePressureLocalIslandWitnessList_tailDiagnosis_overlap_lift
          hobs))
  · exact Or.inr hdeep

/--
Weak tail diagnosis with the lifted overlap branch downgraded to ordinary
full-list sorted-before failure.

The recovered branch is still only the tail-pair recovered budget.  This wrapper
is useful for callers that only need to know that the enlarged list fails, while
the obstruction-specific theorem above keeps the sharper evidence.
-/
theorem
    sourcePressureLocalIslandWitnessList_tailFailure_oneStepDiagnosis_under_cons_or_listFailure
    {n : OddNat} {k r : ℕ}
    {W1 W2 W3 : SourcePressureLocalIslandWitness n k r}
    {rest : List (SourcePressureLocalIslandWitness n k r)}
    (h2pos :
      0 < (sourcePressureIntervalPulseAddress_of_localIslandWitness W2).len)
    (h3pos :
      0 < (sourcePressureIntervalPulseAddress_of_localIslandWitness W3).len)
    (htail :
      SourcePressureLocalIslandWitnessListHasSortedBeforeFailure
        (W2 :: W3 :: rest)) :
    ((∃ hrev : SourcePressureLocalIslandWitnessBefore W3 W2,
      (((sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair
        W2 W3 hrev).items).map
        (fun A => SourcePressureIntervalNetDrop n k r A.start A.len)).sum ≤ -2)
      ∨ SourcePressureLocalIslandWitnessListHasSortedBeforeFailure
          (W1 :: W2 :: W3 :: rest))
    ∨ SourcePressureLocalIslandWitnessListHasSortedBeforeFailure
        (W3 :: rest) := by
  rcases sourcePressureLocalIslandWitnessList_tailFailure_oneStepDiagnosis_under_cons
      h2pos h3pos htail with hdiag | hdeep
  · rcases hdiag with hrecovered | hobs
    · exact Or.inl (Or.inl hrecovered)
    · exact Or.inl (Or.inr
        (SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction.hasSortedBeforeFailure
          hobs))
  · exact Or.inr hdeep

/--
Diagnose a tail pair failure under a newly supplied head.

The recovered branch is attached to the tail pair `W2, W3`.  The obstruction
branch is the lifted adjacent overlap on the bounded three-witness list.
-/
theorem sourcePressureLocalIslandWitnessList_tailPair_failure_under_cons_diagnosis
    {n : OddNat} {k r : ℕ}
    {W1 W2 W3 : SourcePressureLocalIslandWitness n k r}
    (h2pos :
      0 < (sourcePressureIntervalPulseAddress_of_localIslandWitness W2).len)
    (h3pos :
      0 < (sourcePressureIntervalPulseAddress_of_localIslandWitness W3).len)
    (htail :
      SourcePressureLocalIslandWitnessListHasSortedBeforeFailure [W2, W3]) :
    (∃ hrev : SourcePressureLocalIslandWitnessBefore W3 W2,
      (((sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair
        W2 W3 hrev).items).map
        (fun A => SourcePressureIntervalNetDrop n k r A.start A.len)).sum ≤ -2)
    ∨ SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction
        [W1, W2, W3] := by
  rcases sourcePressureLocalIslandWitnessList_tailFailure_oneStepDiagnosis_under_cons
      h2pos h3pos htail with hdiag | hsingle
  · exact hdiag
  · exact False.elim
      (SourcePressureLocalIslandWitnessListHasSortedBeforeFailure_singleton_false
        hsingle)

/--
Bounded diagnosis for a three-witness sorted-before failure.

The failure of `[W1, W2, W3]` is diagnosed by one of its two adjacent pairs.
Recovered budgets remain pair-local: either `W1, W2` or `W2, W3`.  This is a
fixed length-three theorem, not a recursive classifier.
-/
theorem sourcePressureLocalIslandWitnessList_failure_threeDiagnosis
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
    ((∃ hrev : SourcePressureLocalIslandWitnessBefore W2 W1,
      (((sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair
        W1 W2 hrev).items).map
        (fun A => SourcePressureIntervalNetDrop n k r A.start A.len)).sum ≤ -2)
      ∨ SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction
          [W1, W2, W3])
    ∨
    ((∃ hrev : SourcePressureLocalIslandWitnessBefore W3 W2,
      (((sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair
        W2 W3 hrev).items).map
        (fun A => SourcePressureIntervalNetDrop n k r A.start A.len)).sum ≤ -2)
      ∨ SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction
          [W1, W2, W3]) := by
  rcases sourcePressureLocalIslandWitnessList_failure_oneStepDiagnosis
      h1pos h2pos h with hhead | htail
  · exact Or.inl hhead
  · exact Or.inr
      (sourcePressureLocalIslandWitnessList_tailPair_failure_under_cons_diagnosis
        h2pos h3pos htail)

/--
Length-three diagnosis with overlap branches weakened to ordinary failure of
the same three-witness list.

The recovered alternatives are still pair-local.  This wrapper is deliberately
bounded to length three and does not perform list sorting or union accounting.
-/
theorem sourcePressureLocalIslandWitnessList_failure_threeDiagnosis_or_listFailure
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
    ((∃ hrev : SourcePressureLocalIslandWitnessBefore W2 W1,
      (((sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair
        W1 W2 hrev).items).map
        (fun A => SourcePressureIntervalNetDrop n k r A.start A.len)).sum ≤ -2)
      ∨ SourcePressureLocalIslandWitnessListHasSortedBeforeFailure
          [W1, W2, W3])
    ∨
    ((∃ hrev : SourcePressureLocalIslandWitnessBefore W3 W2,
      (((sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair
        W2 W3 hrev).items).map
        (fun A => SourcePressureIntervalNetDrop n k r A.start A.len)).sum ≤ -2)
      ∨ SourcePressureLocalIslandWitnessListHasSortedBeforeFailure
          [W1, W2, W3]) := by
  rcases sourcePressureLocalIslandWitnessList_failure_threeDiagnosis
      h1pos h2pos h3pos h with hhead | htail
  · rcases hhead with hrecovered | hobs
    · exact Or.inl (Or.inl hrecovered)
    · exact Or.inl (Or.inr
        (SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction.hasSortedBeforeFailure
          hobs))
  · rcases htail with hrecovered | hobs
    · exact Or.inr (Or.inl hrecovered)
    · exact Or.inr (Or.inr
        (SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction.hasSortedBeforeFailure
          hobs))

/--
Head-pair split with the obstruction branch weakened to ordinary list
sorted-before failure.

This is useful for consumers that do not need to inspect the overlap
obstruction itself.
-/
theorem sourcePressureLocalIslandWitnessList_headPair_failure_recovered_or_listFailure
    {n : OddNat} {k r : ℕ}
    {W1 W2 : SourcePressureLocalIslandWitness n k r}
    {rest : List (SourcePressureLocalIslandWitness n k r)}
    (h1pos :
      0 < (sourcePressureIntervalPulseAddress_of_localIslandWitness W1).len)
    (h2pos :
      0 < (sourcePressureIntervalPulseAddress_of_localIslandWitness W2).len)
    (hfail : SourcePressureLocalIslandWitnessListHasSortedBeforeFailure [W1, W2]) :
    (∃ hrev : SourcePressureLocalIslandWitnessBefore W2 W1,
      (((sourcePressureAccountedIntervalFamily_of_reversedLocalIslandWitnessPair
        W1 W2 hrev).items).map
        (fun A => SourcePressureIntervalNetDrop n k r A.start A.len)).sum ≤ -2)
    ∨ SourcePressureLocalIslandWitnessListHasSortedBeforeFailure
        (W1 :: W2 :: rest) := by
  rcases
      sourcePressureLocalIslandWitnessList_headPair_failure_recovered_or_adjacentOverlapObstruction
        h1pos h2pos hfail with hrecovered | hobs
  · exact Or.inl hrecovered
  · exact Or.inr
      (SourcePressureLocalIslandWitnessListHasAdjacentOverlapObstruction.hasSortedBeforeFailure
        hobs)

/--
Raw-argument version of the sorted pair budget.
-/
theorem sourcePressureLocalIsland_pair_sum_le_neg_two
    (n : OddNat) (k r j1 j2 : ℕ)
    (h1 : SourcePressureLocalIsland n k r j1)
    (h2 : SourcePressureLocalIsland n k r j2)
    (hbefore :
      SourcePressureLocalIslandWitnessBefore
        (⟨j1, h1⟩ : SourcePressureLocalIslandWitness n k r)
        (⟨j2, h2⟩ : SourcePressureLocalIslandWitness n k r)) :
    (((sourcePressureAccountedIntervalFamily_of_sortedLocalIslandWitnessPair
      (⟨j1, h1⟩ : SourcePressureLocalIslandWitness n k r)
      (⟨j2, h2⟩ : SourcePressureLocalIslandWitness n k r)
      hbefore).items).map
      (fun A => SourcePressureIntervalNetDrop n k r A.start A.len)).sum ≤ -2 :=
  sourcePressureAccountedIntervalFamily_of_sortedLocalIslandWitnessPair_sum_le_neg_two
    (⟨j1, h1⟩ : SourcePressureLocalIslandWitness n k r)
    (⟨j2, h2⟩ : SourcePressureLocalIslandWitness n k r)
    hbefore

/--
Raw-argument strict negative version of the sorted pair budget.
-/
theorem sourcePressureLocalIsland_pair_sum_neg
    (n : OddNat) (k r j1 j2 : ℕ)
    (h1 : SourcePressureLocalIsland n k r j1)
    (h2 : SourcePressureLocalIsland n k r j2)
    (hbefore :
      SourcePressureLocalIslandWitnessBefore
        (⟨j1, h1⟩ : SourcePressureLocalIslandWitness n k r)
        (⟨j2, h2⟩ : SourcePressureLocalIslandWitness n k r)) :
    (((sourcePressureAccountedIntervalFamily_of_sortedLocalIslandWitnessPair
      (⟨j1, h1⟩ : SourcePressureLocalIslandWitness n k r)
      (⟨j2, h2⟩ : SourcePressureLocalIslandWitness n k r)
      hbefore).items).map
      (fun A => SourcePressureIntervalNetDrop n k r A.start A.len)).sum < 0 :=
  sourcePressureAccountedIntervalFamily_of_sortedLocalIslandWitnessPair_sum_neg
    (⟨j1, h1⟩ : SourcePressureLocalIslandWitness n k r)
    (⟨j2, h2⟩ : SourcePressureLocalIslandWitness n k r)
    hbefore

/-- Singleton sorted-family budget wrapper. -/
theorem sourcePressureAccountedIntervalFamily_sorted_singleton_sum_le_neg_one
    {n : OddNat} {k r : ℕ}
    (A : SourcePressureAccountedInterval n k r) :
    ((sourcePressureAccountedIntervalFamily_sorted_singleton A).items.map (fun A =>
      SourcePressureIntervalNetDrop n k r A.start A.len)).sum ≤ -1 := by
  simpa [sourcePressureAccountedIntervalFamily_sorted_singleton] using
    sourcePressureAccountedIntervalFamily_singleton_sum_le_neg_one A

/-- Sorted-cons family budget wrapper. -/
theorem sourcePressureAccountedIntervalFamily_sorted_cons_sum_le_neg_length
    {n : OddNat} {k r : ℕ}
    (A B : SourcePressureAccountedInterval n k r)
    (rest : List (SourcePressureAccountedInterval n k r))
    (hAB : SourcePressureAccountedIntervalBefore A B)
    (htail : SourcePressureAccountedIntervalListSortedBefore (B :: rest)) :
    (((sourcePressureAccountedIntervalFamily_sorted_cons A B rest hAB htail).items).map (fun A =>
      SourcePressureIntervalNetDrop n k r A.start A.len)).sum ≤
        -(((A :: B :: rest).length : ℕ) : ℤ) := by
  simpa [sourcePressureAccountedIntervalFamily_sorted_cons] using
    sourcePressureAccountedIntervalFamily_of_sortedBefore_sum_le_neg_length
      (A :: B :: rest)
      (sourcePressureAccountedIntervalListSortedBefore_cons hAB htail)


end DkMath.Collatz
