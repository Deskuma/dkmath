/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Collatz.PetalBridge.PressureFrontier

#print "file: DkMath.Collatz.PetalBridge.PressureAccounting"

namespace DkMath.Collatz

/-
Checkpoint 146: local interval accounting for source pressure.

This file is deliberately narrower than a global Collatz argument.  It only
turns the address and pulse API into endpoint facts and finite balance-sheet
identities.  It does not assert maximality, uniqueness, coverage, prefix
behavior, or Collatz convergence.
-/

/--
Accumulated source-pressure net drop over a finite interval.

The interval is explicit: it starts at the relative pressure-depth index
`start` and has length `len`.  This is only a finite accounting abbreviation;
it does not assert that the interval is maximal, disjoint from another
interval, covering, or prefix-shaped.
-/
noncomputable def SourcePressureIntervalNetDrop
    (n : OddNat) (k r start len : ℕ) : ℤ :=
  (Finset.range len).sum (fun i =>
    SourcePressureNetDropInt n k r (start + i))

/-- The start depth of an interval-pulse address has positive margin. -/
theorem sourcePressureIntervalPulseAddress_start_margin_pos
    {n : OddNat} {k r : ℕ}
    (A : SourcePressureIntervalPulseAddress n k r) :
    0 < SourcePressureMarginInt n k (r + A.start) := by
  have h := (sourcePressureIntervalPulseAddress_left_signChange A).2
  have hstart := sourcePressureIntervalPulseAddress_start_pos A
  have hidx : r + (A.start - 1) + 1 = r + A.start := by
    omega
  simpa [hidx] using h

/-- The end depth of an interval-pulse address has positive margin. -/
theorem sourcePressureIntervalPulseAddress_end_margin_pos
    {n : OddNat} {k r : ℕ}
    (A : SourcePressureIntervalPulseAddress n k r) :
    0 < SourcePressureMarginInt n k (r + (A.start + A.len - 1)) :=
  (sourcePressureIntervalPulseAddress_right_signChange A).1

/-- The depth before the start of an interval-pulse address has nonpositive margin. -/
theorem sourcePressureIntervalPulseAddress_before_start_nonpos
    {n : OddNat} {k r : ℕ}
    (A : SourcePressureIntervalPulseAddress n k r) :
    SourcePressureMarginInt n k (r + (A.start - 1)) ≤ 0 :=
  (sourcePressureIntervalPulseAddress_left_signChange A).1

/-- The depth after the end of an interval-pulse address has nonpositive margin. -/
theorem sourcePressureIntervalPulseAddress_after_end_nonpos
    {n : OddNat} {k r : ℕ}
    (A : SourcePressureIntervalPulseAddress n k r) :
    SourcePressureMarginInt n k (r + (A.start + A.len)) ≤ 0 := by
  have h := (sourcePressureIntervalPulseAddress_right_signChange A).2
  have hlen := SourcePressureIntervalPulseAddress.len_pos A
  have hidx : r + (A.start + A.len - 1) + 1 = r + (A.start + A.len) := by
    omega
  simpa [hidx] using h

/--
The left crossing of an interval-pulse address has positive local net drop.

This is a pure integer consequence of `M ≤ 0` and `0 < M + Δ`.
-/
theorem sourcePressureIntervalPulseAddress_left_netDrop_pos
    {n : OddNat} {k r : ℕ}
    (A : SourcePressureIntervalPulseAddress n k r) :
    0 < SourcePressureNetDropInt n k r (A.start - 1) := by
  have h := sourcePressureIntervalPulseAddress_left_crossing A
  omega

/--
The right fall of an interval-pulse address has negative local net drop.

This is a pure integer consequence of `0 < M` and `M + Δ ≤ 0`.
-/
theorem sourcePressureIntervalPulseAddress_right_netDrop_neg
    {n : OddNat} {k r : ℕ}
    (A : SourcePressureIntervalPulseAddress n k r) :
    SourcePressureNetDropInt n k r (A.start + A.len - 1) < 0 := by
  have h := sourcePressureIntervalPulseAddress_right_falling A
  omega

/--
Finite source-pressure accounting over a length-`len` interval.

The accepted normal form keeps the absolute depth as `r + a + len`, matching
Lean's default normalization after `Finset.sum_range_succ`.  The summand uses
the relative edge address `a + i`.
-/
theorem sourcePressureMargin_add_len_eq_start_add_sum_netDrop
    (n : OddNat) (k r a len : ℕ) :
    SourcePressureMarginInt n k (r + a + len) =
      SourcePressureMarginInt n k (r + a) +
        (Finset.range len).sum (fun i =>
          SourcePressureNetDropInt n k r (a + i)) := by
  induction len with
  | zero =>
      simp
  | succ len ih =>
      rw [Finset.sum_range_succ, ← add_assoc]
      have hstep :
          SourcePressureMarginInt n k (r + (a + len) + 1) =
            SourcePressureMarginInt n k (r + (a + len)) +
              SourcePressureNetDropInt n k r (a + len) := by
        simpa [Nat.add_assoc] using
          sourcePressureMargin_next_eq_current_add_netDrop n k r (a + len)
      calc
        SourcePressureMarginInt n k (r + a + (len + 1))
            = SourcePressureMarginInt n k (r + (a + len) + 1) := by
              congr 1
              omega
        _ = SourcePressureMarginInt n k (r + (a + len)) +
              SourcePressureNetDropInt n k r (a + len) := hstep
        _ = (SourcePressureMarginInt n k (r + a) +
              (Finset.range len).sum (fun i =>
                SourcePressureNetDropInt n k r (a + i))) +
              SourcePressureNetDropInt n k r (a + len) := by
              have ih' :
                  SourcePressureMarginInt n k (r + (a + len)) =
                    SourcePressureMarginInt n k (r + a) +
                      (Finset.range len).sum (fun i =>
                        SourcePressureNetDropInt n k r (a + i)) := by
                simpa [Nat.add_assoc] using ih
              rw [ih']
        _ = SourcePressureMarginInt n k (r + a) +
              ((Finset.range len).sum (fun i =>
                SourcePressureNetDropInt n k r (a + i)) +
                SourcePressureNetDropInt n k r (a + len)) := by
              ring

/--
Address-level cumulative accounting identity.

This specializes the generic finite accounting theorem to the positive run
carried by an interval-pulse address.
-/
theorem sourcePressureIntervalPulseAddress_margin_after_eq_start_add_sum_netDrop
    {n : OddNat} {k r : ℕ}
    (A : SourcePressureIntervalPulseAddress n k r) :
    SourcePressureMarginInt n k (r + (A.start + A.len)) =
      SourcePressureMarginInt n k (r + A.start) +
        (Finset.range A.len).sum (fun i =>
          SourcePressureNetDropInt n k r (A.start + i)) := by
  simpa [Nat.add_assoc] using
    sourcePressureMargin_add_len_eq_start_add_sum_netDrop n k r A.start A.len

/--
The accumulated net drop across an interval-pulse address is negative.

The run starts at positive pressure and the depth immediately after the run is
nonpositive, so the interval sum of local net drops must be strictly negative.
-/
theorem sourcePressureIntervalPulseAddress_sum_netDrop_neg
    {n : OddNat} {k r : ℕ}
    (A : SourcePressureIntervalPulseAddress n k r) :
    (Finset.range A.len).sum (fun i =>
      SourcePressureNetDropInt n k r (A.start + i)) < 0 := by
  have hacc :=
    sourcePressureIntervalPulseAddress_margin_after_eq_start_add_sum_netDrop A
  have hstart := sourcePressureIntervalPulseAddress_start_margin_pos A
  have hafter := sourcePressureIntervalPulseAddress_after_end_nonpos A
  omega

/--
The accumulated net drop is exactly the after-margin minus the start-margin.

This is often the most convenient algebraic form of interval accounting:
the finite sum is no longer just known to be negative; it is identified with
the endpoint margin difference.
-/
theorem sourcePressureIntervalPulseAddress_sum_netDrop_eq_after_sub_start
    {n : OddNat} {k r : ℕ}
    (A : SourcePressureIntervalPulseAddress n k r) :
    (Finset.range A.len).sum (fun i =>
      SourcePressureNetDropInt n k r (A.start + i)) =
      SourcePressureMarginInt n k (r + (A.start + A.len)) -
        SourcePressureMarginInt n k (r + A.start) := by
  have hacc :=
    sourcePressureIntervalPulseAddress_margin_after_eq_start_add_sum_netDrop A
  omega

/--
The accumulated net drop is bounded above by the negative start margin.

The after-margin is nonpositive, so the endpoint-difference form immediately
shows that the interval drive must cancel at least the initial positive
pressure margin.
-/
theorem sourcePressureIntervalPulseAddress_sum_netDrop_le_neg_start_margin
    {n : OddNat} {k r : ℕ}
    (A : SourcePressureIntervalPulseAddress n k r) :
    (Finset.range A.len).sum (fun i =>
      SourcePressureNetDropInt n k r (A.start + i)) ≤
      -SourcePressureMarginInt n k (r + A.start) := by
  have hacc :=
    sourcePressureIntervalPulseAddress_margin_after_eq_start_add_sum_netDrop A
  have hafter := sourcePressureIntervalPulseAddress_after_end_nonpos A
  omega

/--
The endpoint accounting inequality in unsolved-for form.

This form is useful when a later proof wants to keep the starting margin and
the accumulated drive on the same side instead of rewriting the sum alone.
-/
theorem sourcePressureIntervalPulseAddress_start_margin_add_sum_netDrop_nonpos
    {n : OddNat} {k r : ℕ}
    (A : SourcePressureIntervalPulseAddress n k r) :
    SourcePressureMarginInt n k (r + A.start) +
      (Finset.range A.len).sum (fun i =>
        SourcePressureNetDropInt n k r (A.start + i)) ≤ 0 := by
  have hacc :=
    sourcePressureIntervalPulseAddress_margin_after_eq_start_add_sum_netDrop A
  have hafter := sourcePressureIntervalPulseAddress_after_end_nonpos A
  omega

/--
Integer-strength form of negative accumulated net drop.

Since the accumulated drive is an integer, strict negativity is equivalent to
being at most `-1`.  This is a convenient bridge for later finite budget
arguments that prefer non-strict inequalities.
-/
theorem sourcePressureIntervalPulseAddress_sum_netDrop_le_neg_one
    {n : OddNat} {k r : ℕ}
    (A : SourcePressureIntervalPulseAddress n k r) :
    (Finset.range A.len).sum (fun i =>
      SourcePressureNetDropInt n k r (A.start + i)) ≤ -1 := by
  have hneg := sourcePressureIntervalPulseAddress_sum_netDrop_neg A
  omega

/--
Endpoint profile bundled for callers that only need signs.

This theorem is intentionally just packaging of local facts.  It does not say
that the pulse is maximal, unique, covering, prefix-shaped, or convergent.
-/
theorem sourcePressureIntervalPulseAddress_endpoint_profile
    {n : OddNat} {k r : ℕ}
    (A : SourcePressureIntervalPulseAddress n k r) :
    SourcePressureMarginInt n k (r + (A.start - 1)) ≤ 0 ∧
      0 < SourcePressureMarginInt n k (r + A.start) ∧
      0 < SourcePressureMarginInt n k (r + (A.start + A.len - 1)) ∧
      SourcePressureMarginInt n k (r + (A.start + A.len)) ≤ 0 :=
  ⟨sourcePressureIntervalPulseAddress_before_start_nonpos A,
    sourcePressureIntervalPulseAddress_start_margin_pos A,
    sourcePressureIntervalPulseAddress_end_margin_pos A,
    sourcePressureIntervalPulseAddress_after_end_nonpos A⟩

/--
Accounting profile bundled for callers that need both boundary signs and the
finite negative drive.

This is the compact observation form of checkpoint 146 plus the follow-up
accounting consequences.
-/
theorem sourcePressureIntervalPulseAddress_accounting_profile
    {n : OddNat} {k r : ℕ}
    (A : SourcePressureIntervalPulseAddress n k r) :
    SourcePressureMarginInt n k (r + (A.start - 1)) ≤ 0 ∧
      0 < SourcePressureMarginInt n k (r + A.start) ∧
      SourcePressureMarginInt n k (r + (A.start + A.len)) ≤ 0 ∧
      (Finset.range A.len).sum (fun i =>
        SourcePressureNetDropInt n k r (A.start + i)) < 0 ∧
      (Finset.range A.len).sum (fun i =>
        SourcePressureNetDropInt n k r (A.start + i)) ≤
        -SourcePressureMarginInt n k (r + A.start) :=
  ⟨sourcePressureIntervalPulseAddress_before_start_nonpos A,
    sourcePressureIntervalPulseAddress_start_margin_pos A,
    sourcePressureIntervalPulseAddress_after_end_nonpos A,
    sourcePressureIntervalPulseAddress_sum_netDrop_neg A,
    sourcePressureIntervalPulseAddress_sum_netDrop_le_neg_start_margin A⟩

/-- Interval-net-drop wrapper for the endpoint-difference accounting identity. -/
theorem sourcePressureIntervalPulseAddress_intervalNetDrop_eq_after_sub_start
    {n : OddNat} {k r : ℕ}
    (A : SourcePressureIntervalPulseAddress n k r) :
    SourcePressureIntervalNetDrop n k r A.start A.len =
      SourcePressureMarginInt n k (r + (A.start + A.len)) -
        SourcePressureMarginInt n k (r + A.start) := by
  simpa [SourcePressureIntervalNetDrop] using
    sourcePressureIntervalPulseAddress_sum_netDrop_eq_after_sub_start A

/-- Interval-net-drop wrapper for the start-margin budget bound. -/
theorem sourcePressureIntervalPulseAddress_intervalNetDrop_le_neg_start_margin
    {n : OddNat} {k r : ℕ}
    (A : SourcePressureIntervalPulseAddress n k r) :
    SourcePressureIntervalNetDrop n k r A.start A.len ≤
      -SourcePressureMarginInt n k (r + A.start) := by
  simpa [SourcePressureIntervalNetDrop] using
    sourcePressureIntervalPulseAddress_sum_netDrop_le_neg_start_margin A

/-- Interval-net-drop wrapper for the integer-strength budget bound. -/
theorem sourcePressureIntervalPulseAddress_intervalNetDrop_le_neg_one
    {n : OddNat} {k r : ℕ}
    (A : SourcePressureIntervalPulseAddress n k r) :
    SourcePressureIntervalNetDrop n k r A.start A.len ≤ -1 := by
  simpa [SourcePressureIntervalNetDrop] using
    sourcePressureIntervalPulseAddress_sum_netDrop_le_neg_one A

/-- Interval-net-drop wrapper for strict negativity. -/
theorem sourcePressureIntervalPulseAddress_intervalNetDrop_neg
    {n : OddNat} {k r : ℕ}
    (A : SourcePressureIntervalPulseAddress n k r) :
    SourcePressureIntervalNetDrop n k r A.start A.len < 0 := by
  simpa [SourcePressureIntervalNetDrop] using
    sourcePressureIntervalPulseAddress_sum_netDrop_neg A

/--
Thin carrier for an explicitly accounted pressure interval.

This structure records exactly the facts needed for local interval accounting:
positive start margin, nonpositive after-margin, and the finite balance-sheet
identity.  It is not a maximal-run, cover, disjoint-family, prefix, or
convergence object.
-/
structure SourcePressureAccountedInterval
    (n : OddNat) (k r : ℕ) where
  /-- Relative start pressure-depth index. -/
  start : ℕ
  /-- Interval length. -/
  len : ℕ
  /-- The interval length is positive. -/
  hlen : 0 < len
  /-- The interval begins at positive source-pressure margin. -/
  startMarginPos :
    0 < SourcePressureMarginInt n k (r + start)
  /-- Immediately after the interval, the source-pressure margin is nonpositive. -/
  afterMarginNonpos :
    SourcePressureMarginInt n k (r + (start + len)) ≤ 0
  /-- The interval satisfies the finite source-pressure accounting identity. -/
  accounting :
    SourcePressureMarginInt n k (r + (start + len)) =
      SourcePressureMarginInt n k (r + start) +
        SourcePressureIntervalNetDrop n k r start len

/-- The interval net drop of an accounted interval is negative. -/
theorem sourcePressureAccountedInterval_intervalNetDrop_neg
    {n : OddNat} {k r : ℕ}
    (A : SourcePressureAccountedInterval n k r) :
    SourcePressureIntervalNetDrop n k r A.start A.len < 0 := by
  have hacc := A.accounting
  have hstart := A.startMarginPos
  have hafter := A.afterMarginNonpos
  omega

/-- The interval net drop of an accounted interval is at most `-1`. -/
theorem sourcePressureAccountedInterval_intervalNetDrop_le_neg_one
    {n : OddNat} {k r : ℕ}
    (A : SourcePressureAccountedInterval n k r) :
    SourcePressureIntervalNetDrop n k r A.start A.len ≤ -1 := by
  have hneg := sourcePressureAccountedInterval_intervalNetDrop_neg A
  omega

/-- The interval net drop cancels at least the positive start margin. -/
theorem sourcePressureAccountedInterval_intervalNetDrop_le_neg_start_margin
    {n : OddNat} {k r : ℕ}
    (A : SourcePressureAccountedInterval n k r) :
    SourcePressureIntervalNetDrop n k r A.start A.len ≤
      -SourcePressureMarginInt n k (r + A.start) := by
  have hacc := A.accounting
  have hafter := A.afterMarginNonpos
  omega

/-- Every interval-pulse address induces a thin accounted interval carrier. -/
def sourcePressureAccountedInterval_of_intervalPulseAddress
    {n : OddNat} {k r : ℕ}
    (A : SourcePressureIntervalPulseAddress n k r) :
    SourcePressureAccountedInterval n k r :=
  { start := A.start
    len := A.len
    hlen := SourcePressureIntervalPulseAddress.len_pos A
    startMarginPos := sourcePressureIntervalPulseAddress_start_margin_pos A
    afterMarginNonpos := sourcePressureIntervalPulseAddress_after_end_nonpos A
    accounting := by
      simpa [SourcePressureIntervalNetDrop] using
        sourcePressureIntervalPulseAddress_margin_after_eq_start_add_sum_netDrop A }

/--
Map an explicit list of interval-pulse addresses to accounted intervals.

This is only a carrier conversion.  It preserves the supplied list order and
does not assert that the addresses are maximal, unique, disjoint, covering, or
prefix-shaped.
-/
def sourcePressureAccountedIntervalList_of_intervalPulseAddressList
    {n : OddNat} {k r : ℕ}
    (L : List (SourcePressureIntervalPulseAddress n k r)) :
    List (SourcePressureAccountedInterval n k r) :=
  L.map sourcePressureAccountedInterval_of_intervalPulseAddress

@[simp]
theorem sourcePressureAccountedIntervalList_of_intervalPulseAddressList_length
    {n : OddNat} {k r : ℕ}
    (L : List (SourcePressureIntervalPulseAddress n k r)) :
    (sourcePressureAccountedIntervalList_of_intervalPulseAddressList L).length =
      L.length := by
  simp [sourcePressureAccountedIntervalList_of_intervalPulseAddressList]

/--
Finite-list pressure budget over explicitly provided accounted intervals.

No disjointness, coverage, union accounting, or maximality is used here.  The
statement only says that a list of `m` already-accounted intervals contributes
at most `-m` to the summed interval net drop.
-/
theorem sourcePressureAccountedInterval_list_sum_le_neg_length
    {n : OddNat} {k r : ℕ}
    (L : List (SourcePressureAccountedInterval n k r)) :
    (L.map (fun A =>
      SourcePressureIntervalNetDrop n k r A.start A.len)).sum ≤
        -((L.length : ℕ) : ℤ) := by
  induction L with
  | nil =>
      simp
  | cons A L ih =>
      have hA := sourcePressureAccountedInterval_intervalNetDrop_le_neg_one A
      simp at ih ⊢
      omega

/--
Finite-list pressure budget over explicitly supplied interval-pulse addresses.

This theorem is deliberately just a list-cost statement.  It does not require
the supplied addresses to be sorted or disjoint, and it does not state union
accounting for their covered depths.
-/
theorem sourcePressureIntervalPulseAddressList_sum_le_neg_length
    {n : OddNat} {k r : ℕ}
    (L : List (SourcePressureIntervalPulseAddress n k r)) :
    ((sourcePressureAccountedIntervalList_of_intervalPulseAddressList L).map
      (fun A => SourcePressureIntervalNetDrop n k r A.start A.len)).sum ≤
        -((L.length : ℕ) : ℤ) := by
  simpa [sourcePressureAccountedIntervalList_of_intervalPulseAddressList] using
    sourcePressureAccountedInterval_list_sum_le_neg_length
      (sourcePressureAccountedIntervalList_of_intervalPulseAddressList L)

/--
Any nonempty explicit interval-pulse-address list has negative total listed
net drop after conversion to accounted intervals.

This is only a cost statement for the supplied witnesses; it is not union
accounting over their geometric support.
-/
theorem sourcePressureIntervalPulseAddressList_sum_neg_of_nonempty
    {n : OddNat} {k r : ℕ}
    {L : List (SourcePressureIntervalPulseAddress n k r)}
    (hL : L ≠ []) :
    ((sourcePressureAccountedIntervalList_of_intervalPulseAddressList L).map
      (fun A => SourcePressureIntervalNetDrop n k r A.start A.len)).sum < 0 := by
  have hbudget := sourcePressureIntervalPulseAddressList_sum_le_neg_length L
  have hlen : 0 < L.length := by
    cases L with
    | nil => contradiction
    | cons _ _ => simp
  omega

/--
Any nonempty explicit list of accounted intervals has negative total net drop.

This is again a list budget theorem only; it does not say the intervals are
disjoint or cover any source-pressure region.
-/
theorem sourcePressureAccountedInterval_list_sum_neg_of_nonempty
    {n : OddNat} {k r : ℕ}
    {L : List (SourcePressureAccountedInterval n k r)}
    (hL : L ≠ []) :
    (L.map (fun A =>
      SourcePressureIntervalNetDrop n k r A.start A.len)).sum < 0 := by
  have hbudget := sourcePressureAccountedInterval_list_sum_le_neg_length L
  have hlen : 0 < L.length := by
    cases L with
    | nil => contradiction
    | cons _ _ => simp
  omega

/--
Disjointness vocabulary for two natural-number half-open intervals.

This is only vocabulary.  It is not used here to derive coverage, union
accounting, or decomposition.
-/
def NatIntervalsDisjoint (a len b len' : ℕ) : Prop :=
  a + len ≤ b ∨ b + len' ≤ a

/-- Natural interval disjointness is symmetric. -/
theorem NatIntervalsDisjoint.symm
    {a len b len' : ℕ}
    (h : NatIntervalsDisjoint a len b len') :
    NatIntervalsDisjoint b len' a len := by
  rcases h with h | h
  · exact Or.inr h
  · exact Or.inl h

/--
Disjointness vocabulary for two accounted intervals.

This is intentionally a separate assumption-level predicate.  The existence
of two accounted intervals does not imply disjointness.
-/
def SourcePressureAccountedIntervalsDisjoint
    {n : OddNat} {k r : ℕ}
    (A B : SourcePressureAccountedInterval n k r) : Prop :=
  NatIntervalsDisjoint A.start A.len B.start B.len

/-- Accounted-interval disjointness is symmetric. -/
theorem SourcePressureAccountedIntervalsDisjoint.symm
    {n : OddNat} {k r : ℕ}
    {A B : SourcePressureAccountedInterval n k r}
    (h : SourcePressureAccountedIntervalsDisjoint A B) :
    SourcePressureAccountedIntervalsDisjoint B A :=
  NatIntervalsDisjoint.symm h

/--
Pairwise-disjointness predicate for an explicit list of accounted intervals.

This is only list structure.  It does not assert that the list covers a region,
is maximal, is sorted, or gives a union accounting theorem.
-/
def SourcePressureAccountedIntervalListPairwiseDisjoint
    {n : OddNat} {k r : ℕ}
    (L : List (SourcePressureAccountedInterval n k r)) : Prop :=
  L.Pairwise SourcePressureAccountedIntervalsDisjoint

/-- The empty accounted-interval list is pairwise disjoint. -/
theorem sourcePressureAccountedIntervalListPairwiseDisjoint_nil
    {n : OddNat} {k r : ℕ} :
    SourcePressureAccountedIntervalListPairwiseDisjoint
      ([] : List (SourcePressureAccountedInterval n k r)) :=
  List.Pairwise.nil

/-- A singleton accounted-interval list is pairwise disjoint. -/
theorem sourcePressureAccountedIntervalListPairwiseDisjoint_singleton
    {n : OddNat} {k r : ℕ}
    (A : SourcePressureAccountedInterval n k r) :
    SourcePressureAccountedIntervalListPairwiseDisjoint [A] := by
  simp [SourcePressureAccountedIntervalListPairwiseDisjoint]

/--
Cons constructor for pairwise-disjoint accounted-interval lists.

The head interval must be explicitly disjoint from every tail interval.  No
disjointness is inferred from accounting data alone.
-/
theorem sourcePressureAccountedIntervalListPairwiseDisjoint_cons
    {n : OddNat} {k r : ℕ}
    {A : SourcePressureAccountedInterval n k r}
    {L : List (SourcePressureAccountedInterval n k r)}
    (hhead : ∀ B ∈ L, SourcePressureAccountedIntervalsDisjoint A B)
    (htail : SourcePressureAccountedIntervalListPairwiseDisjoint L) :
    SourcePressureAccountedIntervalListPairwiseDisjoint (A :: L) :=
  List.Pairwise.cons hhead htail

/-- Accounted-interval disjointness can be read in either order. -/
theorem sourcePressureAccountedIntervalsDisjoint_comm
    {n : OddNat} {k r : ℕ}
    {A B : SourcePressureAccountedInterval n k r} :
    SourcePressureAccountedIntervalsDisjoint A B ↔
      SourcePressureAccountedIntervalsDisjoint B A :=
  ⟨SourcePressureAccountedIntervalsDisjoint.symm,
    SourcePressureAccountedIntervalsDisjoint.symm⟩

/--
Pairwise-disjoint accounted intervals remain pairwise disjoint after reversing
the explicit list.

This uses symmetry of the disjointness relation only; it still does not say
anything about coverage or union accounting.
-/
theorem sourcePressureAccountedIntervalListPairwiseDisjoint_reverse
    {n : OddNat} {k r : ℕ}
    {L : List (SourcePressureAccountedInterval n k r)}
    (h : SourcePressureAccountedIntervalListPairwiseDisjoint L) :
    SourcePressureAccountedIntervalListPairwiseDisjoint L.reverse := by
  unfold SourcePressureAccountedIntervalListPairwiseDisjoint at h ⊢
  exact h.reverse.imp (fun hBA =>
    SourcePressureAccountedIntervalsDisjoint.symm hBA)

/--
Thin carrier for an explicit family of accounted intervals.

The pairwise-disjoint field is stored for later decomposition work.  The
current budget theorem below does not use it, because the budget is only over
the explicitly listed interval costs.
-/
structure SourcePressureAccountedIntervalFamily
    (n : OddNat) (k r : ℕ) where
  /-- Explicit accounted intervals. -/
  items : List (SourcePressureAccountedInterval n k r)
  /-- Explicit pairwise-disjointness hypothesis for future union/decomposition work. -/
  pairwiseDisjoint :
    SourcePressureAccountedIntervalListPairwiseDisjoint items

/--
Empty accounted-interval family.

This is only the empty explicit family.  It does not assert that there are no
accounted intervals in the ambient pressure window.
-/
def sourcePressureAccountedIntervalFamily_nil
    (n : OddNat) (k r : ℕ) :
    SourcePressureAccountedIntervalFamily n k r :=
  { items := []
    pairwiseDisjoint :=
      sourcePressureAccountedIntervalListPairwiseDisjoint_nil }

/--
Singleton accounted-interval family.

This packages one already-accounted interval as a family.  It is a local
carrier constructor, not a maximality or coverage statement.
-/
def sourcePressureAccountedIntervalFamily_singleton
    {n : OddNat} {k r : ℕ}
    (A : SourcePressureAccountedInterval n k r) :
    SourcePressureAccountedIntervalFamily n k r :=
  { items := [A]
    pairwiseDisjoint :=
      sourcePressureAccountedIntervalListPairwiseDisjoint_singleton A }

/--
Cons constructor for accounted-interval families.

The new head must be explicitly disjoint from every existing family item.
Nothing in this constructor infers disjointness from pressure accounting alone,
and it still does not introduce coverage, prefix behavior, or union accounting.
-/
def sourcePressureAccountedIntervalFamily_cons
    {n : OddNat} {k r : ℕ}
    (A : SourcePressureAccountedInterval n k r)
    (F : SourcePressureAccountedIntervalFamily n k r)
    (hhead : ∀ B ∈ F.items,
      SourcePressureAccountedIntervalsDisjoint A B) :
    SourcePressureAccountedIntervalFamily n k r :=
  { items := A :: F.items
    pairwiseDisjoint :=
      sourcePressureAccountedIntervalListPairwiseDisjoint_cons
        hhead F.pairwiseDisjoint }

/--
Family budget inherited from the list budget.

The proof does not use `pairwiseDisjoint`: disjointness is stored for later
union/decomposition work, while this theorem only sums the explicit interval
costs already present in the family.
-/
theorem sourcePressureAccountedIntervalFamily_sum_le_neg_length
    {n : OddNat} {k r : ℕ}
    (F : SourcePressureAccountedIntervalFamily n k r) :
    (F.items.map (fun A =>
      SourcePressureIntervalNetDrop n k r A.start A.len)).sum ≤
        -((F.items.length : ℕ) : ℤ) :=
  sourcePressureAccountedInterval_list_sum_le_neg_length F.items

/-- A nonempty accounted-interval family has negative total explicit net drop. -/
theorem sourcePressureAccountedIntervalFamily_sum_neg_of_nonempty
    {n : OddNat} {k r : ℕ}
    (F : SourcePressureAccountedIntervalFamily n k r)
    (hF : F.items ≠ []) :
    (F.items.map (fun A =>
      SourcePressureIntervalNetDrop n k r A.start A.len)).sum < 0 :=
  sourcePressureAccountedInterval_list_sum_neg_of_nonempty hF

/-- The singleton-family budget is the one-interval `≤ -1` budget. -/
theorem sourcePressureAccountedIntervalFamily_singleton_sum_le_neg_one
    {n : OddNat} {k r : ℕ}
    (A : SourcePressureAccountedInterval n k r) :
    ((sourcePressureAccountedIntervalFamily_singleton A).items.map (fun A =>
      SourcePressureIntervalNetDrop n k r A.start A.len)).sum ≤ -1 := by
  simpa [sourcePressureAccountedIntervalFamily_singleton] using
    sourcePressureAccountedInterval_intervalNetDrop_le_neg_one A

/--
The cons-family budget is the general family budget specialized to the cons
constructor.
-/
theorem sourcePressureAccountedIntervalFamily_cons_sum_le_neg_length
    {n : OddNat} {k r : ℕ}
    (A : SourcePressureAccountedInterval n k r)
    (F : SourcePressureAccountedIntervalFamily n k r)
    (hhead : ∀ B ∈ F.items,
      SourcePressureAccountedIntervalsDisjoint A B) :
    (((sourcePressureAccountedIntervalFamily_cons A F hhead).items).map (fun A =>
      SourcePressureIntervalNetDrop n k r A.start A.len)).sum ≤
        -((((sourcePressureAccountedIntervalFamily_cons A F hhead).items.length : ℕ) : ℤ)) :=
  sourcePressureAccountedIntervalFamily_sum_le_neg_length
    (sourcePressureAccountedIntervalFamily_cons A F hhead)

/--
Ordered non-overlap for two natural-number half-open intervals.

This is a direction-sensitive helper for future sorted-family work.
-/
def NatIntervalBefore (a len b _len' : ℕ) : Prop :=
  a + len ≤ b

/--
Overlap vocabulary for two natural-number half-open intervals.

This is the positive counterpart to ordered non-overlap.  The theorem API below
is deliberately conservative: one failed `before` relation is not overlap
evidence, because the intervals may simply be in reverse order.  Overlap is
proved only after both ordered directions are ruled out.
-/
def NatIntervalsOverlap (a lenA b lenB : ℕ) : Prop :=
  a < b + lenB ∧ b < a + lenA

/-- Natural interval overlap is symmetric. -/
theorem NatIntervalsOverlap.symm
    {a lenA b lenB : ℕ}
    (h : NatIntervalsOverlap a lenA b lenB) :
    NatIntervalsOverlap b lenB a lenA :=
  ⟨h.2, h.1⟩

/-- Ordered non-overlap implies ordinary interval disjointness. -/
theorem NatIntervalsDisjoint.of_before
    {a len b len' : ℕ}
    (h : NatIntervalBefore a len b len') :
    NatIntervalsDisjoint a len b len' :=
  Or.inl h

/-- Ordered non-overlap in one direction excludes overlap. -/
theorem NatIntervalsOverlap.not_of_before
    {a lenA b lenB : ℕ}
    (hbefore : NatIntervalBefore a lenA b lenB) :
    ¬ NatIntervalsOverlap a lenA b lenB := by
  change ¬ (a < b + lenB ∧ b < a + lenA)
  change a + lenA ≤ b at hbefore
  intro hoverlap
  omega

/-- Ordered non-overlap in the reverse direction also excludes overlap. -/
theorem NatIntervalsOverlap.not_of_reverseBefore
    {a lenA b lenB : ℕ}
    (hbefore : NatIntervalBefore b lenB a lenA) :
    ¬ NatIntervalsOverlap a lenA b lenB := by
  change ¬ (a < b + lenB ∧ b < a + lenA)
  change b + lenB ≤ a at hbefore
  intro hoverlap
  omega

/--
If neither ordered direction is available, the two half-open intervals overlap.

The length-positivity hypotheses are kept at this API boundary for the pressure
address use case, even though the arithmetic core is already forced by the two
negated `before` inequalities.  Keeping them explicit prevents future callers
from reading a single failed order test as overlap evidence.
-/
theorem NatIntervalsOverlap.of_not_before_not_reverseBefore
    {a lenA b lenB : ℕ}
    (_hApos : 0 < lenA)
    (_hBpos : 0 < lenB)
    (hnotAB : ¬ NatIntervalBefore a lenA b lenB)
    (hnotBA : ¬ NatIntervalBefore b lenB a lenA) :
    NatIntervalsOverlap a lenA b lenB := by
  change ¬ a + lenA ≤ b at hnotAB
  change ¬ b + lenB ≤ a at hnotBA
  change a < b + lenB ∧ b < a + lenA
  omega

/--
Local trichotomy for two half-open natural intervals.

The conclusion is intentionally local: the two supplied intervals are either
ordered one way, ordered the other way, or overlap.  It does not say anything
about a family of intervals, coverage, maximality, or union accounting.
-/
theorem NatIntervalsOverlap.before_or_reverseBefore_or_overlap
    {a lenA b lenB : ℕ}
    (hApos : 0 < lenA)
    (hBpos : 0 < lenB) :
    NatIntervalBefore a lenA b lenB ∨
      NatIntervalBefore b lenB a lenA ∨
        NatIntervalsOverlap a lenA b lenB := by
  by_cases hAB : NatIntervalBefore a lenA b lenB
  · exact Or.inl hAB
  · by_cases hBA : NatIntervalBefore b lenB a lenA
    · exact Or.inr (Or.inl hBA)
    · exact Or.inr (Or.inr
        (NatIntervalsOverlap.of_not_before_not_reverseBefore
          hApos hBpos hAB hBA))

/--
Reason split for a failed ordered interval relation.

If `a` is not before `b`, the failure is either explained by the reverse order
or by genuine overlap.  This is the safe form of failure refinement: a single
failed `before` is still not overlap evidence by itself.
-/
theorem NatIntervalsOverlap.reverseBefore_or_overlap_of_not_before
    {a lenA b lenB : ℕ}
    (hApos : 0 < lenA)
    (hBpos : 0 < lenB)
    (hnotAB : ¬ NatIntervalBefore a lenA b lenB) :
    NatIntervalBefore b lenB a lenA ∨
      NatIntervalsOverlap a lenA b lenB := by
  by_cases hBA : NatIntervalBefore b lenB a lenA
  · exact Or.inl hBA
  · exact Or.inr
      (NatIntervalsOverlap.of_not_before_not_reverseBefore
        hApos hBpos hnotAB hBA)

/--
Transitive-like composition for ordered non-overlap.

The second interval's length is irrelevant for the conclusion because
`NatIntervalBefore a len b len'` only records `a + len ≤ b`.
-/
theorem NatIntervalBefore.trans_like
    {a len b len' c len'' : ℕ}
    (hAB : NatIntervalBefore a len b len')
    (hBC : NatIntervalBefore b len' c len'') :
    NatIntervalBefore a len c len'' := by
  unfold NatIntervalBefore at hAB hBC ⊢
  omega

/-- Ordered non-overlap for two accounted intervals. -/
def SourcePressureAccountedIntervalBefore
    {n : OddNat} {k r : ℕ}
    (A B : SourcePressureAccountedInterval n k r) : Prop :=
  NatIntervalBefore A.start A.len B.start B.len

/--
Ordered non-overlap for two interval-pulse addresses.

This is the direct pulse-address version of `SourcePressureAccountedIntervalBefore`.
Its negation is only a sorted-before failure.  It is not, by itself, overlap
evidence: the addresses may simply be in the reverse order.
-/
def SourcePressureIntervalPulseAddressBefore
    {n : OddNat} {k r : ℕ}
    (A B : SourcePressureIntervalPulseAddress n k r) : Prop :=
  A.start + A.len ≤ B.start

/--
Overlap predicate for two interval-pulse addresses.

This only compares the explicit half-open address intervals.  It does not
merge intervals, prove union accounting, or infer coverage of a pressure
region.
-/
def SourcePressureIntervalPulseAddressOverlap
    {n : OddNat} {k r : ℕ}
    (A B : SourcePressureIntervalPulseAddress n k r) : Prop :=
  NatIntervalsOverlap A.start A.len B.start B.len

/-- Address-level overlap is symmetric. -/
theorem SourcePressureIntervalPulseAddressOverlap.symm
    {n : OddNat} {k r : ℕ}
    {A B : SourcePressureIntervalPulseAddress n k r}
    (h : SourcePressureIntervalPulseAddressOverlap A B) :
    SourcePressureIntervalPulseAddressOverlap B A :=
  NatIntervalsOverlap.symm h

/-- A before relation between pulse addresses excludes address overlap. -/
theorem SourcePressureIntervalPulseAddressOverlap.not_of_before
    {n : OddNat} {k r : ℕ}
    {A B : SourcePressureIntervalPulseAddress n k r}
    (hbefore : SourcePressureIntervalPulseAddressBefore A B) :
    ¬ SourcePressureIntervalPulseAddressOverlap A B :=
  NatIntervalsOverlap.not_of_before hbefore

/-- A reverse before relation between pulse addresses also excludes overlap. -/
theorem SourcePressureIntervalPulseAddressOverlap.not_of_reverseBefore
    {n : OddNat} {k r : ℕ}
    {A B : SourcePressureIntervalPulseAddress n k r}
    (hbefore : SourcePressureIntervalPulseAddressBefore B A) :
    ¬ SourcePressureIntervalPulseAddressOverlap A B :=
  NatIntervalsOverlap.not_of_reverseBefore hbefore

/-- Address overlap excludes the forward before relation. -/
theorem SourcePressureIntervalPulseAddressOverlap.not_before
    {n : OddNat} {k r : ℕ}
    {A B : SourcePressureIntervalPulseAddress n k r}
    (h : SourcePressureIntervalPulseAddressOverlap A B) :
    ¬ SourcePressureIntervalPulseAddressBefore A B := by
  intro hbefore
  exact SourcePressureIntervalPulseAddressOverlap.not_of_before hbefore h

/-- Address overlap excludes the reverse before relation. -/
theorem SourcePressureIntervalPulseAddressOverlap.not_reverseBefore
    {n : OddNat} {k r : ℕ}
    {A B : SourcePressureIntervalPulseAddress n k r}
    (h : SourcePressureIntervalPulseAddressOverlap A B) :
    ¬ SourcePressureIntervalPulseAddressBefore B A := by
  intro hbefore
  exact SourcePressureIntervalPulseAddressOverlap.not_of_reverseBefore hbefore h

/--
If neither pulse address is before the other, then their explicit half-open
address intervals overlap.
-/
theorem SourcePressureIntervalPulseAddressOverlap.of_not_before_not_reverseBefore
    {n : OddNat} {k r : ℕ}
    {A B : SourcePressureIntervalPulseAddress n k r}
    (hApos : 0 < A.len)
    (hBpos : 0 < B.len)
    (hnotAB : ¬ SourcePressureIntervalPulseAddressBefore A B)
    (hnotBA : ¬ SourcePressureIntervalPulseAddressBefore B A) :
    SourcePressureIntervalPulseAddressOverlap A B :=
  NatIntervalsOverlap.of_not_before_not_reverseBefore hApos hBpos hnotAB hnotBA

/-- Local trichotomy for two interval-pulse addresses. -/
theorem SourcePressureIntervalPulseAddressOverlap.before_or_reverseBefore_or_overlap
    {n : OddNat} {k r : ℕ}
    {A B : SourcePressureIntervalPulseAddress n k r}
    (hApos : 0 < A.len)
    (hBpos : 0 < B.len) :
    SourcePressureIntervalPulseAddressBefore A B ∨
      SourcePressureIntervalPulseAddressBefore B A ∨
        SourcePressureIntervalPulseAddressOverlap A B :=
  NatIntervalsOverlap.before_or_reverseBefore_or_overlap hApos hBpos

/--
Failure-reason split for a failed address-level before relation.

The failed order is either reversed, or the two supplied address intervals
overlap.
-/
theorem SourcePressureIntervalPulseAddressOverlap.reverseBefore_or_overlap_of_not_before
    {n : OddNat} {k r : ℕ}
    {A B : SourcePressureIntervalPulseAddress n k r}
    (hApos : 0 < A.len)
    (hBpos : 0 < B.len)
    (hnotAB : ¬ SourcePressureIntervalPulseAddressBefore A B) :
    SourcePressureIntervalPulseAddressBefore B A ∨
      SourcePressureIntervalPulseAddressOverlap A B :=
  NatIntervalsOverlap.reverseBefore_or_overlap_of_not_before hApos hBpos hnotAB

theorem sourcePressureIntervalPulseAddressBefore_iff_accountedBefore
    {n : OddNat} {k r : ℕ}
    {A B : SourcePressureIntervalPulseAddress n k r} :
    SourcePressureIntervalPulseAddressBefore A B ↔
      SourcePressureAccountedIntervalBefore
        (sourcePressureAccountedInterval_of_intervalPulseAddress A)
        (sourcePressureAccountedInterval_of_intervalPulseAddress B) := by
  rfl

/-- Transitive-like composition for ordered accounted intervals. -/
theorem SourcePressureAccountedIntervalBefore.trans_like
    {n : OddNat} {k r : ℕ}
    {A B C : SourcePressureAccountedInterval n k r}
    (hAB : SourcePressureAccountedIntervalBefore A B)
    (hBC : SourcePressureAccountedIntervalBefore B C) :
    SourcePressureAccountedIntervalBefore A C :=
  NatIntervalBefore.trans_like hAB hBC

/-- Ordered accounted intervals are disjoint. -/
theorem SourcePressureAccountedIntervalsDisjoint.of_before
    {n : OddNat} {k r : ℕ}
    {A B : SourcePressureAccountedInterval n k r}
    (h : SourcePressureAccountedIntervalBefore A B) :
    SourcePressureAccountedIntervalsDisjoint A B :=
  NatIntervalsDisjoint.of_before h

/--
Two-element family constructor from ordered non-overlap.

This is a sorted-family seed: `[A, B]` is accepted because `A` lies before
`B`, hence the two intervals are disjoint.  It still says nothing about
covering all positive pressure depths or being a maximal family.
-/
def sourcePressureAccountedIntervalFamily_pair_of_before
    {n : OddNat} {k r : ℕ}
    (A B : SourcePressureAccountedInterval n k r)
    (hAB : SourcePressureAccountedIntervalBefore A B) :
    SourcePressureAccountedIntervalFamily n k r :=
  sourcePressureAccountedIntervalFamily_cons A
    (sourcePressureAccountedIntervalFamily_singleton B)
    (by
      intro C hC
      have hCB : C = B := by
        simpa [sourcePressureAccountedIntervalFamily_singleton] using hC
      subst C
      exact SourcePressureAccountedIntervalsDisjoint.of_before hAB)

/--
Adjacent sortedness for an explicit accounted-interval list.

This predicate only records local ordered non-overlap between neighboring
items.  It is not a coverage, maximality, prefix, or union-accounting claim.
-/
def SourcePressureAccountedIntervalListSortedBefore
    {n : OddNat} {k r : ℕ} :
    List (SourcePressureAccountedInterval n k r) → Prop
  | [] => True
  | [_] => True
  | A :: B :: rest =>
      SourcePressureAccountedIntervalBefore A B ∧
        SourcePressureAccountedIntervalListSortedBefore (B :: rest)

/-- The empty list is sorted by adjacent ordered non-overlap. -/
theorem sourcePressureAccountedIntervalListSortedBefore_nil
    {n : OddNat} {k r : ℕ} :
    SourcePressureAccountedIntervalListSortedBefore
      ([] : List (SourcePressureAccountedInterval n k r)) :=
  trivial

/-- A singleton list is sorted by adjacent ordered non-overlap. -/
theorem sourcePressureAccountedIntervalListSortedBefore_singleton
    {n : OddNat} {k r : ℕ}
    (A : SourcePressureAccountedInterval n k r) :
    SourcePressureAccountedIntervalListSortedBefore [A] :=
  trivial

/-- Cons constructor for adjacent sorted-before lists. -/
theorem sourcePressureAccountedIntervalListSortedBefore_cons
    {n : OddNat} {k r : ℕ}
    {A B : SourcePressureAccountedInterval n k r}
    {rest : List (SourcePressureAccountedInterval n k r)}
    (hAB : SourcePressureAccountedIntervalBefore A B)
    (htail : SourcePressureAccountedIntervalListSortedBefore (B :: rest)) :
    SourcePressureAccountedIntervalListSortedBefore (A :: B :: rest) :=
  ⟨hAB, htail⟩

/--
In an adjacent-sorted tail, a predecessor before the head is before every
element of the tail.

This is the local bridge from adjacent ordering to pairwise disjointness.
-/
theorem SourcePressureAccountedIntervalBefore.before_all_of_sorted_tail
    {n : OddNat} {k r : ℕ}
    {A B : SourcePressureAccountedInterval n k r}
    {rest : List (SourcePressureAccountedInterval n k r)}
    (hAB : SourcePressureAccountedIntervalBefore A B)
    (hsorted :
      SourcePressureAccountedIntervalListSortedBefore (B :: rest)) :
    ∀ C ∈ B :: rest, SourcePressureAccountedIntervalBefore A C := by
  induction rest generalizing A B with
  | nil =>
      intro C hC
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hC
      subst C
      exact hAB
  | cons C rest ih =>
      have hBC : SourcePressureAccountedIntervalBefore B C := hsorted.1
      have htail :
          SourcePressureAccountedIntervalListSortedBefore (C :: rest) :=
        hsorted.2
      intro D hD
      simp only [List.mem_cons] at hD
      rcases hD with hD | hD
      · subst D
        exact hAB
      · have hAC :
            SourcePressureAccountedIntervalBefore A C :=
          SourcePressureAccountedIntervalBefore.trans_like hAB hBC
        exact ih hAC htail D (by simpa using hD)

/-- Sorted-before empty lists are pairwise disjoint. -/
theorem sourcePressureAccountedIntervalListPairwiseDisjoint_of_sortedBefore_nil
    {n : OddNat} {k r : ℕ} :
    SourcePressureAccountedIntervalListPairwiseDisjoint
      ([] : List (SourcePressureAccountedInterval n k r)) :=
  sourcePressureAccountedIntervalListPairwiseDisjoint_nil

/-- Sorted-before singleton lists are pairwise disjoint. -/
theorem sourcePressureAccountedIntervalListPairwiseDisjoint_of_sortedBefore_singleton
    {n : OddNat} {k r : ℕ}
    (A : SourcePressureAccountedInterval n k r) :
    SourcePressureAccountedIntervalListPairwiseDisjoint [A] :=
  sourcePressureAccountedIntervalListPairwiseDisjoint_singleton A

/-- A sorted-before pair is pairwise disjoint. -/
theorem sourcePressureAccountedIntervalListPairwiseDisjoint_of_sortedBefore_pair
    {n : OddNat} {k r : ℕ}
    {A B : SourcePressureAccountedInterval n k r}
    (hAB : SourcePressureAccountedIntervalBefore A B) :
    SourcePressureAccountedIntervalListPairwiseDisjoint [A, B] :=
  (sourcePressureAccountedIntervalFamily_pair_of_before A B hAB).pairwiseDisjoint

/--
Adjacent sortedness implies pairwise disjointness for explicit accounted
interval lists.

The proof turns the adjacent order chain into a head-before-all-tail fact and
then uses `before -> disjoint`.  It still does not say the list covers any
ambient pressure region.
-/
theorem sourcePressureAccountedIntervalListPairwiseDisjoint_of_sortedBefore
    {n : OddNat} {k r : ℕ}
    {L : List (SourcePressureAccountedInterval n k r)}
    (hsorted : SourcePressureAccountedIntervalListSortedBefore L) :
    SourcePressureAccountedIntervalListPairwiseDisjoint L := by
  induction L with
  | nil =>
      exact sourcePressureAccountedIntervalListPairwiseDisjoint_nil
  | cons A L ih =>
      cases L with
      | nil =>
          exact sourcePressureAccountedIntervalListPairwiseDisjoint_singleton A
      | cons B rest =>
          have hAB : SourcePressureAccountedIntervalBefore A B := hsorted.1
          have htailSorted :
              SourcePressureAccountedIntervalListSortedBefore (B :: rest) :=
            hsorted.2
          refine sourcePressureAccountedIntervalListPairwiseDisjoint_cons ?_ ?_
          · intro C hC
            exact SourcePressureAccountedIntervalsDisjoint.of_before
              (SourcePressureAccountedIntervalBefore.before_all_of_sorted_tail
                hAB htailSorted C hC)
          · exact ih htailSorted

/--
Family constructor from an adjacent-sorted explicit list.

This only packages the list and the derived pairwise disjointness.  It is not
a coverage or decomposition theorem.
-/
def sourcePressureAccountedIntervalFamily_of_sortedBefore
    {n : OddNat} {k r : ℕ}
    (L : List (SourcePressureAccountedInterval n k r))
    (hsorted : SourcePressureAccountedIntervalListSortedBefore L) :
    SourcePressureAccountedIntervalFamily n k r :=
  { items := L
    pairwiseDisjoint :=
      sourcePressureAccountedIntervalListPairwiseDisjoint_of_sortedBefore hsorted }

/--
Budget wrapper for a family built from an adjacent-sorted list.

The sorted hypothesis is used only to construct the family; the budget remains
the explicit list budget and does not imply coverage.
-/
theorem sourcePressureAccountedIntervalFamily_of_sortedBefore_sum_le_neg_length
    {n : OddNat} {k r : ℕ}
    (L : List (SourcePressureAccountedInterval n k r))
    (hsorted : SourcePressureAccountedIntervalListSortedBefore L) :
    (((sourcePressureAccountedIntervalFamily_of_sortedBefore L hsorted).items).map (fun A =>
      SourcePressureIntervalNetDrop n k r A.start A.len)).sum ≤
        -((L.length : ℕ) : ℤ) := by
  simpa [sourcePressureAccountedIntervalFamily_of_sortedBefore] using
    sourcePressureAccountedInterval_list_sum_le_neg_length L

/-- Empty sorted-family constructor. -/
def sourcePressureAccountedIntervalFamily_sorted_nil
    (n : OddNat) (k r : ℕ) :
    SourcePressureAccountedIntervalFamily n k r :=
  sourcePressureAccountedIntervalFamily_nil n k r

/-- Singleton sorted-family constructor. -/
def sourcePressureAccountedIntervalFamily_sorted_singleton
    {n : OddNat} {k r : ℕ}
    (A : SourcePressureAccountedInterval n k r) :
    SourcePressureAccountedIntervalFamily n k r :=
  sourcePressureAccountedIntervalFamily_singleton A

/--
Cons a head interval onto an adjacent-sorted nonempty tail and package the
result as an explicit accounted-interval family.

This is still only a constructor for explicitly supplied intervals.
-/
def sourcePressureAccountedIntervalFamily_sorted_cons
    {n : OddNat} {k r : ℕ}
    (A B : SourcePressureAccountedInterval n k r)
    (rest : List (SourcePressureAccountedInterval n k r))
    (hAB : SourcePressureAccountedIntervalBefore A B)
    (htail : SourcePressureAccountedIntervalListSortedBefore (B :: rest)) :
    SourcePressureAccountedIntervalFamily n k r :=
  sourcePressureAccountedIntervalFamily_of_sortedBefore
    (A :: B :: rest)
    (sourcePressureAccountedIntervalListSortedBefore_cons hAB htail)

/--
The head of an adjacent-sorted accounted-interval list is disjoint from every
tail item.

This is the list-facing form needed by later family constructors.  It handles
the empty-tail case directly and the nonempty-tail case through
`before_all_of_sorted_tail`.
-/
theorem sourcePressureAccountedInterval_before_all_tail_of_sortedBefore
    {n : OddNat} {k r : ℕ}
    {A : SourcePressureAccountedInterval n k r}
    {L : List (SourcePressureAccountedInterval n k r)}
    (hsorted : SourcePressureAccountedIntervalListSortedBefore (A :: L)) :
    ∀ B ∈ L, SourcePressureAccountedIntervalsDisjoint A B := by
  cases L with
  | nil =>
      intro B hB
      simp at hB
  | cons B rest =>
      intro C hC
      have hAB : SourcePressureAccountedIntervalBefore A B := hsorted.1
      have htail :
          SourcePressureAccountedIntervalListSortedBefore (B :: rest) :=
        hsorted.2
      exact SourcePressureAccountedIntervalsDisjoint.of_before
        (SourcePressureAccountedIntervalBefore.before_all_of_sorted_tail
          hAB htail C hC)

/-- Adjacent sorted-before failure for one neighboring pair. -/
def SourcePressureAccountedIntervalListSortedBeforeFailsAt
    {n : OddNat} {k r : ℕ}
    (A B : SourcePressureAccountedInterval n k r) : Prop :=
  ¬ SourcePressureAccountedIntervalBefore A B

/--
Existential adjacent sorted-before failure for an explicit list.

This is an obstruction-style predicate: it records where adjacent sortedness
breaks without claiming anything about coverage or dynamics.
-/
def SourcePressureAccountedIntervalListHasSortedBeforeFailure
    {n : OddNat} {k r : ℕ} :
    List (SourcePressureAccountedInterval n k r) → Prop
  | [] => False
  | [_] => False
  | A :: B :: rest =>
      ¬ SourcePressureAccountedIntervalBefore A B ∨
        SourcePressureAccountedIntervalListHasSortedBeforeFailure (B :: rest)

/-- A failed neighboring pair gives a sorted-before failure for the pair list. -/
theorem sourcePressureAccountedIntervalListHasSortedBeforeFailure_pair
    {n : OddNat} {k r : ℕ}
    {A B : SourcePressureAccountedInterval n k r}
    (hfail : ¬ SourcePressureAccountedIntervalBefore A B) :
    SourcePressureAccountedIntervalListHasSortedBeforeFailure [A, B] :=
  Or.inl hfail

/-- A two-element list is sorted exactly when its neighboring pair is before. -/
theorem sourcePressureAccountedIntervalListSortedBefore_pair_iff
    {n : OddNat} {k r : ℕ}
    {A B : SourcePressureAccountedInterval n k r} :
    SourcePressureAccountedIntervalListSortedBefore [A, B] ↔
      SourcePressureAccountedIntervalBefore A B := by
  constructor
  · intro h
    exact h.1
  · intro h
    exact ⟨h, trivial⟩

/-- Pair-level sortedness and failure are exact negations. -/
theorem sourcePressureAccountedIntervalListHasSortedBeforeFailure_pair_iff
    {n : OddNat} {k r : ℕ}
    {A B : SourcePressureAccountedInterval n k r} :
    SourcePressureAccountedIntervalListHasSortedBeforeFailure [A, B] ↔
      ¬ SourcePressureAccountedIntervalBefore A B := by
  constructor
  · intro h
    exact h.elim id False.elim
  · exact sourcePressureAccountedIntervalListHasSortedBeforeFailure_pair

/--
Every explicit accounted-interval list is either adjacent-sorted or carries an
adjacent sorted-before failure.

This is not a coverage dichotomy.  It is only a first-class split for the
explicit list that a caller has already supplied.
-/
theorem sourcePressureAccountedIntervalList_sorted_or_failure
    {n : OddNat} {k r : ℕ}
    (L : List (SourcePressureAccountedInterval n k r)) :
    SourcePressureAccountedIntervalListSortedBefore L ∨
      SourcePressureAccountedIntervalListHasSortedBeforeFailure L := by
  induction L with
  | nil =>
      exact Or.inl trivial
  | cons A L ih =>
      cases L with
      | nil =>
          exact Or.inl trivial
      | cons B rest =>
          by_cases hAB : SourcePressureAccountedIntervalBefore A B
          · rcases ih with htail | htail
            · exact Or.inl
                (sourcePressureAccountedIntervalListSortedBefore_cons hAB htail)
            · exact Or.inr (Or.inr htail)
          · exact Or.inr (Or.inl hAB)

/--
Adjacent sortedness for an explicit interval-pulse-address list.

The predicate is defined by converting addresses to accounted intervals and
reusing the accounted-list sortedness.  It is still only a statement about the
explicit list supplied by the caller.
-/
def SourcePressureIntervalPulseAddressListSortedBefore
    {n : OddNat} {k r : ℕ}
    (L : List (SourcePressureIntervalPulseAddress n k r)) : Prop :=
  SourcePressureAccountedIntervalListSortedBefore
    (sourcePressureAccountedIntervalList_of_intervalPulseAddressList L)

/--
Adjacent sorted-before failure for an explicit interval-pulse-address list.

This is not overlap evidence.  It only records that the converted accounted
list is not adjacent-sorted at some neighboring pair.
-/
def SourcePressureIntervalPulseAddressListHasSortedBeforeFailure
    {n : OddNat} {k r : ℕ}
    (L : List (SourcePressureIntervalPulseAddress n k r)) : Prop :=
  SourcePressureAccountedIntervalListHasSortedBeforeFailure
    (sourcePressureAccountedIntervalList_of_intervalPulseAddressList L)

/--
Every explicit interval-pulse-address list is either adjacent-sorted after
conversion or carries an adjacent sorted-before failure.

This is a list-internal dichotomy only; it is not a coverage or convergence
statement.
-/
theorem sourcePressureIntervalPulseAddressList_sorted_or_failure
    {n : OddNat} {k r : ℕ}
    (L : List (SourcePressureIntervalPulseAddress n k r)) :
    SourcePressureIntervalPulseAddressListSortedBefore L ∨
      SourcePressureIntervalPulseAddressListHasSortedBeforeFailure L :=
  sourcePressureAccountedIntervalList_sorted_or_failure
    (sourcePressureAccountedIntervalList_of_intervalPulseAddressList L)

/-- A two-address list is sorted exactly when the first address is before the second. -/
theorem sourcePressureIntervalPulseAddressListSortedBefore_pair_iff
    {n : OddNat} {k r : ℕ}
    {A B : SourcePressureIntervalPulseAddress n k r} :
    SourcePressureIntervalPulseAddressListSortedBefore [A, B] ↔
      SourcePressureIntervalPulseAddressBefore A B := by
  change
    SourcePressureAccountedIntervalListSortedBefore
      [sourcePressureAccountedInterval_of_intervalPulseAddress A,
        sourcePressureAccountedInterval_of_intervalPulseAddress B] ↔
      SourcePressureIntervalPulseAddressBefore A B
  rw [sourcePressureAccountedIntervalListSortedBefore_pair_iff]
  exact sourcePressureIntervalPulseAddressBefore_iff_accountedBefore.symm

/--
A two-address list has a sorted-before failure exactly when the first address
is not before the second.

Again, this does not imply overlap.  It only detects failure of this chosen
left-to-right order.
-/
theorem sourcePressureIntervalPulseAddressListHasSortedBeforeFailure_pair_iff
    {n : OddNat} {k r : ℕ}
    {A B : SourcePressureIntervalPulseAddress n k r} :
    SourcePressureIntervalPulseAddressListHasSortedBeforeFailure [A, B] ↔
      ¬ SourcePressureIntervalPulseAddressBefore A B := by
  change
    SourcePressureAccountedIntervalListHasSortedBeforeFailure
      [sourcePressureAccountedInterval_of_intervalPulseAddress A,
        sourcePressureAccountedInterval_of_intervalPulseAddress B] ↔
      ¬ SourcePressureIntervalPulseAddressBefore A B
  rw [sourcePressureAccountedIntervalListHasSortedBeforeFailure_pair_iff]
  exact not_congr sourcePressureIntervalPulseAddressBefore_iff_accountedBefore.symm

/--
Thin family carrier for explicit interval-pulse addresses.

This wrapper intentionally stores only the supplied address list.  It has no
coverage, maximality, uniqueness, prefix, disjointness, or union-accounting
field.  Those properties must be supplied later by separate hypotheses.
-/
structure SourcePressureIntervalPulseAddressFamily
    (n : OddNat) (k r : ℕ) where
  /-- Explicit interval-pulse addresses. -/
  items : List (SourcePressureIntervalPulseAddress n k r)

/--
Empty explicit interval-pulse-address family.

This does not say that the ambient pressure window has no pulses.
-/
def sourcePressureIntervalPulseAddressFamily_nil
    (n : OddNat) (k r : ℕ) :
    SourcePressureIntervalPulseAddressFamily n k r :=
  { items := [] }

/--
Singleton explicit interval-pulse-address family.

This packages one already supplied address and makes no maximality or coverage
claim.
-/
def sourcePressureIntervalPulseAddressFamily_singleton
    {n : OddNat} {k r : ℕ}
    (A : SourcePressureIntervalPulseAddress n k r) :
    SourcePressureIntervalPulseAddressFamily n k r :=
  { items := [A] }

/-- Alias for callers that want the producer-facing wording. -/
def sourcePressureIntervalPulseAddressFamily_singleton_of_address
    {n : OddNat} {k r : ℕ}
    (A : SourcePressureIntervalPulseAddress n k r) :
    SourcePressureIntervalPulseAddressFamily n k r :=
  sourcePressureIntervalPulseAddressFamily_singleton A

/--
Singleton family produced from a local pressure island.

This is the only producer bridge added in this checkpoint.  It uses the
existing `sourcePressureIntervalPulseAddress_of_localIsland` producer from
`PressureFrontier` and packages that one explicit address as a singleton
family.  It does not enumerate all local islands or cover an orbit window.
-/
def sourcePressureIntervalPulseAddressFamily_singleton_of_localIsland
    (n : OddNat) (k r j : ℕ)
    (hisland : SourcePressureLocalIsland n k r j) :
    SourcePressureIntervalPulseAddressFamily n k r :=
  sourcePressureIntervalPulseAddressFamily_singleton
    (sourcePressureIntervalPulseAddress_of_localIsland n k r j hisland)

/--
Cons an explicit interval-pulse address onto an explicit family.

This is ordinary list construction only; it does not infer sorting,
disjointness, or union accounting.
-/
def sourcePressureIntervalPulseAddressFamily_cons
    {n : OddNat} {k r : ℕ}
    (A : SourcePressureIntervalPulseAddress n k r)
    (F : SourcePressureIntervalPulseAddressFamily n k r) :
    SourcePressureIntervalPulseAddressFamily n k r :=
  { items := A :: F.items }

@[simp]
theorem sourcePressureIntervalPulseAddressFamily_nil_length
    (n : OddNat) (k r : ℕ) :
    (sourcePressureIntervalPulseAddressFamily_nil n k r).items.length = 0 := by
  rfl

@[simp]
theorem sourcePressureIntervalPulseAddressFamily_singleton_length
    {n : OddNat} {k r : ℕ}
    (A : SourcePressureIntervalPulseAddress n k r) :
    (sourcePressureIntervalPulseAddressFamily_singleton A).items.length = 1 := by
  rfl

@[simp]
theorem sourcePressureIntervalPulseAddressFamily_cons_length
    {n : OddNat} {k r : ℕ}
    (A : SourcePressureIntervalPulseAddress n k r)
    (F : SourcePressureIntervalPulseAddressFamily n k r) :
    (sourcePressureIntervalPulseAddressFamily_cons A F).items.length =
      F.items.length + 1 := by
  simp [sourcePressureIntervalPulseAddressFamily_cons]

/--
Family-level adjacent sortedness for explicit interval-pulse addresses.

This is just list sortedness on `F.items`.
-/
def SourcePressureIntervalPulseAddressFamilySortedBefore
    {n : OddNat} {k r : ℕ}
    (F : SourcePressureIntervalPulseAddressFamily n k r) : Prop :=
  SourcePressureIntervalPulseAddressListSortedBefore F.items

/--
Family-level adjacent sorted-before failure.

This is an order obstruction only.  It does not imply interval overlap:
reversed order is also a sorted-before failure.
-/
def SourcePressureIntervalPulseAddressFamilyHasSortedBeforeFailure
    {n : OddNat} {k r : ℕ}
    (F : SourcePressureIntervalPulseAddressFamily n k r) : Prop :=
  SourcePressureIntervalPulseAddressListHasSortedBeforeFailure F.items

/--
Every explicit interval-pulse-address family is either adjacent-sorted or
carries an adjacent sorted-before failure.

This is not a coverage, maximality, prefix, union-accounting, or convergence
statement.
-/
theorem sourcePressureIntervalPulseAddressFamily_sorted_or_failure
    {n : OddNat} {k r : ℕ}
    (F : SourcePressureIntervalPulseAddressFamily n k r) :
    SourcePressureIntervalPulseAddressFamilySortedBefore F ∨
      SourcePressureIntervalPulseAddressFamilyHasSortedBeforeFailure F :=
  sourcePressureIntervalPulseAddressList_sorted_or_failure F.items

/--
Build an accounted family from an adjacent-sorted interval-pulse-address list.

The family is still the conversion of an explicitly supplied list.  The sorted
hypothesis is only used to obtain pairwise disjointness of the converted
intervals.
-/
def sourcePressureAccountedIntervalFamily_of_sortedIntervalPulseAddressList
    {n : OddNat} {k r : ℕ}
    (L : List (SourcePressureIntervalPulseAddress n k r))
    (hsorted : SourcePressureIntervalPulseAddressListSortedBefore L) :
    SourcePressureAccountedIntervalFamily n k r :=
  sourcePressureAccountedIntervalFamily_of_sortedBefore
    (sourcePressureAccountedIntervalList_of_intervalPulseAddressList L)
    hsorted

@[simp]
theorem sourcePressureAccountedIntervalFamily_of_sortedIntervalPulseAddressList_length
    {n : OddNat} {k r : ℕ}
    (L : List (SourcePressureIntervalPulseAddress n k r))
    (hsorted : SourcePressureIntervalPulseAddressListSortedBefore L) :
    (sourcePressureAccountedIntervalFamily_of_sortedIntervalPulseAddressList
      L hsorted).items.length = L.length := by
  simp [sourcePressureAccountedIntervalFamily_of_sortedIntervalPulseAddressList,
    sourcePressureAccountedIntervalFamily_of_sortedBefore,
    sourcePressureAccountedIntervalList_of_intervalPulseAddressList]

/--
Budget wrapper for a sorted interval-pulse-address family.

The sorted hypothesis packages the family.  The inequality itself is still the
explicit-list budget over the converted address witnesses.
-/
theorem
    sourcePressureAccountedIntervalFamily_of_sortedIntervalPulseAddressList_sum_le_neg_length
    {n : OddNat} {k r : ℕ}
    (L : List (SourcePressureIntervalPulseAddress n k r))
    (hsorted : SourcePressureIntervalPulseAddressListSortedBefore L) :
    (((sourcePressureAccountedIntervalFamily_of_sortedIntervalPulseAddressList
      L hsorted).items).map
      (fun A => SourcePressureIntervalNetDrop n k r A.start A.len)).sum ≤
        -((L.length : ℕ) : ℤ) := by
  simpa [sourcePressureAccountedIntervalFamily_of_sortedIntervalPulseAddressList]
    using sourcePressureIntervalPulseAddressList_sum_le_neg_length L

theorem
    sourcePressureAccountedIntervalFamily_of_sortedIntervalPulseAddressList_sum_neg_of_nonempty
    {n : OddNat} {k r : ℕ}
    {L : List (SourcePressureIntervalPulseAddress n k r)}
    (hsorted : SourcePressureIntervalPulseAddressListSortedBefore L)
    (hL : L ≠ []) :
    (((sourcePressureAccountedIntervalFamily_of_sortedIntervalPulseAddressList
      L hsorted).items).map
      (fun A => SourcePressureIntervalNetDrop n k r A.start A.len)).sum < 0 := by
  simpa [sourcePressureAccountedIntervalFamily_of_sortedIntervalPulseAddressList]
    using sourcePressureIntervalPulseAddressList_sum_neg_of_nonempty hL

/--
Lift a sorted explicit interval-pulse-address family to an accounted interval
family.

The sorted hypothesis packages the converted intervals as pairwise disjoint.
No coverage or union accounting is introduced.
-/
def sourcePressureAccountedIntervalFamily_of_sortedPulseAddressFamily
    {n : OddNat} {k r : ℕ}
    (F : SourcePressureIntervalPulseAddressFamily n k r)
    (hsorted : SourcePressureIntervalPulseAddressFamilySortedBefore F) :
    SourcePressureAccountedIntervalFamily n k r :=
  sourcePressureAccountedIntervalFamily_of_sortedIntervalPulseAddressList
    F.items hsorted

@[simp]
theorem sourcePressureAccountedIntervalFamily_of_sortedPulseAddressFamily_length
    {n : OddNat} {k r : ℕ}
    (F : SourcePressureIntervalPulseAddressFamily n k r)
    (hsorted : SourcePressureIntervalPulseAddressFamilySortedBefore F) :
    (sourcePressureAccountedIntervalFamily_of_sortedPulseAddressFamily
      F hsorted).items.length = F.items.length := by
  simp [sourcePressureAccountedIntervalFamily_of_sortedPulseAddressFamily]

/-- Budget wrapper for a sorted explicit interval-pulse-address family. -/
theorem sourcePressureAccountedIntervalFamily_of_sortedPulseAddressFamily_sum_le_neg_length
    {n : OddNat} {k r : ℕ}
    (F : SourcePressureIntervalPulseAddressFamily n k r)
    (hsorted : SourcePressureIntervalPulseAddressFamilySortedBefore F) :
    (((sourcePressureAccountedIntervalFamily_of_sortedPulseAddressFamily
      F hsorted).items).map
      (fun A => SourcePressureIntervalNetDrop n k r A.start A.len)).sum ≤
        -((F.items.length : ℕ) : ℤ) := by
  simpa [sourcePressureAccountedIntervalFamily_of_sortedPulseAddressFamily]
    using
      sourcePressureAccountedIntervalFamily_of_sortedIntervalPulseAddressList_sum_le_neg_length
        F.items hsorted

/--
Nonempty budget wrapper for a sorted explicit interval-pulse-address family.
-/
theorem sourcePressureAccountedIntervalFamily_of_sortedPulseAddressFamily_sum_neg_of_nonempty
    {n : OddNat} {k r : ℕ}
    (F : SourcePressureIntervalPulseAddressFamily n k r)
    (hsorted : SourcePressureIntervalPulseAddressFamilySortedBefore F)
    (hF : F.items ≠ []) :
    (((sourcePressureAccountedIntervalFamily_of_sortedPulseAddressFamily
      F hsorted).items).map
      (fun A => SourcePressureIntervalNetDrop n k r A.start A.len)).sum < 0 := by
  simpa [sourcePressureAccountedIntervalFamily_of_sortedPulseAddressFamily]
    using
      sourcePressureAccountedIntervalFamily_of_sortedIntervalPulseAddressList_sum_neg_of_nonempty
        hsorted hF

/--
Explicit local-island witness with its pressure-depth index.

The index `j` is part of the witness.  Mathematically this is the intended
`Σ j, SourcePressureLocalIsland n k r j` carrier, but the island predicate
lives in `Prop`, so Lean represents the executable list carrier as a
`Subtype`.
-/
abbrev SourcePressureLocalIslandWitness
    (n : OddNat) (k r : ℕ) :=
  { j : ℕ // SourcePressureLocalIsland n k r j }

/--
Convert one explicit local-island witness to an interval-pulse address.

This uses the existing singleton producer from `PressureFrontier`.  It does
not claim that the witness is part of a complete list of all local islands.
-/
def sourcePressureIntervalPulseAddress_of_localIslandWitness
    {n : OddNat} {k r : ℕ}
    (W : SourcePressureLocalIslandWitness n k r) :
    SourcePressureIntervalPulseAddress n k r :=
  sourcePressureIntervalPulseAddress_of_localIsland n k r W.val W.property

/--
Convert an explicit local-island witness list to a pulse-address family.

The result is only the mapped list of supplied witnesses.  It does not
enumerate all local islands, prove coverage, or identify a canonical frontier
producer.
-/
def sourcePressureIntervalPulseAddressFamily_of_localIslandWitnessList
    {n : OddNat} {k r : ℕ}
    (L : List (SourcePressureLocalIslandWitness n k r)) :
    SourcePressureIntervalPulseAddressFamily n k r :=
  { items := L.map sourcePressureIntervalPulseAddress_of_localIslandWitness }

@[simp]
theorem sourcePressureIntervalPulseAddressFamily_of_localIslandWitnessList_length
    {n : OddNat} {k r : ℕ}
    (L : List (SourcePressureLocalIslandWitness n k r)) :
    (sourcePressureIntervalPulseAddressFamily_of_localIslandWitnessList
      L).items.length = L.length := by
  simp [sourcePressureIntervalPulseAddressFamily_of_localIslandWitnessList]

/--
Sortedness for an explicit local-island witness list after conversion to
interval-pulse addresses.
-/
def SourcePressureLocalIslandWitnessListSortedBefore
    {n : OddNat} {k r : ℕ}
    (L : List (SourcePressureLocalIslandWitness n k r)) : Prop :=
  SourcePressureIntervalPulseAddressFamilySortedBefore
    (sourcePressureIntervalPulseAddressFamily_of_localIslandWitnessList L)

/--
Sorted-before failure for an explicit local-island witness list.

This is still only an order obstruction after conversion.  It does not prove
overlap and does not say that the list covers all local islands.
-/
def SourcePressureLocalIslandWitnessListHasSortedBeforeFailure
    {n : OddNat} {k r : ℕ}
    (L : List (SourcePressureLocalIslandWitness n k r)) : Prop :=
  SourcePressureIntervalPulseAddressFamilyHasSortedBeforeFailure
    (sourcePressureIntervalPulseAddressFamily_of_localIslandWitnessList L)

/--
Every explicit local-island witness list is either sorted after conversion or
carries a sorted-before failure.

This is a statement about the supplied list only; it does not enumerate all
local islands.
-/
theorem sourcePressureLocalIslandWitnessList_sorted_or_failure
    {n : OddNat} {k r : ℕ}
    (L : List (SourcePressureLocalIslandWitness n k r)) :
    SourcePressureLocalIslandWitnessListSortedBefore L ∨
      SourcePressureLocalIslandWitnessListHasSortedBeforeFailure L :=
  sourcePressureIntervalPulseAddressFamily_sorted_or_failure
    (sourcePressureIntervalPulseAddressFamily_of_localIslandWitnessList L)

/--
Lift a sorted explicit local-island witness list to an accounted interval
family.

The sorted hypothesis is inherited through the pulse-address family conversion.
No coverage, maximality, or union accounting is introduced.
-/
def sourcePressureAccountedIntervalFamily_of_sortedLocalIslandWitnessList
    {n : OddNat} {k r : ℕ}
    (L : List (SourcePressureLocalIslandWitness n k r))
    (hsorted : SourcePressureLocalIslandWitnessListSortedBefore L) :
    SourcePressureAccountedIntervalFamily n k r :=
  sourcePressureAccountedIntervalFamily_of_sortedPulseAddressFamily
    (sourcePressureIntervalPulseAddressFamily_of_localIslandWitnessList L)
    hsorted

@[simp]
theorem sourcePressureAccountedIntervalFamily_of_sortedLocalIslandWitnessList_length
    {n : OddNat} {k r : ℕ}
    (L : List (SourcePressureLocalIslandWitness n k r))
    (hsorted : SourcePressureLocalIslandWitnessListSortedBefore L) :
    (sourcePressureAccountedIntervalFamily_of_sortedLocalIslandWitnessList
      L hsorted).items.length = L.length := by
  simp [sourcePressureAccountedIntervalFamily_of_sortedLocalIslandWitnessList]

/--
Budget wrapper for a sorted explicit local-island witness list.
-/
theorem sourcePressureAccountedIntervalFamily_of_sortedLocalIslandWitnessList_sum_le_neg_length
    {n : OddNat} {k r : ℕ}
    (L : List (SourcePressureLocalIslandWitness n k r))
    (hsorted : SourcePressureLocalIslandWitnessListSortedBefore L) :
    (((sourcePressureAccountedIntervalFamily_of_sortedLocalIslandWitnessList
      L hsorted).items).map
      (fun A => SourcePressureIntervalNetDrop n k r A.start A.len)).sum ≤
        -((L.length : ℕ) : ℤ) := by
  simpa [sourcePressureAccountedIntervalFamily_of_sortedLocalIslandWitnessList]
    using
      sourcePressureAccountedIntervalFamily_of_sortedPulseAddressFamily_sum_le_neg_length
        (sourcePressureIntervalPulseAddressFamily_of_localIslandWitnessList L)
        hsorted

/--
Nonempty budget wrapper for a sorted explicit local-island witness list.
-/
theorem sourcePressureAccountedIntervalFamily_of_sortedLocalIslandWitnessList_sum_neg_of_nonempty
    {n : OddNat} {k r : ℕ}
    {L : List (SourcePressureLocalIslandWitness n k r)}
    (hsorted : SourcePressureLocalIslandWitnessListSortedBefore L)
    (hL : L ≠ []) :
    (((sourcePressureAccountedIntervalFamily_of_sortedLocalIslandWitnessList
      L hsorted).items).map
      (fun A => SourcePressureIntervalNetDrop n k r A.start A.len)).sum < 0 := by
  have hitems :
      (sourcePressureIntervalPulseAddressFamily_of_localIslandWitnessList
        L).items ≠ [] := by
    intro h
    apply hL
    simpa [sourcePressureIntervalPulseAddressFamily_of_localIslandWitnessList]
      using h
  simpa [sourcePressureAccountedIntervalFamily_of_sortedLocalIslandWitnessList]
    using
      sourcePressureAccountedIntervalFamily_of_sortedPulseAddressFamily_sum_neg_of_nonempty
        (sourcePressureIntervalPulseAddressFamily_of_localIslandWitnessList L)
        hsorted hitems

/--
Singleton pulse-address family from one local-island witness.
-/
def sourcePressureIntervalPulseAddressFamily_singleton_of_localIslandWitness
    {n : OddNat} {k r : ℕ}
    (W : SourcePressureLocalIslandWitness n k r) :
    SourcePressureIntervalPulseAddressFamily n k r :=
  sourcePressureIntervalPulseAddressFamily_singleton
    (sourcePressureIntervalPulseAddress_of_localIslandWitness W)

@[simp]
theorem sourcePressureIntervalPulseAddressFamily_singleton_of_localIslandWitness_length
    {n : OddNat} {k r : ℕ}
    (W : SourcePressureLocalIslandWitness n k r) :
    (sourcePressureIntervalPulseAddressFamily_singleton_of_localIslandWitness
      W).items.length = 1 := by
  rfl

/--
A singleton local-island witness list is sorted after conversion.

This is only the singleton case for an explicitly supplied witness.
-/
theorem sourcePressureLocalIslandWitnessListSortedBefore_singleton
    {n : OddNat} {k r : ℕ}
    (W : SourcePressureLocalIslandWitness n k r) :
    SourcePressureLocalIslandWitnessListSortedBefore [W] := by
  trivial

/--
A singleton local-island witness list has no adjacent sorted-before failure.
-/
theorem sourcePressureLocalIslandWitnessList_no_failure_singleton
    {n : OddNat} {k r : ℕ}
    (W : SourcePressureLocalIslandWitness n k r) :
    ¬ SourcePressureLocalIslandWitnessListHasSortedBeforeFailure [W] := by
  intro h
  simpa [SourcePressureLocalIslandWitnessListHasSortedBeforeFailure,
    sourcePressureIntervalPulseAddressFamily_of_localIslandWitnessList,
    SourcePressureIntervalPulseAddressFamilyHasSortedBeforeFailure,
    SourcePressureIntervalPulseAddressListHasSortedBeforeFailure,
    sourcePressureAccountedIntervalList_of_intervalPulseAddressList] using h

/-- The empty witness list has no adjacent sorted-before failure. -/
theorem SourcePressureLocalIslandWitnessListHasSortedBeforeFailure_nil_false
    {n : OddNat} {k r : ℕ} :
    ¬ SourcePressureLocalIslandWitnessListHasSortedBeforeFailure
      ([] : List (SourcePressureLocalIslandWitness n k r)) := by
  intro h
  simpa [SourcePressureLocalIslandWitnessListHasSortedBeforeFailure,
    sourcePressureIntervalPulseAddressFamily_of_localIslandWitnessList,
    SourcePressureIntervalPulseAddressFamilyHasSortedBeforeFailure,
    SourcePressureIntervalPulseAddressListHasSortedBeforeFailure,
    sourcePressureAccountedIntervalList_of_intervalPulseAddressList] using h

/-- Name aligned with the failure predicate: singleton lists cannot fail. -/
theorem SourcePressureLocalIslandWitnessListHasSortedBeforeFailure_singleton_false
    {n : OddNat} {k r : ℕ}
    {W : SourcePressureLocalIslandWitness n k r} :
    ¬ SourcePressureLocalIslandWitnessListHasSortedBeforeFailure [W] :=
  sourcePressureLocalIslandWitnessList_no_failure_singleton W

/--
Accounted interval family generated by one explicit local-island witness.

This is the singleton specialization of the sorted witness-list lift.  It does
not claim that this witness is the only local island.
-/
def sourcePressureAccountedIntervalFamily_of_singletonLocalIslandWitness
    {n : OddNat} {k r : ℕ}
    (W : SourcePressureLocalIslandWitness n k r) :
    SourcePressureAccountedIntervalFamily n k r :=
  sourcePressureAccountedIntervalFamily_of_sortedLocalIslandWitnessList
    [W]
    (sourcePressureLocalIslandWitnessListSortedBefore_singleton W)

@[simp]
theorem sourcePressureAccountedIntervalFamily_of_singletonLocalIslandWitness_length
    {n : OddNat} {k r : ℕ}
    (W : SourcePressureLocalIslandWitness n k r) :
    (sourcePressureAccountedIntervalFamily_of_singletonLocalIslandWitness
      W).items.length = 1 := by
  simp [sourcePressureAccountedIntervalFamily_of_singletonLocalIslandWitness]

/--
The singleton local-island witness family carries at most one unit of negative
net drop.
-/
theorem sourcePressureAccountedIntervalFamily_of_singletonLocalIslandWitness_sum_le_neg_one
    {n : OddNat} {k r : ℕ}
    (W : SourcePressureLocalIslandWitness n k r) :
    (((sourcePressureAccountedIntervalFamily_of_singletonLocalIslandWitness
      W).items).map
      (fun A => SourcePressureIntervalNetDrop n k r A.start A.len)).sum ≤ -1 := by
  simpa [sourcePressureAccountedIntervalFamily_of_singletonLocalIslandWitness]
    using
      sourcePressureAccountedIntervalFamily_of_sortedLocalIslandWitnessList_sum_le_neg_length
        [W]
        (sourcePressureLocalIslandWitnessListSortedBefore_singleton W)

/-- The singleton local-island witness family has strictly negative listed cost. -/
theorem sourcePressureAccountedIntervalFamily_of_singletonLocalIslandWitness_sum_neg
    {n : OddNat} {k r : ℕ}
    (W : SourcePressureLocalIslandWitness n k r) :
    (((sourcePressureAccountedIntervalFamily_of_singletonLocalIslandWitness
      W).items).map
      (fun A => SourcePressureIntervalNetDrop n k r A.start A.len)).sum < 0 := by
  simpa [sourcePressureAccountedIntervalFamily_of_singletonLocalIslandWitness]
    using
      sourcePressureAccountedIntervalFamily_of_sortedLocalIslandWitnessList_sum_neg_of_nonempty
        (sourcePressureLocalIslandWitnessListSortedBefore_singleton W)
        (by simp)

/--
The singleton local-island witness family contains exactly the accounted
interval obtained by direct conversion.
-/
theorem sourcePressureAccountedIntervalFamily_of_singletonLocalIslandWitness_items
    {n : OddNat} {k r : ℕ}
    (W : SourcePressureLocalIslandWitness n k r) :
    (sourcePressureAccountedIntervalFamily_of_singletonLocalIslandWitness W).items =
      [sourcePressureAccountedInterval_of_intervalPulseAddress
        (sourcePressureIntervalPulseAddress_of_localIslandWitness W)] := by
  rfl

/--
Raw-argument version of the singleton local-island witness budget.

This packages `j` and `hisland` internally as one explicit witness.
-/
theorem sourcePressureLocalIsland_singleton_sum_le_neg_one
    (n : OddNat) (k r j : ℕ)
    (hisland : SourcePressureLocalIsland n k r j) :
    (((sourcePressureAccountedIntervalFamily_of_singletonLocalIslandWitness
      (⟨j, hisland⟩ : SourcePressureLocalIslandWitness n k r)).items).map
      (fun A => SourcePressureIntervalNetDrop n k r A.start A.len)).sum ≤ -1 :=
  sourcePressureAccountedIntervalFamily_of_singletonLocalIslandWitness_sum_le_neg_one
    (⟨j, hisland⟩ : SourcePressureLocalIslandWitness n k r)

/--
Raw-argument strict negative version for one explicit local-island witness.
-/
theorem sourcePressureLocalIsland_singleton_sum_neg
    (n : OddNat) (k r j : ℕ)
    (hisland : SourcePressureLocalIsland n k r j) :
    (((sourcePressureAccountedIntervalFamily_of_singletonLocalIslandWitness
      (⟨j, hisland⟩ : SourcePressureLocalIslandWitness n k r)).items).map
      (fun A => SourcePressureIntervalNetDrop n k r A.start A.len)).sum < 0 :=
  sourcePressureAccountedIntervalFamily_of_singletonLocalIslandWitness_sum_neg
    (⟨j, hisland⟩ : SourcePressureLocalIslandWitness n k r)

end DkMath.Collatz
