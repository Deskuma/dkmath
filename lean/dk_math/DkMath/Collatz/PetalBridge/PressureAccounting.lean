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

/-- Ordered non-overlap implies ordinary interval disjointness. -/
theorem NatIntervalsDisjoint.of_before
    {a len b len' : ℕ}
    (h : NatIntervalBefore a len b len') :
    NatIntervalsDisjoint a len b len' :=
  Or.inl h

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

end DkMath.Collatz
