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

end DkMath.Collatz
