/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Collatz.PetalBridge.FloatWindow.CanonicalEndpointDrift

#print "file: DkMath.Collatz.PetalBridge.FloatWindow.CanonicalAllOnesDrift"

namespace DkMath.Collatz

/-!
# Cross-root all-ones endpoint drift

The root `2^L - 1` begins with one canonical block of length `L`.  For odd
`L`, its terminal carrier has valuation one.  Varying `L` therefore gives a
cross-root family with growing initial endpoint drift.  This refutes only the
single global ceiling shared by every root; it is not a fixed-root
unboundedness result.
-/

/-- The positive all-ones word of binary length `L`, packaged as an odd root.
The positivity hypothesis excludes the zero word at `L = 0`. -/
noncomputable def allOnesOdd (L : ℕ) (hL : 0 < L) : OddNat := by
  refine ⟨2 ^ L - 1, ?_⟩
  obtain ⟨q, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : L ≠ 0)
  rw [pow_succ]
  have hp : 0 < 2 ^ q := pow_pos (by norm_num) _
  omega

@[simp] theorem allOnesOdd_val (L : ℕ) (hL : 0 < L) :
    (allOnesOdd L hL).1 = 2 ^ L - 1 := rfl

/-- Every first canonical block starts at the root itself. -/
theorem canonicalBlockStartState_zero (n : OddNat) :
    canonicalBlockStartState n 0 = n.1 := by
  unfold canonicalBlockStartState canonicalBlockStartTime
    canonicalEndpointBlockStart
  rfl

/-- The all-ones first block starts at the expected binary word. -/
@[simp] theorem canonicalBlockStartState_allOnesOdd_zero
    (L : ℕ) (hL : 0 < L) :
    canonicalBlockStartState (allOnesOdd L hL) 0 = 2 ^ L - 1 := by
  rw [canonicalBlockStartState_zero]
  rfl

/-- The first canonical block of `2^L - 1` has exact length `L`. -/
@[simp] theorem canonicalBlockLength_allOnesOdd_zero
    (L : ℕ) (hL : 0 < L) :
    canonicalBlockLength (allOnesOdd L hL) 0 = L := by
  rw [canonicalBlockLength_eq_v2_startState_add_one,
    canonicalBlockStartState_allOnesOdd_zero]
  have hp : 0 < 2 ^ L := pow_pos (by norm_num) _
  have hadd : 2 ^ L - 1 + 1 = 2 ^ L := by omega
  rw [hadd]
  change v2 (pow2 L) = L
  exact v2_pow2 L

/-- Removing the initial exact power of two leaves odd core one. -/
@[simp] theorem canonicalBlockOddCore_allOnesOdd_zero
    (L : ℕ) (hL : 0 < L) :
    canonicalBlockOddCore (allOnesOdd L hL) 0 = 1 := by
  unfold canonicalBlockOddCore
  rw [canonicalBlockStartState_allOnesOdd_zero,
    canonicalBlockLength_allOnesOdd_zero]
  have hp : 0 < 2 ^ L := pow_pos (by norm_num) _
  have hadd : 2 ^ L - 1 + 1 = 2 ^ L := by omega
  rw [hadd]
  simp

/-- The first all-ones terminal carrier is `3^L - 1`. -/
@[simp] theorem canonicalBlockTerminalCarrier_allOnesOdd_zero
    (L : ℕ) (hL : 0 < L) :
    canonicalBlockTerminalCarrier (allOnesOdd L hL) 0 = 3 ^ L - 1 := by
  unfold canonicalBlockTerminalCarrier
  rw [canonicalBlockLength_allOnesOdd_zero,
    canonicalBlockOddCore_allOnesOdd_zero]
  simp

/-- Powers of nine are one modulo four. -/
private theorem nine_pow_mod_four (r : ℕ) :
    9 ^ r % 4 = 1 := by
  induction r with
  | zero => norm_num
  | succ r ih =>
      rw [pow_succ, Nat.mul_mod, ih]

/-- An odd power of three is three modulo four. -/
private theorem three_pow_odd_mod_four (r : ℕ) :
    3 ^ (2 * r + 1) % 4 = 3 := by
  have hpow : 3 ^ (2 * r + 1) = 3 * 9 ^ r := by
    rw [show 2 * r + 1 = 2 * r + 1 by rfl, pow_add, pow_mul]
    norm_num
    ring
  rw [hpow, Nat.mul_mod, nine_pow_mod_four]

/-- The carrier following an odd-length all-ones block is two modulo four. -/
private theorem three_pow_odd_sub_one_mod_four (r : ℕ) :
    (3 ^ (2 * r + 1) - 1) % 4 = 2 := by
  have hmod := three_pow_odd_mod_four r
  have hsplit := Nat.mod_add_div (3 ^ (2 * r + 1)) 4
  have heq : 3 ^ (2 * r + 1) =
      4 * (3 ^ (2 * r + 1) / 4) + 3 := by
    omega
  rw [heq]
  simp

/-- The exact terminal valuation of every odd-length all-ones initial block is
one. -/
theorem v2_three_pow_odd_sub_one (r : ℕ) :
    v2 (3 ^ (2 * r + 1) - 1) = 1 := by
  let c := 3 ^ (2 * r + 1) - 1
  have hc4 : c % 4 = 2 := by
    simpa [c] using three_pow_odd_sub_one_mod_four r
  have hcpos : 0 < c := by
    dsimp [c]
    have hp : 1 < 3 ^ (2 * r + 1) := by
      exact one_lt_pow₀ (by omega) (by omega)
    omega
  have hceven : c % 2 = 0 := by omega
  have hhalfodd : (c / 2) % 2 = 1 := by omega
  rw [v2_step_of_even c hceven hcpos, v2_odd _ hhalfodd]

/-- Canonical terminal valuation of the odd-length all-ones first block. -/
@[simp] theorem canonicalBlockTerminalValuation_allOnesOdd_odd_zero
    (r : ℕ) :
    canonicalBlockTerminalValuation
      (allOnesOdd (2 * r + 1) (by omega)) 0 = 1 := by
  unfold canonicalBlockTerminalValuation
  rw [canonicalBlockTerminalCarrier_allOnesOdd_zero]
  exact v2_three_pow_odd_sub_one r

/-- Exact next-start state after an odd-length all-ones initial block. -/
theorem canonicalBlockNextStartState_allOnesOdd_odd_zero
    (r : ℕ) :
    canonicalBlockNextStartState
        (allOnesOdd (2 * r + 1) (by omega)) 0 =
      (3 ^ (2 * r + 1) - 1) / 2 := by
  rw [canonicalBlockNextStartState_eq_terminalCarrier_div_pow_valuation,
    canonicalBlockTerminalCarrier_allOnesOdd_zero,
    canonicalBlockTerminalValuation_allOnesOdd_odd_zero]
  norm_num

/-! ## Growing cross-root drift -/

/-- Binary width of a positive finite all-ones word is its exponent. -/
theorem bitWidth_two_pow_sub_one
    (L : ℕ) (hL : 0 < L) :
    bitWidth (2 ^ L - 1) = L := by
  have hpow : 2 ^ L = 2 ^ (L - 1) * 2 := by
    have hsplit : L = (L - 1) + 1 := by omega
    calc
      2 ^ L = 2 ^ ((L - 1) + 1) := congrArg (fun e => 2 ^ e) hsplit
      _ = 2 ^ (L - 1) * 2 := by rw [pow_succ]
  have hp : 0 < 2 ^ (L - 1) := pow_pos (by norm_num) _
  have hlo : 2 ^ (L - 1) ≤ 2 ^ L - 1 := by omega
  have hhi : 2 ^ L - 1 < 2 ^ ((L - 1) + 1) := by
    have hsplit : L = (L - 1) + 1 := by omega
    rw [← hsplit]
    omega
  have hwidth := bitWidth_eq_add_one_of_pow_le_lt hlo hhi
  omega

/-- Elementary exponential estimate used by the all-ones width lower bound. -/
private theorem two_mul_eight_pow_add_one_le_three_mul_nine_pow
    (r : ℕ) :
    2 * 8 ^ r + 1 ≤ 3 * 9 ^ r := by
  induction r with
  | zero => norm_num
  | succ r ih =>
      rw [pow_succ, pow_succ]
      have hpos : 0 < 9 ^ r := pow_pos (by norm_num) _
      nlinarith

/-- The odd-power carrier dominates the binary scale needed for a linear
width gain. -/
private theorem two_pow_three_mul_add_one_le_three_pow_odd_sub_one
    (r : ℕ) :
    2 ^ (3 * r + 1) ≤ 3 ^ (2 * r + 1) - 1 := by
  have hbase := two_mul_eight_pow_add_one_le_three_mul_nine_pow r
  have htwo : 2 ^ (3 * r + 1) = 2 * 8 ^ r := by
    calc
      2 ^ (3 * r + 1) = 2 ^ (3 * r) * 2 := by rw [pow_succ]
      _ = (2 ^ 3) ^ r * 2 := by rw [pow_mul]
      _ = 2 * 8 ^ r := by norm_num; ring
  have hthree : 3 ^ (2 * r + 1) = 3 * 9 ^ r := by
    calc
      3 ^ (2 * r + 1) = 3 ^ (2 * r) * 3 := by rw [pow_succ]
      _ = (3 ^ 2) ^ r * 3 := by rw [pow_mul]
      _ = 3 * 9 ^ r := by norm_num; ring
  rw [htwo, hthree]
  omega

/-- The next start after the odd all-ones block contains the `2^(3r)` binary
scale. -/
theorem two_pow_three_mul_le_allOnesOdd_nextStart (r : ℕ) :
    2 ^ (3 * r) ≤
      canonicalBlockNextStartState
        (allOnesOdd (2 * r + 1) (by omega)) 0 := by
  rw [canonicalBlockNextStartState_allOnesOdd_odd_zero]
  apply (Nat.le_div_iff_mul_le (by norm_num : 0 < (2 : ℕ))).2
  calc
    2 ^ (3 * r) * 2 = 2 ^ (3 * r + 1) := by rw [pow_succ]
    _ ≤ 3 ^ (2 * r + 1) - 1 :=
      two_pow_three_mul_add_one_le_three_pow_odd_sub_one r

/-- The next-start binary width is at least `3r+1`. -/
theorem three_mul_add_one_le_bitWidth_allOnesOdd_nextStart (r : ℕ) :
    3 * r + 1 ≤ bitWidth
      (canonicalBlockNextStartState
        (allOnesOdd (2 * r + 1) (by omega)) 0) := by
  let x := canonicalBlockNextStartState
    (allOnesOdd (2 * r + 1) (by omega)) 0
  have hlower : 2 ^ (3 * r) ≤ x := by
    simpa [x] using two_pow_three_mul_le_allOnesOdd_nextStart r
  have hxpos : 0 < x := (pow_pos (by norm_num) _).trans_le hlower
  have hlt : 2 ^ (3 * r) < 2 ^ bitWidth x :=
    hlower.trans_lt (lt_pow_bitWidth hxpos)
  have hexp : 3 * r < bitWidth x :=
    (Nat.pow_lt_pow_iff_right Nat.one_lt_two).mp hlt
  change 3 * r + 1 ≤ bitWidth x
  omega

/-- Initial endpoint drift in the odd all-ones family grows at least linearly
with the root parameter. -/
theorem le_endpointAccountingTerm_allOnesOdd_odd_zero (r : ℕ) :
    (r : ℤ) ≤ endpointAccountingTerm
      (allOnesOdd (2 * r + 1) (by omega)) 0 := by
  rw [endpointAccountingTerm_eq_canonicalBlock_bitWidth_sub,
    canonicalBlockNextStartState_allOnesOdd_odd_zero,
    canonicalBlockStartState_allOnesOdd_zero]
  rw [bitWidth_two_pow_sub_one (2 * r + 1) (by omega)]
  have hwidth := three_mul_add_one_le_bitWidth_allOnesOdd_nextStart r
  rw [canonicalBlockNextStartState_allOnesOdd_odd_zero] at hwidth
  omega

/-- Across the family of odd roots, initial endpoint drift exceeds every
integer threshold.  The quantified root depends on `B`; this theorem therefore
does not make a fixed-root assertion. -/
theorem exists_endpointAccountingTerm_gt (B : ℤ) :
    ∃ n : OddNat, B < endpointAccountingTerm n 0 := by
  let r := B.natAbs + 1
  refine ⟨allOnesOdd (2 * r + 1) (by omega), ?_⟩
  have hr : B < (r : ℤ) := by
    have habs : B ≤ |B| := le_abs_self B
    have hcast : (B.natAbs : ℤ) = |B| := by simp
    rw [← hcast] at habs
    simp [r]
    omega
  exact hr.trans_le (le_endpointAccountingTerm_allOnesOdd_odd_zero r)

/-- There is no one endpoint-drift ceiling uniform across every odd root. -/
theorem not_globalEndpointDriftBound :
    ¬ GlobalEndpointDriftBound := by
  rintro ⟨B, hB⟩
  obtain ⟨n, hn⟩ := exists_endpointAccountingTerm_gt B
  have hupper := hB n 0
  omega

/-!
`not_globalEndpointDriftBound` varies the root with `r`.  It does not imply
`¬ RootwiseEndpointDriftBound n` for any fixed `n`; that arithmetic question
remains the exact fixed-root boundary isolated by cp-339.
-/

end DkMath.Collatz
