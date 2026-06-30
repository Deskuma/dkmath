/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Collatz.Accelerated
import DkMath.Collatz.Shift
import DkMath.Petal.RangeFamily

#print "file: DkMath.Collatz.PetalBridge"

/-!
# Collatz Petal Bridge

This file is a small observation window between the accelerated Collatz
dynamics and the Petal range-family API.

The bridge is intentionally thin.  It does not claim any Collatz convergence
or nontrivial cycle theorem.  It only fixes the common language:

```text
accelerated Collatz orbit segment
  -> range-indexed labels
  -> either pairwise separated, or a collision closes that route as False
```

For Petal/ABC routes, a repeated label means that a proposed independent
range-family cannot be counted as `k` independent carriers.  For Collatz
dynamics, the same collision is not merely a failure: it is the observable
shape of a merge, fold, or cycle candidate.
-/

namespace DkMath.Collatz

/--
Raw 2-adic height observation for a natural state.

This is the address-like Collatz quantity:

```text
n -> v2 (3n + 1)
```

For an odd state it is exactly the accelerated Collatz observation `s`.
-/
def rawHeightLabel (n : ℕ) : ℕ :=
  v2 (3 * n + 1)

/--
The finite observation window for the first `k` accelerated Collatz states.

This is intentionally just `Finset.range k`; the point is to give the Collatz
side a named window that can later carry address, height, or statistical
observations.
-/
def OrbitWindow (_n : OddNat) (k : ℕ) : Finset ℕ :=
  Finset.range k

/--
The natural-number label of the `i`-th accelerated Collatz odd state.

This is the Collatz-facing candidate for a Petal `qOf i` label.  It deliberately
forgets the proof that the state is odd and keeps only the observed address
value.
-/
noncomputable def oddOrbitLabel (n : OddNat) (i : ℕ) : ℕ :=
  (iterateT i n).1

/--
The 2-adic height observed at the `i`-th accelerated Collatz odd state.

This is the first address-like label attached to the Collatz observation window.
-/
noncomputable def orbitWindowHeight (n : OddNat) (i : ℕ) : ℕ :=
  rawHeightLabel (oddOrbitLabel n i)

/--
The ordered height profile observed in the first `k` accelerated Collatz
states.

This keeps order, unlike a finite support/image view.  It is the window-level
form of the sequence summed by `sumS`.
-/
noncomputable def orbitWindowHeightSeq (n : OddNat) (k : ℕ) : List ℕ :=
  (List.range k).map (orbitWindowHeight n)

/--
The first `k` accelerated Collatz odd-state labels are pairwise separated.

This is the Collatz-specific spelling of the RangeFamily pairwise condition:
different in-range times have different observed odd states.
-/
def OddOrbitLabelsPairwiseSeparated (n : OddNat) (k : ℕ) : Prop :=
  ∀ i, i < k → ∀ j, j < k → i ≠ j → oddOrbitLabel n i ≠ oddOrbitLabel n j

/--
Window-level spelling of pairwise separation for accelerated Collatz labels.
-/
def OrbitWindowSeparated (n : OddNat) (k : ℕ) : Prop :=
  OddOrbitLabelsPairwiseSeparated n k

/--
Window-level collision: two distinct in-window times have the same accelerated
odd-state label.

For Petal/ABC this blocks independent range counting.  For Collatz dynamics it
is the observable merge/fold/cycle signal.
-/
def OrbitWindowCollision (n : OddNat) (k : ℕ) : Prop :=
  ∃ i j, i < k ∧ j < k ∧ i ≠ j ∧ oddOrbitLabel n i = oddOrbitLabel n j

/--
The named Collatz observation window is definitionally the range window.
-/
theorem orbitWindow_eq_range (n : OddNat) (k : ℕ) :
    OrbitWindow n k = Finset.range k := rfl

/--
Raw height agrees with the existing Collatz observation `s` on odd states.
-/
theorem rawHeightLabel_eq_s (n : OddNat) :
    rawHeightLabel n.1 = s n := rfl

/--
The window height is the existing Collatz observation `s` applied to the
corresponding accelerated state.
-/
theorem orbitWindowHeight_eq_s_iterateT (n : OddNat) (i : ℕ) :
    orbitWindowHeight n i = s (iterateT i n) := rfl

/--
The `v2` observation is at least `2` exactly when `4` divides the observed
nonzero natural.

This is the valuation-to-divisibility bridge used to turn Collatz height
conditions into residue/address conditions.
-/
theorem two_le_v2_iff_four_dvd
    {m : ℕ} (hm : m ≠ 0) :
    2 ≤ v2 m ↔ 4 ∣ m := by
  simpa [v2] using
    (DkMath.ABC.padicValNat_le_iff_dvd Nat.prime_two hm 2)

/--
Raw Collatz height is at least `2` exactly when `4` divides `3n + 1`.
-/
theorem rawHeightLabel_two_le_iff_four_dvd_threeNPlusOne
    (n : ℕ) :
    2 ≤ rawHeightLabel n ↔ 4 ∣ 3 * n + 1 := by
  exact two_le_v2_iff_four_dvd (by omega : 3 * n + 1 ≠ 0)

/--
Orbit-window height is at least `2` exactly when `4` divides the next
`3m + 1` value for the observed odd-state label.
-/
theorem orbitWindowHeight_two_le_iff_four_dvd
    (n : OddNat) (i : ℕ) :
    2 ≤ orbitWindowHeight n i ↔
      4 ∣ 3 * oddOrbitLabel n i + 1 := by
  exact rawHeightLabel_two_le_iff_four_dvd_threeNPlusOne (oddOrbitLabel n i)

/--
For an odd natural `m`, the condition `4 | 3m + 1` is the same as
`m % 4 = 1`.

This is the first residue-address reading of a Collatz height condition.
-/
theorem odd_four_dvd_three_mul_add_one_iff_mod_four_eq_one
    {m : ℕ} (hmOdd : m % 2 = 1) :
    4 ∣ 3 * m + 1 ↔ m % 4 = 1 := by
  constructor
  · intro h
    omega
  · intro h
    omega

/--
`height >= 2` in the Collatz observation window is the same as the current odd
state label lying in residue class `1 mod 4`.
-/
theorem orbitWindowHeight_two_le_iff_mod_four_eq_one
    (n : OddNat) (i : ℕ) :
    2 ≤ orbitWindowHeight n i ↔ oddOrbitLabel n i % 4 = 1 := by
  rw [orbitWindowHeight_two_le_iff_four_dvd]
  exact odd_four_dvd_three_mul_add_one_iff_mod_four_eq_one (iterateT i n).2

/--
The `v2` observation is at least `3` exactly when `8` divides the observed
nonzero natural.

This is the next residue-address experiment after the mod `4` bridge.
-/
theorem three_le_v2_iff_eight_dvd
    {m : ℕ} (hm : m ≠ 0) :
    3 ≤ v2 m ↔ 8 ∣ m := by
  simpa [v2] using
    (DkMath.ABC.padicValNat_le_iff_dvd Nat.prime_two hm 3)

/--
Raw Collatz height is at least `3` exactly when `8` divides `3n + 1`.
-/
theorem rawHeightLabel_three_le_iff_eight_dvd_threeNPlusOne
    (n : ℕ) :
    3 ≤ rawHeightLabel n ↔ 8 ∣ 3 * n + 1 := by
  exact three_le_v2_iff_eight_dvd (by omega : 3 * n + 1 ≠ 0)

/--
For an odd natural `m`, the condition `8 | 3m + 1` is the same as
`m % 8 = 5`.

This records the next residue class after the mod `4` observation.
-/
theorem odd_eight_dvd_three_mul_add_one_iff_mod_eight_eq_five
    {m : ℕ} (hmOdd : m % 2 = 1) :
    8 ∣ 3 * m + 1 ↔ m % 8 = 5 := by
  constructor
  · intro h
    omega
  · intro h
    omega

/--
`height >= 3` in the Collatz observation window is the same as the current odd
state label lying in residue class `5 mod 8`.
-/
theorem orbitWindowHeight_three_le_iff_mod_eight_eq_five
    (n : OddNat) (i : ℕ) :
    3 ≤ orbitWindowHeight n i ↔ oddOrbitLabel n i % 8 = 5 := by
  change 3 ≤ rawHeightLabel (oddOrbitLabel n i) ↔ oddOrbitLabel n i % 8 = 5
  rw [rawHeightLabel_three_le_iff_eight_dvd_threeNPlusOne]
  exact odd_eight_dvd_three_mul_add_one_iff_mod_eight_eq_five (iterateT i n).2

/--
The ordered height profile has length equal to the window size.
-/
theorem orbitWindowHeightSeq_length (n : OddNat) (k : ℕ) :
    (orbitWindowHeightSeq n k).length = k := by
  simp [orbitWindowHeightSeq]

/--
The sum of the ordered height profile is exactly the existing Collatz `sumS`.

This connects the Petal-style finite observation window with the existing
Collatz drift/statistics API.
-/
theorem orbitWindowHeightSeq_sum_eq_sumS (n : OddNat) (k : ℕ) :
    (orbitWindowHeightSeq n k).sum = sumS n k := by
  induction k with
  | zero =>
      simp [orbitWindowHeightSeq, sumS]
  | succ k ih =>
      have ih' :
          (List.map (orbitWindowHeight n) (List.range k)).sum = sumS n k := by
        simpa [orbitWindowHeightSeq] using ih
      simp [orbitWindowHeightSeq, List.range_succ, sumS,
        orbitWindowHeight_eq_s_iterateT, ih']

/--
If every height in the window is at least `threshold`, then the accumulated
Collatz height is at least `k * threshold`.

This is the integer threshold form of an average-height lower bound.  It avoids
real logarithms and keeps the bridge on the combinatorial side.
-/
theorem orbitWindowHeightSeq_sum_ge_of_forall_ge
    (n : OddNat) {k threshold : ℕ}
    (h : ∀ i, i < k → threshold ≤ orbitWindowHeight n i) :
    k * threshold ≤ sumS n k := by
  induction k with
  | zero =>
      simp [sumS]
  | succ k ih =>
      have hprefix : ∀ i, i < k → threshold ≤ orbitWindowHeight n i := by
        intro i hi
        exact h i (Nat.lt_trans hi (Nat.lt_succ_self k))
      have hlast : threshold ≤ orbitWindowHeight n k := h k (Nat.lt_succ_self k)
      have ih' : k * threshold ≤ sumS n k := ih hprefix
      rw [sumS, ← orbitWindowHeight_eq_s_iterateT]
      rw [Nat.succ_mul]
      exact Nat.add_le_add ih' hlast

/--
The prefix of the ordered height profile has sum `sumS n r`, as long as the
prefix length `r` lies inside the ambient window `k`.
-/
theorem orbitWindowHeightSeq_take_sum_eq_sumS
    (n : OddNat) {r k : ℕ} (hr : r ≤ k) :
    ((orbitWindowHeightSeq n k).take r).sum = sumS n r := by
  rw [← orbitWindowHeightSeq_sum_eq_sumS n r]
  simp [orbitWindowHeightSeq, ← List.map_take, List.take_range, Nat.min_eq_left hr]

/--
The prefix of length `r` has length `r` when `r` lies inside the window.
-/
theorem orbitWindowHeightSeq_take_length
    (n : OddNat) {r k : ℕ} (hr : r ≤ k) :
    ((orbitWindowHeightSeq n k).take r).length = r := by
  simp [orbitWindowHeightSeq_length, Nat.min_eq_left hr]

/--
Reading the ordered height profile at an in-window time recovers the pointwise
height observation.
-/
theorem orbitWindowHeightSeq_get?_eq_some
    (n : OddNat) {i k : ℕ} (hi : i < k) :
    (orbitWindowHeightSeq n k)[i]? = some (orbitWindowHeight n i) := by
  simp [orbitWindowHeightSeq, hi]

/--
Reading a prefix of the ordered height profile recovers the same pointwise
height observation while the index remains inside the prefix.
-/
theorem orbitWindowHeightSeq_take_get?_eq_some
    (n : OddNat) {i r k : ℕ} (hi : i < r) (hr : r ≤ k) :
    ((orbitWindowHeightSeq n k).take r)[i]? = some (orbitWindowHeight n i) := by
  rw [List.getElem?_take_of_lt hi]
  exact orbitWindowHeightSeq_get?_eq_some n (Nat.lt_of_lt_of_le hi hr)

/--
The integer threshold lower bound also applies to prefixes.
-/
theorem orbitWindowHeightSeq_prefix_sum_ge_of_forall_ge
    (n : OddNat) {r k threshold : ℕ} (hr : r ≤ k)
    (h : ∀ i, i < r → threshold ≤ orbitWindowHeight n i) :
    r * threshold ≤ ((orbitWindowHeightSeq n k).take r).sum := by
  rw [orbitWindowHeightSeq_take_sum_eq_sumS n hr]
  exact orbitWindowHeightSeq_sum_ge_of_forall_ge n h

/--
Equal Collatz orbit labels have equal height observations.
-/
theorem orbitWindowHeight_eq_of_oddOrbitLabel_eq
    {n : OddNat} {i j : ℕ}
    (hlabel : oddOrbitLabel n i = oddOrbitLabel n j) :
    orbitWindowHeight n i = orbitWindowHeight n j := by
  simp [orbitWindowHeight, hlabel]

/--
A label collision forces equality of the height observations at the colliding
times.

If the orbit has returned to the same odd state, then the next `v2` height read
from that state is also the same.
-/
theorem orbitWindowHeight_eq_of_collision
    {n : OddNat} {k i j : ℕ}
    (_hi : i < k) (_hj : j < k)
    (hlabel : oddOrbitLabel n i = oddOrbitLabel n j) :
    orbitWindowHeight n i = orbitWindowHeight n j :=
  orbitWindowHeight_eq_of_oddOrbitLabel_eq hlabel

/--
Equal accelerated Collatz states have equal height observations.
-/
theorem orbitWindowHeight_eq_of_same_iterateT
    {n : OddNat} {i j : ℕ}
    (hstate : iterateT i n = iterateT j n) :
    orbitWindowHeight n i = orbitWindowHeight n j :=
  orbitWindowHeight_eq_of_oddOrbitLabel_eq (congrArg Subtype.val hstate)

/--
Number of occurrences of an exact height inside the ordered window profile.
-/
noncomputable def orbitWindowHeightCountEq (n : OddNat) (k h : ℕ) : ℕ :=
  (orbitWindowHeightSeq n k).countP (fun x => x == h)

/--
Number of entries whose height is at least `threshold` inside the ordered
window profile.
-/
noncomputable def orbitWindowHeightCountGe (n : OddNat) (k threshold : ℕ) : ℕ :=
  (orbitWindowHeightSeq n k).countP (fun x => decide (threshold ≤ x))

/--
Number of in-window odd-state labels in residue class `1 mod 4`.

This is the residue-address counterpart of `orbitWindowHeightCountGe n k 2`.
-/
noncomputable def orbitWindowResidueCountMod4EqOne
    (n : OddNat) (k : ℕ) : ℕ :=
  (List.range k).countP
    (fun i => decide (oddOrbitLabel n i % 4 = 1))

/--
The exact-height occupation count is bounded by the window size.
-/
theorem orbitWindowHeightCountEq_le_window
    (n : OddNat) (k h : ℕ) :
    orbitWindowHeightCountEq n k h ≤ k := by
  unfold orbitWindowHeightCountEq
  simpa [orbitWindowHeightSeq_length] using
    (List.countP_le_length (p := fun x => x == h) (l := orbitWindowHeightSeq n k))

/--
The threshold occupation count is bounded by the window size.
-/
theorem orbitWindowHeightCountGe_le_window
    (n : OddNat) (k threshold : ℕ) :
    orbitWindowHeightCountGe n k threshold ≤ k := by
  unfold orbitWindowHeightCountGe
  simpa [orbitWindowHeightSeq_length] using
    (List.countP_le_length
      (p := fun x => decide (threshold ≤ x)) (l := orbitWindowHeightSeq n k))

/--
The mod `4` residue count is bounded by the window size.
-/
theorem orbitWindowResidueCountMod4EqOne_le_window
    (n : OddNat) (k : ℕ) :
    orbitWindowResidueCountMod4EqOne n k ≤ k := by
  unfold orbitWindowResidueCountMod4EqOne
  simpa using
    (List.countP_le_length
      (p := fun i => decide (oddOrbitLabel n i % 4 = 1)) (l := List.range k))

/--
Counting `height >= 2` entries is the same as counting odd-state labels in
residue class `1 mod 4`.

This turns the second Collatz height layer into a residue-address occupation
count.
-/
theorem orbitWindowHeightCountGe_two_eq_residueCount_mod4_eq_one
    (n : OddNat) (k : ℕ) :
    orbitWindowHeightCountGe n k 2 =
      orbitWindowResidueCountMod4EqOne n k := by
  unfold orbitWindowHeightCountGe orbitWindowResidueCountMod4EqOne orbitWindowHeightSeq
  induction k with
  | zero =>
      simp
  | succ k ih =>
      rw [List.range_succ]
      have hiff := orbitWindowHeight_two_le_iff_mod_four_eq_one n k
      by_cases hheight : 2 ≤ orbitWindowHeight n k
      · have hres : oddOrbitLabel n k % 4 = 1 := hiff.mp hheight
        simp [ih, hheight, hres]
      · have hres : oddOrbitLabel n k % 4 ≠ 1 := by
          intro h
          exact hheight (hiff.mpr h)
        simp [ih, hheight, hres]

/--
If every in-window height is exactly `h`, then the exact-height occupation
count fills the whole window.
-/
theorem orbitWindowHeightCountEq_eq_window_of_forall_eq
    (n : OddNat) {k h : ℕ}
    (hall : ∀ i, i < k → orbitWindowHeight n i = h) :
    orbitWindowHeightCountEq n k h = k := by
  unfold orbitWindowHeightCountEq orbitWindowHeightSeq
  induction k with
  | zero =>
      simp
  | succ k ih =>
      have hprefix : ∀ i, i < k → orbitWindowHeight n i = h := by
        intro i hi
        exact hall i (Nat.lt_trans hi (Nat.lt_succ_self k))
      have hlast : orbitWindowHeight n k = h := hall k (Nat.lt_succ_self k)
      simp [List.range_succ, ih hprefix, hlast]

/--
If every in-window height is at least `threshold`, then the threshold
occupation count fills the whole window.
-/
theorem orbitWindowHeightCountGe_eq_window_of_forall_ge
    (n : OddNat) {k threshold : ℕ}
    (hall : ∀ i, i < k → threshold ≤ orbitWindowHeight n i) :
    orbitWindowHeightCountGe n k threshold = k := by
  unfold orbitWindowHeightCountGe orbitWindowHeightSeq
  induction k with
  | zero =>
      simp
  | succ k ih =>
      have hprefix : ∀ i, i < k → threshold ≤ orbitWindowHeight n i := by
        intro i hi
        exact hall i (Nat.lt_trans hi (Nat.lt_succ_self k))
      have hlast : threshold ≤ orbitWindowHeight n k := hall k (Nat.lt_succ_self k)
      simp [List.range_succ, ih hprefix, hlast]

/--
The `height >= threshold` occupation count gives a direct lower bound for the
accumulated Collatz height.

If `c` entries in the window have height at least `threshold`, then those
entries alone contribute at least `c * threshold` to `sumS`.
-/
theorem orbitWindowHeightSeq_sum_ge_countGe_mul_threshold
    (n : OddNat) (k threshold : ℕ) :
    orbitWindowHeightCountGe n k threshold * threshold ≤ sumS n k := by
  induction k with
  | zero =>
      simp [orbitWindowHeightCountGe, orbitWindowHeightSeq, sumS]
  | succ k ih =>
      have ih' :
          List.countP ((fun x => decide (threshold ≤ x)) ∘ orbitWindowHeight n)
              (List.range k) * threshold ≤ sumS n k := by
        simpa [orbitWindowHeightCountGe, orbitWindowHeightSeq] using ih
      by_cases hlast : threshold ≤ orbitWindowHeight n k
      · rw [sumS, ← orbitWindowHeight_eq_s_iterateT]
        unfold orbitWindowHeightCountGe orbitWindowHeightSeq
        rw [List.range_succ]
        simp only [List.map_append, List.map_cons, List.map_nil, List.countP_append,
          List.countP_map, List.countP_singleton, decide_eq_true_eq, ge_iff_le,
          hlast, if_true, Nat.add_mul, one_mul]
        exact Nat.add_le_add ih' hlast
      · rw [sumS, ← orbitWindowHeight_eq_s_iterateT]
        unfold orbitWindowHeightCountGe orbitWindowHeightSeq
        rw [List.range_succ]
        simp only [List.map_append, List.map_cons, List.map_nil, List.countP_append,
          List.countP_map, List.countP_singleton, decide_eq_true_eq, ge_iff_le,
          hlast, if_false, Nat.add_zero]
        exact Nat.le_add_right_of_le ih'

/--
The exact-height count is bounded by the corresponding threshold count.

Every entry with height exactly `h` is also an entry with height at least `h`.
-/
theorem orbitWindowHeightCountEq_le_countGe
    (n : OddNat) (k h : ℕ) :
    orbitWindowHeightCountEq n k h ≤ orbitWindowHeightCountGe n k h := by
  unfold orbitWindowHeightCountEq orbitWindowHeightCountGe orbitWindowHeightSeq
  induction k with
  | zero =>
      simp
  | succ k ih =>
      have ih' :
          List.countP ((fun x => x == h) ∘ orbitWindowHeight n) (List.range k) ≤
            List.countP ((fun x => decide (h ≤ x)) ∘ orbitWindowHeight n)
              (List.range k) := by
        simpa [List.countP_map] using ih
      by_cases hlast : orbitWindowHeight n k = h
      · rw [List.range_succ]
        have hself : h ≤ h := le_rfl
        simp only [List.map_append, List.map_cons, List.map_nil, List.countP_append,
          List.countP_map, List.countP_singleton, beq_iff_eq, decide_eq_true_eq,
          ge_iff_le, hlast, hself, if_true]
        exact Nat.add_le_add ih' le_rfl
      · rw [List.range_succ]
        simp only [List.map_append, List.map_cons, List.map_nil, List.countP_append,
          List.countP_map, List.countP_singleton, beq_iff_eq, decide_eq_true_eq,
          ge_iff_le, hlast, if_false]
        exact Nat.le_add_right_of_le ih'

/--
The exact-height occupation count gives a direct lower bound for the
accumulated Collatz height.

If `c` entries in the window have height exactly `h`, then those entries alone
contribute `c * h` to the lower-bound side.
-/
theorem orbitWindowHeightSeq_sum_ge_countEq_mul_height
    (n : OddNat) (k h : ℕ) :
    orbitWindowHeightCountEq n k h * h ≤ sumS n k := by
  exact le_trans
    (Nat.mul_le_mul_right h (orbitWindowHeightCountEq_le_countGe n k h))
    (orbitWindowHeightSeq_sum_ge_countGe_mul_threshold n k h)

/--
Threshold occupation count inside a prefix of an ambient ordered window.

The argument order keeps the ambient window size `k` visible, because callers
often work inside one large observation window and then inspect a prefix.
-/
noncomputable def orbitWindowHeightPrefixCountGe
    (n : OddNat) (k r threshold : ℕ) : ℕ :=
  ((orbitWindowHeightSeq n k).take r).countP
    (fun x => decide (threshold ≤ x))

/--
Prefix threshold occupation agrees with the standalone count for the prefix
length, as long as the prefix lies inside the ambient window.
-/
theorem orbitWindowHeightPrefixCountGe_eq_countGe
    (n : OddNat) {r k threshold : ℕ} (hr : r ≤ k) :
    orbitWindowHeightPrefixCountGe n k r threshold =
      orbitWindowHeightCountGe n r threshold := by
  unfold orbitWindowHeightPrefixCountGe orbitWindowHeightCountGe
  simp [orbitWindowHeightSeq, ← List.map_take, List.take_range, Nat.min_eq_left hr]

/--
Prefix threshold occupation gives a lower bound for the corresponding partial
Collatz accumulated height.
-/
theorem orbitWindowHeightPrefixCountGe_mul_le_sumS
    (n : OddNat) {r k threshold : ℕ} (hr : r ≤ k) :
    orbitWindowHeightPrefixCountGe n k r threshold * threshold ≤ sumS n r := by
  rw [orbitWindowHeightPrefixCountGe_eq_countGe n hr]
  exact orbitWindowHeightSeq_sum_ge_countGe_mul_threshold n r threshold

/--
Minimal finite layer-cake lower bound for the first two height layers.

Each entry with height at least `1` contributes one unit, and each entry with
height at least `2` contributes one more unit.  This is the first local
occupation-measure form of the Collatz drift lower-bound engine.
-/
theorem orbitWindowHeightSeq_sum_ge_countGe_one_add_countGe_two
    (n : OddNat) (k : ℕ) :
    orbitWindowHeightCountGe n k 1 + orbitWindowHeightCountGe n k 2 ≤
      sumS n k := by
  induction k with
  | zero =>
      simp [orbitWindowHeightCountGe, orbitWindowHeightSeq, sumS]
  | succ k ih =>
      have ih' :
          List.countP ((fun x => decide (1 ≤ x)) ∘ orbitWindowHeight n)
              (List.range k) +
            List.countP ((fun x => decide (2 ≤ x)) ∘ orbitWindowHeight n)
              (List.range k) ≤ sumS n k := by
        simpa [orbitWindowHeightCountGe, orbitWindowHeightSeq] using ih
      by_cases htwo : 2 ≤ orbitWindowHeight n k
      · have hone : 1 ≤ orbitWindowHeight n k := Nat.le_trans (by decide) htwo
        rw [sumS, ← orbitWindowHeight_eq_s_iterateT]
        unfold orbitWindowHeightCountGe orbitWindowHeightSeq
        rw [List.range_succ]
        simp only [List.map_append, List.map_cons, List.map_nil, List.countP_append,
          List.countP_map, List.countP_singleton, decide_eq_true_eq, ge_iff_le,
          hone, htwo, if_true]
        omega
      · by_cases hone : 1 ≤ orbitWindowHeight n k
        · rw [sumS, ← orbitWindowHeight_eq_s_iterateT]
          unfold orbitWindowHeightCountGe orbitWindowHeightSeq
          rw [List.range_succ]
          simp only [List.map_append, List.map_cons, List.map_nil, List.countP_append,
            List.countP_map, List.countP_singleton, decide_eq_true_eq, ge_iff_le,
            hone, htwo, if_true, if_false]
          omega
        · rw [sumS, ← orbitWindowHeight_eq_s_iterateT]
          unfold orbitWindowHeightCountGe orbitWindowHeightSeq
          rw [List.range_succ]
          simp only [List.map_append, List.map_cons, List.map_nil, List.countP_append,
            List.countP_map, List.countP_singleton, decide_eq_true_eq, ge_iff_le,
            hone, htwo, if_false]
          exact Nat.le_add_right_of_le ih'

/--
Every accelerated Collatz odd state has height at least `1`.

This is the observation-window spelling of `v2_3n_plus_1_ge_1`: for an odd
state, `3n + 1` is even, so at least one factor of `2` is peeled off.
-/
theorem orbitWindowHeight_one_le
    (n : OddNat) (i : ℕ) :
    1 ≤ orbitWindowHeight n i := by
  rw [orbitWindowHeight_eq_s_iterateT]
  simpa [s, threeNPlusOne] using
    v2_3n_plus_1_ge_1 (iterateT i n).1 (iterateT i n).2

/--
The `height >= 1` occupation count fills the whole observation window.

For Collatz odd-state dynamics, every accelerated step peels off at least one
factor of `2`.
-/
theorem orbitWindowHeightCountGe_one_eq_window
    (n : OddNat) (k : ℕ) :
    orbitWindowHeightCountGe n k 1 = k :=
  orbitWindowHeightCountGe_eq_window_of_forall_ge n
    (by
      intro i _hi
      exact orbitWindowHeight_one_le n i)

/--
Collatz-specific two-layer drift lower bound.

The first layer contributes one unit at every step.  The second layer counts
the steps where at least one additional factor of `2` is peeled off.
-/
theorem orbitWindowHeightSeq_sum_ge_window_add_countGe_two
    (n : OddNat) (k : ℕ) :
    k + orbitWindowHeightCountGe n k 2 ≤ sumS n k := by
  simpa [orbitWindowHeightCountGe_one_eq_window n k] using
    orbitWindowHeightSeq_sum_ge_countGe_one_add_countGe_two n k

/--
The prefix `height >= 1` count fills the prefix length.
-/
theorem orbitWindowHeightPrefixCountGe_one_eq
    (n : OddNat) {r k : ℕ} (hr : r ≤ k) :
    orbitWindowHeightPrefixCountGe n k r 1 = r := by
  rw [orbitWindowHeightPrefixCountGe_eq_countGe n hr]
  exact orbitWindowHeightCountGe_one_eq_window n r

/--
Prefix version of the Collatz-specific two-layer drift lower bound.

Inside a larger observation window, the first `r` steps contribute at least
`r`, plus one more unit for every prefix step whose height is at least `2`.
-/
theorem orbitWindowHeightPrefix_sum_ge_window_add_countGe_two
    (n : OddNat) {r k : ℕ} (hr : r ≤ k) :
    r + orbitWindowHeightPrefixCountGe n k r 2 ≤ sumS n r := by
  rw [orbitWindowHeightPrefixCountGe_eq_countGe n hr]
  simpa [orbitWindowHeightCountGe_one_eq_window n r] using
    orbitWindowHeightSeq_sum_ge_countGe_one_add_countGe_two n r

/--
Threshold occupation is antitone in the threshold.

Raising the threshold can only remove entries from the counted regime.
-/
theorem orbitWindowHeightCountGe_antitone
    (n : OddNat) (k : ℕ) {a b : ℕ}
    (hab : a ≤ b) :
    orbitWindowHeightCountGe n k b ≤ orbitWindowHeightCountGe n k a := by
  unfold orbitWindowHeightCountGe orbitWindowHeightSeq
  induction k with
  | zero =>
      simp
  | succ k ih =>
      have ih' :
          List.countP ((fun x => decide (b ≤ x)) ∘ orbitWindowHeight n)
              (List.range k) ≤
            List.countP ((fun x => decide (a ≤ x)) ∘ orbitWindowHeight n)
              (List.range k) := by
        simpa [List.countP_map] using ih
      by_cases hb : b ≤ orbitWindowHeight n k
      · have ha : a ≤ orbitWindowHeight n k := le_trans hab hb
        rw [List.range_succ]
        simp only [List.map_append, List.map_cons, List.map_nil, List.countP_append,
          List.countP_map, List.countP_singleton, decide_eq_true_eq, ge_iff_le,
          hb, ha, if_true]
        exact Nat.add_le_add ih' le_rfl
      · rw [List.range_succ]
        simp only [List.map_append, List.map_cons, List.map_nil, List.countP_append,
          List.countP_map, List.countP_singleton, decide_eq_true_eq, ge_iff_le,
          hb, if_false]
        exact Nat.le_add_right_of_le ih'

/--
Experimental finite layer-cake lower bound for the first three height layers.

This extends the two-layer theorem by adding the `height >= 3` occupation
layer.  It is intentionally concrete: if this shape remains useful, the next
step is a general finite layer-cake theorem over `Finset.range H`.
-/
theorem orbitWindowHeightSeq_sum_ge_countGe_one_add_countGe_two_add_countGe_three
    (n : OddNat) (k : ℕ) :
    orbitWindowHeightCountGe n k 1 + orbitWindowHeightCountGe n k 2 +
        orbitWindowHeightCountGe n k 3 ≤ sumS n k := by
  induction k with
  | zero =>
      simp [orbitWindowHeightCountGe, orbitWindowHeightSeq, sumS]
  | succ k ih =>
      have ih' :
          List.countP ((fun x => decide (1 ≤ x)) ∘ orbitWindowHeight n)
              (List.range k) +
              List.countP ((fun x => decide (2 ≤ x)) ∘ orbitWindowHeight n)
                (List.range k) +
            List.countP ((fun x => decide (3 ≤ x)) ∘ orbitWindowHeight n)
              (List.range k) ≤ sumS n k := by
        simpa [orbitWindowHeightCountGe, orbitWindowHeightSeq] using ih
      by_cases hthree : 3 ≤ orbitWindowHeight n k
      · have htwo : 2 ≤ orbitWindowHeight n k := Nat.le_trans (by decide) hthree
        have hone : 1 ≤ orbitWindowHeight n k := Nat.le_trans (by decide) htwo
        rw [sumS, ← orbitWindowHeight_eq_s_iterateT]
        unfold orbitWindowHeightCountGe orbitWindowHeightSeq
        rw [List.range_succ]
        simp only [List.map_append, List.map_cons, List.map_nil, List.countP_append,
          List.countP_map, List.countP_singleton, decide_eq_true_eq, ge_iff_le,
          hone, htwo, hthree, if_true]
        omega
      · by_cases htwo : 2 ≤ orbitWindowHeight n k
        · have hone : 1 ≤ orbitWindowHeight n k := Nat.le_trans (by decide) htwo
          rw [sumS, ← orbitWindowHeight_eq_s_iterateT]
          unfold orbitWindowHeightCountGe orbitWindowHeightSeq
          rw [List.range_succ]
          simp only [List.map_append, List.map_cons, List.map_nil, List.countP_append,
            List.countP_map, List.countP_singleton, decide_eq_true_eq, ge_iff_le,
            hone, htwo, hthree, if_true, if_false]
          omega
        · by_cases hone : 1 ≤ orbitWindowHeight n k
          · rw [sumS, ← orbitWindowHeight_eq_s_iterateT]
            unfold orbitWindowHeightCountGe orbitWindowHeightSeq
            rw [List.range_succ]
            simp only [List.map_append, List.map_cons, List.map_nil, List.countP_append,
              List.countP_map, List.countP_singleton, decide_eq_true_eq, ge_iff_le,
              hone, htwo, hthree, if_true, if_false]
            omega
          · rw [sumS, ← orbitWindowHeight_eq_s_iterateT]
            unfold orbitWindowHeightCountGe orbitWindowHeightSeq
            rw [List.range_succ]
            simp only [List.map_append, List.map_cons, List.map_nil, List.countP_append,
              List.countP_map, List.countP_singleton, decide_eq_true_eq, ge_iff_le,
              hone, htwo, hthree, if_false]
            exact Nat.le_add_right_of_le ih'

/--
Only `x` of the positive thresholds can be visible below a natural height `x`.

This is the local counting fact behind the finite layer-cake theorem: among
the thresholds `1, 2, ..., H`, at most `x` thresholds are `<= x`.
-/
private theorem range_threshold_count_le
    (H x : ℕ) :
    ((Finset.range H).filter (fun t => t + 1 ≤ x)).card ≤ x := by
  calc
    ((Finset.range H).filter (fun t => t + 1 ≤ x)).card
        ≤ (Finset.range x).card := by
          apply Finset.card_le_card
          intro t ht
          have htx : t + 1 ≤ x := (Finset.mem_filter.mp ht).2
          have htlt : t < x := Nat.lt_of_succ_le htx
          simpa using htlt
    _ = x := by
      simp

/--
Finite layer-cake lower bound for a list of natural heights.

The sum of threshold occupations over thresholds `1, ..., H` is bounded by the
ordinary sum of the list.  This is Collatz-independent and keeps the finite
counting engine separate from the orbit-window vocabulary.
-/
private theorem list_sum_ge_sum_countGe_range
    (l : List ℕ) (H : ℕ) :
    (Finset.range H).sum
        (fun t => l.countP (fun x => decide (t + 1 ≤ x)))
      ≤ l.sum := by
  induction l with
  | nil =>
      simp
  | cons x xs ih =>
      have hhead :
          (Finset.range H).sum (fun t => if t + 1 ≤ x then 1 else 0) ≤ x := by
        calc
          (Finset.range H).sum (fun t => if t + 1 ≤ x then 1 else 0)
              = ((Finset.range H).filter (fun t => t + 1 ≤ x)).card := by
                simp
          _ ≤ x := range_threshold_count_le H x
      calc
        (Finset.range H).sum
            (fun t => (x :: xs).countP (fun y => decide (t + 1 ≤ y)))
            =
          (Finset.range H).sum (fun t => (if t + 1 ≤ x then 1 else 0) +
              xs.countP (fun y => decide (t + 1 ≤ y))) := by
              apply Finset.sum_congr rfl
              intro t _ht
              by_cases ht : t < x
              · have ht' : t + 1 ≤ x := Nat.succ_le_iff.mpr ht
                simp [ht, ht', Nat.add_comm]
              · have ht' : ¬ t + 1 ≤ x := by
                  intro h
                  exact ht (Nat.lt_of_succ_le h)
                simp [ht, ht']
        _ =
          (Finset.range H).sum (fun t => if t + 1 ≤ x then 1 else 0) +
            (Finset.range H).sum
              (fun t => xs.countP (fun y => decide (t + 1 ≤ y))) := by
              rw [Finset.sum_add_distrib]
        _ ≤ x + xs.sum := Nat.add_le_add hhead ih
        _ = (x :: xs).sum := by
          simp

/--
General finite layer-cake lower bound for the ordered Collatz height profile.

The first `H` threshold occupation layers are jointly bounded by the accumulated
Collatz height `sumS`.
-/
theorem orbitWindowHeightSeq_sum_ge_sum_countGe_range
    (n : OddNat) (k H : ℕ) :
    (Finset.range H).sum
        (fun t => orbitWindowHeightCountGe n k (t + 1))
      ≤ sumS n k := by
  have h := list_sum_ge_sum_countGe_range (orbitWindowHeightSeq n k) H
  rw [orbitWindowHeightSeq_sum_eq_sumS n k] at h
  simpa [orbitWindowHeightCountGe] using h

/--
Four-layer finite layer-cake lower bound, now derived from the general theorem.

This is kept as an explicit experiment witness: the fixed-depth layer lemmas no
longer need independent induction proofs once the general finite layer-cake
theorem is available.
-/
theorem orbitWindowHeightSeq_sum_ge_countGe_one_add_countGe_two_add_countGe_three_add_countGe_four
    (n : OddNat) (k : ℕ) :
    orbitWindowHeightCountGe n k 1 + orbitWindowHeightCountGe n k 2 +
        orbitWindowHeightCountGe n k 3 + orbitWindowHeightCountGe n k 4 ≤
      sumS n k := by
  have h := orbitWindowHeightSeq_sum_ge_sum_countGe_range n k 4
  norm_num [Finset.sum_range_succ, Nat.add_assoc] at h
  simpa [Nat.add_assoc] using h

/--
Prefix version of the finite layer-cake lower bound.

Inside an ambient `k`-window, the first `r` observations have the same finite
layer-cake budget as the standalone `r`-window.
-/
theorem orbitWindowHeightPrefix_sum_ge_sum_countGe_range
    (n : OddNat) {r k H : ℕ} (hr : r ≤ k) :
    (Finset.range H).sum
        (fun t => orbitWindowHeightPrefixCountGe n k r (t + 1))
      ≤ sumS n r := by
  have h := orbitWindowHeightSeq_sum_ge_sum_countGe_range n r H
  simpa [orbitWindowHeightPrefixCountGe_eq_countGe n hr] using h

/--
Collatz-specific finite layer-cake tail bound.

The first layer is always the full window size `k`; the remaining finite
layers measure additional peeling events.
-/
theorem orbitWindowHeightSeq_sum_ge_window_add_sum_countGe_tail
    (n : OddNat) (k H : ℕ) :
    k + (Finset.range H).sum
        (fun t => orbitWindowHeightCountGe n k (t + 2))
      ≤ sumS n k := by
  simpa [Finset.sum_range_succ', orbitWindowHeightCountGe_one_eq_window n k,
    Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    orbitWindowHeightSeq_sum_ge_sum_countGe_range n k (H + 1)

/--
Prefix version of the Collatz-specific finite layer-cake tail bound.
-/
theorem orbitWindowHeightPrefix_sum_ge_window_add_sum_countGe_tail
    (n : OddNat) {r k H : ℕ} (hr : r ≤ k) :
    r + (Finset.range H).sum
        (fun t => orbitWindowHeightPrefixCountGe n k r (t + 2))
      ≤ sumS n r := by
  simpa [Finset.sum_range_succ', orbitWindowHeightPrefixCountGe_one_eq n hr,
    Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    orbitWindowHeightPrefix_sum_ge_sum_countGe_range n (r := r) (k := k) (H := H + 1) hr

/--
If at least `m` observations have height `>= 2`, then the accumulated height is
at least `k + m`.
-/
theorem orbitWindowHeightSeq_sum_ge_window_add_of_countGe_two_ge
    (n : OddNat) (k m : ℕ)
    (hm : m ≤ orbitWindowHeightCountGe n k 2) :
    k + m ≤ sumS n k := by
  exact le_trans
    (Nat.add_le_add_left hm k)
    (orbitWindowHeightSeq_sum_ge_window_add_countGe_two n k)

/--
Residue-address drift bridge.

If at least `m` labels in the window lie in residue class `1 mod 4`, then the
second height layer has at least `m` entries, and therefore `sumS n k` is at
least `k + m`.
-/
theorem orbitWindowHeightSeq_sum_ge_window_add_of_residue_mod4_count_ge
    (n : OddNat) (k m : ℕ)
    (hm : m ≤ orbitWindowResidueCountMod4EqOne n k) :
    k + m ≤ sumS n k := by
  rw [← orbitWindowHeightCountGe_two_eq_residueCount_mod4_eq_one n k] at hm
  exact orbitWindowHeightSeq_sum_ge_window_add_of_countGe_two_ge n k m hm

/--
Prefix version: a lower bound on the prefix `height >= 2` occupation gives a
local drift lower bound.
-/
theorem orbitWindowHeightPrefix_sum_ge_window_add_of_countGe_two_ge
    (n : OddNat) {r k m : ℕ} (hr : r ≤ k)
    (hm : m ≤ orbitWindowHeightPrefixCountGe n k r 2) :
    r + m ≤ sumS n r := by
  exact le_trans
    (Nat.add_le_add_left hm r)
    (orbitWindowHeightPrefix_sum_ge_window_add_countGe_two n hr)

/--
Block shifts preserve the raw height when the observed height is below the
block exponent.

This is `v2_shift_invariant` in the observation-window vocabulary.  It is the
first stable bridge from Collatz shift invariance to a Petal-style address
reading: inside a sufficiently large `2^k` block, the height label is conserved.
-/
theorem rawHeightLabel_shift_eq
    (k m n : ℕ)
    (hk : rawHeightLabel n < k) :
    rawHeightLabel (shift k m n) = rawHeightLabel n :=
  v2_shift_invariant k m n hk

/--
Pairwise separated Collatz orbit labels give the Petal range-label injectivity
condition.
-/
theorem oddOrbitLabel_injOn_of_pairwiseSeparated
    (n : OddNat) {k : ℕ}
    (hsep : OddOrbitLabelsPairwiseSeparated n k) :
    Set.InjOn (oddOrbitLabel n) ↑(Finset.range k) :=
  DkMath.Petal.rangeLabel_injOn_of_pairwise_ne hsep

/--
Equal Collatz odd-state labels identify the accelerated states themselves.

Since `OddNat` is a subtype of natural numbers, equality of the stored natural
value is equality of the subtype state.
-/
theorem iterateT_eq_of_oddOrbitLabel_eq
    {n : OddNat} {i j : ℕ}
    (hlabel : oddOrbitLabel n i = oddOrbitLabel n j) :
    iterateT i n = iterateT j n := by
  apply Subtype.ext
  exact hlabel

/--
False/obstruction window for Collatz orbit labels.

If an orbit segment is assumed pairwise separated but two distinct in-range
times have the same odd-state label, the independent Petal range route closes
as `False`.
-/
theorem oddOrbitLabelsPairwiseSeparated_contradiction_of_same_label_ne_index
    {n : OddNat} {k i j : ℕ}
    (hsep : OddOrbitLabelsPairwiseSeparated n k)
    (hi : i < k) (hj : j < k)
    (hlabel : oddOrbitLabel n i = oddOrbitLabel n j)
    (hne : i ≠ j) :
    False :=
  DkMath.Petal.rangeLabel_pairwise_ne_contradiction_of_same_label_ne_index
    hsep hi hj hlabel hne

/--
Collision observation form.

When two different in-range Collatz times have the same label, they are the
same accelerated odd state.  This theorem does not call that good or bad:
Petal/ABC reads it as an independence obstruction, while Collatz reads it as a
merge/fold/cycle candidate.
-/
theorem same_iterateT_of_oddOrbitLabel_collision
    {n : OddNat} {k i j : ℕ}
    (_hi : i < k) (_hj : j < k)
    (hlabel : oddOrbitLabel n i = oddOrbitLabel n j) :
    iterateT i n = iterateT j n :=
  iterateT_eq_of_oddOrbitLabel_eq hlabel

/--
A window collision identifies the two accelerated Collatz states at the
colliding times.
-/
theorem exists_same_iterateT_of_orbitWindowCollision
    {n : OddNat} {k : ℕ}
    (hcollision : OrbitWindowCollision n k) :
    ∃ i j, i < k ∧ j < k ∧ i ≠ j ∧ iterateT i n = iterateT j n := by
  rcases hcollision with ⟨i, j, hi, hj, hne, hlabel⟩
  exact ⟨i, j, hi, hj, hne, iterateT_eq_of_oddOrbitLabel_eq hlabel⟩

/--
Separated windows have no collision.
-/
theorem not_orbitWindowCollision_of_separated
    {n : OddNat} {k : ℕ}
    (hsep : OrbitWindowSeparated n k) :
    ¬ OrbitWindowCollision n k := by
  intro hcollision
  rcases hcollision with ⟨i, j, hi, hj, hne, hlabel⟩
  exact (hsep i hi j hj hne) hlabel

/--
A collision closes the separated-window route as `False`.
-/
theorem orbitWindowSeparated_contradiction_of_collision
    {n : OddNat} {k : ℕ}
    (hsep : OrbitWindowSeparated n k)
    (hcollision : OrbitWindowCollision n k) :
    False :=
  not_orbitWindowCollision_of_separated hsep hcollision

/--
Finite observation split: an accelerated Collatz window is either pairwise
separated, or it contains a collision.

This is not a convergence statement.  It only names the two basic observation
modes for a finite window.
-/
theorem orbitWindowSeparated_or_collision
    (n : OddNat) (k : ℕ) :
    OrbitWindowSeparated n k ∨ OrbitWindowCollision n k := by
  classical
  by_cases hsep : OrbitWindowSeparated n k
  · exact Or.inl hsep
  · right
    unfold OrbitWindowSeparated OddOrbitLabelsPairwiseSeparated at hsep
    push Not at hsep
    rcases hsep with ⟨i, hi, j, hj, hne, hlabel⟩
    exact ⟨i, j, hi, hj, hne, hlabel⟩

end DkMath.Collatz
