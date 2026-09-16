/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Collatz.PetalBridge.PressureCounts

#print "file: DkMath.Collatz.PetalBridge.HeightBudget"

namespace DkMath.Collatz


/--
The prefix mod `4` residue count is bounded by the prefix length.
-/
theorem orbitWindowPrefixResidueCountMod4EqOne_le_prefix
    (n : OddNat) (k r : ℕ) :
    orbitWindowPrefixResidueCountMod4EqOne n k r ≤ r := by
  unfold orbitWindowPrefixResidueCountMod4EqOne
  exact le_trans
    (List.countP_le_length
      (p := fun i => decide (oddOrbitLabel n i % 4 = 1))
      (l := (List.range k).take r))
    (by simp)

/--
Prefix mod `4` residue occupation agrees with the standalone count for the
prefix length, as long as the prefix lies inside the ambient window.
-/
theorem orbitWindowPrefixResidueCountMod4EqOne_eq_residueCount
    (n : OddNat) {r k : ℕ} (hr : r ≤ k) :
    orbitWindowPrefixResidueCountMod4EqOne n k r =
      orbitWindowResidueCountMod4EqOne n r := by
  unfold orbitWindowPrefixResidueCountMod4EqOne orbitWindowResidueCountMod4EqOne
  simp [List.take_range, Nat.min_eq_left hr]

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
Tail `height >= 2` occupation is the same as shifted-tail residue occupation
in class `1 mod 4`.
-/
theorem orbitWindowHeightCountGeTail_two_eq_tailResidueCount_mod4_eq_one
    (n : OddNat) (k : ℕ) :
    orbitWindowHeightCountGeTail n k 2 =
      orbitWindowResidueCountMod4EqOneTail n k := by
  unfold orbitWindowHeightCountGeTail orbitWindowResidueCountMod4EqOneTail
  induction k with
  | zero =>
      simp
  | succ k ih =>
      rw [List.range_succ]
      have hiff := orbitWindowHeight_two_le_iff_mod_four_eq_one n (k + 1)
      by_cases hheight : 2 ≤ orbitWindowHeight n (k + 1)
      · have hres : oddOrbitLabel n (k + 1) % 4 = 1 := hiff.mp hheight
        simp [ih, hheight, hres]
      · have hres : oddOrbitLabel n (k + 1) % 4 ≠ 1 := by
          intro h
          exact hheight (hiff.mpr h)
        simp [ih, hheight, hres]

/--
At parent depth `1`, shifted-tail recovery sibling mass is exactly the
shifted-tail `1 mod 4` cell.
-/
theorem tailRecoveryMass_depth_one_eq_tailResidueCount_mod4_eq_one
    (n : OddNat) (k : ℕ) :
    orbitWindowRecoverySiblingMassPow2Tail n k 1 =
      orbitWindowResidueCountMod4EqOneTail n k := by
  unfold orbitWindowRecoverySiblingMassPow2Tail
  unfold orbitWindowResidueCountPow2Tail
  unfold orbitWindowResidueCountMod4EqOneTail
  simp

/--
At parent depth `1`, shifted-tail recovery sibling mass is contained in the
tail `height >= 2` count.
-/
theorem tailRecoveryMass_depth_one_le_heightCountGe_two
    (n : OddNat) (k : ℕ) :
    orbitWindowRecoverySiblingMassPow2Tail n k 1 ≤
      orbitWindowHeightCountGeTail n k 2 := by
  rw [tailRecoveryMass_depth_one_eq_tailResidueCount_mod4_eq_one]
  rw [orbitWindowHeightCountGeTail_two_eq_tailResidueCount_mod4_eq_one]

/--
Counting `height >= 3` entries is the same as counting odd-state labels in
residue class `5 mod 8`.

This is the mod `8` analogue of the second-layer residue occupation theorem.
-/
theorem orbitWindowHeightCountGe_three_eq_residueCount_mod8_eq_five
    (n : OddNat) (k : ℕ) :
    orbitWindowHeightCountGe n k 3 =
      orbitWindowResidueCountMod8EqFive n k := by
  unfold orbitWindowHeightCountGe orbitWindowResidueCountMod8EqFive orbitWindowHeightSeq
  induction k with
  | zero =>
      simp
  | succ k ih =>
      rw [List.range_succ]
      have hiff := orbitWindowHeight_three_le_iff_mod_eight_eq_five n k
      by_cases hheight : 3 ≤ orbitWindowHeight n k
      · have hres : oddOrbitLabel n k % 8 = 5 := hiff.mp hheight
        simp [ih, hheight, hres]
      · have hres : oddOrbitLabel n k % 8 ≠ 5 := by
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
          hlast, ite_true, Nat.add_mul, one_mul]
        exact Nat.add_le_add ih' hlast
      · rw [sumS, ← orbitWindowHeight_eq_s_iterateT]
        unfold orbitWindowHeightCountGe orbitWindowHeightSeq
        rw [List.range_succ]
        simp only [List.map_append, List.map_cons, List.map_nil, List.countP_append,
          List.countP_map, List.countP_singleton, decide_eq_true_eq, ge_iff_le,
          hlast, ite_false, Nat.add_zero]
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
          ge_iff_le, hlast, hself, ite_true]
        exact Nat.add_le_add ih' le_rfl
      · rw [List.range_succ]
        simp only [List.map_append, List.map_cons, List.map_nil, List.countP_append,
          List.countP_map, List.countP_singleton, beq_iff_eq, decide_eq_true_eq,
          ge_iff_le, hlast, ite_false]
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
Prefix `height >= 2` occupation is the same as prefix mod `4` residue
occupation.
-/
theorem orbitWindowHeightPrefixCountGe_two_eq_prefixResidueCount_mod4_eq_one
    (n : OddNat) {r k : ℕ} (hr : r ≤ k) :
    orbitWindowHeightPrefixCountGe n k r 2 =
      orbitWindowPrefixResidueCountMod4EqOne n k r := by
  rw [orbitWindowHeightPrefixCountGe_eq_countGe n hr]
  rw [orbitWindowHeightCountGe_two_eq_residueCount_mod4_eq_one]
  rw [← orbitWindowPrefixResidueCountMod4EqOne_eq_residueCount n hr]

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
          hone, htwo, ite_true]
        omega
      · by_cases hone : 1 ≤ orbitWindowHeight n k
        · rw [sumS, ← orbitWindowHeight_eq_s_iterateT]
          unfold orbitWindowHeightCountGe orbitWindowHeightSeq
          rw [List.range_succ]
          simp only [List.map_append, List.map_cons, List.map_nil, List.countP_append,
            List.countP_map, List.countP_singleton, decide_eq_true_eq, ge_iff_le,
            hone, htwo, ite_true, ite_false]
          omega
        · rw [sumS, ← orbitWindowHeight_eq_s_iterateT]
          unfold orbitWindowHeightCountGe orbitWindowHeightSeq
          rw [List.range_succ]
          simp only [List.map_append, List.map_cons, List.map_nil, List.countP_append,
            List.countP_map, List.countP_singleton, decide_eq_true_eq, ge_iff_le,
            hone, htwo, ite_false]
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
The second exact Collatz height layer is residue class `1 mod 8`.

This refines `height >= 2` by excluding the `height >= 3` residue class.
-/
theorem orbitWindowHeight_eq_two_iff_mod_eight_eq_one
    (n : OddNat) (i : ℕ) :
    orbitWindowHeight n i = 2 ↔ oddOrbitLabel n i % 8 = 1 := by
  constructor
  · intro hheight
    have htwo : 2 ≤ orbitWindowHeight n i := by omega
    have hnotThree : ¬ 3 ≤ orbitWindowHeight n i := by omega
    have hmod4 : oddOrbitLabel n i % 4 = 1 :=
      (orbitWindowHeight_two_le_iff_mod_four_eq_one n i).mp htwo
    have hnotFive : oddOrbitLabel n i % 8 ≠ 5 := by
      intro hfive
      exact hnotThree ((orbitWindowHeight_three_le_iff_mod_eight_eq_five n i).mpr hfive)
    cases odd_mod_eight_eq_one_or_three_or_five_or_seven (iterateT i n).2 with
    | inl hOne =>
        change oddOrbitLabel n i % 8 = 1 at hOne
        exact hOne
    | inr hrest =>
        cases hrest with
        | inl hThree =>
            change oddOrbitLabel n i % 8 = 3 at hThree
            omega
        | inr hrest =>
            cases hrest with
            | inl hFive =>
                change oddOrbitLabel n i % 8 = 5 at hFive
                exact (hnotFive hFive).elim
            | inr hSeven =>
                change oddOrbitLabel n i % 8 = 7 at hSeven
                omega
  · intro hmod
    have htwo : 2 ≤ orbitWindowHeight n i := by
      apply (orbitWindowHeight_two_le_iff_mod_four_eq_one n i).mpr
      omega
    have hnotThree : ¬ 3 ≤ orbitWindowHeight n i := by
      intro hthree
      have hfive := (orbitWindowHeight_three_le_iff_mod_eight_eq_five n i).mp hthree
      omega
    omega

/--
The first Collatz height layer is exact height `1` precisely on residue class
`3 mod 4`.

Together with `orbitWindowHeight_two_le_iff_mod_four_eq_one`, this closes the
first mod `4` residue partition at the pointwise level.
-/
theorem orbitWindowHeight_eq_one_iff_mod_four_eq_three
    (n : OddNat) (i : ℕ) :
    orbitWindowHeight n i = 1 ↔ oddOrbitLabel n i % 4 = 3 := by
  constructor
  · intro hheight
    have hnotTwo : ¬ 2 ≤ orbitWindowHeight n i := by omega
    have hnotOne : oddOrbitLabel n i % 4 ≠ 1 := by
      intro hmod
      exact hnotTwo ((orbitWindowHeight_two_le_iff_mod_four_eq_one n i).mpr hmod)
    cases odd_mod_four_eq_one_or_three (iterateT i n).2 with
    | inl hmod =>
        change oddOrbitLabel n i % 4 = 1 at hmod
        exact (hnotOne hmod).elim
    | inr hmod =>
        change oddOrbitLabel n i % 4 = 3 at hmod
        exact hmod
  · intro hmod
    have hOne : 1 ≤ orbitWindowHeight n i := orbitWindowHeight_one_le n i
    have hnotTwo : ¬ 2 ≤ orbitWindowHeight n i := by
      intro htwo
      have hmodOne := (orbitWindowHeight_two_le_iff_mod_four_eq_one n i).mp htwo
      omega
    omega

/--
Tail exact height `1` occupation is the same as shifted-tail residue
occupation in class `3 mod 4`.
-/
theorem orbitWindowHeightCountEqTail_one_eq_tailResidueCount_mod4_eq_three
    (n : OddNat) (k : ℕ) :
    orbitWindowHeightCountEqTail n k 1 =
      orbitWindowResidueCountMod4EqThreeTail n k := by
  unfold orbitWindowHeightCountEqTail orbitWindowResidueCountMod4EqThreeTail
  induction k with
  | zero =>
      simp
  | succ k ih =>
      rw [List.range_succ]
      have hiff := orbitWindowHeight_eq_one_iff_mod_four_eq_three n (k + 1)
      by_cases hheight : orbitWindowHeight n (k + 1) = 1
      · have hres : oddOrbitLabel n (k + 1) % 4 = 3 := hiff.mp hheight
        simp [ih, hheight, hres]
      · have hres : oddOrbitLabel n (k + 1) % 4 ≠ 3 := by
          intro h
          exact hheight (hiff.mpr h)
        simp [ih, hheight, hres]

/--
At depth `2`, shifted-tail retention is exactly the shifted-tail `3 mod 4`
cell, hence it is the same mass as the tail exact-height-one count.

This is the safe tail-facing height bridge for the continuation-retention
channel.  It also records why the tempting `height >= 2` target is the wrong
one at this depth.
-/
theorem tailRetentionMass_depth_two_eq_heightCountEq_one
    (n : OddNat) (k : ℕ) :
    orbitWindowRetentionMassPow2Tail n k 2 =
      orbitWindowHeightCountEqTail n k 1 := by
  have htail :
      orbitWindowRetentionMassPow2Tail n k 2 =
        orbitWindowResidueCountMod4EqThreeTail n k := by
    unfold orbitWindowRetentionMassPow2Tail
    unfold orbitWindowResidueCountPow2Tail
    unfold orbitWindowResidueCountMod4EqThreeTail
    simp
  rw [htail]
  rw [← orbitWindowHeightCountEqTail_one_eq_tailResidueCount_mod4_eq_three]

/--
At depth `2`, shifted-tail retention is bounded by the tail exact-height-one
count.
-/
theorem tailRetentionMass_depth_two_le_heightCountEq_one
    (n : OddNat) (k : ℕ) :
    orbitWindowRetentionMassPow2Tail n k 2 ≤
      orbitWindowHeightCountEqTail n k 1 := by
  rw [tailRetentionMass_depth_two_eq_heightCountEq_one]

/--
At parent depth `2`, shifted-tail recovery sibling mass is exactly the
shifted-tail `3 mod 8` cell.

Thus this channel is not immediate `height >= 2`; it is the delayed-peeling
color inside exact height `1`.
-/
theorem tailRecoveryMass_depth_two_eq_tailResidueCount_mod8_eq_three
    (n : OddNat) (k : ℕ) :
    orbitWindowRecoverySiblingMassPow2Tail n k 2 =
      orbitWindowResidueCountMod8EqThreeTail n k := by
  unfold orbitWindowRecoverySiblingMassPow2Tail
  unfold orbitWindowResidueCountPow2Tail
  unfold orbitWindowResidueCountMod8EqThreeTail
  simp

/--
At parent depth `2`, shifted-tail recovery sibling mass is bounded by the
delayed-peeling `3 mod 8` tail color.
-/
theorem tailRecoveryMass_depth_two_le_tailResidueCount_mod8_eq_three
    (n : OddNat) (k : ℕ) :
    orbitWindowRecoverySiblingMassPow2Tail n k 2 ≤
      orbitWindowResidueCountMod8EqThreeTail n k := by
  rw [tailRecoveryMass_depth_two_eq_tailResidueCount_mod8_eq_three]

/--
The shifted tail splits into exact height `1` and height at least `2`.

Every accelerated Collatz tail state has height at least `1`, so an entry is
either the retaining exact-height-one layer or the extra-peeling layer.
-/
theorem orbitWindowHeightTail_countGe_two_add_countEq_one_eq_window
    (n : OddNat) (k : ℕ) :
    orbitWindowHeightCountGeTail n k 2 +
      orbitWindowHeightCountEqTail n k 1 = k := by
  induction k with
  | zero =>
      simp [orbitWindowHeightCountGeTail, orbitWindowHeightCountEqTail]
  | succ k ih =>
      rw [orbitWindowHeightCountGeTail_succ]
      rw [orbitWindowHeightCountEqTail_succ]
      have hone : 1 ≤ orbitWindowHeight n (k + 1) :=
        orbitWindowHeight_one_le n (k + 1)
      by_cases htwo : 2 ≤ orbitWindowHeight n (k + 1)
      · have hnotOne : orbitWindowHeight n (k + 1) ≠ 1 := by
          omega
        simp [htwo, hnotOne]
        omega
      · have hOne : orbitWindowHeight n (k + 1) = 1 := by
          omega
        simp [hOne]
        omega

/--
Exact height `1` is the union of the two mod `8` channels `3` and `7`.
-/
theorem orbitWindowHeight_eq_one_iff_mod_eight_eq_three_or_seven
    (n : OddNat) (i : ℕ) :
    orbitWindowHeight n i = 1 ↔
      oddOrbitLabel n i % 8 = 3 ∨ oddOrbitLabel n i % 8 = 7 := by
  constructor
  · intro hheight
    have hmod4 := (orbitWindowHeight_eq_one_iff_mod_four_eq_three n i).mp hheight
    cases odd_mod_eight_eq_one_or_three_or_five_or_seven (iterateT i n).2 with
    | inl hOne =>
        change oddOrbitLabel n i % 8 = 1 at hOne
        omega
    | inr hrest =>
        cases hrest with
        | inl hThree =>
            change oddOrbitLabel n i % 8 = 3 at hThree
            exact Or.inl hThree
        | inr hrest =>
            cases hrest with
            | inl hFive =>
                change oddOrbitLabel n i % 8 = 5 at hFive
                omega
            | inr hSeven =>
                change oddOrbitLabel n i % 8 = 7 at hSeven
                exact Or.inr hSeven
  · intro hmod
    apply (orbitWindowHeight_eq_one_iff_mod_four_eq_three n i).mpr
    cases hmod with
    | inl hThree =>
        omega
    | inr hSeven =>
        omega


end DkMath.Collatz
