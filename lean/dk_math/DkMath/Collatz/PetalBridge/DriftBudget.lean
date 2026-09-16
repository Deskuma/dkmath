/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Collatz.PetalBridge.TailGrammar

#print "file: DkMath.Collatz.PetalBridge.DriftBudget"

namespace DkMath.Collatz


/--
Every `7 mod 8` source label contributes a shifted-tail entry with exact
height `1`.

This is the retention-channel counterpart of the delayed-peeling theorem for
the `3 mod 8` source channel.
-/
theorem orbitWindowResidueCountMod8EqSeven_le_tailHeightCountEq_one
    (n : OddNat) (k : ℕ) :
    orbitWindowResidueCountMod8EqSeven n k ≤
      orbitWindowHeightCountEqTail n k 1 := by
  rw [orbitWindowHeightCountEqTail_one_eq_tailResidueCount_mod4_eq_three]
  exact residueCountMod8EqSeven_le_nextResidueCountMod4EqThree n k

/--
Source-channel sum bound through the tail partition.

The `3 mod 8` source feeds the tail extra-peeling side, and the `7 mod 8`
source feeds the tail exact-height-one side.  Since those two tail sides
partition the tail window, the two source counts together cannot exceed `k`.
-/
theorem orbitWindowResidueCountMod8EqThree_add_seven_le_tail_partition
    (n : OddNat) (k : ℕ) :
    orbitWindowResidueCountMod8EqThree n k +
      orbitWindowResidueCountMod8EqSeven n k ≤ k := by
  have h3 :
      orbitWindowResidueCountMod8EqThree n k ≤
        orbitWindowHeightCountGeTail n k 2 :=
    orbitWindowResidueCountMod8EqThree_le_tailHeightCountGe_two n k
  have h7 :
      orbitWindowResidueCountMod8EqSeven n k ≤
        orbitWindowHeightCountEqTail n k 1 :=
    orbitWindowResidueCountMod8EqSeven_le_tailHeightCountEq_one n k
  have hsplit := orbitWindowHeightTail_countGe_two_add_countEq_one_eq_window n k
  omega

/--
The shifted-tail threshold count is contained in the ordinary count over the
one-step-longer window.

The tail observes times `1..k`; the ordinary `(k + 1)` window observes
`0..k`, so it contains the same tail entries plus the initial time.
-/
theorem orbitWindowHeightCountGeTail_le_countGe_succ
    (n : OddNat) (k threshold : ℕ) :
    orbitWindowHeightCountGeTail n k threshold ≤
      orbitWindowHeightCountGe n (k + 1) threshold := by
  induction k with
  | zero =>
      unfold orbitWindowHeightCountGeTail
      simp
  | succ k ih =>
      rw [orbitWindowHeightCountGeTail_succ]
      rw [orbitWindowHeightCountGe_succ]
      exact Nat.add_le_add ih le_rfl

/--
The zeroth natural orbit label is the initial odd state.
-/
theorem oddOrbitLabel_zero_eq
    (n : OddNat) :
    oddOrbitLabel n 0 = n.1 := rfl

/--
Restarting the orbit at `iterateT i n` makes its zeroth label equal to the
original label at time `i`.
-/
theorem oddOrbitLabel_iterateT_zero_eq
    (n : OddNat) (i : ℕ) :
    oddOrbitLabel (iterateT i n) 0 = oddOrbitLabel n i := rfl

/--
Two-step delayed-peeling experiment.

Starting at `3 mod 8`, the current step contributes height `1`, and the next
step contributes at least height `2`.  Hence the first two accelerated
Collatz height observations sum to at least `3`.
-/
theorem sumS_two_steps_ge_three_of_mod_eight_eq_three
    (n : OddNat)
    (hmod : oddOrbitLabel n 0 % 8 = 3) :
    3 ≤ sumS n 2 := by
  have h0 : orbitWindowHeight n 0 = 1 :=
    (orbitWindowHeight_eq_one_iff_mod_eight_eq_three_or_seven n 0).mpr
      (Or.inl hmod)
  have h1 : 2 ≤ orbitWindowHeight n 1 :=
    orbitWindowNextHeight_two_le_of_mod_eight_eq_three n 0 hmod
  calc
    3 ≤ orbitWindowHeight n 0 + orbitWindowHeight n 1 := by
      omega
    _ = sumS n 2 := by
      simp [sumS, orbitWindowHeight_eq_s_iterateT]

/--
Localized two-step delayed-peeling experiment.

The pointwise two-step theorem can be restarted at any accelerated state
`iterateT i n`.
-/
theorem sumS_two_steps_ge_three_of_mod_eight_eq_three_at
    (n : OddNat) (i : ℕ)
    (hmod : oddOrbitLabel n i % 8 = 3) :
    3 ≤ sumS (iterateT i n) 2 := by
  apply sumS_two_steps_ge_three_of_mod_eight_eq_three
  simpa [oddOrbitLabel_iterateT_zero_eq] using hmod

/--
Two-step retention witness for the `7 -> 7` pattern.

If the first two labels both lie in residue class `7 mod 8`, then both
observed heights are exact height `1`, so the two-step accumulated height is
exactly `2`.
-/
theorem sumS_two_steps_eq_two_of_mod_eight_eq_seven_and_next_mod_eight_eq_seven
    (n : OddNat)
    (h0 : oddOrbitLabel n 0 % 8 = 7)
    (h1 : oddOrbitLabel n 1 % 8 = 7) :
    sumS n 2 = 2 := by
  have hh0 : orbitWindowHeight n 0 = 1 :=
    (orbitWindowHeight_eq_one_iff_mod_eight_eq_three_or_seven n 0).mpr
      (Or.inr h0)
  have hh1 : orbitWindowHeight n 1 = 1 :=
    (orbitWindowHeight_eq_one_iff_mod_eight_eq_three_or_seven n 1).mpr
      (Or.inr h1)
  calc
    sumS n 2 = orbitWindowHeight n 0 + orbitWindowHeight n 1 := by
      simp [sumS, orbitWindowHeight_eq_s_iterateT]
    _ = 2 := by
      omega

/--
Three-step recovery from the `7 mod 16` subchannel.

The first step is exact height `1`; the next label lands in `3 mod 8`, hence
the second step is also exact height `1` but forces height at least `2` on the
third step.  Thus the first three heights contribute at least `1 + 1 + 2`.
-/
theorem sumS_three_steps_ge_four_of_mod_sixteen_eq_seven
    (n : OddNat)
    (hmod : oddOrbitLabel n 0 % 16 = 7) :
    4 ≤ sumS n 3 := by
  have hmod8 : oddOrbitLabel n 0 % 8 = 7 := by
    omega
  have h0 : orbitWindowHeight n 0 = 1 :=
    (orbitWindowHeight_eq_one_iff_mod_eight_eq_three_or_seven n 0).mpr
      (Or.inr hmod8)
  have h1mod :
      oddOrbitLabel n 1 % 8 = 3 :=
    oddOrbitLabel_succ_mod_eight_eq_three_of_mod_sixteen_eq_seven n 0 hmod
  have h1 : orbitWindowHeight n 1 = 1 :=
    (orbitWindowHeight_eq_one_iff_mod_eight_eq_three_or_seven n 1).mpr
      (Or.inl h1mod)
  have h2 : 2 ≤ orbitWindowHeight n 2 :=
    orbitWindowNextHeight_two_le_of_mod_eight_eq_three n 1 h1mod
  calc
    4 ≤ orbitWindowHeight n 0 + orbitWindowHeight n 1 +
        orbitWindowHeight n 2 := by
      omega
    _ = sumS n 3 := by
      simp [sumS, orbitWindowHeight_eq_s_iterateT]

/--
Four-step recovery from the `15 mod 32` subchannel.

The branch first continues exact height-one behavior through `7 mod 16` and
then `3 mod 8`, but the fourth observed height is at least `2`.  Thus the
first four heights contribute at least `1 + 1 + 1 + 2`.
-/
theorem sumS_four_steps_ge_five_of_mod_thirtytwo_eq_fifteen
    (n : OddNat)
    (hmod : oddOrbitLabel n 0 % 32 = 15) :
    5 ≤ sumS n 4 := by
  have hmod8 : oddOrbitLabel n 0 % 8 = 7 := by
    omega
  have h0 : orbitWindowHeight n 0 = 1 :=
    (orbitWindowHeight_eq_one_iff_mod_eight_eq_three_or_seven n 0).mpr
      (Or.inr hmod8)
  have h1mod16 :
      oddOrbitLabel n 1 % 16 = 7 :=
    oddOrbitLabel_succ_mod_sixteen_eq_seven_of_mod_thirtytwo_eq_fifteen
      n 0 hmod
  have h1mod8 : oddOrbitLabel n 1 % 8 = 7 := by
    omega
  have h1 : orbitWindowHeight n 1 = 1 :=
    (orbitWindowHeight_eq_one_iff_mod_eight_eq_three_or_seven n 1).mpr
      (Or.inr h1mod8)
  have h2mod :
      oddOrbitLabel n 2 % 8 = 3 :=
    oddOrbitLabel_succ_mod_eight_eq_three_of_mod_sixteen_eq_seven
      n 1 h1mod16
  have h2 : orbitWindowHeight n 2 = 1 :=
    (orbitWindowHeight_eq_one_iff_mod_eight_eq_three_or_seven n 2).mpr
      (Or.inl h2mod)
  have h3 : 2 ≤ orbitWindowHeight n 3 :=
    orbitWindowNextHeight_two_le_of_mod_eight_eq_three n 2 h2mod
  calc
    5 ≤ orbitWindowHeight n 0 + orbitWindowHeight n 1 +
        orbitWindowHeight n 2 + orbitWindowHeight n 3 := by
      omega
    _ = sumS n 4 := by
      simp [sumS, orbitWindowHeight_eq_s_iterateT]

/--
Five-step recovery from the `31 mod 64` subchannel.

This is the next rung of the verified retention ladder.  The branch moves
through `15 mod 32`, `7 mod 16`, and `3 mod 8`, and then returns an extra
peeling step.
-/
theorem sumS_five_steps_ge_six_of_mod_sixtyfour_eq_thirtyone
    (n : OddNat)
    (hmod : oddOrbitLabel n 0 % 64 = 31) :
    6 ≤ sumS n 5 := by
  have hmod8 : oddOrbitLabel n 0 % 8 = 7 := by
    omega
  have h0 : orbitWindowHeight n 0 = 1 :=
    (orbitWindowHeight_eq_one_iff_mod_eight_eq_three_or_seven n 0).mpr
      (Or.inr hmod8)
  have h1mod32 :
      oddOrbitLabel n 1 % 32 = 15 :=
    oddOrbitLabel_succ_mod_thirtytwo_eq_fifteen_of_mod_sixtyfour_eq_thirtyone
      n 0 hmod
  have h1mod8 : oddOrbitLabel n 1 % 8 = 7 := by
    omega
  have h1 : orbitWindowHeight n 1 = 1 :=
    (orbitWindowHeight_eq_one_iff_mod_eight_eq_three_or_seven n 1).mpr
      (Or.inr h1mod8)
  have h2mod16 :
      oddOrbitLabel n 2 % 16 = 7 :=
    oddOrbitLabel_succ_mod_sixteen_eq_seven_of_mod_thirtytwo_eq_fifteen
      n 1 h1mod32
  have h2mod8 : oddOrbitLabel n 2 % 8 = 7 := by
    omega
  have h2 : orbitWindowHeight n 2 = 1 :=
    (orbitWindowHeight_eq_one_iff_mod_eight_eq_three_or_seven n 2).mpr
      (Or.inr h2mod8)
  have h3mod :
      oddOrbitLabel n 3 % 8 = 3 :=
    oddOrbitLabel_succ_mod_eight_eq_three_of_mod_sixteen_eq_seven
      n 2 h2mod16
  have h3 : orbitWindowHeight n 3 = 1 :=
    (orbitWindowHeight_eq_one_iff_mod_eight_eq_three_or_seven n 3).mpr
      (Or.inl h3mod)
  have h4 : 2 ≤ orbitWindowHeight n 4 :=
    orbitWindowNextHeight_two_le_of_mod_eight_eq_three n 3 h3mod
  calc
    6 ≤ orbitWindowHeight n 0 + orbitWindowHeight n 1 +
        orbitWindowHeight n 2 + orbitWindowHeight n 3 +
        orbitWindowHeight n 4 := by
      omega
    _ = sumS n 5 := by
      simp [sumS, orbitWindowHeight_eq_s_iterateT]

/--
Counting exact height `1` entries is the same as counting odd-state labels in
residue class `3 mod 4`.
-/
theorem orbitWindowHeightCountEq_one_eq_residueCount_mod4_eq_three
    (n : OddNat) (k : ℕ) :
    orbitWindowHeightCountEq n k 1 =
      orbitWindowResidueCountMod4EqThree n k := by
  unfold orbitWindowHeightCountEq orbitWindowResidueCountMod4EqThree orbitWindowHeightSeq
  induction k with
  | zero =>
      simp
  | succ k ih =>
      rw [List.range_succ]
      have hiff := orbitWindowHeight_eq_one_iff_mod_four_eq_three n k
      by_cases hheight : orbitWindowHeight n k = 1
      · have hres : oddOrbitLabel n k % 4 = 3 := hiff.mp hheight
        simp [ih, hheight, hres]
      · have hres : oddOrbitLabel n k % 4 ≠ 3 := by
          intro h
          exact hheight (hiff.mpr h)
        simp [ih, hheight, hres]

/--
Counting exact height `2` entries is the same as counting odd-state labels in
residue class `1 mod 8`.
-/
theorem orbitWindowHeightCountEq_two_eq_residueCount_mod8_eq_one
    (n : OddNat) (k : ℕ) :
    orbitWindowHeightCountEq n k 2 =
      orbitWindowResidueCountMod8EqOne n k := by
  unfold orbitWindowHeightCountEq orbitWindowResidueCountMod8EqOne orbitWindowHeightSeq
  induction k with
  | zero =>
      simp
  | succ k ih =>
      rw [List.range_succ]
      have hiff := orbitWindowHeight_eq_two_iff_mod_eight_eq_one n k
      by_cases hheight : orbitWindowHeight n k = 2
      · have hres : oddOrbitLabel n k % 8 = 1 := hiff.mp hheight
        simp [ih, hheight, hres]
      · have hres : oddOrbitLabel n k % 8 ≠ 1 := by
          intro h
          exact hheight (hiff.mpr h)
        simp [ih, hheight, hres]

/--
The two odd residue classes modulo `4` fill the whole observation window.
-/
theorem orbitWindowResidueCountMod4EqOne_add_eqThree_eq_window
    (n : OddNat) (k : ℕ) :
    orbitWindowResidueCountMod4EqOne n k +
      orbitWindowResidueCountMod4EqThree n k = k := by
  unfold orbitWindowResidueCountMod4EqOne orbitWindowResidueCountMod4EqThree
  induction k with
  | zero =>
      simp
  | succ k ih =>
      rw [List.range_succ]
      cases odd_mod_four_eq_one_or_three (iterateT k n).2 with
      | inl hOne =>
          change oddOrbitLabel n k % 4 = 1 at hOne
          simp [hOne]
          omega
      | inr hThree =>
          change oddOrbitLabel n k % 4 = 3 at hThree
          simp [hThree]
          omega

/--
The four odd residue classes modulo `8` fill the whole observation window.
-/
theorem orbitWindowResidueCountMod8_partition_eq_window
    (n : OddNat) (k : ℕ) :
    orbitWindowResidueCountMod8EqOne n k +
      orbitWindowResidueCountMod8EqThree n k +
      orbitWindowResidueCountMod8EqFive n k +
      orbitWindowResidueCountMod8EqSeven n k = k := by
  unfold orbitWindowResidueCountMod8EqOne orbitWindowResidueCountMod8EqThree
    orbitWindowResidueCountMod8EqFive orbitWindowResidueCountMod8EqSeven
  induction k with
  | zero =>
      simp
  | succ k ih =>
      rw [List.range_succ]
      cases odd_mod_eight_eq_one_or_three_or_five_or_seven (iterateT k n).2 with
      | inl hOne =>
          change oddOrbitLabel n k % 8 = 1 at hOne
          simp [hOne]
          omega
      | inr hrest =>
          cases hrest with
          | inl hThree =>
              change oddOrbitLabel n k % 8 = 3 at hThree
              simp [hThree]
              omega
          | inr hrest =>
              cases hrest with
              | inl hFive =>
                  change oddOrbitLabel n k % 8 = 5 at hFive
                  simp [hFive]
                  omega
              | inr hSeven =>
                  change oddOrbitLabel n k % 8 = 7 at hSeven
                  simp [hSeven]
                  omega

/--
The two exact-height-one source channels cannot exceed the window size.

This proof reads directly from the mod `8` partition.
-/
theorem orbitWindowResidueCountMod8EqThree_add_seven_le_window
    (n : OddNat) (k : ℕ) :
    orbitWindowResidueCountMod8EqThree n k +
      orbitWindowResidueCountMod8EqSeven n k ≤ k := by
  have hpart := orbitWindowResidueCountMod8_partition_eq_window n k
  omega

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
          hb, ha, ite_true]
        exact Nat.add_le_add ih' le_rfl
      · rw [List.range_succ]
        simp only [List.map_append, List.map_cons, List.map_nil, List.countP_append,
          List.countP_map, List.countP_singleton, decide_eq_true_eq, ge_iff_le,
          hb, ite_false]
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
          hone, htwo, hthree, ite_true]
        omega
      · by_cases htwo : 2 ≤ orbitWindowHeight n k
        · have hone : 1 ≤ orbitWindowHeight n k := Nat.le_trans (by decide) htwo
          rw [sumS, ← orbitWindowHeight_eq_s_iterateT]
          unfold orbitWindowHeightCountGe orbitWindowHeightSeq
          rw [List.range_succ]
          simp only [List.map_append, List.map_cons, List.map_nil, List.countP_append,
            List.countP_map, List.countP_singleton, decide_eq_true_eq, ge_iff_le,
            hone, htwo, hthree, ite_true, ite_false]
          omega
        · by_cases hone : 1 ≤ orbitWindowHeight n k
          · rw [sumS, ← orbitWindowHeight_eq_s_iterateT]
            unfold orbitWindowHeightCountGe orbitWindowHeightSeq
            rw [List.range_succ]
            simp only [List.map_append, List.map_cons, List.map_nil, List.countP_append,
              List.countP_map, List.countP_singleton, decide_eq_true_eq, ge_iff_le,
              hone, htwo, hthree, ite_true, ite_false]
            omega
          · rw [sumS, ← orbitWindowHeight_eq_s_iterateT]
            unfold orbitWindowHeightCountGe orbitWindowHeightSeq
            rw [List.range_succ]
            simp only [List.map_append, List.map_cons, List.map_nil, List.countP_append,
              List.countP_map, List.countP_singleton, decide_eq_true_eq, ge_iff_le,
              hone, htwo, hthree, ite_false]
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
Strong tail-count drift budget.

The `(k + 1)` ordinary window supplies the base peeling layer, and the shifted
tail `height >= 2` count supplies the delayed extra layer.
-/
theorem orbitWindowHeightSeq_sum_ge_succ_window_add_tailCountGe_two
    (n : OddNat) (k : ℕ) :
    (k + 1) + orbitWindowHeightCountGeTail n k 2 ≤ sumS n (k + 1) := by
  exact orbitWindowHeightSeq_sum_ge_window_add_of_countGe_two_ge
    n (k + 1) (orbitWindowHeightCountGeTail n k 2)
    (orbitWindowHeightCountGeTail_le_countGe_succ n k 2)

/--
Weak tail-count drift budget.

The shifted-tail `height >= 2` entries contribute extra peeling inside the
one-step-longer accumulated window.
-/
theorem orbitWindowHeightSeq_sum_ge_window_add_tailCountGe_two
    (n : OddNat) (k : ℕ) :
    k + orbitWindowHeightCountGeTail n k 2 ≤ sumS n (k + 1) := by
  exact le_trans
    (by
      have h :
          k + orbitWindowHeightCountGeTail n k 2 ≤
            (k + 1) + orbitWindowHeightCountGeTail n k 2 := by
        omega
      exact h)
    (orbitWindowHeightSeq_sum_ge_succ_window_add_tailCountGe_two n k)

/--
Delayed-drift theorem from the `3 mod 8` source channel.

Every source occurrence of `3 mod 8` feeds a shifted-tail `height >= 2` entry,
so it contributes to the accumulated drift over the one-step-longer window.
-/
theorem orbitWindowResidueCountMod8EqThree_delayed_drift
    (n : OddNat) (k : ℕ) :
    k + orbitWindowResidueCountMod8EqThree n k ≤ sumS n (k + 1) := by
  exact le_trans
    (Nat.add_le_add_left
      (orbitWindowResidueCountMod8EqThree_le_tailHeightCountGe_two n k) k)
    (orbitWindowHeightSeq_sum_ge_window_add_tailCountGe_two n k)

/--
Strong delayed-drift theorem from the `3 mod 8` source channel.

This is the count-level form of delayed peeling:

```text
base layer over 0..k
  +
source count of 3 mod 8 over 0..k-1
  <= sumS over 0..k
```
-/
theorem orbitWindowResidueCountMod8EqThree_delayed_drift_strong
    (n : OddNat) (k : ℕ) :
    (k + 1) + orbitWindowResidueCountMod8EqThree n k ≤ sumS n (k + 1) := by
  exact le_trans
    (Nat.add_le_add_left
      (orbitWindowResidueCountMod8EqThree_le_tailHeightCountGe_two n k) (k + 1))
    (orbitWindowHeightSeq_sum_ge_succ_window_add_tailCountGe_two n k)

/--
Tail-facing delayed-drift theorem from the shifted-tail `3 mod 8` channel.

The shifted-tail `3 mod 8` color does not represent immediate extra peeling in
the same tail window.  It contributes a `height >= 2` tail entry one step later,
so it supplies an extra layer over the next accumulated window.
-/
theorem tailResidueCountMod8EqThree_delayed_drift
    (n : OddNat) (k : ℕ) :
    (k + 1) + orbitWindowResidueCountMod8EqThreeTail n k ≤
      sumS n ((k + 1) + 1) := by
  have htail :
      orbitWindowResidueCountMod8EqThreeTail n k ≤
        orbitWindowHeightCountGeTail n (k + 1) 2 :=
    tailMod8Three_le_nextTailHeightCountGe_two n k
  exact le_trans
    (Nat.add_le_add_left htail (k + 1))
    (orbitWindowHeightSeq_sum_ge_window_add_tailCountGe_two n (k + 1))

/--
Delayed-reservoir budget with a continuing-color remainder.

The `3 mod 8` part of the current exact-height-one reservoir contributes to
the next accumulated `sumS` lower bound.  The `7 mod 8` part is left explicit
as the still-continuing remainder.
-/
theorem tailExactHeightOneReservoir_budget_with_remainder
    (n : OddNat) (k : ℕ) :
    (k + 1) + orbitWindowHeightCountEqTail n k 1 ≤
      sumS n ((k + 1) + 1) +
        orbitWindowResidueCountMod8EqSevenTail n k := by
  rw [tailHeightCountEq_one_split_mod8_three_seven]
  have hthree :
      (k + 1) + orbitWindowResidueCountMod8EqThreeTail n k ≤
        sumS n ((k + 1) + 1) :=
    tailResidueCountMod8EqThree_delayed_drift n k
  omega

/--
Source-continuation depth-two budget with a continuing-color remainder.

Depth-two source continuation enters the shifted-tail exact-height-one
reservoir.  The `3 mod 8` part contributes to the next `sumS` lower bound, and
the `7 mod 8` part remains as an explicit delayed reservoir remainder.
-/
theorem sourceContinuationMass_depth_two_delayed_budget_with_tailSeven_remainder
    (n : OddNat) (k : ℕ) :
    (k + 1) + orbitWindowContinuationSiblingMassPow2 n k 2 ≤
      sumS n ((k + 1) + 1) +
        orbitWindowResidueCountMod8EqSevenTail n k := by
  have hsource :
      orbitWindowContinuationSiblingMassPow2 n k 2 ≤
        orbitWindowResidueCountMod8EqThreeTail n k +
          orbitWindowResidueCountMod8EqSevenTail n k :=
    sourceContinuationMass_depth_two_le_tailMod8Three_add_tailMod8Seven n k
  have hthree :
      (k + 1) + orbitWindowResidueCountMod8EqThreeTail n k ≤
        sumS n ((k + 1) + 1) :=
    tailResidueCountMod8EqThree_delayed_drift n k
  omega

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
Three-layer residue-address drift bridge.

If at least `m` labels in the window lie in residue class `5 mod 8`, then the
third height layer contributes at least `m` additional units on top of the
base layer and the second layer.
-/
theorem orbitWindowHeightSeq_sum_ge_window_add_countGe_two_add_of_residue_mod8_count_ge
    (n : OddNat) (k m : ℕ)
    (hm : m ≤ orbitWindowResidueCountMod8EqFive n k) :
    k + orbitWindowHeightCountGe n k 2 + m ≤ sumS n k := by
  have htail :
      k + orbitWindowHeightCountGe n k 2 +
          orbitWindowHeightCountGe n k 3 ≤ sumS n k := by
    simpa [orbitWindowHeightCountGe_one_eq_window n k, Nat.add_assoc] using
      orbitWindowHeightSeq_sum_ge_countGe_one_add_countGe_two_add_countGe_three n k
  rw [← orbitWindowHeightCountGe_three_eq_residueCount_mod8_eq_five n k] at hm
  exact le_trans
    (Nat.add_le_add_left hm (k + orbitWindowHeightCountGe n k 2))
    htail

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
Prefix residue-address drift bridge.

If at least `m` labels in the prefix lie in residue class `1 mod 4`, then the
prefix accumulated height is at least `r + m`.
-/
theorem orbitWindowHeightPrefix_sum_ge_window_add_of_residue_mod4_count_ge
    (n : OddNat) {r k m : ℕ} (hr : r ≤ k)
    (hm : m ≤ orbitWindowPrefixResidueCountMod4EqOne n k r) :
    r + m ≤ sumS n r := by
  rw [← orbitWindowHeightPrefixCountGe_two_eq_prefixResidueCount_mod4_eq_one n hr] at hm
  exact orbitWindowHeightPrefix_sum_ge_window_add_of_countGe_two_ge n hr hm


end DkMath.Collatz
