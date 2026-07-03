/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Collatz.PetalBridge.TailSplits

#print "file: DkMath.Collatz.PetalBridge.TailGrammar"

namespace DkMath.Collatz


/--
Orbit-level transition from the `3 mod 8` height-one channel.

The current odd-state label is in residue class `3 mod 8`, so the accelerated
next state `T` lands in residue class `1 mod 4`.
-/
theorem orbitNext_mod_four_eq_one_of_mod_eight_eq_three
    (n : OddNat) (i : ℕ)
    (hmod : oddOrbitLabel n i % 8 = 3) :
    (T (iterateT i n)).1 % 4 = 1 := by
  have hheight : orbitWindowHeight n i = 1 :=
    (orbitWindowHeight_eq_one_iff_mod_eight_eq_three_or_seven n i).mpr
      (Or.inl hmod)
  have hs : s (iterateT i n) = 1 := by
    simpa [orbitWindowHeight_eq_s_iterateT] using hheight
  rw [T_val_eq_three_mul_add_one_div_two_of_s_eq_one (iterateT i n) hs]
  exact next_mod_four_of_mod_eight_eq_three hmod

/--
Orbit-level transition from the `7 mod 8` height-one channel.

The current odd-state label is in residue class `7 mod 8`, so the accelerated
next state `T` lands in residue class `3 mod 4`.
-/
theorem orbitNext_mod_four_eq_three_of_mod_eight_eq_seven
    (n : OddNat) (i : ℕ)
    (hmod : oddOrbitLabel n i % 8 = 7) :
    (T (iterateT i n)).1 % 4 = 3 := by
  have hheight : orbitWindowHeight n i = 1 :=
    (orbitWindowHeight_eq_one_iff_mod_eight_eq_three_or_seven n i).mpr
      (Or.inr hmod)
  have hs : s (iterateT i n) = 1 := by
    simpa [orbitWindowHeight_eq_s_iterateT] using hheight
  rw [T_val_eq_three_mul_add_one_div_two_of_s_eq_one (iterateT i n) hs]
  exact next_mod_four_of_mod_eight_eq_seven hmod

/--
One-step recursion for the accelerated Collatz iterator.

This repackages the recursive definition of `iterateT` in the orientation
needed by orbit-label transition theorems: the next label is obtained by
applying `T` to the current accelerated state.
-/
theorem iterateT_succ_eq_T_iterateT
    (n : OddNat) (i : ℕ) :
    iterateT (i + 1) n = T (iterateT i n) := by
  induction i generalizing n with
  | zero =>
      rfl
  | succ i ih =>
      change iterateT (i + 1) (T n) = T (iterateT i (T n))
      exact ih (T n)

/--
The next natural orbit label is the natural value of `T` applied to the
current accelerated state.
-/
theorem oddOrbitLabel_succ_eq_T_iterateT
    (n : OddNat) (i : ℕ) :
    oddOrbitLabel n (i + 1) = (T (iterateT i n)).1 := by
  unfold oddOrbitLabel
  rw [iterateT_succ_eq_T_iterateT]

/--
The residual shape extracted at index `i` is the next odd orbit label.

This is the checkpoint-127 window lift of
`rawGnomonResidualShape_eq_T_val`.
-/
theorem orbitWindowResidualShape_eq_oddOrbitLabel_succ
    (n : OddNat) (i : ℕ) :
    orbitWindowResidualShape n i = oddOrbitLabel n (i + 1) := by
  unfold orbitWindowResidualShape oddOrbitLabel
  rw [rawGnomonResidualShape_eq_T_val (iterateT i n)]
  rw [iterateT_succ_eq_T_iterateT]

/--
Residual all-ones depth is the all-ones depth of the next accelerated label.

Checkpoint 133 treats `v2(residual + 1)` as a profile on the shifted odd-label
orbit.  The theorem lives in `TailGrammar`, not `Profiles`, because the
post-refactor import order places the residual-shape/next-label identity here.
This keeps `Profiles` thin and lets downstream pressure modules consume the
shifted-label reading without rebuilding the import graph.
-/
theorem orbitWindowResidualAllOnesDepth_eq_nextLabel
    (n : OddNat) (i : ℕ) :
    orbitWindowResidualAllOnesDepth n i =
      ResidualAllOnesDepth (oddOrbitLabel n (i + 1)) := by
  unfold orbitWindowResidualAllOnesDepth
  rw [orbitWindowResidualShape_eq_oddOrbitLabel_succ]

/--
The residual-shape sequence is exactly the shifted odd-label sequence.

This records that a finite orbit window is a chain of residual-shape
extractions.
-/
theorem orbitWindowResidualShapeSeq_eq_shifted_oddOrbitLabels
    (n : OddNat) (k : ℕ) :
    orbitWindowResidualShapeSeq n k =
      (List.range k).map (fun i => oddOrbitLabel n (i + 1)) := by
  unfold orbitWindowResidualShapeSeq
  apply List.map_congr_left
  intro i _hi
  exact orbitWindowResidualShape_eq_oddOrbitLabel_succ n i

/--
Reading the residual-shape profile at an in-window time recovers the shifted
odd label.
-/
theorem orbitWindowResidualShapeSeq_get?_eq_some_shifted_label
    (n : OddNat) {i k : ℕ} (hi : i < k) :
    (orbitWindowResidualShapeSeq n k)[i]? =
      some (oddOrbitLabel n (i + 1)) := by
  rw [orbitWindowResidualShapeSeq_eq_shifted_oddOrbitLabels]
  simp [hi]

/--
Reading the all-ones-depth residual profile can be stated directly in terms of
the next accelerated label.

This is the list-level companion to
`orbitWindowResidualAllOnesDepth_eq_nextLabel`; it is the Lean-side handle for
the Python scan columns based on residual all-ones depth.
-/
theorem orbitWindowResidualAllOnesDepthSeq_get?_eq_some_nextLabel
    (n : OddNat) {i k : ℕ} (hi : i < k) :
    (orbitWindowResidualAllOnesDepthSeq n k)[i]? =
      some (ResidualAllOnesDepth (oddOrbitLabel n (i + 1))) := by
  rw [orbitWindowResidualAllOnesDepthSeq_get?_eq_some n hi]
  rw [orbitWindowResidualAllOnesDepth_eq_nextLabel]

/--
Window-level raw gnomon factorization.

At each observed label, the raw gnomon step decomposes into the observed
window height and the residual shape that becomes the next label.
-/
theorem orbitWindow_rawGnomonStep_factor
    (n : OddNat) (i : ℕ) :
    RawGnomonStep (oddOrbitLabel n i) =
      2 ^ orbitWindowHeight n i * orbitWindowResidualShape n i := by
  rw [orbitWindowHeight_eq_rawGnomonHeight_oddOrbitLabel]
  unfold orbitWindowResidualShape oddOrbitLabel
  exact rawGnomonStep_eq_pow_height_mul_residualShape (iterateT i n)

/--
The first failed depth in the finite window has nonzero raw gnomon remainder.
-/
theorem orbitWindow_firstFailed_remainder_ne_zero
    (n : OddNat) (i : ℕ) :
    RawGnomonRemainderAtDepth
        (oddOrbitLabel n i)
        (orbitWindowFirstFailedPow2Depth n i) ≠ 0 := by
  unfold orbitWindowFirstFailedPow2Depth oddOrbitLabel
  exact rawGnomonRemainderAtDepth_firstFailed_ne_zero (iterateT i n)

/--
Label-sequence transition from the `3 mod 8` height-one channel.

If the current label is `3 mod 8`, then the next orbit label lies in
residue class `1 mod 4`.
-/
theorem oddOrbitLabel_succ_mod_four_eq_one_of_mod_eight_eq_three
    (n : OddNat) (i : ℕ)
    (hmod : oddOrbitLabel n i % 8 = 3) :
    oddOrbitLabel n (i + 1) % 4 = 1 := by
  rw [oddOrbitLabel_succ_eq_T_iterateT]
  exact orbitNext_mod_four_eq_one_of_mod_eight_eq_three n i hmod

/--
Label-sequence transition from the `7 mod 8` height-one channel.

If the current label is `7 mod 8`, then the next orbit label lies in
residue class `3 mod 4`.
-/
theorem oddOrbitLabel_succ_mod_four_eq_three_of_mod_eight_eq_seven
    (n : OddNat) (i : ℕ)
    (hmod : oddOrbitLabel n i % 8 = 7) :
    oddOrbitLabel n (i + 1) % 4 = 3 := by
  rw [oddOrbitLabel_succ_eq_T_iterateT]
  exact orbitNext_mod_four_eq_three_of_mod_eight_eq_seven n i hmod

/--
The `7 mod 16` subchannel moves to `3 mod 8` at the next label.

This is the recovery branch inside the `7 mod 8` retention channel.
-/
theorem oddOrbitLabel_succ_mod_eight_eq_three_of_mod_sixteen_eq_seven
    (n : OddNat) (i : ℕ)
    (hmod : oddOrbitLabel n i % 16 = 7) :
    oddOrbitLabel n (i + 1) % 8 = 3 := by
  have hmod8 : oddOrbitLabel n i % 8 = 7 := by
    omega
  have hheight : orbitWindowHeight n i = 1 :=
    (orbitWindowHeight_eq_one_iff_mod_eight_eq_three_or_seven n i).mpr
      (Or.inr hmod8)
  have hs : s (iterateT i n) = 1 := by
    simpa [orbitWindowHeight_eq_s_iterateT] using hheight
  rw [oddOrbitLabel_succ_eq_T_iterateT]
  rw [T_val_eq_three_mul_add_one_div_two_of_s_eq_one (iterateT i n) hs]
  exact next_mod_eight_of_mod_sixteen_eq_seven hmod

/--
The `15 mod 16` subchannel continues as `7 mod 8` at the next label.

This is the next retention-continuation branch.
-/
theorem oddOrbitLabel_succ_mod_eight_eq_seven_of_mod_sixteen_eq_fifteen
    (n : OddNat) (i : ℕ)
    (hmod : oddOrbitLabel n i % 16 = 15) :
    oddOrbitLabel n (i + 1) % 8 = 7 := by
  have hmod8 : oddOrbitLabel n i % 8 = 7 := by
    omega
  have hheight : orbitWindowHeight n i = 1 :=
    (orbitWindowHeight_eq_one_iff_mod_eight_eq_three_or_seven n i).mpr
      (Or.inr hmod8)
  have hs : s (iterateT i n) = 1 := by
    simpa [orbitWindowHeight_eq_s_iterateT] using hheight
  rw [oddOrbitLabel_succ_eq_T_iterateT]
  rw [T_val_eq_three_mul_add_one_div_two_of_s_eq_one (iterateT i n) hs]
  exact next_mod_eight_of_mod_sixteen_eq_fifteen hmod

/--
The `15 mod 32` subchannel moves to `7 mod 16` at the next label.

This is the recovery branch inside the `15 mod 16` retention-continuation
channel.
-/
theorem oddOrbitLabel_succ_mod_sixteen_eq_seven_of_mod_thirtytwo_eq_fifteen
    (n : OddNat) (i : ℕ)
    (hmod : oddOrbitLabel n i % 32 = 15) :
    oddOrbitLabel n (i + 1) % 16 = 7 := by
  have hmod8 : oddOrbitLabel n i % 8 = 7 := by
    omega
  have hheight : orbitWindowHeight n i = 1 :=
    (orbitWindowHeight_eq_one_iff_mod_eight_eq_three_or_seven n i).mpr
      (Or.inr hmod8)
  have hs : s (iterateT i n) = 1 := by
    simpa [orbitWindowHeight_eq_s_iterateT] using hheight
  rw [oddOrbitLabel_succ_eq_T_iterateT]
  rw [T_val_eq_three_mul_add_one_div_two_of_s_eq_one (iterateT i n) hs]
  exact next_mod_sixteen_of_mod_thirtytwo_eq_fifteen hmod

/--
The `31 mod 32` subchannel continues as `15 mod 16` at the next label.

This is the next retention-continuation branch.  Continuing exact height-one
motion now forces the source into a thinner 2-adic cylinder.
-/
theorem oddOrbitLabel_succ_mod_sixteen_eq_fifteen_of_mod_thirtytwo_eq_thirtyone
    (n : OddNat) (i : ℕ)
    (hmod : oddOrbitLabel n i % 32 = 31) :
    oddOrbitLabel n (i + 1) % 16 = 15 := by
  have hmod8 : oddOrbitLabel n i % 8 = 7 := by
    omega
  have hheight : orbitWindowHeight n i = 1 :=
    (orbitWindowHeight_eq_one_iff_mod_eight_eq_three_or_seven n i).mpr
      (Or.inr hmod8)
  have hs : s (iterateT i n) = 1 := by
    simpa [orbitWindowHeight_eq_s_iterateT] using hheight
  rw [oddOrbitLabel_succ_eq_T_iterateT]
  rw [T_val_eq_three_mul_add_one_div_two_of_s_eq_one (iterateT i n) hs]
  exact next_mod_sixteen_of_mod_thirtytwo_eq_thirtyone hmod

/--
The `31 mod 64` subchannel moves to `15 mod 32` at the next label.

This is the next recovery sibling inside the narrowing retention cylinder.
-/
theorem oddOrbitLabel_succ_mod_thirtytwo_eq_fifteen_of_mod_sixtyfour_eq_thirtyone
    (n : OddNat) (i : ℕ)
    (hmod : oddOrbitLabel n i % 64 = 31) :
    oddOrbitLabel n (i + 1) % 32 = 15 := by
  have hmod8 : oddOrbitLabel n i % 8 = 7 := by
    omega
  have hheight : orbitWindowHeight n i = 1 :=
    (orbitWindowHeight_eq_one_iff_mod_eight_eq_three_or_seven n i).mpr
      (Or.inr hmod8)
  have hs : s (iterateT i n) = 1 := by
    simpa [orbitWindowHeight_eq_s_iterateT] using hheight
  rw [oddOrbitLabel_succ_eq_T_iterateT]
  rw [T_val_eq_three_mul_add_one_div_two_of_s_eq_one (iterateT i n) hs]
  exact next_mod_thirtytwo_of_mod_sixtyfour_eq_thirtyone hmod

/--
The `63 mod 64` subchannel continues as `31 mod 32` at the next label.

The low-peeling path survives only by entering the next thinner cylinder.
-/
theorem oddOrbitLabel_succ_mod_thirtytwo_eq_thirtyone_of_mod_sixtyfour_eq_sixtythree
    (n : OddNat) (i : ℕ)
    (hmod : oddOrbitLabel n i % 64 = 63) :
    oddOrbitLabel n (i + 1) % 32 = 31 := by
  have hmod8 : oddOrbitLabel n i % 8 = 7 := by
    omega
  have hheight : orbitWindowHeight n i = 1 :=
    (orbitWindowHeight_eq_one_iff_mod_eight_eq_three_or_seven n i).mpr
      (Or.inr hmod8)
  have hs : s (iterateT i n) = 1 := by
    simpa [orbitWindowHeight_eq_s_iterateT] using hheight
  rw [oddOrbitLabel_succ_eq_T_iterateT]
  rw [T_val_eq_three_mul_add_one_div_two_of_s_eq_one (iterateT i n) hs]
  exact next_mod_thirtytwo_of_mod_sixtyfour_eq_sixtythree hmod

/--
The `63 mod 128` subchannel moves to `31 mod 64` at the next label.

This is the level-`4` recovery sibling inside the narrowing retention cylinder.
-/
theorem oddOrbitLabel_succ_mod_sixtyfour_eq_thirtyone_of_mod_onehundredtwentyeight_eq_sixtythree
    (n : OddNat) (i : ℕ)
    (hmod : oddOrbitLabel n i % 128 = 63) :
    oddOrbitLabel n (i + 1) % 64 = 31 := by
  have hmod8 : oddOrbitLabel n i % 8 = 7 := by
    omega
  have hheight : orbitWindowHeight n i = 1 :=
    (orbitWindowHeight_eq_one_iff_mod_eight_eq_three_or_seven n i).mpr
      (Or.inr hmod8)
  have hs : s (iterateT i n) = 1 := by
    simpa [orbitWindowHeight_eq_s_iterateT] using hheight
  rw [oddOrbitLabel_succ_eq_T_iterateT]
  rw [T_val_eq_three_mul_add_one_div_two_of_s_eq_one (iterateT i n) hs]
  exact next_mod_sixtyfour_of_mod_onehundredtwentyeight_eq_sixtythree hmod

/--
The `127 mod 128` subchannel continues as `63 mod 64` at the next label.

The low-peeling path survives by entering the next thinner all-ones cylinder.
-/
theorem oddOrbitLabel_succ_mod64_eq63_of_mod128_eq127
    (n : OddNat) (i : ℕ)
    (hmod : oddOrbitLabel n i % 128 = 127) :
    oddOrbitLabel n (i + 1) % 64 = 63 := by
  have hmod8 : oddOrbitLabel n i % 8 = 7 := by
    omega
  have hheight : orbitWindowHeight n i = 1 :=
    (orbitWindowHeight_eq_one_iff_mod_eight_eq_three_or_seven n i).mpr
      (Or.inr hmod8)
  have hs : s (iterateT i n) = 1 := by
    simpa [orbitWindowHeight_eq_s_iterateT] using hheight
  rw [oddOrbitLabel_succ_eq_T_iterateT]
  rw [T_val_eq_three_mul_add_one_div_two_of_s_eq_one (iterateT i n) hs]
  exact next_mod_sixtyfour_of_mod_onehundredtwentyeight_eq_onehundredtwentyseven hmod

/--
The `127 mod 256` subchannel moves to `63 mod 128` at the next label.

This is the level-`5` recovery sibling inside the narrowing retention cylinder.
-/
theorem oddOrbitLabel_succ_mod128_eq63_of_mod256_eq127
    (n : OddNat) (i : ℕ)
    (hmod : oddOrbitLabel n i % 256 = 127) :
    oddOrbitLabel n (i + 1) % 128 = 63 := by
  have hmod8 : oddOrbitLabel n i % 8 = 7 := by
    omega
  have hheight : orbitWindowHeight n i = 1 :=
    (orbitWindowHeight_eq_one_iff_mod_eight_eq_three_or_seven n i).mpr
      (Or.inr hmod8)
  have hs : s (iterateT i n) = 1 := by
    simpa [orbitWindowHeight_eq_s_iterateT] using hheight
  rw [oddOrbitLabel_succ_eq_T_iterateT]
  rw [T_val_eq_three_mul_add_one_div_two_of_s_eq_one (iterateT i n) hs]
  exact
    next_mod_onehundredtwentyeight_of_mod_twohundredfiftysix_eq_onehundredtwentyseven
      hmod

/--
The `255 mod 256` subchannel continues as `127 mod 128` at the next label.

The low-peeling path survives by entering the next thinner all-ones cylinder.
-/
theorem oddOrbitLabel_succ_mod128_eq127_of_mod256_eq255
    (n : OddNat) (i : ℕ)
    (hmod : oddOrbitLabel n i % 256 = 255) :
    oddOrbitLabel n (i + 1) % 128 = 127 := by
  have hmod8 : oddOrbitLabel n i % 8 = 7 := by
    omega
  have hheight : orbitWindowHeight n i = 1 :=
    (orbitWindowHeight_eq_one_iff_mod_eight_eq_three_or_seven n i).mpr
      (Or.inr hmod8)
  have hs : s (iterateT i n) = 1 := by
    simpa [orbitWindowHeight_eq_s_iterateT] using hheight
  rw [oddOrbitLabel_succ_eq_T_iterateT]
  rw [T_val_eq_three_mul_add_one_div_two_of_s_eq_one (iterateT i n) hs]
  exact
    next_mod_onehundredtwentyeight_of_mod_twohundredfiftysix_eq_twohundredfiftyfive
      hmod

/--
General orbit-label transition for the recovery sibling.

If the current label lies in the recovery sibling modulo `2^(r + 2)` and
`2 <= r`, then the source is in the exact height-one `7 mod 8` channel and the
next accelerated label lands in the outward retention residue.
-/
theorem oddOrbitLabel_succ_recovery_residue_of_mod
    (r : ℕ) (hr : 2 ≤ r) (n : OddNat) (i : ℕ)
    (hmod :
      oddOrbitLabel n i % (2 ^ (r + 2)) = 2 ^ (r + 1) - 1) :
    oddOrbitLabel n (i + 1) % (2 ^ (r + 1)) = 2 ^ r - 1 := by
  have hmod8 : oddOrbitLabel n i % 8 = 7 :=
    mod_eight_eq_seven_of_recovery_residue_of_two_le r (oddOrbitLabel n i) hr hmod
  have hheight : orbitWindowHeight n i = 1 :=
    (orbitWindowHeight_eq_one_iff_mod_eight_eq_three_or_seven n i).mpr
      (Or.inr hmod8)
  have hs : s (iterateT i n) = 1 := by
    simpa [orbitWindowHeight_eq_s_iterateT] using hheight
  rw [oddOrbitLabel_succ_eq_T_iterateT]
  rw [T_val_eq_three_mul_add_one_div_two_of_s_eq_one (iterateT i n) hs]
  exact next_recovery_residue_of_mod r (oddOrbitLabel n i) hmod

/--
General orbit-label transition for the continuation sibling.

If the current label lies in the continuation sibling modulo `2^(r + 2)` and
`1 <= r`, then the source is in the exact height-one `7 mod 8` channel and the
next accelerated label lands in the next retention cell.
-/
theorem oddOrbitLabel_succ_continuation_residue_of_mod
    (r : ℕ) (hr : 1 ≤ r) (n : OddNat) (i : ℕ)
    (hmod :
      oddOrbitLabel n i % (2 ^ (r + 2)) = 2 ^ (r + 2) - 1) :
    oddOrbitLabel n (i + 1) % (2 ^ (r + 1)) =
      2 ^ (r + 1) - 1 := by
  have hmod8 : oddOrbitLabel n i % 8 = 7 :=
    mod_eight_eq_seven_of_continuation_residue_of_one_le
      r (oddOrbitLabel n i) hr hmod
  have hheight : orbitWindowHeight n i = 1 :=
    (orbitWindowHeight_eq_one_iff_mod_eight_eq_three_or_seven n i).mpr
      (Or.inr hmod8)
  have hs : s (iterateT i n) = 1 := by
    simpa [orbitWindowHeight_eq_s_iterateT] using hheight
  rw [oddOrbitLabel_succ_eq_T_iterateT]
  rw [T_val_eq_three_mul_add_one_div_two_of_s_eq_one (iterateT i n) hs]
  exact next_continuation_residue_of_mod r (oddOrbitLabel n i) hmod

/--
Delayed peeling from the `3 mod 8` height-one channel.

The current step has exact height `1`, but the next label lands in
`1 mod 4`, so the next observed height is at least `2`.
-/
theorem orbitWindowNextHeight_two_le_of_mod_eight_eq_three
    (n : OddNat) (i : ℕ)
    (hmod : oddOrbitLabel n i % 8 = 3) :
    2 ≤ orbitWindowHeight n (i + 1) := by
  apply (orbitWindowHeight_two_le_iff_mod_four_eq_one n (i + 1)).mpr
  exact oddOrbitLabel_succ_mod_four_eq_one_of_mod_eight_eq_three n i hmod

/--
Every shifted-tail `3 mod 8` entry contributes a shifted-tail `height >= 2`
entry one step later.

The source side counts labels at times `1..k`; the target side counts heights
at times `1..k+1`, so the delayed image fits into the one-step-longer tail
window.
-/
theorem tailMod8Three_le_nextTailHeightCountGe_two
    (n : OddNat) (k : ℕ) :
    orbitWindowResidueCountMod8EqThreeTail n k ≤
      orbitWindowHeightCountGeTail n (k + 1) 2 := by
  unfold orbitWindowResidueCountMod8EqThreeTail
  unfold orbitWindowHeightCountGeTail
  induction k with
  | zero =>
      simp
  | succ k ih =>
      rw [List.range_succ, List.range_succ]
      have htransition :
          oddOrbitLabel n (k + 1) % 8 = 3 →
            2 ≤ orbitWindowHeight n ((k + 1) + 1) :=
        orbitWindowNextHeight_two_le_of_mod_eight_eq_three n (k + 1)
      by_cases hsource : oddOrbitLabel n (k + 1) % 8 = 3
      · have htarget : 2 ≤ orbitWindowHeight n ((k + 1) + 1) :=
          htransition hsource
        simp [hsource, htarget]
        omega
      · by_cases htarget : 2 ≤ orbitWindowHeight n ((k + 1) + 1)
        · simp [hsource, htarget]
          omega
        · simp [hsource, htarget]
          omega

/--
The `7 mod 8` height-one channel remains an exact height-one channel at the
next label.

This is the complementary transition to the delayed-peeling
`3 mod 8 -> next height >= 2` edge.
-/
theorem orbitWindowNextHeight_eq_one_of_mod_eight_eq_seven
    (n : OddNat) (i : ℕ)
    (hmod : oddOrbitLabel n i % 8 = 7) :
    orbitWindowHeight n (i + 1) = 1 := by
  apply (orbitWindowHeight_eq_one_iff_mod_four_eq_three n (i + 1)).mpr
  exact oddOrbitLabel_succ_mod_four_eq_three_of_mod_eight_eq_seven n i hmod

/--
Every shifted-tail `7 mod 8` entry remains in the shifted-tail exact-height-one
reservoir one step later.

This is the count-level recursion edge for the continuing color.
-/
theorem tailMod8Seven_le_nextTailHeightCountEq_one
    (n : OddNat) (k : ℕ) :
    orbitWindowResidueCountMod8EqSevenTail n k ≤
      orbitWindowHeightCountEqTail n (k + 1) 1 := by
  unfold orbitWindowResidueCountMod8EqSevenTail
  unfold orbitWindowHeightCountEqTail
  induction k with
  | zero =>
      simp
  | succ k ih =>
      rw [List.range_succ, List.range_succ]
      have htransition :
          oddOrbitLabel n (k + 1) % 8 = 7 →
            orbitWindowHeight n ((k + 1) + 1) = 1 :=
        orbitWindowNextHeight_eq_one_of_mod_eight_eq_seven n (k + 1)
      by_cases hsource : oddOrbitLabel n (k + 1) % 8 = 7
      · have htarget : orbitWindowHeight n ((k + 1) + 1) = 1 :=
          htransition hsource
        simp [hsource, htarget]
        omega
      · by_cases htarget : orbitWindowHeight n ((k + 1) + 1) = 1
        · simp [hsource, htarget]
          omega
        · simp [hsource, htarget]
          omega

/--
The shifted-tail `7 mod 8` continuing color enters the next shifted-tail
exact-height-one reservoir, which then splits again into `3 mod 8` and
`7 mod 8` colors.
-/
theorem tailMod8Seven_le_nextTailMod8Three_add_nextTailMod8Seven
    (n : OddNat) (k : ℕ) :
    orbitWindowResidueCountMod8EqSevenTail n k ≤
      orbitWindowResidueCountMod8EqThreeTail n (k + 1) +
        orbitWindowResidueCountMod8EqSevenTail n (k + 1) := by
  have h :
      orbitWindowResidueCountMod8EqSevenTail n k ≤
        orbitWindowHeightCountEqTail n (k + 1) 1 :=
    tailMod8Seven_le_nextTailHeightCountEq_one n k
  rw [tailHeightCountEq_one_split_mod8_three_seven] at h
  exact h

/--
Level-alias version of the level-`1` recursion edge.

The level-`1` remainder enters the next tail reservoir and splits into the
level-`1` falling color and the level-`1` remainder at the next window.
-/
theorem tailRemainderLevel1_step_grammar
    (n : OddNat) (k : ℕ) :
    TailRemainderLevel1 n k ≤
      TailFallingLevel1 n (k + 1) + TailRemainderLevel1 n (k + 1) := by
  unfold TailRemainderLevel1 TailFallingLevel1
  exact tailMod8Seven_le_nextTailMod8Three_add_nextTailMod8Seven n k

/--
The shifted-tail `15 mod 16` continuing color enters the next shifted-tail
`7 mod 16 / 15 mod 16` split.

This is the level-`2` recursion edge of the delayed-reservoir tower.
-/
theorem tailMod16Fifteen_le_nextTailMod16Seven_add_nextTailMod16Fifteen
    (n : OddNat) (k : ℕ) :
    orbitWindowResidueCountMod16EqFifteenTail n k ≤
      orbitWindowResidueCountMod16EqSevenTail n (k + 1) +
        orbitWindowResidueCountMod16EqFifteenTail n (k + 1) := by
  unfold orbitWindowResidueCountMod16EqFifteenTail
  unfold orbitWindowResidueCountMod16EqSevenTail
  induction k with
  | zero =>
      simp
  | succ k ih =>
      rw [List.range_succ, List.range_succ]
      have htransitionSeven :
          oddOrbitLabel n (k + 1) % 32 = 15 →
            oddOrbitLabel n ((k + 1) + 1) % 16 = 7 :=
        oddOrbitLabel_succ_mod_sixteen_eq_seven_of_mod_thirtytwo_eq_fifteen
          n (k + 1)
      have htransitionFifteen :
          oddOrbitLabel n (k + 1) % 32 = 31 →
            oddOrbitLabel n ((k + 1) + 1) % 16 = 15 :=
        oddOrbitLabel_succ_mod_sixteen_eq_fifteen_of_mod_thirtytwo_eq_thirtyone
          n (k + 1)
      by_cases hsource : oddOrbitLabel n (k + 1) % 16 = 15
      · have hchild :
            oddOrbitLabel n (k + 1) % 32 = 15 ∨
              oddOrbitLabel n (k + 1) % 32 = 31 := by
          omega
        cases hchild with
        | inl hfifteen =>
            have htargetSeven :
                oddOrbitLabel n ((k + 1) + 1) % 16 = 7 :=
              htransitionSeven hfifteen
            have htargetNotFifteen :
                oddOrbitLabel n ((k + 1) + 1) % 16 ≠ 15 := by
              omega
            simp [hsource, htargetSeven]
            omega
        | inr h31 =>
            have htargetFifteen :
                oddOrbitLabel n ((k + 1) + 1) % 16 = 15 :=
              htransitionFifteen h31
            simp [hsource, htargetFifteen]
            omega
      · by_cases htargetSeven : oddOrbitLabel n ((k + 1) + 1) % 16 = 7
        · simp [hsource, htargetSeven]
          omega
        · by_cases htargetFifteen :
            oddOrbitLabel n ((k + 1) + 1) % 16 = 15
          · simp [hsource, htargetFifteen]
            omega
          · simp [hsource, htargetSeven, htargetFifteen]
            omega

/--
Level-alias version of the level-`2` recursion edge.

The level-`2` remainder re-enters the next level-`2` falling/remainder split.
-/
theorem tailRemainderLevel2_step_grammar
    (n : OddNat) (k : ℕ) :
    TailRemainderLevel2 n k ≤
      TailFallingLevel2 n (k + 1) + TailRemainderLevel2 n (k + 1) := by
  unfold TailRemainderLevel2 TailFallingLevel2
  exact tailMod16Fifteen_le_nextTailMod16Seven_add_nextTailMod16Fifteen n k

/--
The shifted-tail `31 mod 32` continuing color enters the next shifted-tail
`15 mod 32 / 31 mod 32` split.

This is the level-`3` recursion edge of the delayed-reservoir tower.
-/
theorem tailMod32ThirtyOne_le_nextTailMod32Fifteen_add_nextTailMod32ThirtyOne
    (n : OddNat) (k : ℕ) :
    orbitWindowResidueCountMod32EqThirtyOneTail n k ≤
      orbitWindowResidueCountMod32EqFifteenTail n (k + 1) +
        orbitWindowResidueCountMod32EqThirtyOneTail n (k + 1) := by
  unfold orbitWindowResidueCountMod32EqThirtyOneTail
  unfold orbitWindowResidueCountMod32EqFifteenTail
  induction k with
  | zero =>
      simp
  | succ k ih =>
      rw [List.range_succ, List.range_succ]
      have htransitionFifteen :
          oddOrbitLabel n (k + 1) % 64 = 31 →
            oddOrbitLabel n ((k + 1) + 1) % 32 = 15 :=
        oddOrbitLabel_succ_mod_thirtytwo_eq_fifteen_of_mod_sixtyfour_eq_thirtyone
          n (k + 1)
      have htransitionThirtyOne :
          oddOrbitLabel n (k + 1) % 64 = 63 →
            oddOrbitLabel n ((k + 1) + 1) % 32 = 31 :=
        oddOrbitLabel_succ_mod_thirtytwo_eq_thirtyone_of_mod_sixtyfour_eq_sixtythree
          n (k + 1)
      by_cases hsource : oddOrbitLabel n (k + 1) % 32 = 31
      · have hchild :
            oddOrbitLabel n (k + 1) % 64 = 31 ∨
              oddOrbitLabel n (k + 1) % 64 = 63 := by
          omega
        cases hchild with
        | inl h31 =>
            have htargetFifteen :
                oddOrbitLabel n ((k + 1) + 1) % 32 = 15 :=
              htransitionFifteen h31
            simp [hsource, htargetFifteen]
            omega
        | inr h63 =>
            have htargetThirtyOne :
                oddOrbitLabel n ((k + 1) + 1) % 32 = 31 :=
              htransitionThirtyOne h63
            simp [hsource, htargetThirtyOne]
            omega
      · by_cases htargetFifteen :
            oddOrbitLabel n ((k + 1) + 1) % 32 = 15
        · simp [hsource, htargetFifteen]
          omega
        · by_cases htargetThirtyOne :
            oddOrbitLabel n ((k + 1) + 1) % 32 = 31
          · simp [hsource, htargetThirtyOne]
            omega
          · simp [hsource, htargetFifteen, htargetThirtyOne]
            omega

/--
Level-alias version of the level-`3` recursion edge.

The level-`3` remainder re-enters the next level-`3` falling/remainder split.
-/
theorem tailRemainderLevel3_step_grammar
    (n : OddNat) (k : ℕ) :
    TailRemainderLevel3 n k ≤
      TailFallingLevel3 n (k + 1) + TailRemainderLevel3 n (k + 1) := by
  unfold TailRemainderLevel3 TailFallingLevel3
  exact tailMod32ThirtyOne_le_nextTailMod32Fifteen_add_nextTailMod32ThirtyOne n k

/--
The shifted-tail `63 mod 64` continuing color enters the next shifted-tail
`31 mod 64 / 63 mod 64` split.

This is the level-`4` recursion edge of the delayed-reservoir tower.
-/
theorem tailMod64SixtyThree_le_nextTailMod64ThirtyOne_add_nextTailMod64SixtyThree
    (n : OddNat) (k : ℕ) :
    orbitWindowResidueCountMod64EqSixtyThreeTail n k ≤
      orbitWindowResidueCountMod64EqThirtyOneTail n (k + 1) +
        orbitWindowResidueCountMod64EqSixtyThreeTail n (k + 1) := by
  unfold orbitWindowResidueCountMod64EqSixtyThreeTail
  unfold orbitWindowResidueCountMod64EqThirtyOneTail
  induction k with
  | zero =>
      simp
  | succ k ih =>
      rw [List.range_succ, List.range_succ]
      have htransitionThirtyOne :
          oddOrbitLabel n (k + 1) % 128 = 63 →
            oddOrbitLabel n ((k + 1) + 1) % 64 = 31 :=
        oddOrbitLabel_succ_mod_sixtyfour_eq_thirtyone_of_mod_onehundredtwentyeight_eq_sixtythree
          n (k + 1)
      have htransitionSixtyThree :
          oddOrbitLabel n (k + 1) % 128 = 127 →
            oddOrbitLabel n ((k + 1) + 1) % 64 = 63 :=
        oddOrbitLabel_succ_mod64_eq63_of_mod128_eq127 n (k + 1)
      by_cases hsource : oddOrbitLabel n (k + 1) % 64 = 63
      · have hchild :
            oddOrbitLabel n (k + 1) % 128 = 63 ∨
              oddOrbitLabel n (k + 1) % 128 = 127 := by
          omega
        cases hchild with
        | inl h63 =>
            have htargetThirtyOne :
                oddOrbitLabel n ((k + 1) + 1) % 64 = 31 :=
              htransitionThirtyOne h63
            simp [hsource, htargetThirtyOne]
            omega
        | inr h127 =>
            have htargetSixtyThree :
                oddOrbitLabel n ((k + 1) + 1) % 64 = 63 :=
              htransitionSixtyThree h127
            simp [hsource, htargetSixtyThree]
            omega
      · by_cases htargetThirtyOne :
            oddOrbitLabel n ((k + 1) + 1) % 64 = 31
        · simp [hsource, htargetThirtyOne]
          omega
        · by_cases htargetSixtyThree :
            oddOrbitLabel n ((k + 1) + 1) % 64 = 63
          · simp [hsource, htargetSixtyThree]
            omega
          · simp [hsource, htargetThirtyOne, htargetSixtyThree]
            omega

/--
Level-alias version of the level-`4` recursion edge.

The level-`4` remainder re-enters the next level-`4` falling/remainder split.
-/
theorem tailRemainderLevel4_step_grammar
    (n : OddNat) (k : ℕ) :
    TailRemainderLevel4 n k ≤
      TailFallingLevel4 n (k + 1) + TailRemainderLevel4 n (k + 1) := by
  unfold TailRemainderLevel4 TailFallingLevel4
  exact tailMod64SixtyThree_le_nextTailMod64ThirtyOne_add_nextTailMod64SixtyThree n k

/--
The shifted-tail `127 mod 128` continuing color enters the next shifted-tail
`63 mod 128 / 127 mod 128` split.

This is the level-`5` recursion edge of the delayed-reservoir tower.
-/
theorem tailMod128Eq127_le_nextTailMod128Eq63_add_nextTailMod128Eq127
    (n : OddNat) (k : ℕ) :
    orbitWindowResidueCountMod128EqOneHundredTwentySevenTail n k ≤
      orbitWindowResidueCountMod128EqSixtyThreeTail n (k + 1) +
        orbitWindowResidueCountMod128EqOneHundredTwentySevenTail n (k + 1) := by
  unfold orbitWindowResidueCountMod128EqOneHundredTwentySevenTail
  unfold orbitWindowResidueCountMod128EqSixtyThreeTail
  induction k with
  | zero =>
      simp
  | succ k ih =>
      rw [List.range_succ, List.range_succ]
      have htransitionSixtyThree :
          oddOrbitLabel n (k + 1) % 256 = 127 →
            oddOrbitLabel n ((k + 1) + 1) % 128 = 63 :=
        oddOrbitLabel_succ_mod128_eq63_of_mod256_eq127 n (k + 1)
      have htransitionOneHundredTwentySeven :
          oddOrbitLabel n (k + 1) % 256 = 255 →
            oddOrbitLabel n ((k + 1) + 1) % 128 = 127 :=
        oddOrbitLabel_succ_mod128_eq127_of_mod256_eq255 n (k + 1)
      by_cases hsource : oddOrbitLabel n (k + 1) % 128 = 127
      · have hchild :
            oddOrbitLabel n (k + 1) % 256 = 127 ∨
              oddOrbitLabel n (k + 1) % 256 = 255 := by
          omega
        cases hchild with
        | inl h127 =>
            have htargetSixtyThree :
                oddOrbitLabel n ((k + 1) + 1) % 128 = 63 :=
              htransitionSixtyThree h127
            simp [hsource, htargetSixtyThree]
            omega
        | inr h255 =>
            have htargetOneHundredTwentySeven :
                oddOrbitLabel n ((k + 1) + 1) % 128 = 127 :=
              htransitionOneHundredTwentySeven h255
            simp [hsource, htargetOneHundredTwentySeven]
            omega
      · by_cases htargetSixtyThree :
            oddOrbitLabel n ((k + 1) + 1) % 128 = 63
        · simp [hsource, htargetSixtyThree]
          omega
        · by_cases htargetOneHundredTwentySeven :
            oddOrbitLabel n ((k + 1) + 1) % 128 = 127
          · simp [hsource, htargetOneHundredTwentySeven]
            omega
          · simp [hsource, htargetSixtyThree, htargetOneHundredTwentySeven]
            omega

/--
Level-alias version of the level-`5` recursion edge.

The level-`5` remainder re-enters the next level-`5` falling/remainder split.
-/
theorem tailRemainderLevel5_step_grammar
    (n : OddNat) (k : ℕ) :
    TailRemainderLevel5 n k ≤
      TailFallingLevel5 n (k + 1) + TailRemainderLevel5 n (k + 1) := by
  unfold TailRemainderLevel5 TailFallingLevel5
  exact
    tailMod128Eq127_le_nextTailMod128Eq63_add_nextTailMod128Eq127
      n k

/--
One-step grammar for the shifted-tail exact-height-one reservoir.

Each current exact-height-one tail entry either contributes to the next tail
`height >= 2` count through the `3 mod 8` delayed-peeling color, or remains in
the next exact-height-one reservoir through the `7 mod 8` continuing color.
-/
theorem tailExactHeightOneReservoir_step_grammar
    (n : OddNat) (k : ℕ) :
    orbitWindowHeightCountEqTail n k 1 ≤
      orbitWindowHeightCountGeTail n (k + 1) 2 +
        orbitWindowHeightCountEqTail n (k + 1) 1 := by
  rw [tailHeightCountEq_one_split_mod8_three_seven]
  have hthree :
      orbitWindowResidueCountMod8EqThreeTail n k ≤
        orbitWindowHeightCountGeTail n (k + 1) 2 :=
    tailMod8Three_le_nextTailHeightCountGe_two n k
  have hseven :
      orbitWindowResidueCountMod8EqSevenTail n k ≤
        orbitWindowHeightCountEqTail n (k + 1) 1 :=
    tailMod8Seven_le_nextTailHeightCountEq_one n k
  omega

/--
The `7 mod 16` branch recovers delayed peeling after two transitions.

At time `i`, the label is in the retaining `7 mod 8` channel.  The finer
`7 mod 16` coordinate sends the next label to `3 mod 8`, so the following
height is at least `2`.
-/
theorem orbitWindowNextNextHeight_two_le_of_mod_sixteen_eq_seven
    (n : OddNat) (i : ℕ)
    (hmod : oddOrbitLabel n i % 16 = 7) :
    2 ≤ orbitWindowHeight n (i + 2) := by
  have hnext :
      oddOrbitLabel n (i + 1) % 8 = 3 :=
    oddOrbitLabel_succ_mod_eight_eq_three_of_mod_sixteen_eq_seven n i hmod
  simpa [Nat.add_assoc] using
    orbitWindowNextHeight_two_le_of_mod_eight_eq_three n (i + 1) hnext

/--
The `15 mod 32` branch recovers delayed peeling after three transitions.

The first transition sends `15 mod 32` to `7 mod 16`; the existing
`7 mod 16` recovery branch then forces an extra peeling height two steps later.
-/
theorem orbitWindowNextNextNextHeight_two_le_of_mod_thirtytwo_eq_fifteen
    (n : OddNat) (i : ℕ)
    (hmod : oddOrbitLabel n i % 32 = 15) :
    2 ≤ orbitWindowHeight n (i + 3) := by
  have hnext :
      oddOrbitLabel n (i + 1) % 16 = 7 :=
    oddOrbitLabel_succ_mod_sixteen_eq_seven_of_mod_thirtytwo_eq_fifteen
      n i hmod
  simpa [Nat.add_assoc] using
    orbitWindowNextNextHeight_two_le_of_mod_sixteen_eq_seven n (i + 1) hnext

/--
The `31 mod 64` branch recovers delayed peeling after four transitions.

It first moves to `15 mod 32`; the already-fixed `15 mod 32` recovery branch
then forces an extra peeling height three transitions later.
-/
theorem orbitWindowNextNextNextNextHeight_two_le_of_mod_sixtyfour_eq_thirtyone
    (n : OddNat) (i : ℕ)
    (hmod : oddOrbitLabel n i % 64 = 31) :
    2 ≤ orbitWindowHeight n (i + 4) := by
  have hnext :
      oddOrbitLabel n (i + 1) % 32 = 15 :=
    oddOrbitLabel_succ_mod_thirtytwo_eq_fifteen_of_mod_sixtyfour_eq_thirtyone
      n i hmod
  simpa [Nat.add_assoc] using
    orbitWindowNextNextNextHeight_two_le_of_mod_thirtytwo_eq_fifteen
      n (i + 1) hnext

/--
Every `3 mod 8` label in a window contributes a `1 mod 4` label in the
shifted tail window.

This is the first count-level transition statistic: the source channel is
counted at time `i`, and the receiver channel is counted at time `i + 1`.
-/
theorem orbitWindowResidueCountMod8EqThree_le_tailMod4EqOne
    (n : OddNat) (k : ℕ) :
    orbitWindowResidueCountMod8EqThree n k ≤
      orbitWindowResidueCountMod4EqOneTail n k := by
  unfold orbitWindowResidueCountMod8EqThree orbitWindowResidueCountMod4EqOneTail
  induction k with
  | zero =>
      simp
  | succ k ih =>
      rw [List.range_succ]
      have htransition :
          oddOrbitLabel n k % 8 = 3 →
            oddOrbitLabel n (k + 1) % 4 = 1 :=
        oddOrbitLabel_succ_mod_four_eq_one_of_mod_eight_eq_three n k
      by_cases hsource : oddOrbitLabel n k % 8 = 3
      · have htail : oddOrbitLabel n (k + 1) % 4 = 1 := htransition hsource
        simp [hsource, htail, ih]
      · by_cases htail : oddOrbitLabel n (k + 1) % 4 = 1
        · exact by
            simpa [hsource, htail] using Nat.le_succ_of_le ih
        · simp [hsource, htail, ih]

/--
Every `3 mod 8` source label contributes a shifted-tail entry with
height at least `2`.
-/
theorem orbitWindowResidueCountMod8EqThree_le_tailHeightCountGe_two
    (n : OddNat) (k : ℕ) :
    orbitWindowResidueCountMod8EqThree n k ≤
      orbitWindowHeightCountGeTail n k 2 := by
  rw [orbitWindowHeightCountGeTail_two_eq_tailResidueCount_mod4_eq_one]
  exact orbitWindowResidueCountMod8EqThree_le_tailMod4EqOne n k

/--
Every `7 mod 8` label in a window contributes a `3 mod 4` label in the
shifted tail window.
-/
theorem residueCountMod8EqSeven_le_nextResidueCountMod4EqThree
    (n : OddNat) (k : ℕ) :
    orbitWindowResidueCountMod8EqSeven n k ≤
      orbitWindowResidueCountMod4EqThreeTail n k := by
  unfold orbitWindowResidueCountMod8EqSeven orbitWindowResidueCountMod4EqThreeTail
  induction k with
  | zero =>
      simp
  | succ k ih =>
      rw [List.range_succ]
      have htransition :
          oddOrbitLabel n k % 8 = 7 →
            oddOrbitLabel n (k + 1) % 4 = 3 :=
        oddOrbitLabel_succ_mod_four_eq_three_of_mod_eight_eq_seven n k
      by_cases hsource : oddOrbitLabel n k % 8 = 7
      · have htail : oddOrbitLabel n (k + 1) % 4 = 3 := htransition hsource
        simp [hsource, htail, ih]
      · by_cases htail : oddOrbitLabel n (k + 1) % 4 = 3
        · exact by
            simpa [hsource, htail] using Nat.le_succ_of_le ih
        · simp [hsource, htail, ih]

/--
Count-level recursive Petal transition for the recovery sibling.

Every source-window label in the recovery sibling modulo `2^(r + 2)`
contributes a shifted-tail label in the outward retention residue modulo
`2^(r + 1)`.
-/
theorem orbitWindowRecoverySiblingCount_le_tailRetentionResidueCount
    (r : ℕ) (hr : 2 ≤ r) (n : OddNat) (k : ℕ) :
    orbitWindowResidueCountPow2 n k (r + 2) (2 ^ (r + 1) - 1) ≤
      orbitWindowResidueCountPow2Tail n k (r + 1) (2 ^ r - 1) := by
  unfold orbitWindowResidueCountPow2 orbitWindowResidueCountPow2Tail
  induction k with
  | zero =>
      simp
  | succ k ih =>
      rw [List.range_succ]
      have htransition :
          oddOrbitLabel n k % (2 ^ (r + 2)) = 2 ^ (r + 1) - 1 →
            oddOrbitLabel n (k + 1) % (2 ^ (r + 1)) = 2 ^ r - 1 :=
        oddOrbitLabel_succ_recovery_residue_of_mod r hr n k
      by_cases hsource :
          oddOrbitLabel n k % (2 ^ (r + 2)) = 2 ^ (r + 1) - 1
      · have htail :
            oddOrbitLabel n (k + 1) % (2 ^ (r + 1)) = 2 ^ r - 1 :=
          htransition hsource
        simp [hsource, htail, ih]
      · by_cases htail :
            oddOrbitLabel n (k + 1) % (2 ^ (r + 1)) = 2 ^ r - 1
        · exact by
            simpa [hsource, htail] using Nat.le_succ_of_le ih
        · simp [hsource, htail, ih]

/--
Helper-routed version of the recovery sibling count transition.

This theorem has the same statement as
`orbitWindowRecoverySiblingCount_le_tailRetentionResidueCount`, but it records
the preferred finite channel-flow route:

`pointwise residue transition -> count-level source <= shifted-tail target`.
-/
theorem orbitWindowRecoverySiblingCount_le_tailRetentionResidueCount_via_helper
    (r : ℕ) (hr : 2 ≤ r) (n : OddNat) (k : ℕ) :
    orbitWindowResidueCountPow2 n k (r + 2) (2 ^ (r + 1) - 1) ≤
      orbitWindowResidueCountPow2Tail n k (r + 1) (2 ^ r - 1) := by
  apply orbitWindowResidueCountPow2_le_tail_of_pointwise
  intro i _hi hsource
  exact oddOrbitLabel_succ_recovery_residue_of_mod r hr n i hsource

/--
Mass-name spelling of the recovery channel-flow theorem.

At parent depth `r + 1`, the source recovery sibling flows into the shifted-tail
recovery sibling at parent depth `r`.
-/
theorem orbitWindowRecoverySiblingMass_succ_le_tailRecoverySiblingMass
    (r : ℕ) (hr : 2 ≤ r) (n : OddNat) (k : ℕ) :
    orbitWindowRecoverySiblingMassPow2 n k (r + 1) ≤
      orbitWindowRecoverySiblingMassPow2Tail n k r := by
  unfold orbitWindowRecoverySiblingMassPow2 orbitWindowRecoverySiblingMassPow2Tail
  exact orbitWindowRecoverySiblingCount_le_tailRetentionResidueCount_via_helper r hr n k

/--
Forcing-name alias for the recovery channel-flow theorem.

The source recovery mass at parent depth `r + 1` forces at least that much mass
in the shifted-tail recovery sibling at parent depth `r`.
-/
theorem orbitWindowRecoveryMass_forces_tailRecovery
    (r : ℕ) (hr : 2 ≤ r) (n : OddNat) (k : ℕ) :
    orbitWindowRecoverySiblingMassPow2 n k (r + 1) ≤
      orbitWindowRecoverySiblingMassPow2Tail n k r :=
  orbitWindowRecoverySiblingMass_succ_le_tailRecoverySiblingMass r hr n k

/--
Source recovery mass at parent depth `3` lands in the shifted-tail delayed
`3 mod 8` color.

This is the recovery-side counterpart to the continuation-retention reservoir
result: recovery does not land directly in `height >= 2` at this depth, but it
does land in the color that peels on the next step.
-/
theorem sourceRecoveryMass_depth_three_le_tailResidueCount_mod8_eq_three
    (n : OddNat) (k : ℕ) :
    orbitWindowRecoverySiblingMassPow2 n k 3 ≤
      orbitWindowResidueCountMod8EqThreeTail n k := by
  have hflow :
      orbitWindowRecoverySiblingMassPow2 n k (2 + 1) ≤
        orbitWindowRecoverySiblingMassPow2Tail n k 2 :=
    orbitWindowRecoveryMass_forces_tailRecovery 2 (by omega) n k
  have htail :
      orbitWindowRecoverySiblingMassPow2Tail n k 2 ≤
        orbitWindowResidueCountMod8EqThreeTail n k :=
    tailRecoveryMass_depth_two_le_tailResidueCount_mod8_eq_three n k
  simpa using le_trans hflow htail

/--
Count-level recursive Petal transition for the continuation sibling.

Every source-window label in the continuation sibling modulo `2^(r + 2)`
contributes a shifted-tail label in the next retention cell modulo
`2^(r + 1)`.
-/
theorem orbitWindowContinuationSiblingCount_le_tailRetentionResidueCount
    (r : ℕ) (hr : 1 ≤ r) (n : OddNat) (k : ℕ) :
    orbitWindowResidueCountPow2 n k (r + 2) (2 ^ (r + 2) - 1) ≤
      orbitWindowResidueCountPow2Tail n k (r + 1) (2 ^ (r + 1) - 1) := by
  unfold orbitWindowResidueCountPow2 orbitWindowResidueCountPow2Tail
  induction k with
  | zero =>
      simp
  | succ k ih =>
      rw [List.range_succ]
      have htransition :
          oddOrbitLabel n k % (2 ^ (r + 2)) = 2 ^ (r + 2) - 1 →
            oddOrbitLabel n (k + 1) % (2 ^ (r + 1)) = 2 ^ (r + 1) - 1 :=
        oddOrbitLabel_succ_continuation_residue_of_mod r hr n k
      by_cases hsource :
          oddOrbitLabel n k % (2 ^ (r + 2)) = 2 ^ (r + 2) - 1
      · have htail :
            oddOrbitLabel n (k + 1) % (2 ^ (r + 1)) = 2 ^ (r + 1) - 1 :=
          htransition hsource
        simp [hsource, htail, ih]
      · by_cases htail :
            oddOrbitLabel n (k + 1) % (2 ^ (r + 1)) = 2 ^ (r + 1) - 1
        · exact by
            simpa [hsource, htail] using Nat.le_succ_of_le ih
        · simp [hsource, htail, ih]

/--
Helper-routed version of the continuation sibling count transition.

This theorem has the same statement as
`orbitWindowContinuationSiblingCount_le_tailRetentionResidueCount`, but it
records the preferred finite channel-flow route:

`pointwise residue transition -> count-level source <= shifted-tail target`.
-/
theorem orbitWindowContinuationSiblingCount_le_tailRetentionResidueCount_via_helper
    (r : ℕ) (hr : 1 ≤ r) (n : OddNat) (k : ℕ) :
    orbitWindowResidueCountPow2 n k (r + 2) (2 ^ (r + 2) - 1) ≤
      orbitWindowResidueCountPow2Tail n k (r + 1) (2 ^ (r + 1) - 1) := by
  apply orbitWindowResidueCountPow2_le_tail_of_pointwise
  intro i _hi hsource
  exact oddOrbitLabel_succ_continuation_residue_of_mod r hr n i hsource

/--
Mass-name spelling of the continuation channel-flow theorem.

At parent depth `r + 1`, the source continuation sibling flows into tail
retention at depth `r + 1`.
-/
theorem orbitWindowContinuationSiblingMass_succ_le_tailRetentionMass
    (r : ℕ) (hr : 1 ≤ r) (n : OddNat) (k : ℕ) :
    orbitWindowContinuationSiblingMassPow2 n k (r + 1) ≤
      orbitWindowRetentionMassPow2Tail n k (r + 1) := by
  unfold orbitWindowContinuationSiblingMassPow2 orbitWindowRetentionMassPow2Tail
  exact orbitWindowContinuationSiblingCount_le_tailRetentionResidueCount_via_helper r hr n k

/--
Forcing-name alias for the continuation channel-flow theorem.

The source continuation mass at parent depth `r + 1` must fit inside shifted-tail
retention at the same depth.
-/
theorem orbitWindowContinuationMass_forces_tailRetention
    (r : ℕ) (hr : 1 ≤ r) (n : OddNat) (k : ℕ) :
    orbitWindowContinuationSiblingMassPow2 n k (r + 1) ≤
      orbitWindowRetentionMassPow2Tail n k (r + 1) :=
  orbitWindowContinuationSiblingMass_succ_le_tailRetentionMass r hr n k

/--
Continuation mass is bounded by the two child masses of the shifted-tail
retention cylinder.

This packages the two-step reading:

`source continuation <= tail retention`
and
`tail retention = tail recovery + tail continuation`.
-/
theorem orbitWindowContinuationMass_le_tailRecovery_add_tailContinuation
    (r : ℕ) (hr : 1 ≤ r) (n : OddNat) (k : ℕ) :
    orbitWindowContinuationSiblingMassPow2 n k (r + 1) ≤
      orbitWindowRecoverySiblingMassPow2Tail n k (r + 1) +
        orbitWindowContinuationSiblingMassPow2Tail n k (r + 1) := by
  calc
    orbitWindowContinuationSiblingMassPow2 n k (r + 1)
        ≤ orbitWindowRetentionMassPow2Tail n k (r + 1) :=
          orbitWindowContinuationMass_forces_tailRetention r hr n k
    _ = orbitWindowRecoverySiblingMassPow2Tail n k (r + 1) +
          orbitWindowContinuationSiblingMassPow2Tail n k (r + 1) := by
        rw [orbitWindowRetentionMassPow2Tail_split]

/--
Tail-budget spelling of
`orbitWindowContinuationMass_le_tailRecovery_add_tailContinuation`.
-/
theorem orbitWindowContinuationMass_tailBudget
    (r : ℕ) (hr : 1 ≤ r) (n : OddNat) (k : ℕ) :
    orbitWindowContinuationSiblingMassPow2 n k (r + 1) ≤
      orbitWindowRecoverySiblingMassPow2Tail n k (r + 1) +
        orbitWindowContinuationSiblingMassPow2Tail n k (r + 1) :=
  orbitWindowContinuationMass_le_tailRecovery_add_tailContinuation r hr n k

/--
Meaning-name alias for the continuation-to-tail-retention channel.

At parent depth `r + 1`, source continuation mass lands inside shifted-tail
retention at the same depth.
-/
theorem sourceContinuationMass_le_tailRetentionMass
    (r : ℕ) (hr : 1 ≤ r) (n : OddNat) (k : ℕ) :
    orbitWindowContinuationSiblingMassPow2 n k (r + 1) ≤
      orbitWindowRetentionMassPow2Tail n k (r + 1) :=
  orbitWindowContinuationMass_forces_tailRetention r hr n k

/--
Meaning-name alias for the shifted-tail split budget of source continuation
mass.
-/
theorem sourceContinuationMass_le_tailSplitMass
    (r : ℕ) (hr : 1 ≤ r) (n : OddNat) (k : ℕ) :
    orbitWindowContinuationSiblingMassPow2 n k (r + 1) ≤
      orbitWindowRecoverySiblingMassPow2Tail n k (r + 1) +
        orbitWindowContinuationSiblingMassPow2Tail n k (r + 1) :=
  orbitWindowContinuationMass_le_tailRecovery_add_tailContinuation r hr n k

/--
Source continuation mass at parent depth `2` lands inside the shifted-tail
exact-height-one count.

This is the corrected direct source-continuation-mass to tail-height bridge:
the continuation-retention channel feeds `3 mod 4`, not `1 mod 4`.
-/
theorem sourceContinuationMass_depth_two_le_tailHeightCountEq_one
    (n : OddNat) (k : ℕ) :
    orbitWindowContinuationSiblingMassPow2 n k 2 ≤
      orbitWindowHeightCountEqTail n k 1 := by
  have hflow :
      orbitWindowContinuationSiblingMassPow2 n k (1 + 1) ≤
        orbitWindowRetentionMassPow2Tail n k (1 + 1) :=
    sourceContinuationMass_le_tailRetentionMass 1 (by omega) n k
  have hheight :
      orbitWindowRetentionMassPow2Tail n k 2 ≤
        orbitWindowHeightCountEqTail n k 1 :=
    tailRetentionMass_depth_two_le_heightCountEq_one n k
  simpa using le_trans hflow hheight

/--
Source continuation mass at parent depth `2` enters the shifted-tail
exact-height-one reservoir, which splits into the delayed `3 mod 8` color and
the continuing `7 mod 8` color.
-/
theorem sourceContinuationMass_depth_two_le_tailMod8Three_add_tailMod8Seven
    (n : OddNat) (k : ℕ) :
    orbitWindowContinuationSiblingMassPow2 n k 2 ≤
      orbitWindowResidueCountMod8EqThreeTail n k +
        orbitWindowResidueCountMod8EqSevenTail n k := by
  have h :
      orbitWindowContinuationSiblingMassPow2 n k 2 ≤
        orbitWindowHeightCountEqTail n k 1 :=
    sourceContinuationMass_depth_two_le_tailHeightCountEq_one n k
  rw [tailHeightCountEq_one_split_mod8_three_seven] at h
  exact h

/--
Tail continuation sibling mass is definitionally the same as tail retention at
the next depth.
-/
theorem orbitWindowContinuationSiblingMassPow2Tail_eq_retentionMassTail_succ
    (n : OddNat) (k r : ℕ) :
    orbitWindowContinuationSiblingMassPow2Tail n k r =
      orbitWindowRetentionMassPow2Tail n k (r + 1) := by
  rfl


end DkMath.Collatz
