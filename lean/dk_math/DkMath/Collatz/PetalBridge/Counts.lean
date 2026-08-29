/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Collatz.PetalBridge.Profiles

#print "file: DkMath.Collatz.PetalBridge.Counts"

namespace DkMath.Collatz


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
Number of shifted-tail entries whose height is at least `threshold`.

This counts the observations at times `1, 2, ..., k`, indexed as `i + 1` for
`i < k`.  It is the height-side receiver for delayed transition counts.
-/
noncomputable def orbitWindowHeightCountGeTail
    (n : OddNat) (k threshold : ℕ) : ℕ :=
  (List.range k).countP
    (fun i => decide (threshold ≤ orbitWindowHeight n (i + 1)))

/--
Number of shifted-tail entries whose height is exactly `h`.

This is the exact-height counterpart of `orbitWindowHeightCountGeTail`.  It is
used to record retention channels such as `7 mod 8 -> next exact height 1`.
-/
noncomputable def orbitWindowHeightCountEqTail
    (n : OddNat) (k h : ℕ) : ℕ :=
  (List.range k).countP
    (fun i => decide (orbitWindowHeight n (i + 1) = h))

/--
Number of in-window odd-state labels in residue class `1 mod 4`.

This is the residue-address counterpart of `orbitWindowHeightCountGe n k 2`.
-/
noncomputable def orbitWindowResidueCountMod4EqOne
    (n : OddNat) (k : ℕ) : ℕ :=
  (List.range k).countP
    (fun i => decide (oddOrbitLabel n i % 4 = 1))

/--
Number of in-window odd-state labels in residue class `3 mod 4`.

This is the residue-address counterpart of exact height `1`.
-/
noncomputable def orbitWindowResidueCountMod4EqThree
    (n : OddNat) (k : ℕ) : ℕ :=
  (List.range k).countP
    (fun i => decide (oddOrbitLabel n i % 4 = 3))

/--
Number of in-window odd-state labels in residue class `1 mod 8`.

This is the residue-address counterpart of exact height `2`.
-/
noncomputable def orbitWindowResidueCountMod8EqOne
    (n : OddNat) (k : ℕ) : ℕ :=
  (List.range k).countP
    (fun i => decide (oddOrbitLabel n i % 8 = 1))

/--
Number of in-window odd-state labels in residue class `3 mod 8`.

This is one of the two exact height-one transition channels.
-/
noncomputable def orbitWindowResidueCountMod8EqThree
    (n : OddNat) (k : ℕ) : ℕ :=
  (List.range k).countP
    (fun i => decide (oddOrbitLabel n i % 8 = 3))

/--
Number of in-window odd-state labels in residue class `5 mod 8`.

This is the residue-address counterpart of `orbitWindowHeightCountGe n k 3`.
-/
noncomputable def orbitWindowResidueCountMod8EqFive
    (n : OddNat) (k : ℕ) : ℕ :=
  (List.range k).countP
    (fun i => decide (oddOrbitLabel n i % 8 = 5))

/--
Number of in-window odd-state labels in residue class `7 mod 8`.

This is one of the two exact height-one transition channels.
-/
noncomputable def orbitWindowResidueCountMod8EqSeven
    (n : OddNat) (k : ℕ) : ℕ :=
  (List.range k).countP
    (fun i => decide (oddOrbitLabel n i % 8 = 7))

/--
Generic residue-cell occupation count for a power-of-two modulus.

This is the coordinate-count version of the concrete `mod 4` and `mod 8`
counts above.  It counts how many labels in the window lie in a chosen residue
class modulo `2^depth`.
-/
noncomputable def orbitWindowResidueCountPow2
    (n : OddNat) (k depth residue : ℕ) : ℕ :=
  (List.range k).countP
    (fun i => decide (oddOrbitLabel n i % (2 ^ depth) = residue))

/--
Number of shifted-tail labels in residue class `1 mod 4`.

This counts the labels at times `1, 2, ..., k`, indexed as `i + 1` for
`i < k`.  It is the receiving window for the transition
`current mod 8 = 3 -> next mod 4 = 1`.
-/
noncomputable def orbitWindowResidueCountMod4EqOneTail
    (n : OddNat) (k : ℕ) : ℕ :=
  (List.range k).countP
    (fun i => decide (oddOrbitLabel n (i + 1) % 4 = 1))

/--
Number of shifted-tail labels in residue class `3 mod 4`.

This counts the labels at times `1, 2, ..., k`, indexed as `i + 1` for
`i < k`.  It is the receiving window for the transition
`current mod 8 = 7 -> next mod 4 = 3`.
-/
noncomputable def orbitWindowResidueCountMod4EqThreeTail
    (n : OddNat) (k : ℕ) : ℕ :=
  (List.range k).countP
    (fun i => decide (oddOrbitLabel n (i + 1) % 4 = 3))

/--
Number of shifted-tail labels in residue class `3 mod 8`.

This is one delayed-peeling color inside the shifted-tail exact-height-one
reservoir.
-/
noncomputable def orbitWindowResidueCountMod8EqThreeTail
    (n : OddNat) (k : ℕ) : ℕ :=
  (List.range k).countP
    (fun i => decide (oddOrbitLabel n (i + 1) % 8 = 3))

/--
Number of shifted-tail labels in residue class `7 mod 8`.

This is the continuing color inside the shifted-tail exact-height-one
reservoir.
-/
noncomputable def orbitWindowResidueCountMod8EqSevenTail
    (n : OddNat) (k : ℕ) : ℕ :=
  (List.range k).countP
    (fun i => decide (oddOrbitLabel n (i + 1) % 8 = 7))

/--
Number of shifted-tail labels in residue class `7 mod 16`.

This is the delayed-peeling child inside the shifted-tail `7 mod 8`
continuing color.
-/
noncomputable def orbitWindowResidueCountMod16EqSevenTail
    (n : OddNat) (k : ℕ) : ℕ :=
  (List.range k).countP
    (fun i => decide (oddOrbitLabel n (i + 1) % 16 = 7))

/--
Number of shifted-tail labels in residue class `15 mod 16`.

This is the continuing child inside the shifted-tail `7 mod 8` continuing
color.
-/
noncomputable def orbitWindowResidueCountMod16EqFifteenTail
    (n : OddNat) (k : ℕ) : ℕ :=
  (List.range k).countP
    (fun i => decide (oddOrbitLabel n (i + 1) % 16 = 15))

/--
Number of shifted-tail labels in residue class `15 mod 32`.

This is the delayed-peeling child inside the shifted-tail `15 mod 16`
continuing color.
-/
noncomputable def orbitWindowResidueCountMod32EqFifteenTail
    (n : OddNat) (k : ℕ) : ℕ :=
  (List.range k).countP
    (fun i => decide (oddOrbitLabel n (i + 1) % 32 = 15))

/--
Number of shifted-tail labels in residue class `31 mod 32`.

This is the continuing child inside the shifted-tail `15 mod 16` continuing
color.
-/
noncomputable def orbitWindowResidueCountMod32EqThirtyOneTail
    (n : OddNat) (k : ℕ) : ℕ :=
  (List.range k).countP
    (fun i => decide (oddOrbitLabel n (i + 1) % 32 = 31))

/--
Number of shifted-tail labels in residue class `31 mod 64`.

This is the delayed-peeling child inside the shifted-tail `31 mod 32`
continuing color.
-/
noncomputable def orbitWindowResidueCountMod64EqThirtyOneTail
    (n : OddNat) (k : ℕ) : ℕ :=
  (List.range k).countP
    (fun i => decide (oddOrbitLabel n (i + 1) % 64 = 31))

/--
Number of shifted-tail labels in residue class `63 mod 64`.

This is the continuing child inside the shifted-tail `31 mod 32` continuing
color.
-/
noncomputable def orbitWindowResidueCountMod64EqSixtyThreeTail
    (n : OddNat) (k : ℕ) : ℕ :=
  (List.range k).countP
    (fun i => decide (oddOrbitLabel n (i + 1) % 64 = 63))

/--
Number of shifted-tail labels in residue class `63 mod 128`.

This is the delayed-peeling child inside the shifted-tail `63 mod 64`
continuing color.
-/
noncomputable def orbitWindowResidueCountMod128EqSixtyThreeTail
    (n : OddNat) (k : ℕ) : ℕ :=
  (List.range k).countP
    (fun i => decide (oddOrbitLabel n (i + 1) % 128 = 63))

/--
Number of shifted-tail labels in residue class `127 mod 128`.

This is the continuing child inside the shifted-tail `63 mod 64` continuing
color.
-/
noncomputable def orbitWindowResidueCountMod128EqOneHundredTwentySevenTail
    (n : OddNat) (k : ℕ) : ℕ :=
  (List.range k).countP
    (fun i => decide (oddOrbitLabel n (i + 1) % 128 = 127))

/--
Number of shifted-tail labels in residue class `127 mod 256`.

This is the delayed-peeling child inside the shifted-tail `127 mod 128`
continuing color.
-/
noncomputable def orbitWindowResidueCountMod256EqOneHundredTwentySevenTail
    (n : OddNat) (k : ℕ) : ℕ :=
  (List.range k).countP
    (fun i => decide (oddOrbitLabel n (i + 1) % 256 = 127))

/--
Number of shifted-tail labels in residue class `255 mod 256`.

This is the continuing child inside the shifted-tail `127 mod 128`
continuing color.
-/
noncomputable def orbitWindowResidueCountMod256EqTwoHundredFiftyFiveTail
    (n : OddNat) (k : ℕ) : ℕ :=
  (List.range k).countP
    (fun i => decide (oddOrbitLabel n (i + 1) % 256 = 255))

/-- Level `0` tail remainder: the whole shifted-tail exact-height-one reservoir. -/
noncomputable def TailRemainderLevel0 (n : OddNat) (k : ℕ) : ℕ :=
  orbitWindowHeightCountEqTail n k 1

/-- Level `1` tail remainder: the shifted-tail `7 mod 8` continuing color. -/
noncomputable def TailRemainderLevel1 (n : OddNat) (k : ℕ) : ℕ :=
  orbitWindowResidueCountMod8EqSevenTail n k

/-- Level `2` tail remainder: the shifted-tail `15 mod 16` continuing color. -/
noncomputable def TailRemainderLevel2 (n : OddNat) (k : ℕ) : ℕ :=
  orbitWindowResidueCountMod16EqFifteenTail n k

/-- Level `1` falling color: the shifted-tail `3 mod 8` delayed-peeling color. -/
noncomputable def TailFallingLevel1 (n : OddNat) (k : ℕ) : ℕ :=
  orbitWindowResidueCountMod8EqThreeTail n k

/-- Level `2` falling color: the shifted-tail `7 mod 16` delayed-peeling color. -/
noncomputable def TailFallingLevel2 (n : OddNat) (k : ℕ) : ℕ :=
  orbitWindowResidueCountMod16EqSevenTail n k

/-- Level `3` tail remainder: the shifted-tail `31 mod 32` continuing color. -/
noncomputable def TailRemainderLevel3 (n : OddNat) (k : ℕ) : ℕ :=
  orbitWindowResidueCountMod32EqThirtyOneTail n k

/-- Level `3` falling color: the shifted-tail `15 mod 32` delayed-peeling color. -/
noncomputable def TailFallingLevel3 (n : OddNat) (k : ℕ) : ℕ :=
  orbitWindowResidueCountMod32EqFifteenTail n k

/-- Level `4` tail remainder: the shifted-tail `63 mod 64` continuing color. -/
noncomputable def TailRemainderLevel4 (n : OddNat) (k : ℕ) : ℕ :=
  orbitWindowResidueCountMod64EqSixtyThreeTail n k

/-- Level `4` falling color: the shifted-tail `31 mod 64` delayed-peeling color. -/
noncomputable def TailFallingLevel4 (n : OddNat) (k : ℕ) : ℕ :=
  orbitWindowResidueCountMod64EqThirtyOneTail n k

/-- Level `5` tail remainder: the shifted-tail `127 mod 128` continuing color. -/
noncomputable def TailRemainderLevel5 (n : OddNat) (k : ℕ) : ℕ :=
  orbitWindowResidueCountMod128EqOneHundredTwentySevenTail n k

/-- Level `5` falling color: the shifted-tail `63 mod 128` delayed-peeling color. -/
noncomputable def TailFallingLevel5 (n : OddNat) (k : ℕ) : ℕ :=
  orbitWindowResidueCountMod128EqSixtyThreeTail n k

/--
Generic shifted-tail residue-cell occupation count for a power-of-two modulus.

This counts labels at times `1, 2, ..., k`, indexed as `i + 1`, in a chosen
residue class modulo `2^depth`.
-/
noncomputable def orbitWindowResidueCountPow2Tail
    (n : OddNat) (k depth residue : ℕ) : ℕ :=
  (List.range k).countP
    (fun i => decide (oddOrbitLabel n (i + 1) % (2 ^ depth) = residue))

/--
Residue count inside a prefix of an ambient observation window.

The ambient window size `k` is kept in the arguments to match the existing
prefix height-count API.
-/
noncomputable def orbitWindowPrefixResidueCountMod4EqOne
    (n : OddNat) (k r : ℕ) : ℕ :=
  ((List.range k).take r).countP
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
The shifted-tail threshold occupation count is bounded by the tail window size.
-/
theorem orbitWindowHeightCountGeTail_le_window
    (n : OddNat) (k threshold : ℕ) :
    orbitWindowHeightCountGeTail n k threshold ≤ k := by
  unfold orbitWindowHeightCountGeTail
  simpa using
    (List.countP_le_length
      (p := fun i => decide (threshold ≤ orbitWindowHeight n (i + 1)))
      (l := List.range k))

/--
The shifted-tail exact-height occupation count is bounded by the tail window
size.
-/
theorem orbitWindowHeightCountEqTail_le_window
    (n : OddNat) (k h : ℕ) :
    orbitWindowHeightCountEqTail n k h ≤ k := by
  unfold orbitWindowHeightCountEqTail
  simpa using
    (List.countP_le_length
      (p := fun i => decide (orbitWindowHeight n (i + 1) = h))
      (l := List.range k))

/--
Successor formula for ordinary threshold occupation counts.
-/
theorem orbitWindowHeightCountGe_succ
    (n : OddNat) (k threshold : ℕ) :
    orbitWindowHeightCountGe n (k + 1) threshold =
      orbitWindowHeightCountGe n k threshold +
        if threshold ≤ orbitWindowHeight n k then 1 else 0 := by
  unfold orbitWindowHeightCountGe orbitWindowHeightSeq
  rw [List.range_succ]
  by_cases h : threshold ≤ orbitWindowHeight n k
  · simp [h]
  · simp [h]

/--
Successor formula for shifted-tail threshold occupation counts.
-/
theorem orbitWindowHeightCountGeTail_succ
    (n : OddNat) (k threshold : ℕ) :
    orbitWindowHeightCountGeTail n (k + 1) threshold =
      orbitWindowHeightCountGeTail n k threshold +
        if threshold ≤ orbitWindowHeight n (k + 1) then 1 else 0 := by
  unfold orbitWindowHeightCountGeTail
  rw [List.range_succ]
  by_cases h : threshold ≤ orbitWindowHeight n (k + 1)
  · simp [h]
  · simp [h]

/--
Successor formula for shifted-tail exact-height occupation counts.
-/
theorem orbitWindowHeightCountEqTail_succ
    (n : OddNat) (k h : ℕ) :
    orbitWindowHeightCountEqTail n (k + 1) h =
      orbitWindowHeightCountEqTail n k h +
        if orbitWindowHeight n (k + 1) = h then 1 else 0 := by
  unfold orbitWindowHeightCountEqTail
  rw [List.range_succ]
  by_cases hlast : orbitWindowHeight n (k + 1) = h
  · simp [hlast]
  · simp [hlast]

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
The mod `4 = 3` residue count is bounded by the window size.
-/
theorem orbitWindowResidueCountMod4EqThree_le_window
    (n : OddNat) (k : ℕ) :
    orbitWindowResidueCountMod4EqThree n k ≤ k := by
  unfold orbitWindowResidueCountMod4EqThree
  simpa using
    (List.countP_le_length
      (p := fun i => decide (oddOrbitLabel n i % 4 = 3)) (l := List.range k))

/--
The mod `8 = 1` residue count is bounded by the window size.
-/
theorem orbitWindowResidueCountMod8EqOne_le_window
    (n : OddNat) (k : ℕ) :
    orbitWindowResidueCountMod8EqOne n k ≤ k := by
  unfold orbitWindowResidueCountMod8EqOne
  simpa using
    (List.countP_le_length
      (p := fun i => decide (oddOrbitLabel n i % 8 = 1)) (l := List.range k))

/--
The mod `8 = 3` residue count is bounded by the window size.
-/
theorem orbitWindowResidueCountMod8EqThree_le_window
    (n : OddNat) (k : ℕ) :
    orbitWindowResidueCountMod8EqThree n k ≤ k := by
  unfold orbitWindowResidueCountMod8EqThree
  simpa using
    (List.countP_le_length
      (p := fun i => decide (oddOrbitLabel n i % 8 = 3)) (l := List.range k))

/--
The mod `8` residue count is bounded by the window size.
-/
theorem orbitWindowResidueCountMod8EqFive_le_window
    (n : OddNat) (k : ℕ) :
    orbitWindowResidueCountMod8EqFive n k ≤ k := by
  unfold orbitWindowResidueCountMod8EqFive
  simpa using
    (List.countP_le_length
      (p := fun i => decide (oddOrbitLabel n i % 8 = 5)) (l := List.range k))

/--
The mod `8 = 7` residue count is bounded by the window size.
-/
theorem orbitWindowResidueCountMod8EqSeven_le_window
    (n : OddNat) (k : ℕ) :
    orbitWindowResidueCountMod8EqSeven n k ≤ k := by
  unfold orbitWindowResidueCountMod8EqSeven
  simpa using
    (List.countP_le_length
      (p := fun i => decide (oddOrbitLabel n i % 8 = 7)) (l := List.range k))

/--
The generic power-of-two residue count is bounded by the window size.
-/
theorem orbitWindowResidueCountPow2_le_window
    (n : OddNat) (k depth residue : ℕ) :
    orbitWindowResidueCountPow2 n k depth residue ≤ k := by
  unfold orbitWindowResidueCountPow2
  simpa using
    (List.countP_le_length
      (p := fun i => decide (oddOrbitLabel n i % (2 ^ depth) = residue))
      (l := List.range k))

/--
The shifted-tail mod `4 = 1` residue count is bounded by the window size.
-/
theorem orbitWindowResidueCountMod4EqOneTail_le_window
    (n : OddNat) (k : ℕ) :
    orbitWindowResidueCountMod4EqOneTail n k ≤ k := by
  unfold orbitWindowResidueCountMod4EqOneTail
  simpa using
    (List.countP_le_length
      (p := fun i => decide (oddOrbitLabel n (i + 1) % 4 = 1)) (l := List.range k))

/--
The shifted-tail mod `4 = 3` residue count is bounded by the window size.
-/
theorem orbitWindowResidueCountMod4EqThreeTail_le_window
    (n : OddNat) (k : ℕ) :
    orbitWindowResidueCountMod4EqThreeTail n k ≤ k := by
  unfold orbitWindowResidueCountMod4EqThreeTail
  simpa using
    (List.countP_le_length
      (p := fun i => decide (oddOrbitLabel n (i + 1) % 4 = 3)) (l := List.range k))

/--
The generic shifted-tail power-of-two residue count is bounded by the window
size.
-/
theorem orbitWindowResidueCountPow2Tail_le_window
    (n : OddNat) (k depth residue : ℕ) :
    orbitWindowResidueCountPow2Tail n k depth residue ≤ k := by
  unfold orbitWindowResidueCountPow2Tail
  simpa using
    (List.countP_le_length
      (p := fun i => decide (oddOrbitLabel n (i + 1) % (2 ^ depth) = residue))
      (l := List.range k))

/--
The named `7 mod 8` source count is the depth-`3` instance of the generic
power-of-two residue count.
-/
theorem orbitWindowResidueCountMod8EqSeven_eq_pow2
    (n : OddNat) (k : ℕ) :
    orbitWindowResidueCountMod8EqSeven n k =
      orbitWindowResidueCountPow2 n k 3 7 := by
  rfl

/--
Successor formula for the generic source-window power-of-two residue count.
-/
theorem orbitWindowResidueCountPow2_succ
    (n : OddNat) (k depth residue : ℕ) :
    orbitWindowResidueCountPow2 n (k + 1) depth residue =
      orbitWindowResidueCountPow2 n k depth residue +
        if oddOrbitLabel n k % (2 ^ depth) = residue then 1 else 0 := by
  unfold orbitWindowResidueCountPow2
  rw [List.range_succ]
  by_cases h : oddOrbitLabel n k % (2 ^ depth) = residue
  · simp [h]
  · simp [h]

/--
Successor formula for the generic shifted-tail power-of-two residue count.
-/
theorem orbitWindowResidueCountPow2Tail_succ
    (n : OddNat) (k depth residue : ℕ) :
    orbitWindowResidueCountPow2Tail n (k + 1) depth residue =
      orbitWindowResidueCountPow2Tail n k depth residue +
        if oddOrbitLabel n (k + 1) % (2 ^ depth) = residue then 1 else 0 := by
  unfold orbitWindowResidueCountPow2Tail
  rw [List.range_succ]
  by_cases h : oddOrbitLabel n (k + 1) % (2 ^ depth) = residue
  · simp [h]
  · simp [h]

/--
At depth `0`, every label lies in the unique residue cell `0 mod 1`.
-/
theorem orbitWindowResidueCountPow2_depth_zero_eq_window
    (n : OddNat) (k : ℕ) :
    orbitWindowResidueCountPow2 n k 0 0 = k := by
  induction k with
  | zero =>
      rfl
  | succ k ih =>
      rw [orbitWindowResidueCountPow2_succ, ih]
      have hlast : oddOrbitLabel n k % 2 ^ 0 = 0 := by
        rw [pow_zero, Nat.mod_one]
      rw [ite_eq_left hlast]

/--
Residues outside the modulus range have zero occupation.
-/
theorem orbitWindowResidueCountPow2_eq_zero_of_modulus_le_residue
    (n : OddNat) (k depth residue : ℕ)
    (hres : 2 ^ depth ≤ residue) :
    orbitWindowResidueCountPow2 n k depth residue = 0 := by
  unfold orbitWindowResidueCountPow2
  induction k with
  | zero =>
      simp
  | succ k ih =>
      rw [List.range_succ]
      have hneq :
          oddOrbitLabel n k % (2 ^ depth) ≠ residue := by
        have hlt : oddOrbitLabel n k % (2 ^ depth) < 2 ^ depth :=
          Nat.mod_lt _ (pow_pos (by decide) depth)
        omega
      simp [ih, hneq]

/--
One label contributes to exactly one residue cell at a fixed power-of-two
depth.
-/
theorem pow2_residue_indicator_sum_eq_one
    (depth x : ℕ) :
    (Finset.range (2 ^ depth)).sum
      (fun residue => if x % (2 ^ depth) = residue then (1 : ℕ) else 0) = 1 := by
  have hoff :
      ∀ residue ∈ Finset.range (2 ^ depth), residue ≠ x % (2 ^ depth) →
        (fun residue => if x % (2 ^ depth) = residue then (1 : ℕ) else 0) residue = 0 := by
    intro residue _ hne
    simp [hne.symm]
  have hnot :
      x % (2 ^ depth) ∉ Finset.range (2 ^ depth) →
        (fun residue => if x % (2 ^ depth) = residue then (1 : ℕ) else 0)
          (x % (2 ^ depth)) = 0 := by
    intro hnot
    exact (hnot (Finset.mem_range.mpr (Nat.mod_lt _ (pow_pos (by decide) depth)))).elim
  simpa using Finset.sum_eq_single (s := Finset.range (2 ^ depth))
    (a := x % (2 ^ depth))
    (f := fun residue => if x % (2 ^ depth) = residue then (1 : ℕ) else 0)
    hoff hnot

/--
At any fixed power-of-two depth, the residue-cell occupation counts partition
the whole observation window.
-/
theorem orbitWindowResidueCountPow2_sum_eq_window
    (n : OddNat) (k depth : ℕ) :
    (Finset.range (2 ^ depth)).sum
      (fun residue => orbitWindowResidueCountPow2 n k depth residue) = k := by
  induction k with
  | zero =>
      simp [orbitWindowResidueCountPow2]
  | succ k ih =>
      calc
        (Finset.range (2 ^ depth)).sum
            (fun residue => orbitWindowResidueCountPow2 n (k + 1) depth residue)
            =
          (Finset.range (2 ^ depth)).sum
            (fun residue =>
              orbitWindowResidueCountPow2 n k depth residue +
                if oddOrbitLabel n k % (2 ^ depth) = residue then (1 : ℕ) else 0) := by
            apply Finset.sum_congr rfl
            intro residue _
            rw [orbitWindowResidueCountPow2_succ]
        _ =
          (Finset.range (2 ^ depth)).sum
              (fun residue => orbitWindowResidueCountPow2 n k depth residue) +
            (Finset.range (2 ^ depth)).sum
              (fun residue =>
                if oddOrbitLabel n k % (2 ^ depth) = residue then (1 : ℕ) else 0) := by
            rw [Finset.sum_add_distrib]
        _ = k + 1 := by
            rw [ih, pow2_residue_indicator_sum_eq_one]

/--
At any fixed power-of-two depth, the shifted-tail residue-cell occupation
counts partition the whole shifted observation window.
-/
theorem orbitWindowResidueCountPow2Tail_sum_eq_window
    (n : OddNat) (k depth : ℕ) :
    (Finset.range (2 ^ depth)).sum
      (fun residue => orbitWindowResidueCountPow2Tail n k depth residue) = k := by
  induction k with
  | zero =>
      simp [orbitWindowResidueCountPow2Tail]
  | succ k ih =>
      calc
        (Finset.range (2 ^ depth)).sum
            (fun residue => orbitWindowResidueCountPow2Tail n (k + 1) depth residue)
            =
          (Finset.range (2 ^ depth)).sum
            (fun residue =>
              orbitWindowResidueCountPow2Tail n k depth residue +
                if oddOrbitLabel n (k + 1) % (2 ^ depth) = residue then (1 : ℕ) else 0) := by
            apply Finset.sum_congr rfl
            intro residue _
            rw [orbitWindowResidueCountPow2Tail_succ]
        _ =
          (Finset.range (2 ^ depth)).sum
              (fun residue => orbitWindowResidueCountPow2Tail n k depth residue) +
            (Finset.range (2 ^ depth)).sum
              (fun residue =>
                if oddOrbitLabel n (k + 1) % (2 ^ depth) = residue then (1 : ℕ) else 0) := by
            rw [Finset.sum_add_distrib]
        _ = k + 1 := by
            rw [ih, pow2_residue_indicator_sum_eq_one]

/--
Depth-`3` source distribution sanity check.

This is the `mod 8` instance of the generic power-of-two source partition.
-/
theorem orbitWindowResidueCountPow2_depth_three_sum_eq_window
    (n : OddNat) (k : ℕ) :
    (Finset.range 8).sum
      (fun residue => orbitWindowResidueCountPow2 n k 3 residue) = k := by
  simpa using orbitWindowResidueCountPow2_sum_eq_window n k 3

/--
Depth-`3` shifted-tail distribution sanity check.

This is the `mod 8` instance of the generic power-of-two shifted-tail
partition.
-/
theorem orbitWindowResidueCountPow2Tail_depth_three_sum_eq_window
    (n : OddNat) (k : ℕ) :
    (Finset.range 8).sum
      (fun residue => orbitWindowResidueCountPow2Tail n k 3 residue) = k := by
  simpa using orbitWindowResidueCountPow2Tail_sum_eq_window n k 3

/--
Lift a pointwise source-to-tail residue transition to an occupation-count
inequality.

This is the generic finite channel-flow helper: once each source residue hit
inside the first `k` labels is known to land in a chosen shifted-tail residue
cell, the source occupation count is bounded by the target tail occupation
count.
-/
theorem orbitWindowResidueCountPow2_le_tail_of_pointwise
    (n : OddNat) (k sourceDepth sourceResidue targetDepth targetResidue : ℕ)
    (h :
      ∀ i, i < k →
        oddOrbitLabel n i % (2 ^ sourceDepth) = sourceResidue →
          oddOrbitLabel n (i + 1) % (2 ^ targetDepth) = targetResidue) :
    orbitWindowResidueCountPow2 n k sourceDepth sourceResidue ≤
      orbitWindowResidueCountPow2Tail n k targetDepth targetResidue := by
  induction k with
  | zero =>
      simp [orbitWindowResidueCountPow2, orbitWindowResidueCountPow2Tail]
  | succ k ih =>
      rw [orbitWindowResidueCountPow2_succ]
      rw [orbitWindowResidueCountPow2Tail_succ]
      have hprev :
          ∀ i, i < k →
            oddOrbitLabel n i % (2 ^ sourceDepth) = sourceResidue →
              oddOrbitLabel n (i + 1) % (2 ^ targetDepth) = targetResidue := by
        intro i hi
        exact h i (Nat.lt_trans hi (Nat.lt_succ_self k))
      have ih' := ih hprev
      by_cases hsource : oddOrbitLabel n k % (2 ^ sourceDepth) = sourceResidue
      · have htail :
            oddOrbitLabel n (k + 1) % (2 ^ targetDepth) = targetResidue :=
          h k (Nat.lt_succ_self k) hsource
        simp [hsource, htail, ih']
      · by_cases htail : oddOrbitLabel n (k + 1) % (2 ^ targetDepth) = targetResidue
        · exact by
            simpa [hsource, htail] using Nat.le_succ_of_le ih'
        · simpa [hsource, htail] using ih'

/--
Conceptual alias for source-side power-of-two residue distribution
conservation.

This is the No.100 finite channel-flow spelling of
`orbitWindowResidueCountPow2_sum_eq_window`.
-/
theorem sourcePow2Distribution_total
    (n : OddNat) (k depth : ℕ) :
    (Finset.range (2 ^ depth)).sum
      (fun residue => orbitWindowResidueCountPow2 n k depth residue) = k :=
  orbitWindowResidueCountPow2_sum_eq_window n k depth

/--
Conceptual alias for shifted-tail power-of-two residue distribution
conservation.

This is the No.100 finite channel-flow spelling of
`orbitWindowResidueCountPow2Tail_sum_eq_window`.
-/
theorem tailPow2Distribution_total
    (n : OddNat) (k depth : ℕ) :
    (Finset.range (2 ^ depth)).sum
      (fun residue => orbitWindowResidueCountPow2Tail n k depth residue) = k :=
  orbitWindowResidueCountPow2Tail_sum_eq_window n k depth


end DkMath.Collatz
