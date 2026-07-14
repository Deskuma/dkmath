/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Collatz.PetalBridge.HeightBudget

#print "file: DkMath.Collatz.PetalBridge.TailSplits"

namespace DkMath.Collatz


/--
The shifted-tail exact-height-one reservoir splits into the delayed-peeling
color `3 mod 8` and the continuing color `7 mod 8`.
-/
theorem tailHeightCountEq_one_split_mod8_three_seven
    (n : OddNat) (k : ℕ) :
    orbitWindowHeightCountEqTail n k 1 =
      orbitWindowResidueCountMod8EqThreeTail n k +
        orbitWindowResidueCountMod8EqSevenTail n k := by
  unfold orbitWindowHeightCountEqTail
  unfold orbitWindowResidueCountMod8EqThreeTail
  unfold orbitWindowResidueCountMod8EqSevenTail
  induction k with
  | zero =>
      simp
  | succ k ih =>
      rw [List.range_succ]
      have hiff := orbitWindowHeight_eq_one_iff_mod_eight_eq_three_or_seven n (k + 1)
      by_cases hheight : orbitWindowHeight n (k + 1) = 1
      · cases hiff.mp hheight with
        | inl hthree =>
            simp [ih, hheight, hthree, Nat.add_assoc, Nat.add_comm]
        | inr hseven =>
            simp [ih, hheight, hseven, Nat.add_comm, Nat.add_left_comm]
      · have hnotThree : oddOrbitLabel n (k + 1) % 8 ≠ 3 := by
          intro hthree
          exact hheight (hiff.mpr (Or.inl hthree))
        have hnotSeven : oddOrbitLabel n (k + 1) % 8 ≠ 7 := by
          intro hseven
          exact hheight (hiff.mpr (Or.inr hseven))
        simp [ih, hheight, hnotThree, hnotSeven]

/--
The shifted-tail `7 mod 8` continuing color splits into its two children
modulo `16`: the delayed-peeling child `7 mod 16` and the continuing child
`15 mod 16`.
-/
theorem tailResidueCountMod8EqSeven_split_mod16_seven_fifteen
    (n : OddNat) (k : ℕ) :
    orbitWindowResidueCountMod8EqSevenTail n k =
      orbitWindowResidueCountMod16EqSevenTail n k +
        orbitWindowResidueCountMod16EqFifteenTail n k := by
  unfold orbitWindowResidueCountMod8EqSevenTail
  unfold orbitWindowResidueCountMod16EqSevenTail
  unfold orbitWindowResidueCountMod16EqFifteenTail
  induction k with
  | zero =>
      simp
  | succ k ih =>
      rw [List.range_succ]
      by_cases hseven : oddOrbitLabel n (k + 1) % 16 = 7
      · have hmod8 : oddOrbitLabel n (k + 1) % 8 = 7 := by
          omega
        have hnotFifteen : oddOrbitLabel n (k + 1) % 16 ≠ 15 := by
          omega
        simp [ih, hmod8, hseven, Nat.add_assoc, Nat.add_comm]
      · by_cases hfifteen : oddOrbitLabel n (k + 1) % 16 = 15
        · have hmod8 : oddOrbitLabel n (k + 1) % 8 = 7 := by
            omega
          simp [ih, hmod8, hfifteen, Nat.add_comm, Nat.add_left_comm]
        · have hnotMod8 : oddOrbitLabel n (k + 1) % 8 ≠ 7 := by
            intro hmod8
            have hchild :
                oddOrbitLabel n (k + 1) % 16 = 7 ∨
                  oddOrbitLabel n (k + 1) % 16 = 15 := by
              omega
            cases hchild with
            | inl h =>
                exact hseven h
            | inr h =>
            exact hfifteen h
          simp [ih, hnotMod8, hseven, hfifteen]

/--
The shifted-tail `15 mod 16` continuing color splits into its two children
modulo `32`: the delayed-peeling child `15 mod 32` and the continuing child
`31 mod 32`.
-/
theorem tailResidueCountMod16EqFifteen_split_mod32_fifteen_thirtyOne
    (n : OddNat) (k : ℕ) :
    orbitWindowResidueCountMod16EqFifteenTail n k =
      orbitWindowResidueCountMod32EqFifteenTail n k +
        orbitWindowResidueCountMod32EqThirtyOneTail n k := by
  unfold orbitWindowResidueCountMod16EqFifteenTail
  unfold orbitWindowResidueCountMod32EqFifteenTail
  unfold orbitWindowResidueCountMod32EqThirtyOneTail
  induction k with
  | zero =>
      simp
  | succ k ih =>
      rw [List.range_succ]
      by_cases hfifteen : oddOrbitLabel n (k + 1) % 32 = 15
      · have hmod16 : oddOrbitLabel n (k + 1) % 16 = 15 := by
          omega
        simp [ih, hmod16, hfifteen, Nat.add_assoc, Nat.add_comm]
      · by_cases h31 : oddOrbitLabel n (k + 1) % 32 = 31
        · have hmod16 : oddOrbitLabel n (k + 1) % 16 = 15 := by
            omega
          simp [ih, hmod16, h31, Nat.add_comm, Nat.add_left_comm]
        · have hnotMod16 : oddOrbitLabel n (k + 1) % 16 ≠ 15 := by
            intro hmod16
            have hchild :
                oddOrbitLabel n (k + 1) % 32 = 15 ∨
                  oddOrbitLabel n (k + 1) % 32 = 31 := by
              omega
            cases hchild with
            | inl h =>
                exact hfifteen h
            | inr h =>
                exact h31 h
          simp [ih, hnotMod16, hfifteen, h31]

/--
Level-alias version of the level-`1` static split.

The level-`1` remainder is the sum of the level-`2` falling color and the
level-`2` remainder.
-/
theorem tailRemainderLevel1_static_split
    (n : OddNat) (k : ℕ) :
    TailRemainderLevel1 n k =
      TailFallingLevel2 n k + TailRemainderLevel2 n k := by
  unfold TailRemainderLevel1 TailFallingLevel2 TailRemainderLevel2
  exact tailResidueCountMod8EqSeven_split_mod16_seven_fifteen n k

/--
The shifted-tail `31 mod 32` continuing color splits into its two children
modulo `64`: the delayed-peeling child `31 mod 64` and the continuing child
`63 mod 64`.
-/
theorem tailResidueCountMod32EqThirtyOne_split_mod64_thirtyOne_sixtyThree
    (n : OddNat) (k : ℕ) :
    orbitWindowResidueCountMod32EqThirtyOneTail n k =
      orbitWindowResidueCountMod64EqThirtyOneTail n k +
        orbitWindowResidueCountMod64EqSixtyThreeTail n k := by
  unfold orbitWindowResidueCountMod32EqThirtyOneTail
  unfold orbitWindowResidueCountMod64EqThirtyOneTail
  unfold orbitWindowResidueCountMod64EqSixtyThreeTail
  induction k with
  | zero =>
      simp
  | succ k ih =>
      rw [List.range_succ]
      by_cases h31 : oddOrbitLabel n (k + 1) % 64 = 31
      · have hmod32 : oddOrbitLabel n (k + 1) % 32 = 31 := by
          omega
        simp [ih, hmod32, h31, Nat.add_assoc, Nat.add_comm]
      · by_cases h63 : oddOrbitLabel n (k + 1) % 64 = 63
        · have hmod32 : oddOrbitLabel n (k + 1) % 32 = 31 := by
            omega
          simp [ih, hmod32, h63, Nat.add_comm, Nat.add_left_comm]
        · have hnotMod32 : oddOrbitLabel n (k + 1) % 32 ≠ 31 := by
            intro hmod32
            have hchild :
                oddOrbitLabel n (k + 1) % 64 = 31 ∨
                  oddOrbitLabel n (k + 1) % 64 = 63 := by
              omega
            cases hchild with
            | inl h =>
                exact h31 h
            | inr h =>
                exact h63 h
          simp [ih, hnotMod32, h31, h63]

/--
Level-alias version of the level-`2` static split.

The level-`2` remainder is the sum of the level-`3` falling color and the
level-`3` remainder.
-/
theorem tailRemainderLevel2_static_split
    (n : OddNat) (k : ℕ) :
    TailRemainderLevel2 n k =
      TailFallingLevel3 n k + TailRemainderLevel3 n k := by
  unfold TailRemainderLevel2 TailFallingLevel3 TailRemainderLevel3
  exact tailResidueCountMod16EqFifteen_split_mod32_fifteen_thirtyOne n k

/--
The shifted-tail `63 mod 64` continuing color splits into its two children
modulo `128`: the delayed-peeling child `63 mod 128` and the continuing child
`127 mod 128`.
-/
theorem tailResidueCountMod64EqSixtyThree_split_mod128_sixtyThree_oneHundredTwentySeven
    (n : OddNat) (k : ℕ) :
    orbitWindowResidueCountMod64EqSixtyThreeTail n k =
      orbitWindowResidueCountMod128EqSixtyThreeTail n k +
        orbitWindowResidueCountMod128EqOneHundredTwentySevenTail n k := by
  unfold orbitWindowResidueCountMod64EqSixtyThreeTail
  unfold orbitWindowResidueCountMod128EqSixtyThreeTail
  unfold orbitWindowResidueCountMod128EqOneHundredTwentySevenTail
  induction k with
  | zero =>
      simp
  | succ k ih =>
      rw [List.range_succ]
      by_cases h63 : oddOrbitLabel n (k + 1) % 128 = 63
      · have hmod64 : oddOrbitLabel n (k + 1) % 64 = 63 := by
          omega
        simp [ih, hmod64, h63, Nat.add_assoc, Nat.add_comm]
      · by_cases h127 : oddOrbitLabel n (k + 1) % 128 = 127
        · have hmod64 : oddOrbitLabel n (k + 1) % 64 = 63 := by
            omega
          simp [ih, hmod64, h127, Nat.add_comm, Nat.add_left_comm]
        · have hnotMod64 : oddOrbitLabel n (k + 1) % 64 ≠ 63 := by
            intro hmod64
            have hchild :
                oddOrbitLabel n (k + 1) % 128 = 63 ∨
                  oddOrbitLabel n (k + 1) % 128 = 127 := by
              omega
            cases hchild with
            | inl h =>
                exact h63 h
            | inr h =>
                exact h127 h
          simp [ih, hnotMod64, h63, h127]

/--
Level-alias version of the level-`3` static split.

The level-`3` remainder is the sum of the level-`4` falling color and the
level-`4` remainder.
-/
theorem tailRemainderLevel3_static_split
    (n : OddNat) (k : ℕ) :
    TailRemainderLevel3 n k =
      TailFallingLevel4 n k + TailRemainderLevel4 n k := by
  unfold TailRemainderLevel3 TailFallingLevel4 TailRemainderLevel4
  exact tailResidueCountMod32EqThirtyOne_split_mod64_thirtyOne_sixtyThree n k

/--
The shifted-tail `127 mod 128` continuing color splits into its two children
modulo `256`: the delayed-peeling child `127 mod 256` and the continuing child
`255 mod 256`.
-/
theorem tailResidueCountMod128EqOneHundredTwentySeven_split_mod256
    (n : OddNat) (k : ℕ) :
    orbitWindowResidueCountMod128EqOneHundredTwentySevenTail n k =
      orbitWindowResidueCountMod256EqOneHundredTwentySevenTail n k +
        orbitWindowResidueCountMod256EqTwoHundredFiftyFiveTail n k := by
  unfold orbitWindowResidueCountMod128EqOneHundredTwentySevenTail
  unfold orbitWindowResidueCountMod256EqOneHundredTwentySevenTail
  unfold orbitWindowResidueCountMod256EqTwoHundredFiftyFiveTail
  induction k with
  | zero =>
      simp
  | succ k ih =>
      rw [List.range_succ]
      by_cases h127 : oddOrbitLabel n (k + 1) % 256 = 127
      · have hmod128 : oddOrbitLabel n (k + 1) % 128 = 127 := by
          omega
        simp [ih, hmod128, h127, Nat.add_assoc, Nat.add_comm]
      · by_cases h255 : oddOrbitLabel n (k + 1) % 256 = 255
        · have hmod128 : oddOrbitLabel n (k + 1) % 128 = 127 := by
            omega
          simp [ih, hmod128, h255, Nat.add_comm, Nat.add_left_comm]
        · have hnotMod128 : oddOrbitLabel n (k + 1) % 128 ≠ 127 := by
            intro hmod128
            have hchild :
                oddOrbitLabel n (k + 1) % 256 = 127 ∨
                  oddOrbitLabel n (k + 1) % 256 = 255 := by
              omega
            cases hchild with
            | inl h =>
                exact h127 h
            | inr h =>
                exact h255 h
          simp [ih, hnotMod128, h127, h255]

/--
Level-alias version of the level-`4` static split.

The level-`4` remainder is the sum of the level-`5` falling color and the
level-`5` remainder.
-/
theorem tailRemainderLevel4_static_split
    (n : OddNat) (k : ℕ) :
    TailRemainderLevel4 n k =
      TailFallingLevel5 n k + TailRemainderLevel5 n k := by
  unfold TailRemainderLevel4 TailFallingLevel5 TailRemainderLevel5
  exact tailResidueCountMod64EqSixtyThree_split_mod128_sixtyThree_oneHundredTwentySeven n k


end DkMath.Collatz
