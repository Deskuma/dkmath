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
An odd natural number is in residue class `1` or `3` modulo `4`.
-/
theorem odd_mod_four_eq_one_or_three
    {m : ℕ} (hmOdd : m % 2 = 1) :
    m % 4 = 1 ∨ m % 4 = 3 := by
  omega

/--
An odd natural number is in one of the four odd residue classes modulo `8`.
-/
theorem odd_mod_eight_eq_one_or_three_or_five_or_seven
    {m : ℕ} (hmOdd : m % 2 = 1) :
    m % 8 = 1 ∨ m % 8 = 3 ∨ m % 8 = 5 ∨ m % 8 = 7 := by
  omega

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
The `v2` observation is at least `4` exactly when `16` divides the observed
nonzero natural.
-/
theorem four_le_v2_iff_sixteen_dvd
    {m : ℕ} (hm : m ≠ 0) :
    4 ≤ v2 m ↔ 16 ∣ m := by
  simpa [v2] using
    (DkMath.ABC.padicValNat_le_iff_dvd Nat.prime_two hm 4)

/--
Raw Collatz height is at least `3` exactly when `8` divides `3n + 1`.
-/
theorem rawHeightLabel_three_le_iff_eight_dvd_threeNPlusOne
    (n : ℕ) :
    3 ≤ rawHeightLabel n ↔ 8 ∣ 3 * n + 1 := by
  exact three_le_v2_iff_eight_dvd (by omega : 3 * n + 1 ≠ 0)

/--
Raw Collatz height is at least `4` exactly when `16` divides `3n + 1`.
-/
theorem rawHeightLabel_four_le_iff_sixteen_dvd_threeNPlusOne
    (n : ℕ) :
    4 ≤ rawHeightLabel n ↔ 16 ∣ 3 * n + 1 := by
  exact four_le_v2_iff_sixteen_dvd (by omega : 3 * n + 1 ≠ 0)

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
For an odd natural `m`, the condition `16 | 3m + 1` is the same as
`m % 16 = 5`.
-/
theorem odd_sixteen_dvd_three_mul_add_one_iff_mod_sixteen_eq_five
    {m : ℕ} (hmOdd : m % 2 = 1) :
    16 ∣ 3 * m + 1 ↔ m % 16 = 5 := by
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
`height >= 4` in the Collatz observation window is the same as the current odd
state label lying in residue class `5 mod 16`.

This fixed-coordinate experiment supports the later general `2^r` residue
coordinate route.
-/
theorem orbitWindowHeight_four_le_iff_mod_sixteen_eq_five
    (n : OddNat) (i : ℕ) :
    4 ≤ orbitWindowHeight n i ↔ oddOrbitLabel n i % 16 = 5 := by
  change 4 ≤ rawHeightLabel (oddOrbitLabel n i) ↔ oddOrbitLabel n i % 16 = 5
  rw [rawHeightLabel_four_le_iff_sixteen_dvd_threeNPlusOne]
  exact odd_sixteen_dvd_three_mul_add_one_iff_mod_sixteen_eq_five (iterateT i n).2

/--
If `m = 3 mod 8`, then the height-one Collatz branch sends
`(3m + 1) / 2` to residue class `1 mod 4`.
-/
theorem next_mod_four_of_mod_eight_eq_three
    {m : ℕ} (hm : m % 8 = 3) :
    ((3 * m + 1) / 2) % 4 = 1 := by
  omega

/--
If `m = 7 mod 8`, then the height-one Collatz branch sends
`(3m + 1) / 2` to residue class `3 mod 4`.
-/
theorem next_mod_four_of_mod_eight_eq_seven
    {m : ℕ} (hm : m % 8 = 7) :
    ((3 * m + 1) / 2) % 4 = 3 := by
  omega

/--
The `7 mod 16` subchannel of `7 mod 8` exits retention toward `3 mod 8`.
-/
theorem next_mod_eight_of_mod_sixteen_eq_seven
    {m : ℕ} (hm : m % 16 = 7) :
    ((3 * m + 1) / 2) % 8 = 3 := by
  omega

/--
The `15 mod 16` subchannel of `7 mod 8` continues retention as `7 mod 8`.
-/
theorem next_mod_eight_of_mod_sixteen_eq_fifteen
    {m : ℕ} (hm : m % 16 = 15) :
    ((3 * m + 1) / 2) % 8 = 7 := by
  omega

/--
The `15 mod 32` subchannel of `15 mod 16` exits retention one level down:
after one height-one step, the next label is `7 mod 16`.
-/
theorem next_mod_sixteen_of_mod_thirtytwo_eq_fifteen
    {m : ℕ} (hm : m % 32 = 15) :
    ((3 * m + 1) / 2) % 16 = 7 := by
  omega

/--
The `31 mod 32` subchannel of `15 mod 16` continues retention as
`15 mod 16`.
-/
theorem next_mod_sixteen_of_mod_thirtytwo_eq_thirtyone
    {m : ℕ} (hm : m % 32 = 31) :
    ((3 * m + 1) / 2) % 16 = 15 := by
  omega

/--
The `31 mod 64` subchannel of `31 mod 32` exits retention one level down:
after one height-one step, the next label is `15 mod 32`.
-/
theorem next_mod_thirtytwo_of_mod_sixtyfour_eq_thirtyone
    {m : ℕ} (hm : m % 64 = 31) :
    ((3 * m + 1) / 2) % 32 = 15 := by
  omega

/--
The `63 mod 64` subchannel of `31 mod 32` continues retention as
`31 mod 32`.
-/
theorem next_mod_thirtytwo_of_mod_sixtyfour_eq_sixtythree
    {m : ℕ} (hm : m % 64 = 63) :
    ((3 * m + 1) / 2) % 32 = 31 := by
  omega

/--
Raw arithmetic anchor for the next recovery sibling:
`63 mod 128` maps to `31 mod 64`.
-/
theorem next_mod_sixtyfour_of_mod_onehundredtwentyeight_eq_sixtythree
    {m : ℕ} (hm : m % 128 = 63) :
    ((3 * m + 1) / 2) % 64 = 31 := by
  omega

/--
Raw arithmetic anchor for the next continuation sibling:
`127 mod 128` maps to `63 mod 64`.
-/
theorem next_mod_sixtyfour_of_mod_onehundredtwentyeight_eq_onehundredtwentyseven
    {m : ℕ} (hm : m % 128 = 127) :
    ((3 * m + 1) / 2) % 64 = 63 := by
  omega

/--
Raw arithmetic anchor for the `mod 256` recovery sibling:
`127 mod 256` maps to `63 mod 128`.
-/
theorem next_mod_onehundredtwentyeight_of_mod_twohundredfiftysix_eq_onehundredtwentyseven
    {m : ℕ} (hm : m % 256 = 127) :
    ((3 * m + 1) / 2) % 128 = 63 := by
  omega

/--
Raw arithmetic anchor for the `mod 256` continuation sibling:
`255 mod 256` maps to `127 mod 128`.
-/
theorem next_mod_onehundredtwentyeight_of_mod_twohundredfiftysix_eq_twohundredfiftyfive
    {m : ℕ} (hm : m % 256 = 255) :
    ((3 * m + 1) / 2) % 128 = 127 := by
  omega

/--
Raw arithmetic anchor for the `mod 512` recovery sibling:
`255 mod 512` maps to `127 mod 256`.
-/
theorem next_mod_twohundredfiftysix_of_mod_fivehundredtwelve_eq_twohundredfiftyfive
    {m : ℕ} (hm : m % 512 = 255) :
    ((3 * m + 1) / 2) % 256 = 127 := by
  omega

/--
Raw arithmetic anchor for the `mod 512` continuation sibling:
`511 mod 512` maps to `255 mod 256`.
-/
theorem next_mod_twohundredfiftysix_of_mod_fivehundredtwelve_eq_fivehundredeleven
    {m : ℕ} (hm : m % 512 = 511) :
    ((3 * m + 1) / 2) % 256 = 255 := by
  omega

/--
The central residue of the Collatz retention cylinder at 2-adic depth `r`.

The visible examples are:

```text
r = 3:  7 mod 8
r = 4: 15 mod 16
r = 5: 31 mod 32
```

This is the residue branch converging to `-1` in the 2-adic address tree.
-/
def twoAdicRetentionResidue (r : ℕ) : ℕ :=
  2 ^ r - 1

/--
The recovery sibling seen when the retention cell at depth `r` is refined to
the next modulus.

It has the same residue value as the current retention cell, but is read inside
the finer modulus `2^(r + 1)`.
-/
def twoAdicRecoverySiblingResidue (r : ℕ) : ℕ :=
  2 ^ r - 1

/--
The continuation sibling seen when the retention cell at depth `r` is refined
to the next modulus.

This is the branch that remains in exact height-one retention and becomes the
next retention cell.
-/
def twoAdicContinuationSiblingResidue (r : ℕ) : ℕ :=
  2 ^ (r + 1) - 1

/--
The recovery sibling is the current retention residue, viewed at a finer
resolution.
-/
theorem twoAdicRecoverySiblingResidue_eq_retentionResidue
    (r : ℕ) :
    twoAdicRecoverySiblingResidue r = twoAdicRetentionResidue r := rfl

/--
The continuation sibling is exactly the next retention residue.

This is the minimal Lean statement of the recursive Petal reading:

```text
ContinuationSibling r = RetentionCell (r + 1)
```
-/
theorem twoAdicContinuationSiblingResidue_eq_retentionResidue_succ
    (r : ℕ) :
    twoAdicContinuationSiblingResidue r =
      twoAdicRetentionResidue (r + 1) := rfl

/--
The recovery sibling in expanded power-of-two form.

At depth `r`, the lower half of the current retention cell is
`2^(r + 1) - 1` modulo `2^(r + 2)`.  One exact height-one Collatz step sends it
to `2^r - 1` modulo `2^(r + 1)`.
-/
theorem next_recovery_residue_expanded
    (r t : ℕ) :
    ((3 * ((2 ^ (r + 2)) * t + (2 ^ (r + 1) - 1)) + 1) / 2) %
        (2 ^ (r + 1)) = 2 ^ r - 1 := by
  have hpow1 : 2 ^ (r + 1) = 2 * 2 ^ r := by
    rw [pow_succ]
    omega
  have hpow2 : 2 ^ (r + 2) = 2 * 2 ^ (r + 1) := by
    rw [show r + 2 = (r + 1) + 1 by omega, pow_succ]
    omega
  have hpos : 0 < 2 ^ r := pow_pos (by decide) r
  have hlt : 2 ^ r - 1 < 2 ^ (r + 1) := by
    omega
  have hdiv :
      (3 * ((2 ^ (r + 2)) * t + (2 ^ (r + 1) - 1)) + 1) / 2 =
        (2 ^ r - 1) + (3 * t + 1) * 2 ^ (r + 1) := by
    have hnum :
        3 * ((2 ^ (r + 2)) * t + (2 ^ (r + 1) - 1)) + 1 =
          2 * ((2 ^ r - 1) + (3 * t + 1) * 2 ^ (r + 1)) := by
      have hsplit : 2 * 2 ^ r - 1 = 2 ^ r + (2 ^ r - 1) := by
        omega
      rw [hpow2, hpow1]
      rw [hsplit]
      ring_nf
      omega
    rw [hnum]
    exact Nat.mul_div_right _ (by decide : 0 < 2)
  rw [hdiv]
  rw [mul_comm (3 * t + 1) (2 ^ (r + 1))]
  rw [Nat.add_mul_mod_self_left]
  exact Nat.mod_eq_of_lt hlt

/--
The continuation sibling in expanded power-of-two form.

At depth `r`, the upper half of the current retention cell is
`2^(r + 2) - 1` modulo `2^(r + 2)`.  One exact height-one Collatz step sends it
to `2^(r + 1) - 1` modulo `2^(r + 1)`, which is the next retention cell.
-/
theorem next_continuation_residue_expanded
    (r t : ℕ) :
    ((3 * ((2 ^ (r + 2)) * t + (2 ^ (r + 2) - 1)) + 1) / 2) %
        (2 ^ (r + 1)) = 2 ^ (r + 1) - 1 := by
  have hpow : 2 ^ (r + 2) = 2 * 2 ^ (r + 1) := by
    rw [show r + 2 = (r + 1) + 1 by omega, pow_succ]
    omega
  have hpos : 0 < 2 ^ (r + 1) := pow_pos (by decide) (r + 1)
  have hlt : 2 ^ (r + 1) - 1 < 2 ^ (r + 1) := by
    omega
  have hdiv :
      (3 * ((2 ^ (r + 2)) * t + (2 ^ (r + 2) - 1)) + 1) / 2 =
        (2 ^ (r + 1) - 1) + (3 * t + 2) * 2 ^ (r + 1) := by
    have hnum :
        3 * ((2 ^ (r + 2)) * t + (2 ^ (r + 2) - 1)) + 1 =
          2 * ((2 ^ (r + 1) - 1) + (3 * t + 2) * 2 ^ (r + 1)) := by
      have hsplit :
          2 * 2 ^ (r + 1) - 1 =
            2 ^ (r + 1) + (2 ^ (r + 1) - 1) := by
        omega
      rw [hpow]
      rw [hsplit]
      ring_nf
      omega
    rw [hnum]
    exact Nat.mul_div_right _ (by decide : 0 < 2)
  rw [hdiv]
  rw [mul_comm (3 * t + 2) (2 ^ (r + 1))]
  rw [Nat.add_mul_mod_self_left]
  exact Nat.mod_eq_of_lt hlt

/--
The recovery sibling in practical residue-class form.

This is the usable version of `next_recovery_residue_expanded`: if an arbitrary
label lies in the recovery sibling modulo `2^(r + 2)`, then one visible
height-one raw step lands in the outward residue `2^r - 1` modulo `2^(r + 1)`.
-/
theorem next_recovery_residue_of_mod
    (r m : ℕ)
    (hm : m % (2 ^ (r + 2)) = 2 ^ (r + 1) - 1) :
    ((3 * m + 1) / 2) % (2 ^ (r + 1)) = 2 ^ r - 1 := by
  let M := 2 ^ (r + 2)
  have hdecomp : m = M * (m / M) + m % M := by
    have h := Nat.mod_add_div m M
    omega
  rw [hdecomp]
  dsimp [M] at hm ⊢
  rw [hm]
  simpa using next_recovery_residue_expanded r (m / 2 ^ (r + 2))

/--
The continuation sibling in practical residue-class form.

If a label lies in the continuation sibling modulo `2^(r + 2)`, then one
visible height-one raw step lands in `2^(r + 1) - 1` modulo `2^(r + 1)`, the
next retention cell.
-/
theorem next_continuation_residue_of_mod
    (r m : ℕ)
    (hm : m % (2 ^ (r + 2)) = 2 ^ (r + 2) - 1) :
    ((3 * m + 1) / 2) % (2 ^ (r + 1)) = 2 ^ (r + 1) - 1 := by
  let M := 2 ^ (r + 2)
  have hdecomp : m = M * (m / M) + m % M := by
    have h := Nat.mod_add_div m M
    omega
  rw [hdecomp]
  dsimp [M] at hm ⊢
  rw [hm]
  simpa using next_continuation_residue_expanded r (m / 2 ^ (r + 2))

/--
Usability test: the `mod 512` recovery anchor follows from the general
residue-class theorem.
-/
theorem next_mod_twohundredfiftysix_of_mod_fivehundredtwelve_eq_twohundredfiftyfive_via_general
    {m : ℕ} (hm : m % 512 = 255) :
    ((3 * m + 1) / 2) % 256 = 127 := by
  simpa using next_recovery_residue_of_mod 7 m hm

/--
Usability test: the `mod 512` continuation anchor follows from the general
residue-class theorem.
-/
theorem next_mod_twohundredfiftysix_of_mod_fivehundredtwelve_eq_fivehundredeleven_via_general
    {m : ℕ} (hm : m % 512 = 511) :
    ((3 * m + 1) / 2) % 256 = 255 := by
  simpa using next_continuation_residue_of_mod 7 m hm

/--
For depth at least `2`, a recovery sibling residue is an exact height-one
source residue modulo `8`.
-/
theorem recovery_residue_mod_eight_eq_seven
    (r : ℕ) (hr : 2 ≤ r) :
    (2 ^ (r + 1) - 1) % 8 = 7 := by
  rcases exists_add_of_le hr with ⟨k, rfl⟩
  rw [show 2 + k + 1 = 3 + k by omega, pow_add]
  norm_num
  have hsplit : 8 * 2 ^ k - 1 = 7 + (2 ^ k - 1) * 8 := by
    have hpos : 0 < 2 ^ k := pow_pos (by decide) k
    omega
  rw [hsplit]
  rw [Nat.add_mul_mod_self_right]

/--
For depth at least `1`, a continuation sibling residue is an exact height-one
source residue modulo `8`.
-/
theorem continuation_residue_mod_eight_eq_seven
    (r : ℕ) (hr : 1 ≤ r) :
    (2 ^ (r + 2) - 1) % 8 = 7 := by
  rcases exists_add_of_le hr with ⟨k, rfl⟩
  rw [show 1 + k + 2 = 3 + k by omega, pow_add]
  norm_num
  have hsplit : 8 * 2 ^ k - 1 = 7 + (2 ^ k - 1) * 8 := by
    have hpos : 0 < 2 ^ k := pow_pos (by decide) k
    omega
  rw [hsplit]
  rw [Nat.add_mul_mod_self_right]

/--
Reduce a residue through a smaller modulus.

If `d` divides `M`, then reducing modulo `M` first does not change the final
residue modulo `d`.  This is the local residue-cell bridge used to read a
large 2-adic address through its visible `mod 8` entry channel.
-/
theorem mod_eq_mod_of_dvd_modulus
    {a M d : ℕ} (hd : d ∣ M) :
    a % d = (a % M) % d := by
  rw [← Nat.mod_mod_of_dvd a hd]

/--
A recovery sibling cell, at depth at least `2`, starts in the exact
height-one `7 mod 8` source channel.
-/
theorem mod_eight_eq_seven_of_recovery_residue_of_two_le
    (r m : ℕ) (hr : 2 ≤ r)
    (hm : m % (2 ^ (r + 2)) = 2 ^ (r + 1) - 1) :
    m % 8 = 7 := by
  have hpow : 8 ∣ 2 ^ (r + 2) := by
    rcases exists_add_of_le hr with ⟨k, rfl⟩
    rw [show 2 + k + 2 = 3 + (k + 1) by omega, pow_add]
    norm_num
  rw [mod_eq_mod_of_dvd_modulus hpow, hm]
  exact recovery_residue_mod_eight_eq_seven r hr

/--
A continuation sibling cell, at depth at least `1`, starts in the exact
height-one `7 mod 8` source channel.
-/
theorem mod_eight_eq_seven_of_continuation_residue_of_one_le
    (r m : ℕ) (hr : 1 ≤ r)
    (hm : m % (2 ^ (r + 2)) = 2 ^ (r + 2) - 1) :
    m % 8 = 7 := by
  have hpow : 8 ∣ 2 ^ (r + 2) := by
    rcases exists_add_of_le hr with ⟨k, rfl⟩
    rw [show 1 + k + 2 = 3 + k by omega, pow_add]
    norm_num
  rw [mod_eq_mod_of_dvd_modulus hpow, hm]
  exact continuation_residue_mod_eight_eq_seven r hr

/--
On the exact height-one channel, the accelerated Collatz map is the visible
one-step expression `(3m + 1) / 2`.
-/
theorem T_val_eq_three_mul_add_one_div_two_of_s_eq_one
    (n : OddNat) (h : s n = 1) :
    (T n).1 = (3 * n.1 + 1) / 2 := by
  have hv : v2 (3 * n.1 + 1) = 1 := by
    simpa [s, threeNPlusOne] using h
  unfold T
  simp [threeNPlusOne, hv, pow2]

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
