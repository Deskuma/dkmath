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
      rw [if_pos hlast]

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

/--
Conceptual alias for finite power-of-two channel flow.

A pointwise residue transition from source labels to shifted-tail labels gives
a count-level occupation inequality between the two channel distributions.
-/
theorem pow2ChannelFlow_of_pointwise
    (n : OddNat) (k sourceDepth sourceResidue targetDepth targetResidue : ℕ)
    (h :
      ∀ i, i < k →
        oddOrbitLabel n i % (2 ^ sourceDepth) = sourceResidue →
          oddOrbitLabel n (i + 1) % (2 ^ targetDepth) = targetResidue) :
    orbitWindowResidueCountPow2 n k sourceDepth sourceResidue ≤
      orbitWindowResidueCountPow2Tail n k targetDepth targetResidue :=
  orbitWindowResidueCountPow2_le_tail_of_pointwise
    n k sourceDepth sourceResidue targetDepth targetResidue h

/--
Finite natural-number witness that a count occupies at most half of a window.

This intentionally avoids division: `2 * count <= k` is the finite form of
`count / k <= 1 / 2`, with no zero-window or coercion overhead.
-/
def AtMostHalf (count k : ℕ) : Prop :=
  2 * count ≤ k

/--
Finite natural-number witness that a count occupies more than half of a window.

This is the strict counterpart of `AtMostHalf`.
-/
def MoreThanHalf (count k : ℕ) : Prop :=
  k < 2 * count

/-- Every finite count is either at most half or more than half. -/
theorem atMostHalf_or_moreThanHalf
    (count k : ℕ) :
    AtMostHalf count k ∨ MoreThanHalf count k := by
  unfold AtMostHalf MoreThanHalf
  omega

/--
Finite natural-number witness for `count / k <= num / den`.

The inequality is represented without division:

`den * count <= num * k`.
-/
def AtMostRatioNat (num den count k : ℕ) : Prop :=
  den * count ≤ num * k

/-- Constructor spelling for `AtMostHalf`. -/
theorem atMostHalf_of_count_le_half
    (count k : ℕ)
    (h : 2 * count ≤ k) :
    AtMostHalf count k :=
  h

/-- Reflexive finite ratio witness in the division-free encoding. -/
theorem atMostRatioNat_refl
    (count k : ℕ) :
    AtMostRatioNat k k count count := by
  unfold AtMostRatioNat
  rfl

/-- `AtMostHalf` is the special `1/2` case of `AtMostRatioNat`. -/
theorem atMostHalf_iff_atMostRatioNat_one_two
    (count k : ℕ) :
    AtMostHalf count k ↔ AtMostRatioNat 1 2 count k := by
  unfold AtMostHalf AtMostRatioNat
  simp

/-- A plain count bound is the `1/1` finite ratio witness. -/
theorem atMostRatioNat_one_one_of_le
    {count k : ℕ} (h : count ≤ k) :
    AtMostRatioNat 1 1 count k := by
  simpa [AtMostRatioNat] using h

/--
Source retention mass at depth `r`.

This is the occupation count of the all-ones residue cell `2^r - 1` in the
source window.
-/
noncomputable def orbitWindowRetentionMassPow2
    (n : OddNat) (k r : ℕ) : ℕ :=
  orbitWindowResidueCountPow2 n k r (2 ^ r - 1)

/--
Shifted-tail retention mass at depth `r`.

This is the tail-window counterpart of `orbitWindowRetentionMassPow2`.
-/
noncomputable def orbitWindowRetentionMassPow2Tail
    (n : OddNat) (k r : ℕ) : ℕ :=
  orbitWindowResidueCountPow2Tail n k r (2 ^ r - 1)

/--
Recovery sibling mass inside the next deeper source layer.

At parent depth `r`, this is the child residue `2^r - 1` at depth `r + 1`.
-/
noncomputable def orbitWindowRecoverySiblingMassPow2
    (n : OddNat) (k r : ℕ) : ℕ :=
  orbitWindowResidueCountPow2 n k (r + 1) (2 ^ r - 1)

/--
Continuation sibling mass inside the next deeper source layer.

At parent depth `r`, this is the child residue `2^(r+1) - 1` at depth `r + 1`.
-/
noncomputable def orbitWindowContinuationSiblingMassPow2
    (n : OddNat) (k r : ℕ) : ℕ :=
  orbitWindowResidueCountPow2 n k (r + 1) (2 ^ (r + 1) - 1)

/--
Shifted-tail recovery sibling mass at parent depth `r`.

This is the tail-window child residue `2^r - 1` at depth `r + 1`.
-/
noncomputable def orbitWindowRecoverySiblingMassPow2Tail
    (n : OddNat) (k r : ℕ) : ℕ :=
  orbitWindowResidueCountPow2Tail n k (r + 1) (2 ^ r - 1)

/--
Shifted-tail continuation sibling mass at parent depth `r`.

This is definitionally the same residue shape as tail retention at depth
`r + 1`.
-/
noncomputable def orbitWindowContinuationSiblingMassPow2Tail
    (n : OddNat) (k r : ℕ) : ℕ :=
  orbitWindowResidueCountPow2Tail n k (r + 1) (2 ^ (r + 1) - 1)

/-- Source retention mass is bounded by the window size. -/
theorem orbitWindowRetentionMassPow2_le_window
    (n : OddNat) (k r : ℕ) :
    orbitWindowRetentionMassPow2 n k r ≤ k := by
  unfold orbitWindowRetentionMassPow2
  exact orbitWindowResidueCountPow2_le_window n k r (2 ^ r - 1)

/-- Shifted-tail retention mass is bounded by the window size. -/
theorem orbitWindowRetentionMassPow2Tail_le_window
    (n : OddNat) (k r : ℕ) :
    orbitWindowRetentionMassPow2Tail n k r ≤ k := by
  unfold orbitWindowRetentionMassPow2Tail
  exact orbitWindowResidueCountPow2Tail_le_window n k r (2 ^ r - 1)

/-- Recovery sibling mass is bounded by the window size. -/
theorem orbitWindowRecoverySiblingMassPow2_le_window
    (n : OddNat) (k r : ℕ) :
    orbitWindowRecoverySiblingMassPow2 n k r ≤ k := by
  unfold orbitWindowRecoverySiblingMassPow2
  exact orbitWindowResidueCountPow2_le_window n k (r + 1) (2 ^ r - 1)

/-- Continuation sibling mass is bounded by the window size. -/
theorem orbitWindowContinuationSiblingMassPow2_le_window
    (n : OddNat) (k r : ℕ) :
    orbitWindowContinuationSiblingMassPow2 n k r ≤ k := by
  unfold orbitWindowContinuationSiblingMassPow2
  exact orbitWindowResidueCountPow2_le_window n k (r + 1) (2 ^ (r + 1) - 1)

/-- Shifted-tail recovery sibling mass is bounded by the window size. -/
theorem orbitWindowRecoverySiblingMassPow2Tail_le_window
    (n : OddNat) (k r : ℕ) :
    orbitWindowRecoverySiblingMassPow2Tail n k r ≤ k := by
  unfold orbitWindowRecoverySiblingMassPow2Tail
  exact orbitWindowResidueCountPow2Tail_le_window n k (r + 1) (2 ^ r - 1)

/-- Shifted-tail continuation sibling mass is bounded by the window size. -/
theorem orbitWindowContinuationSiblingMassPow2Tail_le_window
    (n : OddNat) (k r : ℕ) :
    orbitWindowContinuationSiblingMassPow2Tail n k r ≤ k := by
  unfold orbitWindowContinuationSiblingMassPow2Tail
  exact orbitWindowResidueCountPow2Tail_le_window n k (r + 1) (2 ^ (r + 1) - 1)

/-- The all-ones retention residue is inside its power-of-two modulus. -/
theorem twoAdicRetentionResidue_lt_pow
    (r : ℕ) :
    2 ^ r - 1 < 2 ^ r := by
  have hpos : 0 < 2 ^ r := pow_pos (by decide) r
  omega

/--
Pointwise refinement of a power-of-two residue cell.

If `residue` is a valid cell at depth `depth`, then a number in that cell has
one of exactly two residues at depth `depth + 1`: the left child `residue` or
the right child `residue + 2^depth`.
-/
theorem mod_pow2_succ_eq_left_or_right_of_mod_pow2_eq
    (x depth residue : ℕ)
    (_hres : residue < 2 ^ depth)
    (h : x % (2 ^ depth) = residue) :
    x % (2 ^ (depth + 1)) = residue ∨
      x % (2 ^ (depth + 1)) = residue + 2 ^ depth := by
  let m := 2 ^ depth
  let y := x % (2 ^ (depth + 1))
  have hmpos : 0 < m := by
    dsimp [m]
    exact pow_pos (by decide) depth
  have hpow : 2 ^ (depth + 1) = 2 * m := by
    dsimp [m]
    rw [pow_succ]
    ring
  have hmod : y % m = residue := by
    dsimp [y, m]
    rw [← h]
    rw [Nat.mod_mod_of_dvd]
    · exact ⟨2, by rw [hpow, Nat.mul_comm]⟩
  have hylt : y < 2 * m := by
    dsimp [y]
    rw [hpow]
    exact Nat.mod_lt _ (Nat.mul_pos (by decide) hmpos)
  have hdecomp : y = y % m + m * (y / m) := by
    exact (Nat.mod_add_div y m).symm
  have hydiv_lt : y / m < 2 := by
    exact (Nat.div_lt_iff_lt_mul hmpos).2 hylt
  have hydiv_cases : y / m = 0 ∨ y / m = 1 :=
    Nat.le_one_iff_eq_zero_or_eq_one.mp (Nat.lt_succ_iff.mp hydiv_lt)
  cases hydiv_cases with
  | inl hzero =>
      left
      rw [hzero, mul_zero, add_zero, hmod] at hdecomp
      dsimp [y] at hdecomp
      exact hdecomp
  | inr hone =>
      right
      rw [hone, mul_one, hmod] at hdecomp
      dsimp [y, m] at hdecomp
      exact hdecomp

/--
The two child residues at the next power-of-two depth both collapse back to
the parent residue.
-/
theorem mod_pow2_eq_of_mod_pow2_succ_eq_left_or_right
    (x depth residue : ℕ)
    (hres : residue < 2 ^ depth)
    (h :
      x % (2 ^ (depth + 1)) = residue ∨
        x % (2 ^ (depth + 1)) = residue + 2 ^ depth) :
    x % (2 ^ depth) = residue := by
  have hdvd : 2 ^ depth ∣ 2 ^ (depth + 1) := by
    exact ⟨2, by rw [pow_succ, Nat.mul_comm]⟩
  cases h with
  | inl hleft =>
      calc
        x % (2 ^ depth)
            = (x % (2 ^ (depth + 1))) % (2 ^ depth) := by
                rw [Nat.mod_mod_of_dvd _ hdvd]
        _ = residue % (2 ^ depth) := by rw [hleft]
        _ = residue := Nat.mod_eq_of_lt hres
  | inr hright =>
      calc
        x % (2 ^ depth)
            = (x % (2 ^ (depth + 1))) % (2 ^ depth) := by
                rw [Nat.mod_mod_of_dvd _ hdvd]
        _ = (residue + 2 ^ depth) % (2 ^ depth) := by rw [hright]
        _ = residue := by
          rw [Nat.add_mod_right, Nat.mod_eq_of_lt hres]

/--
Pointwise `0/1` indicator split for a valid power-of-two residue cell.

The parent cell at depth `depth` is the disjoint union of the left child
`residue` and the right child `residue + 2^depth` at depth `depth + 1`.
-/
theorem pow2ResidueIndicator_refine_succ
    (x depth residue : ℕ)
    (hres : residue < 2 ^ depth) :
    (if x % (2 ^ depth) = residue then 1 else 0) =
      (if x % (2 ^ (depth + 1)) = residue then 1 else 0) +
        if x % (2 ^ (depth + 1)) = residue + 2 ^ depth then 1 else 0 := by
  by_cases hparent : x % (2 ^ depth) = residue
  · have hsplit :=
      mod_pow2_succ_eq_left_or_right_of_mod_pow2_eq x depth residue hres hparent
    cases hsplit with
    | inl hleft =>
        simp [hparent, hleft]
    | inr hright =>
        simp [hparent, hright]
  · have hleft_not : x % (2 ^ (depth + 1)) ≠ residue := by
      intro hleft
      exact hparent
        (mod_pow2_eq_of_mod_pow2_succ_eq_left_or_right
          x depth residue hres (Or.inl hleft))
    have hright_not :
        x % (2 ^ (depth + 1)) ≠ residue + 2 ^ depth := by
      intro hright
      exact hparent
        (mod_pow2_eq_of_mod_pow2_succ_eq_left_or_right
          x depth residue hres (Or.inr hright))
    simp [hparent, hleft_not, hright_not]

/--
Depth refinement for generic source-window residue counts.

Counting a valid parent cell at depth `depth` is the same as counting both of
its child cells at depth `depth + 1`.
-/
theorem orbitWindowResidueCountPow2_refine_succ
    (n : OddNat) (k depth residue : ℕ)
    (hres : residue < 2 ^ depth) :
    orbitWindowResidueCountPow2 n k depth residue =
      orbitWindowResidueCountPow2 n k (depth + 1) residue +
        orbitWindowResidueCountPow2 n k (depth + 1) (residue + 2 ^ depth) := by
  induction k with
  | zero =>
      simp [orbitWindowResidueCountPow2]
  | succ k ih =>
      rw [orbitWindowResidueCountPow2_succ]
      rw [orbitWindowResidueCountPow2_succ]
      rw [orbitWindowResidueCountPow2_succ]
      rw [ih]
      have hindicator :=
        pow2ResidueIndicator_refine_succ (oddOrbitLabel n k) depth residue hres
      omega

/--
Retention mass splits into the recovery and continuation sibling masses at the
next depth.
-/
theorem orbitWindowRetentionMass_split
    (n : OddNat) (k r : ℕ) :
    orbitWindowRetentionMassPow2 n k r =
      orbitWindowRecoverySiblingMassPow2 n k r +
        orbitWindowContinuationSiblingMassPow2 n k r := by
  unfold orbitWindowRetentionMassPow2
  unfold orbitWindowRecoverySiblingMassPow2
  unfold orbitWindowContinuationSiblingMassPow2
  have hres : 2 ^ r - 1 < 2 ^ r := twoAdicRetentionResidue_lt_pow r
  have hsplit :=
    orbitWindowResidueCountPow2_refine_succ n k r (2 ^ r - 1) hres
  have hright : 2 ^ r - 1 + 2 ^ r = 2 ^ (r + 1) - 1 := by
    have hpos : 0 < 2 ^ r := pow_pos (by decide) r
    rw [pow_succ]
    omega
  simpa [hright] using hsplit

/-- Recovery sibling mass is bounded by the parent retention mass. -/
theorem orbitWindowRecoverySiblingMassPow2_le_retentionMass
    (n : OddNat) (k r : ℕ) :
    orbitWindowRecoverySiblingMassPow2 n k r ≤
      orbitWindowRetentionMassPow2 n k r := by
  rw [orbitWindowRetentionMass_split]
  omega

/-- Continuation sibling mass is bounded by the parent retention mass. -/
theorem orbitWindowContinuationSiblingMassPow2_le_retentionMass
    (n : OddNat) (k r : ℕ) :
    orbitWindowContinuationSiblingMassPow2 n k r ≤
      orbitWindowRetentionMassPow2 n k r := by
  rw [orbitWindowRetentionMass_split]
  omega

/--
Depth refinement for generic shifted-tail residue counts.

This is the tail-window counterpart of
`orbitWindowResidueCountPow2_refine_succ`.
-/
theorem orbitWindowResidueCountPow2Tail_refine_succ
    (n : OddNat) (k depth residue : ℕ)
    (hres : residue < 2 ^ depth) :
    orbitWindowResidueCountPow2Tail n k depth residue =
      orbitWindowResidueCountPow2Tail n k (depth + 1) residue +
        orbitWindowResidueCountPow2Tail n k (depth + 1)
          (residue + 2 ^ depth) := by
  induction k with
  | zero =>
      simp [orbitWindowResidueCountPow2Tail]
  | succ k ih =>
      rw [orbitWindowResidueCountPow2Tail_succ]
      rw [orbitWindowResidueCountPow2Tail_succ]
      rw [orbitWindowResidueCountPow2Tail_succ]
      rw [ih]
      have hindicator :=
        pow2ResidueIndicator_refine_succ
          (oddOrbitLabel n (k + 1)) depth residue hres
      omega

/--
Tail retention mass splits into the tail recovery and tail continuation sibling
masses at the next depth.
-/
theorem orbitWindowRetentionMassPow2Tail_split
    (n : OddNat) (k r : ℕ) :
    orbitWindowRetentionMassPow2Tail n k r =
      orbitWindowRecoverySiblingMassPow2Tail n k r +
        orbitWindowContinuationSiblingMassPow2Tail n k r := by
  unfold orbitWindowRetentionMassPow2Tail
  unfold orbitWindowRecoverySiblingMassPow2Tail
  unfold orbitWindowContinuationSiblingMassPow2Tail
  have hres : 2 ^ r - 1 < 2 ^ r := twoAdicRetentionResidue_lt_pow r
  have hsplit :=
    orbitWindowResidueCountPow2Tail_refine_succ n k r (2 ^ r - 1) hres
  have hright : 2 ^ r - 1 + 2 ^ r = 2 ^ (r + 1) - 1 := by
    have hpos : 0 < 2 ^ r := pow_pos (by decide) r
    rw [pow_succ]
    omega
  simpa [hright] using hsplit

/-- Tail recovery sibling mass is bounded by tail retention mass. -/
theorem orbitWindowRecoverySiblingMassPow2Tail_le_retentionMassTail
    (n : OddNat) (k r : ℕ) :
    orbitWindowRecoverySiblingMassPow2Tail n k r ≤
      orbitWindowRetentionMassPow2Tail n k r := by
  rw [orbitWindowRetentionMassPow2Tail_split]
  omega

/-- Tail continuation sibling mass is bounded by tail retention mass. -/
theorem orbitWindowContinuationSiblingMassPow2Tail_le_retentionMassTail
    (n : OddNat) (k r : ℕ) :
    orbitWindowContinuationSiblingMassPow2Tail n k r ≤
      orbitWindowRetentionMassPow2Tail n k r := by
  rw [orbitWindowRetentionMassPow2Tail_split]
  omega

/--
If source continuation mass is no larger than source recovery mass, then source
continuation occupies at most half of the parent retention mass.
-/
theorem atMostHalf_continuation_of_continuation_le_recovery
    (n : OddNat) (k r : ℕ)
    (h :
      orbitWindowContinuationSiblingMassPow2 n k r ≤
        orbitWindowRecoverySiblingMassPow2 n k r) :
    AtMostHalf
      (orbitWindowContinuationSiblingMassPow2 n k r)
      (orbitWindowRetentionMassPow2 n k r) := by
  unfold AtMostHalf
  rw [orbitWindowRetentionMass_split]
  omega

/--
If tail continuation mass is no larger than tail recovery mass, then tail
continuation occupies at most half of tail retention mass.
-/
theorem atMostHalf_tailContinuation_of_tailContinuation_le_tailRecovery
    (n : OddNat) (k r : ℕ)
    (h :
      orbitWindowContinuationSiblingMassPow2Tail n k r ≤
        orbitWindowRecoverySiblingMassPow2Tail n k r) :
    AtMostHalf
      (orbitWindowContinuationSiblingMassPow2Tail n k r)
      (orbitWindowRetentionMassPow2Tail n k r) := by
  unfold AtMostHalf
  rw [orbitWindowRetentionMassPow2Tail_split]
  omega

/--
If source recovery accounts for at least half of source retention, then source
continuation is at most half of source retention.
-/
theorem atMostHalf_continuation_of_retention_le_two_recovery
    (n : OddNat) (k r : ℕ)
    (h :
      orbitWindowRetentionMassPow2 n k r ≤
        2 * orbitWindowRecoverySiblingMassPow2 n k r) :
    AtMostHalf
      (orbitWindowContinuationSiblingMassPow2 n k r)
      (orbitWindowRetentionMassPow2 n k r) := by
  unfold AtMostHalf
  rw [orbitWindowRetentionMass_split] at h ⊢
  omega

/--
If tail recovery accounts for at least half of tail retention, then tail
continuation is at most half of tail retention.
-/
theorem atMostHalf_tailContinuation_of_tailRetention_le_two_tailRecovery
    (n : OddNat) (k r : ℕ)
    (h :
      orbitWindowRetentionMassPow2Tail n k r ≤
        2 * orbitWindowRecoverySiblingMassPow2Tail n k r) :
    AtMostHalf
      (orbitWindowContinuationSiblingMassPow2Tail n k r)
      (orbitWindowRetentionMassPow2Tail n k r) := by
  unfold AtMostHalf
  rw [orbitWindowRetentionMassPow2Tail_split] at h ⊢
  omega

/-- Source continuation mass is at most the whole source retention mass. -/
theorem continuation_atMostRatio_one_one_retention
    (n : OddNat) (k r : ℕ) :
    AtMostRatioNat 1 1
      (orbitWindowContinuationSiblingMassPow2 n k r)
      (orbitWindowRetentionMassPow2 n k r) := by
  apply atMostRatioNat_one_one_of_le
  exact orbitWindowContinuationSiblingMassPow2_le_retentionMass n k r

/-- Tail continuation mass is at most the whole tail retention mass. -/
theorem tailContinuation_atMostRatio_one_one_retention
    (n : OddNat) (k r : ℕ) :
    AtMostRatioNat 1 1
      (orbitWindowContinuationSiblingMassPow2Tail n k r)
      (orbitWindowRetentionMassPow2Tail n k r) := by
  apply atMostRatioNat_one_one_of_le
  exact orbitWindowContinuationSiblingMassPow2Tail_le_retentionMassTail n k r

/-- Source recovery mass is at most the whole source retention mass. -/
theorem recovery_atMostRatio_one_one_retention
    (n : OddNat) (k r : ℕ) :
    AtMostRatioNat 1 1
      (orbitWindowRecoverySiblingMassPow2 n k r)
      (orbitWindowRetentionMassPow2 n k r) := by
  apply atMostRatioNat_one_one_of_le
  exact orbitWindowRecoverySiblingMassPow2_le_retentionMass n k r

/-- Tail recovery mass is at most the whole tail retention mass. -/
theorem tailRecovery_atMostRatio_one_one_retention
    (n : OddNat) (k r : ℕ) :
    AtMostRatioNat 1 1
      (orbitWindowRecoverySiblingMassPow2Tail n k r)
      (orbitWindowRetentionMassPow2Tail n k r) := by
  apply atMostRatioNat_one_one_of_le
  exact orbitWindowRecoverySiblingMassPow2Tail_le_retentionMassTail n k r

/--
Source comparison predicate: recovery mass dominates continuation mass.

This names the local comparison condition that is sufficient for the source
`AtMostHalf` criterion.  It is intentionally a hypothesis package, not an
unconditional theorem.
-/
def RecoveryDominatesContinuation
    (n : OddNat) (k r : ℕ) : Prop :=
  orbitWindowContinuationSiblingMassPow2 n k r ≤
    orbitWindowRecoverySiblingMassPow2 n k r

/--
Tail comparison predicate: tail recovery mass dominates tail continuation mass.
-/
def TailRecoveryDominatesContinuation
    (n : OddNat) (k r : ℕ) : Prop :=
  orbitWindowContinuationSiblingMassPow2Tail n k r ≤
    orbitWindowRecoverySiblingMassPow2Tail n k r

/--
Source budget predicate: recovery covers at least half of retention.

This is often the natural form when a later argument produces a lower bound on
recovery rather than a direct comparison with continuation.
-/
def RecoveryCoversHalfRetention
    (n : OddNat) (k r : ℕ) : Prop :=
  orbitWindowRetentionMassPow2 n k r ≤
    2 * orbitWindowRecoverySiblingMassPow2 n k r

/-- Tail budget predicate: tail recovery covers at least half of tail retention. -/
def TailRecoveryCoversHalfRetention
    (n : OddNat) (k r : ℕ) : Prop :=
  orbitWindowRetentionMassPow2Tail n k r ≤
    2 * orbitWindowRecoverySiblingMassPow2Tail n k r

/--
Finite-depth range form of source recovery dominance.

This keeps the persistent-comparison hypothesis explicit without proving it.
-/
def RecoveryDominatesOnRange
    (n : OddNat) (k r len : ℕ) : Prop :=
  ∀ j, j < len → RecoveryDominatesContinuation n k (r + j)

/-- Finite-depth range form of tail recovery dominance. -/
def TailRecoveryDominatesOnRange
    (n : OddNat) (k r len : ℕ) : Prop :=
  ∀ j, j < len → TailRecoveryDominatesContinuation n k (r + j)

/--
Failure-mode predicate: source continuation strictly outruns recovery.

This is the obstruction-facing complement direction to
`RecoveryDominatesContinuation`.
-/
def ContinuationOutrunsRecovery
    (n : OddNat) (k r : ℕ) : Prop :=
  orbitWindowRecoverySiblingMassPow2 n k r <
    orbitWindowContinuationSiblingMassPow2 n k r

/-- Tail failure-mode predicate: tail continuation strictly outruns tail recovery. -/
def TailContinuationOutrunsRecovery
    (n : OddNat) (k r : ℕ) : Prop :=
  orbitWindowRecoverySiblingMassPow2Tail n k r <
    orbitWindowContinuationSiblingMassPow2Tail n k r

/-- Finite-depth range form of source continuation outrunning recovery. -/
def ContinuationOutrunsRecoveryOnRange
    (n : OddNat) (k r len : ℕ) : Prop :=
  ∀ j, j < len → ContinuationOutrunsRecovery n k (r + j)

/-- Finite-depth range form of tail continuation outrunning recovery. -/
def TailContinuationOutrunsRecoveryOnRange
    (n : OddNat) (k r len : ℕ) : Prop :=
  ∀ j, j < len → TailContinuationOutrunsRecovery n k (r + j)

/-- Each source depth is either recovery-dominant or continuation-outrunning. -/
theorem recoveryDominates_or_continuationOutruns
    (n : OddNat) (k r : ℕ) :
    RecoveryDominatesContinuation n k r ∨
      ContinuationOutrunsRecovery n k r := by
  unfold RecoveryDominatesContinuation ContinuationOutrunsRecovery
  omega

/-- Each tail depth is either recovery-dominant or continuation-outrunning. -/
theorem tailRecoveryDominates_or_tailContinuationOutruns
    (n : OddNat) (k r : ℕ) :
    TailRecoveryDominatesContinuation n k r ∨
      TailContinuationOutrunsRecovery n k r := by
  unfold TailRecoveryDominatesContinuation TailContinuationOutrunsRecovery
  omega

/-- Source continuation outrunning recovery rules out recovery dominance. -/
theorem not_recoveryDominates_of_continuationOutruns
    (n : OddNat) (k r : ℕ)
    (h : ContinuationOutrunsRecovery n k r) :
    ¬ RecoveryDominatesContinuation n k r := by
  intro hdom
  unfold ContinuationOutrunsRecovery at h
  unfold RecoveryDominatesContinuation at hdom
  omega

/-- Tail continuation outrunning recovery rules out tail recovery dominance. -/
theorem not_tailRecoveryDominates_of_tailContinuationOutruns
    (n : OddNat) (k r : ℕ)
    (h : TailContinuationOutrunsRecovery n k r) :
    ¬ TailRecoveryDominatesContinuation n k r := by
  intro hdom
  unfold TailContinuationOutrunsRecovery at h
  unfold TailRecoveryDominatesContinuation at hdom
  omega

/-- Extract a source failure observation from a finite-depth failure range. -/
theorem continuationOutrunsRecovery_of_onRange
    (n : OddNat) (k r len j : ℕ)
    (h : ContinuationOutrunsRecoveryOnRange n k r len)
    (hj : j < len) :
    ContinuationOutrunsRecovery n k (r + j) :=
  h j hj

/-- Extract a tail failure observation from a finite-depth failure range. -/
theorem tailContinuationOutrunsRecovery_of_onRange
    (n : OddNat) (k r len j : ℕ)
    (h : TailContinuationOutrunsRecoveryOnRange n k r len)
    (hj : j < len) :
    TailContinuationOutrunsRecovery n k (r + j) :=
  h j hj

/--
If source continuation outruns recovery, then source continuation occupies more
than half of the parent retention mass.
-/
theorem moreThanHalf_continuation_of_continuationOutruns
    (n : OddNat) (k r : ℕ)
    (h : ContinuationOutrunsRecovery n k r) :
    MoreThanHalf
      (orbitWindowContinuationSiblingMassPow2 n k r)
      (orbitWindowRetentionMassPow2 n k r) := by
  unfold MoreThanHalf
  unfold ContinuationOutrunsRecovery at h
  rw [orbitWindowRetentionMass_split]
  omega

/--
If tail continuation outruns tail recovery, then tail continuation occupies
more than half of tail retention mass.
-/
theorem moreThanHalf_tailContinuation_of_tailContinuationOutruns
    (n : OddNat) (k r : ℕ)
    (h : TailContinuationOutrunsRecovery n k r) :
    MoreThanHalf
      (orbitWindowContinuationSiblingMassPow2Tail n k r)
      (orbitWindowRetentionMassPow2Tail n k r) := by
  unfold MoreThanHalf
  unfold TailContinuationOutrunsRecovery at h
  rw [orbitWindowRetentionMassPow2Tail_split]
  omega

/-- A source failure range gives more-than-half pressure at each depth. -/
theorem moreThanHalf_continuation_of_outRunsOnRange
    (n : OddNat) (k r len j : ℕ)
    (h : ContinuationOutrunsRecoveryOnRange n k r len)
    (hj : j < len) :
    MoreThanHalf
      (orbitWindowContinuationSiblingMassPow2 n k (r + j))
      (orbitWindowRetentionMassPow2 n k (r + j)) :=
  moreThanHalf_continuation_of_continuationOutruns
    n k (r + j) (continuationOutrunsRecovery_of_onRange n k r len j h hj)

/-- A tail failure range gives more-than-half pressure at each depth. -/
theorem moreThanHalf_tailContinuation_of_outRunsOnRange
    (n : OddNat) (k r len j : ℕ)
    (h : TailContinuationOutrunsRecoveryOnRange n k r len)
    (hj : j < len) :
    MoreThanHalf
      (orbitWindowContinuationSiblingMassPow2Tail n k (r + j))
      (orbitWindowRetentionMassPow2Tail n k (r + j)) :=
  moreThanHalf_tailContinuation_of_tailContinuationOutruns
    n k (r + j) (tailContinuationOutrunsRecovery_of_onRange n k r len j h hj)

/--
Generic finite range profile for strict more-than-half pressure.

The functions `count` and `total` are indexed by depth.  The predicate says
that every depth in the interval `[r, r + len)` carries `MoreThanHalf` pressure.
-/
def MoreThanHalfOnRange
    (count total : ℕ → ℕ) (r len : ℕ) : Prop :=
  ∀ j, j < len → MoreThanHalf (count (r + j)) (total (r + j))

/--
Source continuation pressure profile over a finite depth range.

This packages the statement that source continuation occupies more than half
of source retention at every depth in `[r, r + len)`.
-/
def SourceContinuationPressureOnRange
    (n : OddNat) (k r len : ℕ) : Prop :=
  MoreThanHalfOnRange
    (fun d => orbitWindowContinuationSiblingMassPow2 n k d)
    (fun d => orbitWindowRetentionMassPow2 n k d)
    r len

/--
Tail continuation pressure profile over a finite depth range.

This is the shifted-tail counterpart of
`SourceContinuationPressureOnRange`.
-/
def TailContinuationPressureOnRange
    (n : OddNat) (k r len : ℕ) : Prop :=
  MoreThanHalfOnRange
    (fun d => orbitWindowContinuationSiblingMassPow2Tail n k d)
    (fun d => orbitWindowRetentionMassPow2Tail n k d)
    r len

/-- A source failure range promotes to a source continuation pressure profile. -/
theorem sourceContinuationPressure_of_outRunsOnRange
    (n : OddNat) (k r len : ℕ)
    (h : ContinuationOutrunsRecoveryOnRange n k r len) :
    SourceContinuationPressureOnRange n k r len := by
  intro j hj
  exact moreThanHalf_continuation_of_outRunsOnRange n k r len j h hj

/-- A tail failure range promotes to a tail continuation pressure profile. -/
theorem tailContinuationPressure_of_outRunsOnRange
    (n : OddNat) (k r len : ℕ)
    (h : TailContinuationOutrunsRecoveryOnRange n k r len) :
    TailContinuationPressureOnRange n k r len := by
  intro j hj
  exact moreThanHalf_tailContinuation_of_outRunsOnRange n k r len j h hj

/-- Extract source more-than-half pressure from a source pressure profile. -/
theorem moreThanHalf_of_sourceContinuationPressure
    (n : OddNat) (k r len j : ℕ)
    (h : SourceContinuationPressureOnRange n k r len)
    (hj : j < len) :
    MoreThanHalf
      (orbitWindowContinuationSiblingMassPow2 n k (r + j))
      (orbitWindowRetentionMassPow2 n k (r + j)) :=
  h j hj

/-- Extract tail more-than-half pressure from a tail pressure profile. -/
theorem moreThanHalf_of_tailContinuationPressure
    (n : OddNat) (k r len j : ℕ)
    (h : TailContinuationPressureOnRange n k r len)
    (hj : j < len) :
    MoreThanHalf
      (orbitWindowContinuationSiblingMassPow2Tail n k (r + j))
      (orbitWindowRetentionMassPow2Tail n k (r + j)) :=
  h j hj

/--
Number of depths in `[r, r + len)` where source continuation has
more-than-half pressure.

This is a finite depth-mode count, not a window-mass count.
-/
noncomputable def sourceContinuationPressureDepthCount
    (n : OddNat) (k r len : ℕ) : ℕ :=
  by
    classical
    exact
      (List.range len).countP
        (fun j =>
          decide
            (MoreThanHalf
              (orbitWindowContinuationSiblingMassPow2 n k (r + j))
              (orbitWindowRetentionMassPow2 n k (r + j))))

/--
Number of depths in `[r, r + len)` where tail continuation has
more-than-half pressure.
-/
noncomputable def tailContinuationPressureDepthCount
    (n : OddNat) (k r len : ℕ) : ℕ :=
  by
    classical
    exact
      (List.range len).countP
        (fun j =>
          decide
          (MoreThanHalf
              (orbitWindowContinuationSiblingMassPow2Tail n k (r + j))
              (orbitWindowRetentionMassPow2Tail n k (r + j))))

/--
Number of depths in `[r, r + len)` where source continuation is controlled,
meaning it occupies at most half of source retention.
-/
noncomputable def sourceContinuationControlledDepthCount
    (n : OddNat) (k r len : ℕ) : ℕ :=
  by
    classical
    exact
      (List.range len).countP
        (fun j =>
          decide
            (AtMostHalf
              (orbitWindowContinuationSiblingMassPow2 n k (r + j))
              (orbitWindowRetentionMassPow2 n k (r + j))))

/--
Number of depths in `[r, r + len)` where tail continuation is controlled,
meaning it occupies at most half of tail retention.
-/
noncomputable def tailContinuationControlledDepthCount
    (n : OddNat) (k r len : ℕ) : ℕ :=
  by
    classical
    exact
      (List.range len).countP
        (fun j =>
          decide
            (AtMostHalf
              (orbitWindowContinuationSiblingMassPow2Tail n k (r + j))
              (orbitWindowRetentionMassPow2Tail n k (r + j))))

/-- Source pressure-depth count is bounded by the depth-range length. -/
theorem sourceContinuationPressureDepthCount_le_len
    (n : OddNat) (k r len : ℕ) :
    sourceContinuationPressureDepthCount n k r len ≤ len := by
  classical
  unfold sourceContinuationPressureDepthCount
  simpa using
    (List.countP_le_length
      (p :=
        fun j =>
          decide
            (MoreThanHalf
              (orbitWindowContinuationSiblingMassPow2 n k (r + j))
              (orbitWindowRetentionMassPow2 n k (r + j))))
      (l := List.range len))

/-- Tail pressure-depth count is bounded by the depth-range length. -/
theorem tailContinuationPressureDepthCount_le_len
    (n : OddNat) (k r len : ℕ) :
    tailContinuationPressureDepthCount n k r len ≤ len := by
  classical
  unfold tailContinuationPressureDepthCount
  simpa using
    (List.countP_le_length
      (p :=
        fun j =>
          decide
            (MoreThanHalf
              (orbitWindowContinuationSiblingMassPow2Tail n k (r + j))
              (orbitWindowRetentionMassPow2Tail n k (r + j))))
      (l := List.range len))

/-- Source controlled-depth count is bounded by the depth-range length. -/
theorem sourceContinuationControlledDepthCount_le_len
    (n : OddNat) (k r len : ℕ) :
    sourceContinuationControlledDepthCount n k r len ≤ len := by
  classical
  unfold sourceContinuationControlledDepthCount
  simpa using
    (List.countP_le_length
      (p :=
        fun j =>
          decide
            (AtMostHalf
              (orbitWindowContinuationSiblingMassPow2 n k (r + j))
              (orbitWindowRetentionMassPow2 n k (r + j))))
      (l := List.range len))

/-- Tail controlled-depth count is bounded by the depth-range length. -/
theorem tailContinuationControlledDepthCount_le_len
    (n : OddNat) (k r len : ℕ) :
    tailContinuationControlledDepthCount n k r len ≤ len := by
  classical
  unfold tailContinuationControlledDepthCount
  simpa using
    (List.countP_le_length
      (p :=
        fun j =>
          decide
            (AtMostHalf
              (orbitWindowContinuationSiblingMassPow2Tail n k (r + j))
              (orbitWindowRetentionMassPow2Tail n k (r + j))))
      (l := List.range len))

/--
The source depth range splits into controlled depths and pressure depths.
-/
theorem sourceContinuationControlledDepthCount_add_pressureDepthCount_eq_len
    (n : OddNat) (k r len : ℕ) :
    sourceContinuationControlledDepthCount n k r len +
      sourceContinuationPressureDepthCount n k r len = len := by
  classical
  unfold sourceContinuationControlledDepthCount
  unfold sourceContinuationPressureDepthCount
  induction len with
  | zero =>
      simp
  | succ len ih =>
      rw [List.range_succ, List.countP_append, List.countP_append,
        List.countP_singleton, List.countP_singleton]
      have hlast :
          (if decide
              (AtMostHalf
                (orbitWindowContinuationSiblingMassPow2 n k (r + len))
                (orbitWindowRetentionMassPow2 n k (r + len)))
            then 1 else 0) +
            (if decide
              (MoreThanHalf
                (orbitWindowContinuationSiblingMassPow2 n k (r + len))
                (orbitWindowRetentionMassPow2 n k (r + len)))
            then 1 else 0) = 1 := by
        by_cases hc :
            AtMostHalf
              (orbitWindowContinuationSiblingMassPow2 n k (r + len))
              (orbitWindowRetentionMassPow2 n k (r + len))
        · have hnot :
              ¬ MoreThanHalf
                (orbitWindowContinuationSiblingMassPow2 n k (r + len))
                (orbitWindowRetentionMassPow2 n k (r + len)) := by
            intro hm
            unfold AtMostHalf at hc
            unfold MoreThanHalf at hm
            omega
          simp [hc, hnot]
        · have hm :
              MoreThanHalf
                (orbitWindowContinuationSiblingMassPow2 n k (r + len))
                (orbitWindowRetentionMassPow2 n k (r + len)) := by
            cases
                atMostHalf_or_moreThanHalf
                  (orbitWindowContinuationSiblingMassPow2 n k (r + len))
                  (orbitWindowRetentionMassPow2 n k (r + len)) with
            | inl hcontrolled => exact False.elim (hc hcontrolled)
            | inr hpressure => exact hpressure
          simp [hc, hm]
      omega

/--
The tail depth range splits into controlled depths and pressure depths.
-/
theorem tailContinuationControlledDepthCount_add_pressureDepthCount_eq_len
    (n : OddNat) (k r len : ℕ) :
    tailContinuationControlledDepthCount n k r len +
      tailContinuationPressureDepthCount n k r len = len := by
  classical
  unfold tailContinuationControlledDepthCount
  unfold tailContinuationPressureDepthCount
  induction len with
  | zero =>
      simp
  | succ len ih =>
      rw [List.range_succ, List.countP_append, List.countP_append,
        List.countP_singleton, List.countP_singleton]
      have hlast :
          (if decide
              (AtMostHalf
                (orbitWindowContinuationSiblingMassPow2Tail n k (r + len))
                (orbitWindowRetentionMassPow2Tail n k (r + len)))
            then 1 else 0) +
            (if decide
              (MoreThanHalf
                (orbitWindowContinuationSiblingMassPow2Tail n k (r + len))
                (orbitWindowRetentionMassPow2Tail n k (r + len)))
            then 1 else 0) = 1 := by
        by_cases hc :
            AtMostHalf
              (orbitWindowContinuationSiblingMassPow2Tail n k (r + len))
              (orbitWindowRetentionMassPow2Tail n k (r + len))
        · have hnot :
              ¬ MoreThanHalf
                (orbitWindowContinuationSiblingMassPow2Tail n k (r + len))
                (orbitWindowRetentionMassPow2Tail n k (r + len)) := by
            intro hm
            unfold AtMostHalf at hc
            unfold MoreThanHalf at hm
            omega
          simp [hc, hnot]
        · have hm :
              MoreThanHalf
                (orbitWindowContinuationSiblingMassPow2Tail n k (r + len))
                (orbitWindowRetentionMassPow2Tail n k (r + len)) := by
            cases
                atMostHalf_or_moreThanHalf
                  (orbitWindowContinuationSiblingMassPow2Tail n k (r + len))
                  (orbitWindowRetentionMassPow2Tail n k (r + len)) with
            | inl hcontrolled => exact False.elim (hc hcontrolled)
            | inr hpressure => exact hpressure
          simp [hc, hm]
      omega

/--
Source depth-frequency predicate: pressure occupies at most half of the depth
range.
-/
def SourcePressureAtMostHalfOnDepthRange
    (n : OddNat) (k r len : ℕ) : Prop :=
  AtMostHalf (sourceContinuationPressureDepthCount n k r len) len

/--
Source depth-frequency predicate: pressure occupies more than half of the depth
range.
-/
def SourcePressureMoreThanHalfOnDepthRange
    (n : OddNat) (k r len : ℕ) : Prop :=
  MoreThanHalf (sourceContinuationPressureDepthCount n k r len) len

/- Tail depth-frequency predicate: pressure occupies at most half of the depth
range. -/
def TailPressureAtMostHalfOnDepthRange
    (n : OddNat) (k r len : ℕ) : Prop :=
  AtMostHalf (tailContinuationPressureDepthCount n k r len) len

/- Tail depth-frequency predicate: pressure occupies more than half of the
depth range. -/
def TailPressureMoreThanHalfOnDepthRange
    (n : OddNat) (k r len : ℕ) : Prop :=
  MoreThanHalf (tailContinuationPressureDepthCount n k r len) len

/-- Source pressure frequency is either at most half or more than half. -/
theorem sourcePressureAtMostHalf_or_moreThanHalfOnDepthRange
    (n : OddNat) (k r len : ℕ) :
    SourcePressureAtMostHalfOnDepthRange n k r len ∨
      SourcePressureMoreThanHalfOnDepthRange n k r len := by
  unfold SourcePressureAtMostHalfOnDepthRange
  unfold SourcePressureMoreThanHalfOnDepthRange
  exact atMostHalf_or_moreThanHalf
    (sourceContinuationPressureDepthCount n k r len) len

/-- Tail pressure frequency is either at most half or more than half. -/
theorem tailPressureAtMostHalf_or_moreThanHalfOnDepthRange
    (n : OddNat) (k r len : ℕ) :
    TailPressureAtMostHalfOnDepthRange n k r len ∨
      TailPressureMoreThanHalfOnDepthRange n k r len := by
  unfold TailPressureAtMostHalfOnDepthRange
  unfold TailPressureMoreThanHalfOnDepthRange
  exact atMostHalf_or_moreThanHalf
    (tailContinuationPressureDepthCount n k r len) len

/--
If source pressure is at most half of the depth range, then pressure depth
count is bounded by controlled depth count.
-/
theorem sourcePressureDepthCount_le_controlled_of_atMostHalf
    (n : OddNat) (k r len : ℕ)
    (h : SourcePressureAtMostHalfOnDepthRange n k r len) :
    sourceContinuationPressureDepthCount n k r len ≤
      sourceContinuationControlledDepthCount n k r len := by
  unfold SourcePressureAtMostHalfOnDepthRange at h
  unfold AtMostHalf at h
  have hpart :=
    sourceContinuationControlledDepthCount_add_pressureDepthCount_eq_len n k r len
  omega

/--
If source pressure depth count is bounded by controlled depth count, then
source pressure is at most half of the depth range.
-/
theorem sourcePressureAtMostHalf_of_pressureDepthCount_le_controlled
    (n : OddNat) (k r len : ℕ)
    (h :
      sourceContinuationPressureDepthCount n k r len ≤
        sourceContinuationControlledDepthCount n k r len) :
    SourcePressureAtMostHalfOnDepthRange n k r len := by
  unfold SourcePressureAtMostHalfOnDepthRange
  unfold AtMostHalf
  have hpart :=
    sourceContinuationControlledDepthCount_add_pressureDepthCount_eq_len n k r len
  omega

/--
Tail pressure at most half implies tail pressure depth count is bounded by
tail controlled depth count.
-/
theorem tailPressureDepthCount_le_controlled_of_atMostHalf
    (n : OddNat) (k r len : ℕ)
    (h : TailPressureAtMostHalfOnDepthRange n k r len) :
    tailContinuationPressureDepthCount n k r len ≤
      tailContinuationControlledDepthCount n k r len := by
  unfold TailPressureAtMostHalfOnDepthRange at h
  unfold AtMostHalf at h
  have hpart :=
    tailContinuationControlledDepthCount_add_pressureDepthCount_eq_len n k r len
  omega

/- Tail pressure depth count bounded by controlled count gives tail pressure at
most half. -/
theorem tailPressureAtMostHalf_of_pressureDepthCount_le_controlled
    (n : OddNat) (k r len : ℕ)
    (h :
      tailContinuationPressureDepthCount n k r len ≤
        tailContinuationControlledDepthCount n k r len) :
    TailPressureAtMostHalfOnDepthRange n k r len := by
  unfold TailPressureAtMostHalfOnDepthRange
  unfold AtMostHalf
  have hpart :=
    tailContinuationControlledDepthCount_add_pressureDepthCount_eq_len n k r len
  omega

/--
If source pressure occupies more than half of the depth range, then controlled
depth count is strictly smaller than pressure depth count.
-/
theorem sourceControlledDepthCount_lt_pressure_of_pressureMoreThanHalf
    (n : OddNat) (k r len : ℕ)
    (h : SourcePressureMoreThanHalfOnDepthRange n k r len) :
    sourceContinuationControlledDepthCount n k r len <
      sourceContinuationPressureDepthCount n k r len := by
  unfold SourcePressureMoreThanHalfOnDepthRange at h
  unfold MoreThanHalf at h
  have hpart :=
    sourceContinuationControlledDepthCount_add_pressureDepthCount_eq_len n k r len
  omega

/--
If source controlled depth count is strictly smaller than pressure depth count,
then source pressure occupies more than half of the depth range.
-/
theorem sourcePressureMoreThanHalf_of_controlledDepthCount_lt_pressure
    (n : OddNat) (k r len : ℕ)
    (h :
      sourceContinuationControlledDepthCount n k r len <
        sourceContinuationPressureDepthCount n k r len) :
    SourcePressureMoreThanHalfOnDepthRange n k r len := by
  unfold SourcePressureMoreThanHalfOnDepthRange
  unfold MoreThanHalf
  have hpart :=
    sourceContinuationControlledDepthCount_add_pressureDepthCount_eq_len n k r len
  omega

/- Tail more-than-half pressure implies tail controlled depth count is strictly
smaller than tail pressure depth count. -/
theorem tailControlledDepthCount_lt_pressure_of_pressureMoreThanHalf
    (n : OddNat) (k r len : ℕ)
    (h : TailPressureMoreThanHalfOnDepthRange n k r len) :
    tailContinuationControlledDepthCount n k r len <
      tailContinuationPressureDepthCount n k r len := by
  unfold TailPressureMoreThanHalfOnDepthRange at h
  unfold MoreThanHalf at h
  have hpart :=
    tailContinuationControlledDepthCount_add_pressureDepthCount_eq_len n k r len
  omega

/- Tail controlled depth count strictly below pressure depth count gives tail
more-than-half pressure. -/
theorem tailPressureMoreThanHalf_of_controlledDepthCount_lt_pressure
    (n : OddNat) (k r len : ℕ)
    (h :
      tailContinuationControlledDepthCount n k r len <
        tailContinuationPressureDepthCount n k r len) :
    TailPressureMoreThanHalfOnDepthRange n k r len := by
  unfold TailPressureMoreThanHalfOnDepthRange
  unfold MoreThanHalf
  have hpart :=
    tailContinuationControlledDepthCount_add_pressureDepthCount_eq_len n k r len
  omega

/--
Source more-than-half continuation pressure implies source continuation
outruns recovery.
-/
theorem continuationOutruns_of_moreThanHalf_continuation
    (n : OddNat) (k r : ℕ)
    (h :
      MoreThanHalf
        (orbitWindowContinuationSiblingMassPow2 n k r)
        (orbitWindowRetentionMassPow2 n k r)) :
    ContinuationOutrunsRecovery n k r := by
  unfold MoreThanHalf at h
  unfold ContinuationOutrunsRecovery
  rw [orbitWindowRetentionMass_split] at h
  omega

/--
Tail more-than-half continuation pressure implies tail continuation outruns
tail recovery.
-/
theorem tailContinuationOutruns_of_moreThanHalf_tailContinuation
    (n : OddNat) (k r : ℕ)
    (h :
      MoreThanHalf
        (orbitWindowContinuationSiblingMassPow2Tail n k r)
        (orbitWindowRetentionMassPow2Tail n k r)) :
    TailContinuationOutrunsRecovery n k r := by
  unfold MoreThanHalf at h
  unfold TailContinuationOutrunsRecovery
  rw [orbitWindowRetentionMassPow2Tail_split] at h
  omega

/--
Number of depths in `[r, r + len)` where source continuation outruns recovery.

This is the cause-side failure count corresponding to source pressure depth
count.
-/
noncomputable def sourceContinuationOutrunsDepthCount
    (n : OddNat) (k r len : ℕ) : ℕ :=
  by
    classical
    exact
      (List.range len).countP
        (fun j =>
          decide
            (ContinuationOutrunsRecovery n k (r + j)))

/--
Number of depths in `[r, r + len)` where tail continuation outruns tail
recovery.
-/
noncomputable def tailContinuationOutrunsDepthCount
    (n : OddNat) (k r len : ℕ) : ℕ :=
  by
    classical
    exact
      (List.range len).countP
        (fun j =>
          decide
            (TailContinuationOutrunsRecovery n k (r + j)))

/-- Source outruns mode is equivalent to source more-than-half pressure. -/
theorem continuationOutruns_iff_moreThanHalf_continuation
    (n : OddNat) (k r : ℕ) :
    ContinuationOutrunsRecovery n k r ↔
      MoreThanHalf
        (orbitWindowContinuationSiblingMassPow2 n k r)
        (orbitWindowRetentionMassPow2 n k r) := by
  constructor
  · exact moreThanHalf_continuation_of_continuationOutruns n k r
  · exact continuationOutruns_of_moreThanHalf_continuation n k r

/-- Tail outruns mode is equivalent to tail more-than-half pressure. -/
theorem tailContinuationOutruns_iff_moreThanHalf_tailContinuation
    (n : OddNat) (k r : ℕ) :
    TailContinuationOutrunsRecovery n k r ↔
      MoreThanHalf
        (orbitWindowContinuationSiblingMassPow2Tail n k r)
        (orbitWindowRetentionMassPow2Tail n k r) := by
  constructor
  · exact moreThanHalf_tailContinuation_of_tailContinuationOutruns n k r
  · exact tailContinuationOutruns_of_moreThanHalf_tailContinuation n k r

/--
Source cause-side outruns count equals the source pressure depth count.
-/
theorem sourceContinuationOutrunsDepthCount_eq_pressureDepthCount
    (n : OddNat) (k r len : ℕ) :
    sourceContinuationOutrunsDepthCount n k r len =
      sourceContinuationPressureDepthCount n k r len := by
  classical
  unfold sourceContinuationOutrunsDepthCount
  unfold sourceContinuationPressureDepthCount
  induction len with
  | zero =>
      simp
  | succ len ih =>
      rw [List.range_succ, List.countP_append, List.countP_append,
        List.countP_singleton, List.countP_singleton]
      have hlast :
          (if decide (ContinuationOutrunsRecovery n k (r + len)) then 1 else 0) =
            if decide
              (MoreThanHalf
                (orbitWindowContinuationSiblingMassPow2 n k (r + len))
                (orbitWindowRetentionMassPow2 n k (r + len)))
            then 1 else 0 := by
        by_cases h :
            ContinuationOutrunsRecovery n k (r + len)
        · have hp :
              MoreThanHalf
                (orbitWindowContinuationSiblingMassPow2 n k (r + len))
                (orbitWindowRetentionMassPow2 n k (r + len)) :=
            (continuationOutruns_iff_moreThanHalf_continuation
              n k (r + len)).1 h
          simp [h, hp]
        · have hp :
              ¬ MoreThanHalf
                (orbitWindowContinuationSiblingMassPow2 n k (r + len))
                (orbitWindowRetentionMassPow2 n k (r + len)) := by
            intro hpressure
            exact h
              ((continuationOutruns_iff_moreThanHalf_continuation
                n k (r + len)).2 hpressure)
          simp [h, hp]
      rw [ih, hlast]

/--
Tail cause-side outruns count equals the tail pressure depth count.
-/
theorem tailContinuationOutrunsDepthCount_eq_pressureDepthCount
    (n : OddNat) (k r len : ℕ) :
    tailContinuationOutrunsDepthCount n k r len =
      tailContinuationPressureDepthCount n k r len := by
  classical
  unfold tailContinuationOutrunsDepthCount
  unfold tailContinuationPressureDepthCount
  induction len with
  | zero =>
      simp
  | succ len ih =>
      rw [List.range_succ, List.countP_append, List.countP_append,
        List.countP_singleton, List.countP_singleton]
      have hlast :
          (if decide (TailContinuationOutrunsRecovery n k (r + len)) then 1 else 0) =
            if decide
              (MoreThanHalf
                (orbitWindowContinuationSiblingMassPow2Tail n k (r + len))
                (orbitWindowRetentionMassPow2Tail n k (r + len)))
            then 1 else 0 := by
        by_cases h :
            TailContinuationOutrunsRecovery n k (r + len)
        · have hp :
              MoreThanHalf
                (orbitWindowContinuationSiblingMassPow2Tail n k (r + len))
                (orbitWindowRetentionMassPow2Tail n k (r + len)) :=
            (tailContinuationOutruns_iff_moreThanHalf_tailContinuation
              n k (r + len)).1 h
          simp [h, hp]
        · have hp :
              ¬ MoreThanHalf
                (orbitWindowContinuationSiblingMassPow2Tail n k (r + len))
                (orbitWindowRetentionMassPow2Tail n k (r + len)) := by
            intro hpressure
            exact h
              ((tailContinuationOutruns_iff_moreThanHalf_tailContinuation
                n k (r + len)).2 hpressure)
          simp [h, hp]
      rw [ih, hlast]

/-- Source controlled mode implies source recovery dominance. -/
theorem recoveryDominates_of_atMostHalf_continuation
    (n : OddNat) (k r : ℕ)
    (h :
      AtMostHalf
        (orbitWindowContinuationSiblingMassPow2 n k r)
        (orbitWindowRetentionMassPow2 n k r)) :
    RecoveryDominatesContinuation n k r := by
  unfold AtMostHalf at h
  unfold RecoveryDominatesContinuation
  rw [orbitWindowRetentionMass_split] at h
  omega

/-- Tail controlled mode implies tail recovery dominance. -/
theorem tailRecoveryDominates_of_atMostHalf_tailContinuation
    (n : OddNat) (k r : ℕ)
    (h :
      AtMostHalf
        (orbitWindowContinuationSiblingMassPow2Tail n k r)
        (orbitWindowRetentionMassPow2Tail n k r)) :
    TailRecoveryDominatesContinuation n k r := by
  unfold AtMostHalf at h
  unfold TailRecoveryDominatesContinuation
  rw [orbitWindowRetentionMassPow2Tail_split] at h
  omega

/--
Number of depths in `[r, r + len)` where source recovery dominates
continuation.

This is the cause-side controlled count corresponding to source controlled
depth count.
-/
noncomputable def sourceRecoveryDominanceDepthCount
    (n : OddNat) (k r len : ℕ) : ℕ :=
  by
    classical
    exact
      (List.range len).countP
        (fun j =>
          decide
            (RecoveryDominatesContinuation n k (r + j)))

/--
Number of depths in `[r, r + len)` where tail recovery dominates tail
continuation.
-/
noncomputable def tailRecoveryDominanceDepthCount
    (n : OddNat) (k r len : ℕ) : ℕ :=
  by
    classical
    exact
      (List.range len).countP
        (fun j =>
          decide
            (TailRecoveryDominatesContinuation n k (r + j)))

/-- Source recovery dominance is equivalent to source controlled mode. -/
theorem recoveryDominates_iff_atMostHalf_continuation
    (n : OddNat) (k r : ℕ) :
    RecoveryDominatesContinuation n k r ↔
      AtMostHalf
        (orbitWindowContinuationSiblingMassPow2 n k r)
        (orbitWindowRetentionMassPow2 n k r) := by
  constructor
  · intro h
    exact atMostHalf_continuation_of_continuation_le_recovery n k r h
  · exact recoveryDominates_of_atMostHalf_continuation n k r

/-- Tail recovery dominance is equivalent to tail controlled mode. -/
theorem tailRecoveryDominates_iff_atMostHalf_tailContinuation
    (n : OddNat) (k r : ℕ) :
    TailRecoveryDominatesContinuation n k r ↔
      AtMostHalf
        (orbitWindowContinuationSiblingMassPow2Tail n k r)
        (orbitWindowRetentionMassPow2Tail n k r) := by
  constructor
  · intro h
    exact atMostHalf_tailContinuation_of_tailContinuation_le_tailRecovery n k r h
  · exact tailRecoveryDominates_of_atMostHalf_tailContinuation n k r

/--
Source cause-side dominance count equals the source controlled depth count.
-/
theorem sourceRecoveryDominanceDepthCount_eq_controlledDepthCount
    (n : OddNat) (k r len : ℕ) :
    sourceRecoveryDominanceDepthCount n k r len =
      sourceContinuationControlledDepthCount n k r len := by
  classical
  unfold sourceRecoveryDominanceDepthCount
  unfold sourceContinuationControlledDepthCount
  induction len with
  | zero =>
      simp
  | succ len ih =>
      rw [List.range_succ, List.countP_append, List.countP_append,
        List.countP_singleton, List.countP_singleton]
      have hlast :
          (if decide (RecoveryDominatesContinuation n k (r + len)) then 1 else 0) =
            if decide
              (AtMostHalf
                (orbitWindowContinuationSiblingMassPow2 n k (r + len))
                (orbitWindowRetentionMassPow2 n k (r + len)))
            then 1 else 0 := by
        by_cases h :
            RecoveryDominatesContinuation n k (r + len)
        · have hc :
              AtMostHalf
                (orbitWindowContinuationSiblingMassPow2 n k (r + len))
                (orbitWindowRetentionMassPow2 n k (r + len)) :=
            (recoveryDominates_iff_atMostHalf_continuation
              n k (r + len)).1 h
          simp [h, hc]
        · have hc :
              ¬ AtMostHalf
                (orbitWindowContinuationSiblingMassPow2 n k (r + len))
                (orbitWindowRetentionMassPow2 n k (r + len)) := by
            intro hcontrolled
            exact h
              ((recoveryDominates_iff_atMostHalf_continuation
                n k (r + len)).2 hcontrolled)
          simp [h, hc]
      rw [ih, hlast]

/--
Tail cause-side dominance count equals the tail controlled depth count.
-/
theorem tailRecoveryDominanceDepthCount_eq_controlledDepthCount
    (n : OddNat) (k r len : ℕ) :
    tailRecoveryDominanceDepthCount n k r len =
      tailContinuationControlledDepthCount n k r len := by
  classical
  unfold tailRecoveryDominanceDepthCount
  unfold tailContinuationControlledDepthCount
  induction len with
  | zero =>
      simp
  | succ len ih =>
      rw [List.range_succ, List.countP_append, List.countP_append,
        List.countP_singleton, List.countP_singleton]
      have hlast :
          (if decide (TailRecoveryDominatesContinuation n k (r + len)) then 1 else 0) =
            if decide
              (AtMostHalf
                (orbitWindowContinuationSiblingMassPow2Tail n k (r + len))
                (orbitWindowRetentionMassPow2Tail n k (r + len)))
            then 1 else 0 := by
        by_cases h :
            TailRecoveryDominatesContinuation n k (r + len)
        · have hc :
              AtMostHalf
                (orbitWindowContinuationSiblingMassPow2Tail n k (r + len))
                (orbitWindowRetentionMassPow2Tail n k (r + len)) :=
            (tailRecoveryDominates_iff_atMostHalf_tailContinuation
              n k (r + len)).1 h
          simp [h, hc]
        · have hc :
              ¬ AtMostHalf
                (orbitWindowContinuationSiblingMassPow2Tail n k (r + len))
                (orbitWindowRetentionMassPow2Tail n k (r + len)) := by
            intro hcontrolled
            exact h
              ((tailRecoveryDominates_iff_atMostHalf_tailContinuation
                n k (r + len)).2 hcontrolled)
          simp [h, hc]
      rw [ih, hlast]

/--
Cause-side source modes partition the depth range.
-/
theorem sourceCauseSideDepthCount_add_eq_len
    (n : OddNat) (k r len : ℕ) :
    sourceRecoveryDominanceDepthCount n k r len +
      sourceContinuationOutrunsDepthCount n k r len = len := by
  rw [sourceRecoveryDominanceDepthCount_eq_controlledDepthCount]
  rw [sourceContinuationOutrunsDepthCount_eq_pressureDepthCount]
  exact sourceContinuationControlledDepthCount_add_pressureDepthCount_eq_len n k r len

/--
Cause-side tail modes partition the depth range.
-/
theorem tailCauseSideDepthCount_add_eq_len
    (n : OddNat) (k r len : ℕ) :
    tailRecoveryDominanceDepthCount n k r len +
      tailContinuationOutrunsDepthCount n k r len = len := by
  rw [tailRecoveryDominanceDepthCount_eq_controlledDepthCount]
  rw [tailContinuationOutrunsDepthCount_eq_pressureDepthCount]
  exact tailContinuationControlledDepthCount_add_pressureDepthCount_eq_len n k r len

/--
Cause-side source frequency predicate: source continuation outruns recovery in
at most half of the observed depth range.
-/
def SourceOutrunsAtMostHalfOnDepthRange
    (n : OddNat) (k r len : ℕ) : Prop :=
  AtMostHalf (sourceContinuationOutrunsDepthCount n k r len) len

/--
Cause-side source frequency predicate: source continuation outruns recovery in
more than half of the observed depth range.
-/
def SourceOutrunsMoreThanHalfOnDepthRange
    (n : OddNat) (k r len : ℕ) : Prop :=
  MoreThanHalf (sourceContinuationOutrunsDepthCount n k r len) len

/--
Cause-side tail frequency predicate: tail continuation outruns recovery in at
most half of the observed depth range.
-/
def TailOutrunsAtMostHalfOnDepthRange
    (n : OddNat) (k r len : ℕ) : Prop :=
  AtMostHalf (tailContinuationOutrunsDepthCount n k r len) len

/--
Cause-side tail frequency predicate: tail continuation outruns recovery in
more than half of the observed depth range.
-/
def TailOutrunsMoreThanHalfOnDepthRange
    (n : OddNat) (k r len : ℕ) : Prop :=
  MoreThanHalf (tailContinuationOutrunsDepthCount n k r len) len

/-- Source cause-side outruns frequency has the same dichotomy as pressure. -/
theorem sourceOutrunsAtMostHalf_or_moreThanHalfOnDepthRange
    (n : OddNat) (k r len : ℕ) :
    SourceOutrunsAtMostHalfOnDepthRange n k r len ∨
      SourceOutrunsMoreThanHalfOnDepthRange n k r len := by
  unfold SourceOutrunsAtMostHalfOnDepthRange
  unfold SourceOutrunsMoreThanHalfOnDepthRange
  exact atMostHalf_or_moreThanHalf
    (sourceContinuationOutrunsDepthCount n k r len) len

/-- Tail cause-side outruns frequency has the same dichotomy as pressure. -/
theorem tailOutrunsAtMostHalf_or_moreThanHalfOnDepthRange
    (n : OddNat) (k r len : ℕ) :
    TailOutrunsAtMostHalfOnDepthRange n k r len ∨
      TailOutrunsMoreThanHalfOnDepthRange n k r len := by
  unfold TailOutrunsAtMostHalfOnDepthRange
  unfold TailOutrunsMoreThanHalfOnDepthRange
  exact atMostHalf_or_moreThanHalf
    (tailContinuationOutrunsDepthCount n k r len) len

/--
Source cause-side at-most-half frequency is equivalent to descriptive source
pressure at-most-half frequency.
-/
theorem sourceOutrunsAtMostHalf_iff_pressureAtMostHalf
    (n : OddNat) (k r len : ℕ) :
    SourceOutrunsAtMostHalfOnDepthRange n k r len ↔
      SourcePressureAtMostHalfOnDepthRange n k r len := by
  unfold SourceOutrunsAtMostHalfOnDepthRange
  unfold SourcePressureAtMostHalfOnDepthRange
  rw [sourceContinuationOutrunsDepthCount_eq_pressureDepthCount]

/--
Source cause-side more-than-half frequency is equivalent to descriptive source
pressure more-than-half frequency.
-/
theorem sourceOutrunsMoreThanHalf_iff_pressureMoreThanHalf
    (n : OddNat) (k r len : ℕ) :
    SourceOutrunsMoreThanHalfOnDepthRange n k r len ↔
      SourcePressureMoreThanHalfOnDepthRange n k r len := by
  unfold SourceOutrunsMoreThanHalfOnDepthRange
  unfold SourcePressureMoreThanHalfOnDepthRange
  rw [sourceContinuationOutrunsDepthCount_eq_pressureDepthCount]

/--
Tail cause-side at-most-half frequency is equivalent to descriptive tail
pressure at-most-half frequency.
-/
theorem tailOutrunsAtMostHalf_iff_pressureAtMostHalf
    (n : OddNat) (k r len : ℕ) :
    TailOutrunsAtMostHalfOnDepthRange n k r len ↔
      TailPressureAtMostHalfOnDepthRange n k r len := by
  unfold TailOutrunsAtMostHalfOnDepthRange
  unfold TailPressureAtMostHalfOnDepthRange
  rw [tailContinuationOutrunsDepthCount_eq_pressureDepthCount]

/--
Tail cause-side more-than-half frequency is equivalent to descriptive tail
pressure more-than-half frequency.
-/
theorem tailOutrunsMoreThanHalf_iff_pressureMoreThanHalf
    (n : OddNat) (k r len : ℕ) :
    TailOutrunsMoreThanHalfOnDepthRange n k r len ↔
      TailPressureMoreThanHalfOnDepthRange n k r len := by
  unfold TailOutrunsMoreThanHalfOnDepthRange
  unfold TailPressureMoreThanHalfOnDepthRange
  rw [tailContinuationOutrunsDepthCount_eq_pressureDepthCount]

/--
If source outruns depths occupy more than half of the depth range, then they
strictly outnumber source dominance depths.
-/
theorem sourceDominanceDepthCount_lt_outruns_of_outrunsMoreThanHalf
    (n : OddNat) (k r len : ℕ)
    (h : SourceOutrunsMoreThanHalfOnDepthRange n k r len) :
    sourceRecoveryDominanceDepthCount n k r len <
      sourceContinuationOutrunsDepthCount n k r len := by
  unfold SourceOutrunsMoreThanHalfOnDepthRange at h
  unfold MoreThanHalf at h
  have hpart := sourceCauseSideDepthCount_add_eq_len n k r len
  omega

/--
If tail outruns depths occupy more than half of the depth range, then they
strictly outnumber tail dominance depths.
-/
theorem tailDominanceDepthCount_lt_outruns_of_outrunsMoreThanHalf
    (n : OddNat) (k r len : ℕ)
    (h : TailOutrunsMoreThanHalfOnDepthRange n k r len) :
    tailRecoveryDominanceDepthCount n k r len <
      tailContinuationOutrunsDepthCount n k r len := by
  unfold TailOutrunsMoreThanHalfOnDepthRange at h
  unfold MoreThanHalf at h
  have hpart := tailCauseSideDepthCount_add_eq_len n k r len
  omega

/--
Source cause-side outruns-heavy frequency gives descriptive source pressure
heavy frequency.
-/
theorem sourcePressureMoreThanHalf_of_outrunsMoreThanHalf
    (n : OddNat) (k r len : ℕ)
    (h : SourceOutrunsMoreThanHalfOnDepthRange n k r len) :
    SourcePressureMoreThanHalfOnDepthRange n k r len :=
  (sourceOutrunsMoreThanHalf_iff_pressureMoreThanHalf n k r len).1 h

/--
Tail cause-side outruns-heavy frequency gives descriptive tail pressure heavy
frequency.
-/
theorem tailPressureMoreThanHalf_of_outrunsMoreThanHalf
    (n : OddNat) (k r len : ℕ)
    (h : TailOutrunsMoreThanHalfOnDepthRange n k r len) :
    TailPressureMoreThanHalfOnDepthRange n k r len :=
  (tailOutrunsMoreThanHalf_iff_pressureMoreThanHalf n k r len).1 h

/--
Source cause-side outruns-heavy frequency forces descriptive pressure depths to
outnumber controlled depths.
-/
theorem sourceControlledDepthCount_lt_pressure_of_outrunsMoreThanHalf
    (n : OddNat) (k r len : ℕ)
    (h : SourceOutrunsMoreThanHalfOnDepthRange n k r len) :
    sourceContinuationControlledDepthCount n k r len <
      sourceContinuationPressureDepthCount n k r len :=
  sourceControlledDepthCount_lt_pressure_of_pressureMoreThanHalf
    n k r len
    (sourcePressureMoreThanHalf_of_outrunsMoreThanHalf n k r len h)

/--
Tail cause-side outruns-heavy frequency forces descriptive pressure depths to
outnumber controlled depths.
-/
theorem tailControlledDepthCount_lt_pressure_of_outrunsMoreThanHalf
    (n : OddNat) (k r len : ℕ)
    (h : TailOutrunsMoreThanHalfOnDepthRange n k r len) :
    tailContinuationControlledDepthCount n k r len <
      tailContinuationPressureDepthCount n k r len :=
  tailControlledDepthCount_lt_pressure_of_pressureMoreThanHalf
    n k r len
    (tailPressureMoreThanHalf_of_outrunsMoreThanHalf n k r len h)

/--
Source cause-side outruns-heavy frequency guarantees that at least one source
pressure depth exists.
-/
theorem sourcePressureDepthCount_pos_of_outrunsMoreThanHalf
    (n : OddNat) (k r len : ℕ)
    (h : SourceOutrunsMoreThanHalfOnDepthRange n k r len) :
    0 < sourceContinuationPressureDepthCount n k r len := by
  have hlt :
      sourceContinuationControlledDepthCount n k r len <
        sourceContinuationPressureDepthCount n k r len :=
    sourceControlledDepthCount_lt_pressure_of_outrunsMoreThanHalf n k r len h
  omega

/--
Tail cause-side outruns-heavy frequency guarantees that at least one tail
pressure depth exists.
-/
theorem tailPressureDepthCount_pos_of_outrunsMoreThanHalf
    (n : OddNat) (k r len : ℕ)
    (h : TailOutrunsMoreThanHalfOnDepthRange n k r len) :
    0 < tailContinuationPressureDepthCount n k r len := by
  have hlt :
      tailContinuationControlledDepthCount n k r len <
        tailContinuationPressureDepthCount n k r len :=
    tailControlledDepthCount_lt_pressure_of_outrunsMoreThanHalf n k r len h
  omega

/--
If the source outruns side does not fill a nonempty range, then the source
dominance side is present.

This is a small partition-consumption lemma for later recovery-side arguments.
-/
theorem sourceDominanceDepthCount_pos_of_outrunsAtMostHalf_and_not_all_outruns
    (n : OddNat) (k r len : ℕ)
    (_h : SourceOutrunsAtMostHalfOnDepthRange n k r len)
    (hnotAllOutruns :
      sourceContinuationOutrunsDepthCount n k r len < len) :
    0 < sourceRecoveryDominanceDepthCount n k r len := by
  have hpart := sourceCauseSideDepthCount_add_eq_len n k r len
  omega

/--
If the tail outruns side does not fill a nonempty range, then the tail
dominance side is present.

This is the shifted-tail counterpart of the source partition-consumption lemma.
-/
theorem tailDominanceDepthCount_pos_of_outrunsAtMostHalf_and_not_all_outruns
    (n : OddNat) (k r len : ℕ)
    (_h : TailOutrunsAtMostHalfOnDepthRange n k r len)
    (hnotAllOutruns :
      tailContinuationOutrunsDepthCount n k r len < len) :
    0 < tailRecoveryDominanceDepthCount n k r len := by
  have hpart := tailCauseSideDepthCount_add_eq_len n k r len
  omega

/--
If source continuation pressure holds at every depth of the range, then the
source pressure-depth count fills the whole range.
-/
theorem sourceContinuationPressureDepthCount_eq_len_of_pressureOnRange
    (n : OddNat) (k r len : ℕ)
    (h : SourceContinuationPressureOnRange n k r len) :
    sourceContinuationPressureDepthCount n k r len = len := by
  classical
  unfold sourceContinuationPressureDepthCount
  induction len with
  | zero =>
      simp
  | succ len ih =>
      rw [List.range_succ, List.countP_append, List.countP_singleton]
      have ih' :
          (List.range len).countP
              (fun j =>
                decide
                  (MoreThanHalf
                    (orbitWindowContinuationSiblingMassPow2 n k (r + j))
                    (orbitWindowRetentionMassPow2 n k (r + j)))) = len := by
        apply ih
        intro j hj
        exact h j (Nat.lt_trans hj (Nat.lt_succ_self len))
      have hlast :
          decide
              (MoreThanHalf
                (orbitWindowContinuationSiblingMassPow2 n k (r + len))
                (orbitWindowRetentionMassPow2 n k (r + len))) = true := by
        exact decide_eq_true (h len (Nat.lt_succ_self len))
      rw [ih', hlast]
      simp

/--
If tail continuation pressure holds at every depth of the range, then the tail
pressure-depth count fills the whole range.
-/
theorem tailContinuationPressureDepthCount_eq_len_of_pressureOnRange
    (n : OddNat) (k r len : ℕ)
    (h : TailContinuationPressureOnRange n k r len) :
    tailContinuationPressureDepthCount n k r len = len := by
  classical
  unfold tailContinuationPressureDepthCount
  induction len with
  | zero =>
      simp
  | succ len ih =>
      rw [List.range_succ, List.countP_append, List.countP_singleton]
      have ih' :
          (List.range len).countP
              (fun j =>
                decide
                  (MoreThanHalf
                    (orbitWindowContinuationSiblingMassPow2Tail n k (r + j))
                    (orbitWindowRetentionMassPow2Tail n k (r + j)))) = len := by
        apply ih
        intro j hj
        exact h j (Nat.lt_trans hj (Nat.lt_succ_self len))
      have hlast :
          decide
              (MoreThanHalf
                (orbitWindowContinuationSiblingMassPow2Tail n k (r + len))
                (orbitWindowRetentionMassPow2Tail n k (r + len))) = true := by
        exact decide_eq_true (h len (Nat.lt_succ_self len))
      rw [ih', hlast]
      simp

/--
Predicate-facing source half criterion.

This is the readable version of
`atMostHalf_continuation_of_continuation_le_recovery`.
-/
theorem atMostHalf_continuation_of_recoveryDominates
    (n : OddNat) (k r : ℕ)
    (h : RecoveryDominatesContinuation n k r) :
    AtMostHalf
      (orbitWindowContinuationSiblingMassPow2 n k r)
      (orbitWindowRetentionMassPow2 n k r) :=
  atMostHalf_continuation_of_continuation_le_recovery n k r h

/-- Predicate-facing tail half criterion. -/
theorem atMostHalf_tailContinuation_of_tailRecoveryDominates
    (n : OddNat) (k r : ℕ)
    (h : TailRecoveryDominatesContinuation n k r) :
    AtMostHalf
      (orbitWindowContinuationSiblingMassPow2Tail n k r)
      (orbitWindowRetentionMassPow2Tail n k r) :=
  atMostHalf_tailContinuation_of_tailContinuation_le_tailRecovery n k r h

/-- Predicate-facing source half criterion from recovery budget coverage. -/
theorem atMostHalf_continuation_of_recoveryCoversHalf
    (n : OddNat) (k r : ℕ)
    (h : RecoveryCoversHalfRetention n k r) :
    AtMostHalf
      (orbitWindowContinuationSiblingMassPow2 n k r)
      (orbitWindowRetentionMassPow2 n k r) :=
  atMostHalf_continuation_of_retention_le_two_recovery n k r h

/-- Predicate-facing tail half criterion from tail recovery budget coverage. -/
theorem atMostHalf_tailContinuation_of_tailRecoveryCoversHalf
    (n : OddNat) (k r : ℕ)
    (h : TailRecoveryCoversHalfRetention n k r) :
    AtMostHalf
      (orbitWindowContinuationSiblingMassPow2Tail n k r)
      (orbitWindowRetentionMassPow2Tail n k r) :=
  atMostHalf_tailContinuation_of_tailRetention_le_two_tailRecovery n k r h

/-- A range dominance hypothesis yields the source half criterion at each depth. -/
theorem atMostHalf_continuation_of_recoveryDominatesOnRange
    (n : OddNat) (k r len j : ℕ)
    (h : RecoveryDominatesOnRange n k r len) (hj : j < len) :
    AtMostHalf
      (orbitWindowContinuationSiblingMassPow2 n k (r + j))
      (orbitWindowRetentionMassPow2 n k (r + j)) :=
  atMostHalf_continuation_of_recoveryDominates n k (r + j) (h j hj)

/-- A tail range dominance hypothesis yields the tail half criterion at each depth. -/
theorem atMostHalf_tailContinuation_of_tailRecoveryDominatesOnRange
    (n : OddNat) (k r len j : ℕ)
    (h : TailRecoveryDominatesOnRange n k r len) (hj : j < len) :
    AtMostHalf
      (orbitWindowContinuationSiblingMassPow2Tail n k (r + j))
      (orbitWindowRetentionMassPow2Tail n k (r + j)) :=
  atMostHalf_tailContinuation_of_tailRecoveryDominates n k (r + j) (h j hj)

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
More-than-half pressure at depth `2` forces positive depth-two continuation
mass.

This is the first thin entrance from the pressure vocabulary into the delayed
reservoir budget.
-/
theorem sourceContinuationMass_depth_two_pos_of_pressure_depth_two
    (n : OddNat) (k : ℕ)
    (h :
      MoreThanHalf
        (orbitWindowContinuationSiblingMassPow2 n k 2)
        (orbitWindowRetentionMassPow2 n k 2)) :
    0 < orbitWindowContinuationSiblingMassPow2 n k 2 := by
  unfold MoreThanHalf at h
  omega

/--
Meaning-name wrapper for extracting local source pressure from a finite source
pressure profile.

Use this theorem at call sites instead of the more generic internal extractor
when the proof is conceptually moving from range pressure to a local depth.
-/
theorem sourcePressureAtDepth_of_pressureOnRange
    (n : OddNat) (k r len j : ℕ)
    (h : SourceContinuationPressureOnRange n k r len)
    (hj : j < len) :
    MoreThanHalf
      (orbitWindowContinuationSiblingMassPow2 n k (r + j))
      (orbitWindowRetentionMassPow2 n k (r + j)) :=
  moreThanHalf_of_sourceContinuationPressure n k r len j h hj

/--
Local source pressure at any depth forces positive source continuation mass at
that depth.
-/
theorem sourceContinuationMass_pos_of_localPressure
    (n : OddNat) (k r : ℕ)
    (h :
      MoreThanHalf
        (orbitWindowContinuationSiblingMassPow2 n k r)
        (orbitWindowRetentionMassPow2 n k r)) :
    0 < orbitWindowContinuationSiblingMassPow2 n k r := by
  unfold MoreThanHalf at h
  omega

/--
Range pressure yields positive source continuation mass at any selected depth
inside the range.
-/
theorem sourceContinuationMass_pos_of_pressureOnRange_at
    (n : OddNat) (k r len j : ℕ)
    (h : SourceContinuationPressureOnRange n k r len)
    (hj : j < len) :
    0 < orbitWindowContinuationSiblingMassPow2 n k (r + j) :=
  sourceContinuationMass_pos_of_localPressure n k (r + j)
    (sourcePressureAtDepth_of_pressureOnRange n k r len j h hj)

/--
Extract local depth-two source pressure from the one-depth range pressure
profile beginning at depth `2`.
-/
theorem sourcePressureDepthTwo_of_pressureOnRange_two_one
    (n : OddNat) (k : ℕ)
    (h : SourceContinuationPressureOnRange n k 2 1) :
    MoreThanHalf
      (orbitWindowContinuationSiblingMassPow2 n k 2)
      (orbitWindowRetentionMassPow2 n k 2) := by
  simpa using moreThanHalf_of_sourceContinuationPressure n k 2 1 0 h (by omega)

/--
One-depth range pressure at depth `2` forces positive depth-two continuation
mass.
-/
theorem sourceContinuationMass_depth_two_pos_of_pressureOnRange_two_one
    (n : OddNat) (k : ℕ)
    (h : SourceContinuationPressureOnRange n k 2 1) :
    0 < orbitWindowContinuationSiblingMassPow2 n k 2 :=
  sourceContinuationMass_depth_two_pos_of_pressure_depth_two n k
    (sourcePressureDepthTwo_of_pressureOnRange_two_one n k h)

/--
Pressure-facing wrapper for the depth-two delayed-reservoir budget.

The pressure hypothesis is not needed by the inequality itself; it records the
intended caller context, where a pressure-heavy depth supplies positive
continuation mass and then uses the delayed budget.
-/
theorem sourcePressureDepthTwo_delayed_budget_with_tailSeven_remainder
    (n : OddNat) (k : ℕ)
    (_h :
      MoreThanHalf
        (orbitWindowContinuationSiblingMassPow2 n k 2)
        (orbitWindowRetentionMassPow2 n k 2)) :
    (k + 1) + orbitWindowContinuationSiblingMassPow2 n k 2 ≤
      sumS n ((k + 1) + 1) +
        orbitWindowResidueCountMod8EqSevenTail n k :=
  sourceContinuationMass_depth_two_delayed_budget_with_tailSeven_remainder n k

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
