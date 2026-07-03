/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Collatz.PetalBridge.Basic

#print "file: DkMath.Collatz.PetalBridge.Residues"

namespace DkMath.Collatz


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


end DkMath.Collatz
