/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Petal.Counting

#print "file: DkMath.Petal.Address"

/-!
# Petal Addressing

This file fixes the first outer address convention for relative Petal systems.

The address is one-step and outermost.  The channel is internally zero-based:

* channel `0` is the inheritance/core channel;
* channels `1..n` are Petal channels.

The value `m` is read as a one-based position inside the current lap total.
-/

namespace DkMath
namespace Petal

/-- One-step outer block size at the given lap. -/
def relPetalBlockSize (n lap : Nat) : Nat :=
  relPetalTotal n (lap - 1)

/--
Outer Petal address.

`channel = 0` is the inheritance/core channel.  Positive channels are Petal
channels.  `offset` is one-based inside the selected outer block.
-/
structure PetalAddress where
  lap : Nat
  channel : Nat
  offset : Nat
deriving Repr, DecidableEq

/-- The inheritance/core channel is channel `0`. -/
def IsInheritanceChannel (A : PetalAddress) : Prop :=
  A.channel = 0

/-- Petal channels are the positive channels. -/
def IsPetalChannel (A : PetalAddress) : Prop :=
  0 < A.channel

/--
Outer one-step address of a one-based value `m`.

The correctness lemmas are intended for `0 < n`, `0 < lap`, and
`1 <= m <= relPetalTotal n lap`.
-/
def outerPetalAddress (n lap m : Nat) : PetalAddress :=
  let b := relPetalBlockSize n lap
  { lap := lap
    channel := (m - 1) / b
    offset := (m - 1) % b + 1 }

/--
The one-step remainder passed to the next inner lap.

This is the offset component of the outer address.  If the address lands in the
inheritance/core channel, this remainder is the original value itself.
-/
def outerPetalRemainder (n lap m : Nat) : Nat :=
  (outerPetalAddress n lap m).offset

/-- The block size at lap zero is the base unit core. -/
theorem relPetalBlockSize_zero (n : Nat) :
    relPetalBlockSize n 0 = n := by
  simp [relPetalBlockSize, relPetalTotal_zero]

/-- A positive-lap block size is the previous lap total. -/
theorem relPetalBlockSize_succ (n lap : Nat) :
    relPetalBlockSize n (lap + 1) = relPetalTotal n lap := by
  simp [relPetalBlockSize]

/-- The pentagonal one-lap address of `25`. -/
theorem outerPetalAddress_five_one_twentyfive :
    outerPetalAddress 5 1 25 = { lap := 1, channel := 4, offset := 5 } := by
  decide

/--
The pentagonal two-lap address of `25`.

This lands in channel `0`, the inheritance/core channel, with offset `25`.
-/
theorem outerPetalAddress_five_two_twentyfive :
    outerPetalAddress 5 2 25 = { lap := 2, channel := 0, offset := 25 } := by
  decide

/-- The address lap field is definitionally the observed lap. -/
theorem outerPetalAddress_lap (n lap m : Nat) :
    (outerPetalAddress n lap m).lap = lap := by
  rfl

/-- The outer remainder is definitionally the address offset. -/
theorem outerPetalRemainder_eq_offset (n lap m : Nat) :
    outerPetalRemainder n lap m = (outerPetalAddress n lap m).offset := by
  rfl

/-- The address is in the inheritance/core channel exactly when its channel is zero. -/
theorem isInheritanceChannel_iff_channel_eq_zero (A : PetalAddress) :
    IsInheritanceChannel A ↔ A.channel = 0 := by
  rfl

/-- The address is in a Petal channel exactly when its channel is positive. -/
theorem isPetalChannel_iff_channel_pos (A : PetalAddress) :
    IsPetalChannel A ↔ 0 < A.channel := by
  rfl

/-- No address can be both inheritance/core and Petal. -/
theorem not_isPetalChannel_of_isInheritanceChannel {A : PetalAddress}
    (hA : IsInheritanceChannel A) :
    ¬ IsPetalChannel A := by
  intro hP
  unfold IsInheritanceChannel at hA
  unfold IsPetalChannel at hP
  rw [hA] at hP
  exact Nat.not_lt_zero _ hP

/-- A non-inheritance address is a Petal channel. -/
theorem isPetalChannel_of_not_isInheritanceChannel {A : PetalAddress}
    (hA : ¬ IsInheritanceChannel A) :
    IsPetalChannel A := by
  exact Nat.pos_of_ne_zero hA

/-- The offset of an outer address is always positive. -/
theorem outerPetalAddress_offset_pos
    {n lap m : Nat} :
    0 < (outerPetalAddress n lap m).offset := by
  simp [outerPetalAddress]

/-- The outer remainder is always positive. -/
theorem outerPetalRemainder_pos
    {n lap m : Nat} :
    0 < outerPetalRemainder n lap m := by
  exact outerPetalAddress_offset_pos

/-- The offset of a valid address is bounded by the outer block size. -/
theorem outerPetalAddress_offset_le_blockSize
    {n lap m : Nat} (hb : 0 < relPetalBlockSize n lap) :
    (outerPetalAddress n lap m).offset ≤ relPetalBlockSize n lap := by
  rw [outerPetalAddress]
  exact Nat.succ_le_of_lt (Nat.mod_lt _ hb)

/-- The outer remainder is bounded by the outer block size. -/
theorem outerPetalRemainder_le_blockSize
    {n lap m : Nat} (hb : 0 < relPetalBlockSize n lap) :
    outerPetalRemainder n lap m ≤ relPetalBlockSize n lap := by
  exact outerPetalAddress_offset_le_blockSize hb

/--
The channel is bounded by the lap base when the observed value stays inside the
current lap total.
-/
theorem outerPetalAddress_channel_lt_lapBase
    {n lap m : Nat}
    (hlap : 0 < lap)
    (hm : 1 ≤ m)
    (hbound : m ≤ relPetalTotal n lap) :
    (outerPetalAddress n lap m).channel < lapBase n := by
  rcases Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hlap) with ⟨k, rfl⟩
  have hm_pos : 0 < m := hm
  have htotal :
      relPetalTotal n (k + 1) = relPetalTotal n k * lapBase n :=
    relPetalTotal_succ n k
  have hsub_lt : m - 1 < relPetalTotal n k * lapBase n := by
    have hlt : m - 1 < m := Nat.sub_lt hm_pos Nat.zero_lt_one
    exact lt_of_lt_of_le hlt (by simpa [htotal] using hbound)
  rw [outerPetalAddress, relPetalBlockSize_succ]
  exact Nat.div_lt_of_lt_mul hsub_lt

/--
The outer address lands in channel `0` exactly when the zero-based position
`m - 1` is still inside the first outer block.
-/
theorem outerPetalAddress_channel_eq_zero_iff_sub_lt_blockSize
    {n lap m : Nat} (hb : 0 < relPetalBlockSize n lap) :
    (outerPetalAddress n lap m).channel = 0 ↔
      m - 1 < relPetalBlockSize n lap := by
  rw [outerPetalAddress]
  constructor
  · intro h
    by_contra hlt
    have hle : relPetalBlockSize n lap ≤ m - 1 := Nat.le_of_not_gt hlt
    have hdiv_pos : 0 < (m - 1) / relPetalBlockSize n lap :=
      Nat.div_pos hle hb
    change (m - 1) / relPetalBlockSize n lap = 0 at h
    rw [h] at hdiv_pos
    exact Nat.not_lt_zero _ hdiv_pos
  · intro h
    exact Nat.div_eq_of_lt h

/--
For a one-based value, channel `0` is equivalent to staying within the first
outer block.
-/
theorem outerPetalAddress_channel_eq_zero_iff_le_blockSize
    {n lap m : Nat} (hm : 1 ≤ m) (hb : 0 < relPetalBlockSize n lap) :
    (outerPetalAddress n lap m).channel = 0 ↔
      m ≤ relPetalBlockSize n lap := by
  rw [outerPetalAddress_channel_eq_zero_iff_sub_lt_blockSize hb]
  constructor
  · intro h
    exact Nat.le_of_pred_lt h
  · intro h
    exact Nat.sub_one_lt_of_le hm h

/-- The inheritance/core predicate for an outer address is the channel-zero test. -/
theorem outerPetalAddress_isInheritanceChannel_iff_le_blockSize
    {n lap m : Nat} (hm : 1 ≤ m) (hb : 0 < relPetalBlockSize n lap) :
    IsInheritanceChannel (outerPetalAddress n lap m) ↔
      m ≤ relPetalBlockSize n lap := by
  exact outerPetalAddress_channel_eq_zero_iff_le_blockSize hm hb

/-- If a valid one-based value is past the first block, it is in a Petal channel. -/
theorem outerPetalAddress_isPetalChannel_of_blockSize_lt
    {n lap m : Nat}
    (hb : 0 < relPetalBlockSize n lap)
    (hbm : relPetalBlockSize n lap < m) :
    IsPetalChannel (outerPetalAddress n lap m) := by
  apply isPetalChannel_of_not_isInheritanceChannel
  intro h0
  have hm : 1 ≤ m := Nat.succ_le_of_lt (lt_of_le_of_lt (Nat.zero_le _) hbm)
  have hle :
      m ≤ relPetalBlockSize n lap :=
    (outerPetalAddress_channel_eq_zero_iff_le_blockSize hm hb).1 h0
  exact (not_lt_of_ge hle) hbm

/--
If a one-based value stays inside the first outer block, the outer remainder is
the original value.
-/
theorem outerPetalRemainder_eq_self_of_le_blockSize
    {n lap m : Nat}
    (hm : 1 ≤ m)
    (hmb : m ≤ relPetalBlockSize n lap) :
    outerPetalRemainder n lap m = m := by
  have hlt : m - 1 < relPetalBlockSize n lap :=
    Nat.sub_one_lt_of_le hm hmb
  rw [outerPetalRemainder, outerPetalAddress]
  rw [Nat.mod_eq_of_lt hlt]
  exact Nat.sub_add_cancel hm

/--
If the outer address lands in the inheritance/core channel, the outer remainder
is the original value.
-/
theorem outerPetalRemainder_eq_self_of_isInheritanceChannel
    {n lap m : Nat}
    (hm : 1 ≤ m)
    (hb : 0 < relPetalBlockSize n lap)
    (hA : IsInheritanceChannel (outerPetalAddress n lap m)) :
    outerPetalRemainder n lap m = m := by
  have hle : m ≤ relPetalBlockSize n lap :=
    (outerPetalAddress_isInheritanceChannel_iff_le_blockSize hm hb).1 hA
  exact outerPetalRemainder_eq_self_of_le_blockSize hm hle

/--
Channel `0` means the value descends unchanged to the next inner lap.
-/
theorem outerPetalAddress_channel_zero_remainder_eq_self
    {n lap m : Nat}
    (hm : 1 ≤ m)
    (hb : 0 < relPetalBlockSize n lap)
    (hch : (outerPetalAddress n lap m).channel = 0) :
    outerPetalRemainder n lap m = m := by
  exact outerPetalRemainder_eq_self_of_isInheritanceChannel hm hb hch

/--
For a valid one-based value, the remainder is a valid value for the previous
lap total.
-/
theorem outerPetalRemainder_le_prevTotal_of_valid
    {n lap m : Nat}
    (hlap : 0 < lap)
    (hm : 1 ≤ m)
    (hbound : m ≤ relPetalTotal n lap) :
    outerPetalRemainder n lap m ≤ relPetalTotal n (lap - 1) := by
  rcases Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hlap) with ⟨k, rfl⟩
  have hm_pos : 0 < m := hm
  have htotal :
      relPetalTotal n (k + 1) = relPetalTotal n k * lapBase n :=
    relPetalTotal_succ n k
  have htotal_pos : 0 < relPetalTotal n (k + 1) :=
    lt_of_lt_of_le hm_pos hbound
  have hb_prev : 0 < relPetalTotal n k := by
    by_contra hnot
    have hzero : relPetalTotal n k = 0 := Nat.eq_zero_of_not_pos hnot
    rw [htotal, hzero, zero_mul] at htotal_pos
    exact Nat.not_lt_zero _ htotal_pos
  simpa [relPetalBlockSize_succ] using
    (outerPetalRemainder_le_blockSize
      (n := n) (lap := k + 1) (m := m) (by simpa [relPetalBlockSize_succ] using hb_prev))

/--
One-step Petal address decomposition.

For one-based values, the address is the usual quotient/remainder
decomposition:

`m = channel * blockSize + remainder`.
-/
theorem outerPetalAddress_decompose
    {n lap m : Nat}
    (hm : 1 ≤ m) :
    m =
      (outerPetalAddress n lap m).channel * relPetalBlockSize n lap
        + outerPetalRemainder n lap m := by
  let B := relPetalBlockSize n lap
  have hdiv :
      (m - 1) % B + B * ((m - 1) / B) = m - 1 :=
    Nat.mod_add_div (m - 1) B
  rw [outerPetalRemainder, outerPetalAddress]
  change m = ((m - 1) / B) * B + ((m - 1) % B + 1)
  calc
    m = (m - 1) + 1 := by rw [Nat.sub_add_cancel hm]
    _ = ((m - 1) % B + B * ((m - 1) / B)) + 1 := by rw [hdiv]
    _ = B * ((m - 1) / B) + ((m - 1) % B + 1) := by
      omega
    _ = ((m - 1) / B) * B + ((m - 1) % B + 1) := by
      rw [Nat.mul_comm B ((m - 1) / B)]

/--
Zero-based form of the one-step Petal address decomposition.

This is the raw quotient/remainder decomposition behind the one-based address:

`m - 1 = channel * blockSize + (remainder - 1)`.
-/
theorem outerPetalAddress_decompose_sub_one
    {n lap m : Nat} :
    m - 1 =
      (outerPetalAddress n lap m).channel * relPetalBlockSize n lap
        + (outerPetalRemainder n lap m - 1) := by
  let B := relPetalBlockSize n lap
  have hdiv :
      (m - 1) % B + B * ((m - 1) / B) = m - 1 :=
    Nat.mod_add_div (m - 1) B
  have hrem : (((m - 1) % B + 1) - 1) = (m - 1) % B := by
    omega
  rw [outerPetalRemainder, outerPetalAddress]
  change m - 1 = ((m - 1) / B) * B + (((m - 1) % B + 1) - 1)
  rw [hrem]
  conv_lhs => rw [← hdiv]
  rw [Nat.mul_comm B ((m - 1) / B)]
  rw [Nat.add_comm ((m - 1) % B) (((m - 1) / B) * B)]

/-- In the pentagonal two-lap example, the outer remainder stays `25`. -/
theorem outerPetalRemainder_five_two_twentyfive :
    outerPetalRemainder 5 2 25 = 25 := by
  decide

/--
The pentagonal nested-address sample.

Reading `25` at lap `2` first descends unchanged through channel `0`; reading
that remainder at lap `1` lands in Petal channel `4` with offset `5`.
-/
theorem outerPetalAddress_five_inner_after_two_twentyfive :
    outerPetalAddress 5 1 (outerPetalRemainder 5 2 25) =
      { lap := 1, channel := 4, offset := 5 } := by
  decide

/-- A bounded channel is at most the base unit core. -/
theorem outerPetalAddress_channel_le_baseUnitCore
    {n lap m : Nat}
    (hlap : 0 < lap)
    (hm : 1 ≤ m)
    (hbound : m ≤ relPetalTotal n lap) :
    (outerPetalAddress n lap m).channel ≤ baseUnitCore n := by
  have hlt := outerPetalAddress_channel_lt_lapBase
    (n := n) (lap := lap) (m := m) hlap hm hbound
  rw [lapBase_eq_succ] at hlt
  simpa [baseUnitCore] using Nat.lt_succ_iff.mp hlt

end Petal
end DkMath
