/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Collatz.PetalBridge.Counts

#print "file: DkMath.Collatz.PetalBridge.Ratios"

namespace DkMath.Collatz


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


end DkMath.Collatz
