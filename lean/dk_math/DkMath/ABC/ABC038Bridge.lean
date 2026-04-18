/- 
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.ABC.ABC038
import DkMath.ABC.ValuationFlowBridge

#print "file: DkMath.ABC.ABC038Bridge"

namespace DkMath.ABC

/--
Transport a tail bound phrased against `2 ^ channelCount` into the standard
`ABC.TailBound` input used by `ABC038`.
-/
theorem tailBound_of_channelCount_tail_transport
    {a b c d u v : ℕ} {γ : ℝ}
    (F : PrimitiveWitnessFamily a b d)
    (htarget : c = a ^ d - b ^ d)
    (htransport : ABC.rad c ≤ ABC.rad (u * v))
    (hdiff_ne : a ^ d - b ^ d ≠ 0)
    (hγ_nonneg : 0 ≤ γ)
    (htail_count : (ABC.twoTail c : ℝ) ≤ ((2 ^ F.channelCount : ℕ) : ℝ) ^ γ) :
    ABC.TailBound γ u v c := by
  have hcount_le_nat : 2 ^ F.channelCount ≤ ABC.rad (u * v) := by
    exact F.primitive_channel_count_forces_rad_input_lower_bound htarget htransport hdiff_ne
  have hcount_le_real : (((2 ^ F.channelCount : ℕ) : ℝ)) ≤ (ABC.rad (u * v) : ℝ) := by
    exact_mod_cast hcount_le_nat
  have hbase_nonneg : 0 ≤ (((2 ^ F.channelCount : ℕ) : ℝ)) := by
    positivity
  have hpow_le :
      (((2 ^ F.channelCount : ℕ) : ℝ) ^ γ) ≤ (ABC.rad (u * v) : ℝ) ^ γ := by
    exact Real.rpow_le_rpow hbase_nonneg hcount_le_real hγ_nonneg
  exact le_trans htail_count hpow_le

/--
Thin wrapper from a channel-count tail budget to the existing `ABC038`
quality bridge. The radical transport into `rad (u * v)` stays explicit.
-/
theorem quality_le_of_not_bad_with_channelCount_tail_transport
    {a b c d u v : ℕ} {ε δ γ : ℝ}
    (F : PrimitiveWitnessFamily a b d)
    (htarget : c = a ^ d - b ^ d)
    (htransport : ABC.rad c ≤ ABC.rad (u * v))
    (hdiff_ne : a ^ d - b ^ d ≠ 0)
    (hγ_nonneg : 0 ≤ γ)
    (huv_sum : u + v = c)
    (huv_cop : Nat.Coprime u v)
    (hε_pos : 0 < ε)
    (h_not_bad : ¬ ABC.Bad δ (ABC.Triple.mk u v c huv_sum huv_cop))
    (htail_count : (ABC.twoTail c : ℝ) ≤ ((2 ^ F.channelCount : ℕ) : ℝ) ^ γ)
    (hδγ_nonneg : 0 ≤ δ + γ)
    (hδγ_le : δ + γ ≤ ε) :
    ABC.quality (ABC.Triple.mk u v c huv_sum huv_cop) ≤ 1 + ε := by
  have htail : ABC.TailBound γ u v c :=
    tailBound_of_channelCount_tail_transport
      (F := F)
      htarget
      htransport
      hdiff_ne
      hγ_nonneg
      htail_count
  exact ABC.Chernoff.quality_le_of_not_bad_with_tail
    huv_sum
    huv_cop
    hε_pos
    h_not_bad
    htail
    hδγ_nonneg
    hδγ_le

end DkMath.ABC
