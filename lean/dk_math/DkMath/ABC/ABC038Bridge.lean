/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/


import DkMath.ABC.ChernoffQualityBridge
import DkMath.ABC.ValuationFlowBridge

#print "file: DkMath.ABC.ABC038Bridge"

namespace DkMath.ABC

/--
Natural transport route for the `ABC038` bridge: if the target divides the
quality input product, then its radical is bounded by the radical of that
product.
-/
theorem rad_input_transport_of_target_dvd_mul
    {c u v : ℕ}
    (huv_ne : u * v ≠ 0)
    (hcdvd : c ∣ u * v) :
    ABC.rad c ≤ ABC.rad (u * v) := by
  have hrad_dvd : ABC.rad c ∣ ABC.rad (u * v) := by
    exact ABC.rad_dvd_of_dvd huv_ne hcdvd
  have hpos : 0 < ABC.rad (u * v) := by
    exact Finset.prod_pos fun p hp =>
      Nat.Prime.pos (ABC.mem_support_factorization_iff.mp hp).2.1
  exact Nat.le_of_dvd hpos hrad_dvd

/--
First land the counting spine in a target-rad tail budget.
-/
theorem targetRadTailBound_of_channelCount_tail
    {a b c d : ℕ} {γ : ℝ}
    (F : PrimitiveWitnessFamily a b d)
    (htarget : c = a ^ d - b ^ d)
    (hdiff_ne : a ^ d - b ^ d ≠ 0)
    (hγ_nonneg : 0 ≤ γ)
    (htail_count : (ABC.twoTail c : ℝ) ≤ ((2 ^ F.channelCount : ℕ) : ℝ) ^ γ) :
    (ABC.twoTail c : ℝ) ≤ (ABC.rad c : ℝ) ^ γ := by
  have hcount_le_nat : 2 ^ F.channelCount ≤ ABC.rad c := by
    exact F.primitive_witness_family_gives_abc_rad_target_lower_bound
      htarget
      hdiff_ne
  have hcount_le_real : (((2 ^ F.channelCount : ℕ) : ℝ)) ≤ (ABC.rad c : ℝ) := by
    exact_mod_cast hcount_le_nat
  have hbase_nonneg : 0 ≤ (((2 ^ F.channelCount : ℕ) : ℝ)) := by
    positivity
  have hpow_le :
      (((2 ^ F.channelCount : ℕ) : ℝ) ^ γ) ≤ (ABC.rad c : ℝ) ^ γ := by
    exact Real.rpow_le_rpow hbase_nonneg hcount_le_real hγ_nonneg
  exact le_trans htail_count hpow_le

/--
Transport a target-rad tail budget into the standard `ABC.TailBound` input
used by `ABC038`.
-/
theorem tailBound_of_targetRadTail_transport
    {u v c : ℕ} {γ : ℝ}
    (htransport : ABC.rad c ≤ ABC.rad (u * v))
    (hγ_nonneg : 0 ≤ γ)
    (htail_target : (ABC.twoTail c : ℝ) ≤ (ABC.rad c : ℝ) ^ γ) :
    ABC.TailBound γ u v c := by
  have htransport_real : ((ABC.rad c : ℕ) : ℝ) ≤ (ABC.rad (u * v) : ℝ) := by
    exact_mod_cast htransport
  have hbase_nonneg : 0 ≤ (ABC.rad c : ℝ) := by
    positivity
  have hpow_le : (ABC.rad c : ℝ) ^ γ ≤ (ABC.rad (u * v) : ℝ) ^ γ := by
    exact Real.rpow_le_rpow hbase_nonneg htransport_real hγ_nonneg
  exact le_trans htail_target hpow_le

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
  exact tailBound_of_targetRadTail_transport
    htransport
    hγ_nonneg
    (targetRadTailBound_of_channelCount_tail
      (F := F)
      htarget
      hdiff_ne
      hγ_nonneg
      htail_count)

/--
Divisibility-flavoured specialization of the previous bridge: `c ∣ u * v`
supplies the radical transport automatically.
-/
theorem tailBound_of_channelCount_tail_dvd
    {a b c d u v : ℕ} {γ : ℝ}
    (F : PrimitiveWitnessFamily a b d)
    (htarget : c = a ^ d - b ^ d)
    (huv_ne : u * v ≠ 0)
    (hcdvd : c ∣ u * v)
    (hdiff_ne : a ^ d - b ^ d ≠ 0)
    (hγ_nonneg : 0 ≤ γ)
    (htail_count : (ABC.twoTail c : ℝ) ≤ ((2 ^ F.channelCount : ℕ) : ℝ) ^ γ) :
    ABC.TailBound γ u v c := by
  exact tailBound_of_channelCount_tail_transport
    (F := F)
    htarget
    (rad_input_transport_of_target_dvd_mul huv_ne hcdvd)
    hdiff_ne
    hγ_nonneg
    htail_count

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

/--
Quality wrapper fed by a target-rad tail budget, before any transport to
`rad (u * v)` is chosen.
-/
theorem quality_le_of_not_bad_with_targetRadTail_transport
    {u v c : ℕ} {ε δ γ : ℝ}
    (htransport : ABC.rad c ≤ ABC.rad (u * v))
    (hγ_nonneg : 0 ≤ γ)
    (huv_sum : u + v = c)
    (huv_cop : Nat.Coprime u v)
    (hε_pos : 0 < ε)
    (h_not_bad : ¬ ABC.Bad δ (ABC.Triple.mk u v c huv_sum huv_cop))
    (htail_target : (ABC.twoTail c : ℝ) ≤ (ABC.rad c : ℝ) ^ γ)
    (hδγ_nonneg : 0 ≤ δ + γ)
    (hδγ_le : δ + γ ≤ ε) :
    ABC.quality (ABC.Triple.mk u v c huv_sum huv_cop) ≤ 1 + ε := by
  have htail : ABC.TailBound γ u v c :=
    tailBound_of_targetRadTail_transport
      htransport
      hγ_nonneg
      htail_target
  exact ABC.Chernoff.quality_le_of_not_bad_with_tail
    huv_sum
    huv_cop
    hε_pos
    h_not_bad
    htail
    hδγ_nonneg
    hδγ_le

/--
Combine the π-budget on `rad (a * b)` and the target-rad tail budget into a
single `rad (a * b * c)` growth bound on `c`.
-/
theorem radAbcBound_of_pi_targetRadTail
    {a b c : ℕ} {δ γ : ℝ}
    (hπ : (ABC.piSqRad c : ℝ) ≤ (ABC.rad (a * b) : ℝ) ^ δ)
    (htail_target : (ABC.twoTail c : ℝ) ≤ (ABC.rad c : ℝ) ^ γ)
    (habc_ne : a * b * c ≠ 0)
    (hδ_nonneg : 0 ≤ δ)
    (hγ_nonneg : 0 ≤ γ) :
    (c : ℝ) ≤ (ABC.rad (a * b * c) : ℝ) ^ (1 + δ + γ) := by
  by_cases hc : c = 0
  · subst hc
    simp
  have hdec := ABC.decomp_piRad_twoTail_real c hc
  have hπ_pos_left : 0 ≤ (ABC.piSqRad c : ℝ) := by
    exact le_of_lt (ABC.piSqRad_pos c)
  have hradc_pos_left : 0 ≤ (ABC.rad c : ℝ) := by
    exact le_of_lt (ABC.rad_pos_real c)
  have hmul_tail := mul_le_mul_of_nonneg_left htail_target hπ_pos_left
  have hmul := mul_le_mul_of_nonneg_right hmul_tail hradc_pos_left
  have h_tail_shape :
      (c : ℝ) ≤
        (ABC.piSqRad c : ℝ) * (ABC.rad c : ℝ) ^ γ * (ABC.rad c : ℝ) := by
    calc
      (c : ℝ)
        = (ABC.piSqRad c : ℝ) * (ABC.rad c : ℝ) * (ABC.twoTail c : ℝ) := hdec
      _ = (ABC.piSqRad c : ℝ) * (ABC.twoTail c : ℝ) * (ABC.rad c : ℝ) := by ring
      _ ≤ (ABC.piSqRad c : ℝ) * (ABC.rad c : ℝ) ^ γ * (ABC.rad c : ℝ) := hmul
  have hdiv_ab : a * b ∣ a * b * c := by
    refine ⟨c, ?_⟩
    ring
  have hdiv_c : c ∣ a * b * c := by
    refine ⟨a * b, ?_⟩
    ring
  have hradab_le : (ABC.rad (a * b) : ℝ) ≤ (ABC.rad (a * b * c) : ℝ) := by
    exact ABC.rad_le_of_dvd habc_ne hdiv_ab
  have hradc_le : (ABC.rad c : ℝ) ≤ (ABC.rad (a * b * c) : ℝ) := by
    exact ABC.rad_le_of_dvd habc_ne hdiv_c
  have hradab_nonneg : 0 ≤ (ABC.rad (a * b) : ℝ) := by positivity
  have hradc_nonneg : 0 ≤ (ABC.rad c : ℝ) := by positivity
  have hpow_ab :
      (ABC.rad (a * b) : ℝ) ^ δ ≤ (ABC.rad (a * b * c) : ℝ) ^ δ := by
    exact Real.rpow_le_rpow hradab_nonneg hradab_le hδ_nonneg
  have hpow_c :
      (ABC.rad c : ℝ) ^ γ ≤ (ABC.rad (a * b * c) : ℝ) ^ γ := by
    exact Real.rpow_le_rpow hradc_nonneg hradc_le hγ_nonneg
  have hradc_one :
      (ABC.rad c : ℝ) ≤ (ABC.rad (a * b * c) : ℝ) ^ (1 : ℝ) := by
    simpa using hradc_le
  have hpi_tail_bound :
      (ABC.piSqRad c : ℝ) * (ABC.rad c : ℝ) ^ γ * (ABC.rad c : ℝ)
        ≤ (ABC.rad (a * b * c) : ℝ) ^ δ *
            (ABC.rad (a * b * c) : ℝ) ^ γ *
            (ABC.rad (a * b * c) : ℝ) ^ (1 : ℝ) := by
    have hπ_abc :
        (ABC.piSqRad c : ℝ) ≤ (ABC.rad (a * b * c) : ℝ) ^ δ := by
      exact le_trans hπ hpow_ab
    have hmul_left :
        (ABC.piSqRad c : ℝ) * (ABC.rad c : ℝ) ^ γ
          ≤ (ABC.rad (a * b * c) : ℝ) ^ δ *
              (ABC.rad (a * b * c) : ℝ) ^ γ := by
      exact mul_le_mul hπ_abc hpow_c (by positivity) (by positivity)
    exact mul_le_mul hmul_left hradc_one (by positivity) (by positivity)
  calc
    (c : ℝ)
      ≤ (ABC.piSqRad c : ℝ) * (ABC.rad c : ℝ) ^ γ * (ABC.rad c : ℝ) := h_tail_shape
    _ ≤ (ABC.rad (a * b * c) : ℝ) ^ δ *
          (ABC.rad (a * b * c) : ℝ) ^ γ *
          (ABC.rad (a * b * c) : ℝ) ^ (1 : ℝ) := hpi_tail_bound
    _ = (ABC.rad (a * b * c) : ℝ) ^ (1 + δ + γ) := by
      rw [show (1 + δ + γ) = δ + γ + 1 by ring]
      rw [Real.rpow_add (ABC.rad_pos_real (a * b * c)),
        Real.rpow_add (ABC.rad_pos_real (a * b * c))]




#print axioms radAbcBound_of_pi_targetRadTail  -- OK: no-so#rry
-- 'DkMath.ABC.radAbcBound_of_pi_targetRadTail'
-- depends on axioms: [propext, Classical.choice, Quot.sound]




/--
Direct quality route from a target-rad tail budget, landing in the existing
`rad (a * b * c)` analytic bridge.
-/
theorem quality_le_of_pi_targetRadTail_of_radAbc
    {a b c : ℕ} {ε δ γ : ℝ}
    (hε_pos : 0 < ε)
    (hsum : a + b = c)
    (hcop : Nat.Coprime a b)
    (hπ : (ABC.piSqRad c : ℝ) ≤ (ABC.rad (a * b) : ℝ) ^ δ)
    (htail_target : (ABC.twoTail c : ℝ) ≤ (ABC.rad c : ℝ) ^ γ)
    (hδ_nonneg : 0 ≤ δ)
    (hγ_nonneg : 0 ≤ γ)
    (hδγ_le : δ + γ ≤ ε)
    (hrad_gt_one : 1 < (ABC.rad (a * b * c) : ℝ)) :
    ABC.quality (ABC.Triple.mk a b c hsum hcop) ≤ 1 + ε := by
  have hbound_dg :
      (c : ℝ) ≤ (ABC.rad (a * b * c) : ℝ) ^ (1 + δ + γ) := by
    have habc_ne : a * b * c ≠ 0 := by
      intro habc_eq_zero
      have : ABC.rad (a * b * c) = 1 := by
        rw [habc_eq_zero]
        simp
      rw [this] at hrad_gt_one
      norm_num at hrad_gt_one
    simpa [add_assoc, add_left_comm, add_comm] using
      radAbcBound_of_pi_targetRadTail
        (a := a) (b := b) (c := c)
        hπ
        htail_target
        habc_ne
        hδ_nonneg
        hγ_nonneg
  have hbase_ge_one : (1 : ℝ) ≤ (ABC.rad (a * b * c) : ℝ) := by
    exact ABC.one_le_rad_real (a * b * c)
  have hexp_le : 1 + δ + γ ≤ 1 + ε := by
    linarith
  have hpow_le :
      (ABC.rad (a * b * c) : ℝ) ^ (1 + δ + γ)
        ≤ (ABC.rad (a * b * c) : ℝ) ^ (1 + ε) := by
    exact Real.rpow_le_rpow_of_exponent_le hbase_ge_one hexp_le
  have hbound :
      (c : ℝ) ≤ (ABC.rad (a * b * c) : ℝ) ^ (1 + ε) := by
    exact le_trans hbound_dg hpow_le
  have hπ_prod :
      (ABC.piSqRad c : ℝ) ≤ (ABC.rad a * ABC.rad b : ℝ) ^ δ := by
    simpa [ABC.rad_mul_coprime' hcop, Nat.cast_mul] using hπ
  exact ABC.quality_le_of_sqprod_pow_bound_analytic_axiom_to_lemma
    ε
    δ
    hε_pos
    hcop
    hsum
    hπ_prod
    hrad_gt_one
    hbound

/--
Public wrapper from `¬Bad` plus a target-rad tail budget to the `rad (a*b*c)`
quality bridge. The only remaining external assumption is `rad (a*b*c) > 1`.
-/
theorem quality_le_of_not_bad_with_targetRadTail_on_radAbc
    {a b c : ℕ} {ε δ γ : ℝ}
    (hsum : a + b = c)
    (hcop : Nat.Coprime a b)
    (hε_pos : 0 < ε)
    (h_not_bad : ¬ ABC.Bad δ (ABC.Triple.mk a b c hsum hcop))
    (htail_target : (ABC.twoTail c : ℝ) ≤ (ABC.rad c : ℝ) ^ γ)
    (hδ_nonneg : 0 ≤ δ)
    (hγ_nonneg : 0 ≤ γ)
    (hδγ_le : δ + γ ≤ ε)
    (hrad_gt_one : 1 < (ABC.rad (a * b * c) : ℝ)) :
    ABC.quality (ABC.Triple.mk a b c hsum hcop) ≤ 1 + ε := by
  exact quality_le_of_pi_targetRadTail_of_radAbc
    hε_pos
    hsum
    hcop
    (ABC.piSqRad_le_of_not_bad hcop hsum h_not_bad)
    htail_target
    hδ_nonneg
    hγ_nonneg
    hδγ_le
    hrad_gt_one

namespace Chernoff

/--
`ABC038` の convenience theorem 群に合わせた `rad(abc)` 直結版。
`TailBound` の transport を経由せず、target-rad tail budget を直接受け取る。
-/
lemma quality_le_of_not_bad_with_targetRadTail_on_radAbc
    {a b c : ℕ} {ε δ γ : ℝ}
    (hsum : a + b = c)
    (hcop : Nat.Coprime a b)
    (hε_pos : 0 < ε)
    (h_not_bad : ¬ ABC.Bad δ (ABC.Triple.mk a b c hsum hcop))
    (htail_target : (ABC.twoTail c : ℝ) ≤ (ABC.rad c : ℝ) ^ γ)
    (hδ_nonneg : 0 ≤ δ)
    (hγ_nonneg : 0 ≤ γ)
    (hδγ_le : δ + γ ≤ ε)
    (hrad_gt_one : 1 < (ABC.rad (a * b * c) : ℝ)) :
    ABC.quality (ABC.Triple.mk a b c hsum hcop) ≤ 1 + ε := by
  exact DkMath.ABC.quality_le_of_not_bad_with_targetRadTail_on_radAbc
    hsum
    hcop
    hε_pos
    h_not_bad
    htail_target
    hδ_nonneg
    hγ_nonneg
    hδγ_le
    hrad_gt_one

/--
`channelCount` budget をそのまま `ABC038` convenience theorem 風の入口へ流す版。
`rad(c)` tail budget への landing は内部で行う。
-/
lemma quality_le_of_not_bad_with_channelCount_tail_on_radAbc
    {a b c d u v : ℕ} {ε δ γ : ℝ}
    (F : PrimitiveWitnessFamily a b d)
    (htarget : c = a ^ d - b ^ d)
    (hdiff_ne : a ^ d - b ^ d ≠ 0)
    (hγ_nonneg : 0 ≤ γ)
    (huv_sum : u + v = c)
    (huv_cop : Nat.Coprime u v)
    (hε_pos : 0 < ε)
    (h_not_bad : ¬ ABC.Bad δ (ABC.Triple.mk u v c huv_sum huv_cop))
    (htail_count : (ABC.twoTail c : ℝ) ≤ ((2 ^ F.channelCount : ℕ) : ℝ) ^ γ)
    (hδ_nonneg : 0 ≤ δ)
    (hδγ_le : δ + γ ≤ ε)
    (hrad_gt_one : 1 < (ABC.rad (u * v * c) : ℝ)) :
    ABC.quality (ABC.Triple.mk u v c huv_sum huv_cop) ≤ 1 + ε := by
  have htail_target : (ABC.twoTail c : ℝ) ≤ (ABC.rad c : ℝ) ^ γ :=
    DkMath.ABC.targetRadTailBound_of_channelCount_tail
      (F := F)
      htarget
      hdiff_ne
      hγ_nonneg
      htail_count
  exact quality_le_of_not_bad_with_targetRadTail_on_radAbc
    huv_sum
    huv_cop
    hε_pos
    h_not_bad
    htail_target
    hδ_nonneg
    hγ_nonneg
    hδγ_le
    hrad_gt_one

end Chernoff

/--
Divisibility-flavoured quality wrapper. This is the lightest route when
`c ∣ u * v` is easier to prove than a standalone radical transport inequality.
-/
theorem quality_le_of_not_bad_with_channelCount_tail_dvd
    {a b c d u v : ℕ} {ε δ γ : ℝ}
    (F : PrimitiveWitnessFamily a b d)
    (htarget : c = a ^ d - b ^ d)
    (huv_ne : u * v ≠ 0)
    (hcdvd : c ∣ u * v)
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
  exact quality_le_of_not_bad_with_channelCount_tail_transport
    (F := F)
    htarget
    (rad_input_transport_of_target_dvd_mul huv_ne hcdvd)
    hdiff_ne
    hγ_nonneg
    huv_sum
    huv_cop
    hε_pos
    h_not_bad
    htail_count
    hδγ_nonneg
    hδγ_le

end DkMath.ABC
