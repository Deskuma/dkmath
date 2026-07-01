# Collatz Petal Bridge Status

This note records the current contact point between the accelerated Collatz
formalization and the Petal range-family route.

## Current Collatz Surface

Implemented Collatz modules already provide:

```text
DkMath.Collatz.Basic
  C
  OddNat
  threeNPlusOne

DkMath.Collatz.V2
  v2
  v2_3n_plus_1_ge_1
  v2_shift_invariant support lemmas

DkMath.Collatz.Accelerated
  s n = v2 (3n + 1)
  T n = (3n + 1) / 2^(v2 (3n + 1))
  iterateT
  sumS
  driftReal

DkMath.Collatz.Shift
  shift
  v2_shift_invariant
```

This means the implemented Collatz side is currently strongest around:

```text
odd state
2-adic height
2-adic residue class
accelerated transition
orbit segment
block-shift invariance
```

## Petal Contact Point

`DkMath.Petal.RangeFamily` recently introduced a range-indexed observation
layer:

```text
I = Finset.range k
mOf i = i + 1
qOf i = selected label at index i
```

It now has both sides of the test:

```text
pairwise label separation
  -> Set.InjOn qOf ↑(Finset.range k)

same label at two distinct in-range indices
  -> False
```

This is a natural match for Collatz orbit segments.

## New Window

The bridge file is:

```text
DkMath.Collatz.PetalBridge
```

It defines:

```lean
OrbitWindow
rawHeightLabel
oddOrbitLabel
orbitWindowHeight
orbitWindowHeightSeq
OddOrbitLabelsPairwiseSeparated
OrbitWindowSeparated
OrbitWindowCollision
```

where:

```text
OrbitWindow n k = Finset.range k
oddOrbitLabel n i = the natural value of iterateT i n
orbitWindowHeight n i = v2 (3 * oddOrbitLabel n i + 1)
orbitWindowHeightSeq n k = the ordered list of the first k height labels
```

The first theorem set is deliberately thin:

```lean
orbitWindow_eq_range
rawHeightLabel_eq_s
orbitWindowHeight_eq_s_iterateT
two_le_v2_iff_four_dvd
rawHeightLabel_two_le_iff_four_dvd_threeNPlusOne
orbitWindowHeight_two_le_iff_four_dvd
odd_four_dvd_three_mul_add_one_iff_mod_four_eq_one
orbitWindowHeight_two_le_iff_mod_four_eq_one
odd_mod_four_eq_one_or_three
odd_mod_eight_eq_one_or_three_or_five_or_seven
three_le_v2_iff_eight_dvd
four_le_v2_iff_sixteen_dvd
rawHeightLabel_three_le_iff_eight_dvd_threeNPlusOne
rawHeightLabel_four_le_iff_sixteen_dvd_threeNPlusOne
odd_eight_dvd_three_mul_add_one_iff_mod_eight_eq_five
odd_sixteen_dvd_three_mul_add_one_iff_mod_sixteen_eq_five
orbitWindowHeight_three_le_iff_mod_eight_eq_five
orbitWindowHeight_four_le_iff_mod_sixteen_eq_five
next_mod_four_of_mod_eight_eq_three
next_mod_four_of_mod_eight_eq_seven
T_val_eq_three_mul_add_one_div_two_of_s_eq_one
orbitWindowHeightSeq_length
orbitWindowHeightSeq_sum_eq_sumS
orbitWindowHeightSeq_sum_ge_of_forall_ge
orbitWindowHeightSeq_take_sum_eq_sumS
orbitWindowHeightSeq_take_length
orbitWindowHeightSeq_get?_eq_some
orbitWindowHeightSeq_take_get?_eq_some
orbitWindowHeightSeq_prefix_sum_ge_of_forall_ge
orbitWindowHeight_eq_of_oddOrbitLabel_eq
orbitWindowHeight_eq_of_collision
orbitWindowHeight_eq_of_same_iterateT
orbitWindowHeightCountEq
orbitWindowHeightCountGe
orbitWindowHeightCountGeTail
orbitWindowHeightCountEqTail
orbitWindowResidueCountMod4EqOne
orbitWindowResidueCountMod4EqThree
orbitWindowResidueCountMod8EqOne
orbitWindowResidueCountMod8EqThree
orbitWindowResidueCountMod8EqFive
orbitWindowResidueCountMod8EqSeven
orbitWindowResidueCountPow2
orbitWindowResidueCountMod4EqOneTail
orbitWindowResidueCountMod4EqThreeTail
orbitWindowResidueCountPow2Tail
orbitWindowPrefixResidueCountMod4EqOne
orbitWindowHeightCountEq_le_window
orbitWindowHeightCountGe_le_window
orbitWindowHeightCountGeTail_le_window
orbitWindowHeightCountEqTail_le_window
orbitWindowHeightCountGe_succ
orbitWindowHeightCountGeTail_succ
orbitWindowHeightCountEqTail_succ
orbitWindowResidueCountMod4EqOne_le_window
orbitWindowResidueCountMod4EqThree_le_window
orbitWindowResidueCountMod8EqOne_le_window
orbitWindowResidueCountMod8EqThree_le_window
orbitWindowResidueCountMod8EqFive_le_window
orbitWindowResidueCountMod8EqSeven_le_window
orbitWindowResidueCountPow2_le_window
orbitWindowResidueCountMod4EqOneTail_le_window
orbitWindowResidueCountMod4EqThreeTail_le_window
orbitWindowResidueCountPow2Tail_le_window
orbitWindowResidueCountMod8EqSeven_eq_pow2
orbitWindowResidueCountPow2_succ
orbitWindowResidueCountPow2Tail_succ
orbitWindowResidueCountPow2_depth_zero_eq_window
orbitWindowResidueCountPow2_eq_zero_of_modulus_le_residue
pow2_residue_indicator_sum_eq_one
orbitWindowResidueCountPow2_sum_eq_window
orbitWindowResidueCountPow2Tail_sum_eq_window
orbitWindowResidueCountPow2_le_tail_of_pointwise
orbitWindowResidueCountPow2_depth_three_sum_eq_window
orbitWindowResidueCountPow2Tail_depth_three_sum_eq_window
sourcePow2Distribution_total
tailPow2Distribution_total
pow2ChannelFlow_of_pointwise
AtMostHalf
AtMostRatioNat
MoreThanHalf
atMostHalf_of_count_le_half
atMostHalf_or_moreThanHalf
atMostRatioNat_refl
atMostHalf_iff_atMostRatioNat_one_two
atMostRatioNat_one_one_of_le
orbitWindowRetentionMassPow2
orbitWindowRetentionMassPow2Tail
orbitWindowRecoverySiblingMassPow2
orbitWindowContinuationSiblingMassPow2
orbitWindowRecoverySiblingMassPow2Tail
orbitWindowContinuationSiblingMassPow2Tail
orbitWindowRetentionMassPow2_le_window
orbitWindowRetentionMassPow2Tail_le_window
orbitWindowRecoverySiblingMassPow2_le_window
orbitWindowContinuationSiblingMassPow2_le_window
orbitWindowRecoverySiblingMassPow2Tail_le_window
orbitWindowContinuationSiblingMassPow2Tail_le_window
twoAdicRetentionResidue_lt_pow
mod_pow2_succ_eq_left_or_right_of_mod_pow2_eq
mod_pow2_eq_of_mod_pow2_succ_eq_left_or_right
pow2ResidueIndicator_refine_succ
orbitWindowResidueCountPow2_refine_succ
orbitWindowRetentionMass_split
orbitWindowRecoverySiblingMassPow2_le_retentionMass
orbitWindowContinuationSiblingMassPow2_le_retentionMass
orbitWindowResidueCountPow2Tail_refine_succ
orbitWindowRetentionMassPow2Tail_split
orbitWindowRecoverySiblingMassPow2Tail_le_retentionMassTail
orbitWindowContinuationSiblingMassPow2Tail_le_retentionMassTail
atMostHalf_continuation_of_continuation_le_recovery
atMostHalf_tailContinuation_of_tailContinuation_le_tailRecovery
atMostHalf_continuation_of_retention_le_two_recovery
atMostHalf_tailContinuation_of_tailRetention_le_two_tailRecovery
continuation_atMostRatio_one_one_retention
tailContinuation_atMostRatio_one_one_retention
recovery_atMostRatio_one_one_retention
tailRecovery_atMostRatio_one_one_retention
RecoveryDominatesContinuation
TailRecoveryDominatesContinuation
RecoveryCoversHalfRetention
TailRecoveryCoversHalfRetention
RecoveryDominatesOnRange
TailRecoveryDominatesOnRange
ContinuationOutrunsRecovery
TailContinuationOutrunsRecovery
ContinuationOutrunsRecoveryOnRange
TailContinuationOutrunsRecoveryOnRange
recoveryDominates_or_continuationOutruns
tailRecoveryDominates_or_tailContinuationOutruns
not_recoveryDominates_of_continuationOutruns
not_tailRecoveryDominates_of_tailContinuationOutruns
continuationOutrunsRecovery_of_onRange
tailContinuationOutrunsRecovery_of_onRange
moreThanHalf_continuation_of_continuationOutruns
moreThanHalf_tailContinuation_of_tailContinuationOutruns
moreThanHalf_continuation_of_outRunsOnRange
moreThanHalf_tailContinuation_of_outRunsOnRange
MoreThanHalfOnRange
SourceContinuationPressureOnRange
TailContinuationPressureOnRange
sourceContinuationPressure_of_outRunsOnRange
tailContinuationPressure_of_outRunsOnRange
moreThanHalf_of_sourceContinuationPressure
moreThanHalf_of_tailContinuationPressure
sourceContinuationPressureDepthCount
tailContinuationPressureDepthCount
sourceContinuationControlledDepthCount
tailContinuationControlledDepthCount
sourceContinuationPressureDepthCount_le_len
tailContinuationPressureDepthCount_le_len
sourceContinuationControlledDepthCount_le_len
tailContinuationControlledDepthCount_le_len
sourceContinuationControlledDepthCount_add_pressureDepthCount_eq_len
tailContinuationControlledDepthCount_add_pressureDepthCount_eq_len
SourcePressureAtMostHalfOnDepthRange
SourcePressureMoreThanHalfOnDepthRange
TailPressureAtMostHalfOnDepthRange
TailPressureMoreThanHalfOnDepthRange
sourcePressureAtMostHalf_or_moreThanHalfOnDepthRange
tailPressureAtMostHalf_or_moreThanHalfOnDepthRange
sourcePressureDepthCount_le_controlled_of_atMostHalf
sourcePressureAtMostHalf_of_pressureDepthCount_le_controlled
tailPressureDepthCount_le_controlled_of_atMostHalf
tailPressureAtMostHalf_of_pressureDepthCount_le_controlled
sourceControlledDepthCount_lt_pressure_of_pressureMoreThanHalf
sourcePressureMoreThanHalf_of_controlledDepthCount_lt_pressure
tailControlledDepthCount_lt_pressure_of_pressureMoreThanHalf
tailPressureMoreThanHalf_of_controlledDepthCount_lt_pressure
continuationOutruns_of_moreThanHalf_continuation
tailContinuationOutruns_of_moreThanHalf_tailContinuation
sourceContinuationOutrunsDepthCount
tailContinuationOutrunsDepthCount
continuationOutruns_iff_moreThanHalf_continuation
tailContinuationOutruns_iff_moreThanHalf_tailContinuation
sourceContinuationOutrunsDepthCount_eq_pressureDepthCount
tailContinuationOutrunsDepthCount_eq_pressureDepthCount
recoveryDominates_of_atMostHalf_continuation
tailRecoveryDominates_of_atMostHalf_tailContinuation
sourceRecoveryDominanceDepthCount
tailRecoveryDominanceDepthCount
recoveryDominates_iff_atMostHalf_continuation
tailRecoveryDominates_iff_atMostHalf_tailContinuation
sourceRecoveryDominanceDepthCount_eq_controlledDepthCount
tailRecoveryDominanceDepthCount_eq_controlledDepthCount
sourceCauseSideDepthCount_add_eq_len
tailCauseSideDepthCount_add_eq_len
SourceOutrunsAtMostHalfOnDepthRange
SourceOutrunsMoreThanHalfOnDepthRange
TailOutrunsAtMostHalfOnDepthRange
TailOutrunsMoreThanHalfOnDepthRange
sourceOutrunsAtMostHalf_or_moreThanHalfOnDepthRange
tailOutrunsAtMostHalf_or_moreThanHalfOnDepthRange
sourceOutrunsAtMostHalf_iff_pressureAtMostHalf
sourceOutrunsMoreThanHalf_iff_pressureMoreThanHalf
tailOutrunsAtMostHalf_iff_pressureAtMostHalf
tailOutrunsMoreThanHalf_iff_pressureMoreThanHalf
sourceDominanceDepthCount_lt_outruns_of_outrunsMoreThanHalf
tailDominanceDepthCount_lt_outruns_of_outrunsMoreThanHalf
sourcePressureMoreThanHalf_of_outrunsMoreThanHalf
tailPressureMoreThanHalf_of_outrunsMoreThanHalf
sourceControlledDepthCount_lt_pressure_of_outrunsMoreThanHalf
tailControlledDepthCount_lt_pressure_of_outrunsMoreThanHalf
sourcePressureDepthCount_pos_of_outrunsMoreThanHalf
tailPressureDepthCount_pos_of_outrunsMoreThanHalf
sourceDominanceDepthCount_pos_of_outrunsAtMostHalf_and_not_all_outruns
tailDominanceDepthCount_pos_of_outrunsAtMostHalf_and_not_all_outruns
tailRetentionMass_depth_two_eq_heightCountEq_one
tailRetentionMass_depth_two_le_heightCountEq_one
sourceContinuationMass_le_tailRetentionMass
sourceContinuationMass_le_tailSplitMass
sourceContinuationMass_depth_two_le_tailHeightCountEq_one
sourceContinuationPressureDepthCount_eq_len_of_pressureOnRange
tailContinuationPressureDepthCount_eq_len_of_pressureOnRange
atMostHalf_continuation_of_recoveryDominates
atMostHalf_tailContinuation_of_tailRecoveryDominates
atMostHalf_continuation_of_recoveryCoversHalf
atMostHalf_tailContinuation_of_tailRecoveryCoversHalf
atMostHalf_continuation_of_recoveryDominatesOnRange
atMostHalf_tailContinuation_of_tailRecoveryDominatesOnRange
orbitWindowPrefixResidueCountMod4EqOne_le_prefix
orbitWindowPrefixResidueCountMod4EqOne_eq_residueCount
orbitWindowHeightCountGe_two_eq_residueCount_mod4_eq_one
orbitWindowHeightCountGeTail_two_eq_tailResidueCount_mod4_eq_one
orbitWindowHeightCountGe_three_eq_residueCount_mod8_eq_five
orbitWindowHeightCountEq_eq_window_of_forall_eq
orbitWindowHeightCountGe_eq_window_of_forall_ge
orbitWindowHeightSeq_sum_ge_countGe_mul_threshold
orbitWindowHeightCountEq_le_countGe
orbitWindowHeightSeq_sum_ge_countEq_mul_height
orbitWindowHeightPrefixCountGe
orbitWindowHeightPrefixCountGe_eq_countGe
orbitWindowHeightPrefixCountGe_mul_le_sumS
orbitWindowHeightSeq_sum_ge_countGe_one_add_countGe_two
orbitWindowHeight_one_le
orbitWindowHeightCountGe_one_eq_window
orbitWindowHeightSeq_sum_ge_window_add_countGe_two
orbitWindowHeight_eq_two_iff_mod_eight_eq_one
orbitWindowHeight_eq_one_iff_mod_four_eq_three
orbitWindowHeightCountEqTail_one_eq_tailResidueCount_mod4_eq_three
orbitWindowHeightTail_countGe_two_add_countEq_one_eq_window
orbitWindowHeight_eq_one_iff_mod_eight_eq_three_or_seven
orbitNext_mod_four_eq_one_of_mod_eight_eq_three
orbitNext_mod_four_eq_three_of_mod_eight_eq_seven
next_mod_eight_of_mod_sixteen_eq_seven
next_mod_eight_of_mod_sixteen_eq_fifteen
next_mod_sixteen_of_mod_thirtytwo_eq_fifteen
next_mod_sixteen_of_mod_thirtytwo_eq_thirtyone
next_mod_thirtytwo_of_mod_sixtyfour_eq_thirtyone
next_mod_thirtytwo_of_mod_sixtyfour_eq_sixtythree
next_mod_sixtyfour_of_mod_onehundredtwentyeight_eq_sixtythree
next_mod_sixtyfour_of_mod_onehundredtwentyeight_eq_onehundredtwentyseven
next_mod_onehundredtwentyeight_of_mod_twohundredfiftysix_eq_onehundredtwentyseven
next_mod_onehundredtwentyeight_of_mod_twohundredfiftysix_eq_twohundredfiftyfive
next_mod_twohundredfiftysix_of_mod_fivehundredtwelve_eq_twohundredfiftyfive
next_mod_twohundredfiftysix_of_mod_fivehundredtwelve_eq_fivehundredeleven
twoAdicRetentionResidue
twoAdicRecoverySiblingResidue
twoAdicContinuationSiblingResidue
twoAdicRecoverySiblingResidue_eq_retentionResidue
twoAdicContinuationSiblingResidue_eq_retentionResidue_succ
next_recovery_residue_expanded
next_continuation_residue_expanded
next_recovery_residue_of_mod
next_continuation_residue_of_mod
next_mod_twohundredfiftysix_of_mod_fivehundredtwelve_eq_twohundredfiftyfive_via_general
next_mod_twohundredfiftysix_of_mod_fivehundredtwelve_eq_fivehundredeleven_via_general
recovery_residue_mod_eight_eq_seven
continuation_residue_mod_eight_eq_seven
mod_eq_mod_of_dvd_modulus
mod_eight_eq_seven_of_recovery_residue_of_two_le
mod_eight_eq_seven_of_continuation_residue_of_one_le
iterateT_succ_eq_T_iterateT
oddOrbitLabel_succ_eq_T_iterateT
oddOrbitLabel_succ_mod_four_eq_one_of_mod_eight_eq_three
oddOrbitLabel_succ_mod_four_eq_three_of_mod_eight_eq_seven
oddOrbitLabel_succ_mod_eight_eq_three_of_mod_sixteen_eq_seven
oddOrbitLabel_succ_mod_eight_eq_seven_of_mod_sixteen_eq_fifteen
oddOrbitLabel_succ_mod_sixteen_eq_seven_of_mod_thirtytwo_eq_fifteen
oddOrbitLabel_succ_mod_sixteen_eq_fifteen_of_mod_thirtytwo_eq_thirtyone
oddOrbitLabel_succ_mod_thirtytwo_eq_fifteen_of_mod_sixtyfour_eq_thirtyone
oddOrbitLabel_succ_mod_thirtytwo_eq_thirtyone_of_mod_sixtyfour_eq_sixtythree
oddOrbitLabel_succ_recovery_residue_of_mod
oddOrbitLabel_succ_continuation_residue_of_mod
orbitWindowNextHeight_two_le_of_mod_eight_eq_three
orbitWindowNextHeight_eq_one_of_mod_eight_eq_seven
orbitWindowNextNextHeight_two_le_of_mod_sixteen_eq_seven
orbitWindowNextNextNextHeight_two_le_of_mod_thirtytwo_eq_fifteen
orbitWindowNextNextNextNextHeight_two_le_of_mod_sixtyfour_eq_thirtyone
orbitWindowResidueCountMod8EqThree_le_tailMod4EqOne
orbitWindowResidueCountMod8EqThree_le_tailHeightCountGe_two
residueCountMod8EqSeven_le_nextResidueCountMod4EqThree
orbitWindowRecoverySiblingCount_le_tailRetentionResidueCount
orbitWindowContinuationSiblingCount_le_tailRetentionResidueCount
orbitWindowRecoverySiblingCount_le_tailRetentionResidueCount_via_helper
orbitWindowContinuationSiblingCount_le_tailRetentionResidueCount_via_helper
orbitWindowRecoverySiblingMass_succ_le_tailRecoverySiblingMass
orbitWindowRecoveryMass_forces_tailRecovery
orbitWindowContinuationSiblingMass_succ_le_tailRetentionMass
orbitWindowContinuationMass_forces_tailRetention
orbitWindowContinuationMass_le_tailRecovery_add_tailContinuation
orbitWindowContinuationMass_tailBudget
orbitWindowContinuationSiblingMassPow2Tail_eq_retentionMassTail_succ
orbitWindowResidueCountMod8EqSeven_le_tailHeightCountEq_one
orbitWindowResidueCountMod8EqThree_add_seven_le_tail_partition
orbitWindowHeightCountGeTail_le_countGe_succ
sumS_two_steps_ge_three_of_mod_eight_eq_three
sumS_two_steps_ge_three_of_mod_eight_eq_three_at
sumS_two_steps_eq_two_of_mod_eight_eq_seven_and_next_mod_eight_eq_seven
sumS_three_steps_ge_four_of_mod_sixteen_eq_seven
sumS_four_steps_ge_five_of_mod_thirtytwo_eq_fifteen
sumS_five_steps_ge_six_of_mod_sixtyfour_eq_thirtyone
orbitWindowHeightCountEq_one_eq_residueCount_mod4_eq_three
orbitWindowHeightCountEq_two_eq_residueCount_mod8_eq_one
orbitWindowResidueCountMod4EqOne_add_eqThree_eq_window
orbitWindowResidueCountMod8_partition_eq_window
orbitWindowResidueCountMod8EqThree_add_seven_le_window
orbitWindowHeightPrefixCountGe_one_eq
orbitWindowHeightPrefixCountGe_two_eq_prefixResidueCount_mod4_eq_one
orbitWindowHeightPrefix_sum_ge_window_add_countGe_two
orbitWindowHeightCountGe_antitone
orbitWindowHeightSeq_sum_ge_countGe_one_add_countGe_two_add_countGe_three
orbitWindowHeightSeq_sum_ge_sum_countGe_range
orbitWindowHeightSeq_sum_ge_countGe_one_add_countGe_two_add_countGe_three_add_countGe_four
orbitWindowHeightPrefix_sum_ge_sum_countGe_range
orbitWindowHeightSeq_sum_ge_window_add_sum_countGe_tail
orbitWindowHeightPrefix_sum_ge_window_add_sum_countGe_tail
orbitWindowHeightSeq_sum_ge_window_add_of_countGe_two_ge
orbitWindowHeightSeq_sum_ge_succ_window_add_tailCountGe_two
orbitWindowHeightSeq_sum_ge_window_add_tailCountGe_two
orbitWindowResidueCountMod8EqThree_delayed_drift
orbitWindowResidueCountMod8EqThree_delayed_drift_strong
orbitWindowHeightSeq_sum_ge_window_add_of_residue_mod4_count_ge
orbitWindowHeightSeq_sum_ge_window_add_countGe_two_add_of_residue_mod8_count_ge
orbitWindowHeightPrefix_sum_ge_window_add_of_countGe_two_ge
orbitWindowHeightPrefix_sum_ge_window_add_of_residue_mod4_count_ge
rawHeightLabel_shift_eq
oddOrbitLabel_injOn_of_pairwiseSeparated
iterateT_eq_of_oddOrbitLabel_eq
oddOrbitLabelsPairwiseSeparated_contradiction_of_same_label_ne_index
same_iterateT_of_oddOrbitLabel_collision
exists_same_iterateT_of_orbitWindowCollision
not_orbitWindowCollision_of_separated
orbitWindowSeparated_contradiction_of_collision
orbitWindowSeparated_or_collision
```

## Interpretation

For Petal / ABC:

```text
pairwise separated orbit labels
  -> independent range-family labels are available

duplicate label
  -> the independent range-family route closes as False
```

For Collatz dynamics:

```text
duplicate label
  -> same accelerated odd state
  -> merge / fold / cycle candidate
```

So the same event has two readings:

```text
Petal route:
  obstruction to independent counting

Collatz route:
  dynamical collision signal
```

## Does This Change the Current Petal Situation?

Not yet at the level of `supportMass` or `rad` lower bounds.

The new bridge does not prove that Collatz orbit labels are prime labels,
primitive carriers, or Zsigmondy witnesses.  Therefore it does not immediately
feed the `2^k <= supportMass/rad(GN)` endpoint.

What it changes is the diagnostic layer:

```text
Collatz orbit segment
  -> Petal range-label separation test
  -> either separated segment or collision obstruction
```

The current window-level split is:

```text
OrbitWindowSeparated n k
or
OrbitWindowCollision n k
```

This is only a finite observation split.  It does not prove that a Collatz
orbit converges or cycles; it merely fixes the two observation modes available
inside a chosen finite window.

The first address-like observation is now the 2-adic height:

```text
rawHeightLabel n = v2 (3n + 1)
orbitWindowHeight n i = rawHeightLabel (oddOrbitLabel n i)
```

The first residue-address observation is now fixed as well:

```text
height >= 2
  <-> 4 | (3m + 1)
  <-> m % 4 = 1          for odd m

orbitWindowHeight n i >= 2
  <-> oddOrbitLabel n i % 4 = 1
```

Thus the second Collatz height layer has a residue-count reading:

```text
orbitWindowHeightCountGe n k 2
  = orbitWindowResidueCountMod4EqOne n k

m <= orbitWindowResidueCountMod4EqOne n k
  -> k + m <= sumS n k
```

This is the first direct route from a Petal-style residue/address occupation
statement to the Collatz drift input.  The next pointwise residue experiment
also passed:

```text
orbitWindowHeight n i >= 3
  <-> oddOrbitLabel n i % 8 = 5
```

The ordered height profile is now explicitly connected to the existing
Collatz accumulated-height API:

```text
(orbitWindowHeightSeq n k).sum = sumS n k
```

This means the Petal observation window can read the same data in two ways:

```text
ordered local profile:
  [height at time 0, height at time 1, ...]

accumulated drift input:
  sumS n k
```

The profile form is useful for address/window diagnostics, while `sumS` is the
existing Collatz side used by drift and growth estimates.

The next small API layer records how to use the profile:

```text
all heights >= threshold
  -> k * threshold <= sumS n k

take r from a k-window, with r <= k
  -> prefix sum = sumS n r

read index i in a k-window, with i < k
  -> the list entry is orbitWindowHeight n i

same orbit label at i and j
  -> same height at i and j
```

This gives the window a usable sequence interface:

```text
local entries
  -> prefix sums
  -> threshold lower bounds
  -> collision/fold height equality
```

The bridge now also has the first occupation-count vocabulary:

```text
orbitWindowHeightCountEq n k h
  = number of entries with height exactly h

orbitWindowHeightCountGe n k threshold
  = number of entries with height at least threshold

orbitWindowHeightCountGeTail n k threshold
  = number of shifted tail entries, at times i + 1 for i < k,
    whose height is at least threshold

orbitWindowHeightCountEqTail n k h
  = number of shifted tail entries, at times i + 1 for i < k,
    whose height is exactly h

orbitWindowResidueCountMod4EqOne n k
  = number of odd orbit labels congruent to 1 modulo 4

orbitWindowResidueCountMod4EqThree n k
  = number of odd orbit labels congruent to 3 modulo 4

orbitWindowResidueCountMod8EqOne n k
  = number of odd orbit labels congruent to 1 modulo 8

orbitWindowResidueCountMod8EqThree n k
  = number of odd orbit labels congruent to 3 modulo 8

orbitWindowResidueCountMod8EqFive n k
  = number of odd orbit labels congruent to 5 modulo 8

orbitWindowResidueCountMod8EqSeven n k
  = number of odd orbit labels congruent to 7 modulo 8

orbitWindowResidueCountPow2 n k depth residue
  = number of odd orbit labels congruent to residue modulo 2^depth

orbitWindowResidueCountMod4EqOneTail n k
  = number of shifted tail labels, at times i + 1 for i < k,
    congruent to 1 modulo 4

orbitWindowResidueCountMod4EqThreeTail n k
  = number of shifted tail labels, at times i + 1 for i < k,
    congruent to 3 modulo 4

orbitWindowResidueCountPow2Tail n k depth residue
  = number of shifted tail labels, at times i + 1 for i < k,
    congruent to residue modulo 2^depth

orbitWindowPrefixResidueCountMod4EqOne n k r
  = number of prefix labels congruent to 1 modulo 4 inside an ambient k-window
```

The current count API is intentionally minimal:

```text
exact-height count <= k
threshold count <= k
all heights equal h
  -> exact-height count = k
all heights >= threshold
  -> threshold count = k

height >= threshold appears c times
  -> c * threshold <= sumS n k

exact-height count is below threshold count
  -> CountEq h <= CountGe h

height = h appears c times
  -> c * h <= sumS n k

prefix threshold count in a k-window, with r <= k
  -> prefix CountGe * threshold <= sumS n r

first two layer-cake layers
  -> CountGe 1 + CountGe 2 <= sumS n k

Collatz odd-state height floor
  -> CountGe 1 = k

Collatz-specific two-layer lower bound
  -> k + CountGe 2 <= sumS n k

prefix Collatz-specific two-layer lower bound
  -> r + prefix CountGe 2 <= sumS n r

threshold monotonicity
  -> CountGe b <= CountGe a when a <= b

first three layer-cake layers
  -> CountGe 1 + CountGe 2 + CountGe 3 <= sumS n k

finite layer-cake
  -> Sum_{t < H} CountGe (t + 1) <= sumS n k

first four layer-cake layers
  -> CountGe 1 + CountGe 2 + CountGe 3 + CountGe 4 <= sumS n k

finite tail layer-cake
  -> k + Sum_{t < H} CountGe (t + 2) <= sumS n k

external CountGe 2 lower bound
  -> m <= CountGe 2 -> k + m <= sumS n k

mod 4 residue occupation lower bound
  -> m <= residueCountMod4EqOne -> k + m <= sumS n k

prefix mod 4 residue occupation lower bound
  -> m <= prefixResidueCountMod4EqOne -> r + m <= sumS n r

mod 8 residue occupation lower bound
  -> m <= residueCountMod8EqFive
  -> k + CountGe 2 + m <= sumS n k

tail `height >= 2` lower bound
  -> (k + 1) + tail CountGe 2 <= sumS n (k + 1)

delayed `3 mod 8` drift
  -> (k + 1) + residueCountMod8EqThree n k <= sumS n (k + 1)

tail first-layer partition
  -> tail CountGe 2 + tail CountEq 1 = k

retaining `7 mod 8` source
  -> residueCountMod8EqSeven <= tail CountEq 1

generic pow-two residue count
  -> CountPow2 depth residue <= k

generic shifted-tail pow-two residue count
  -> TailCountPow2 depth residue <= k

named `7 mod 8` source count
  -> residueCountMod8EqSeven = CountPow2 depth 3 residue 7

generic pow-two source count successor
  -> CountPow2(k + 1, depth, residue)
     = CountPow2(k, depth, residue) + last-label indicator

generic shifted-tail pow-two count successor
  -> TailCountPow2(k + 1, depth, residue)
     = TailCountPow2(k, depth, residue) + last-tail-label indicator

depth zero sanity check
  -> CountPow2 depth 0 residue 0 = k

out-of-range residue cells
  -> 2^depth <= residue -> CountPow2 depth residue = 0

single-label residue indicator
  -> Sum_{residue < 2^depth} indicator(label % 2^depth = residue) = 1

full pow-two source residue partition
  -> Sum_{residue < 2^depth} CountPow2 depth residue = k

full pow-two shifted-tail residue partition
  -> Sum_{residue < 2^depth} TailCountPow2 depth residue = k

generic pointwise-to-count channel flow
  -> if every source cell hit lands in a target tail cell,
     then source CountPow2 <= target TailCountPow2

depth `3` source distribution sanity
  -> Sum_{residue < 8} CountPow2 depth 3 residue = k

depth `3` shifted-tail distribution sanity
  -> Sum_{residue < 8} TailCountPow2 depth 3 residue = k

helper-routed recursive two-adic Petal channels
  -> recovery source <= outward-retention tail
  -> continuation source <= next-retention tail

No.100 finite channel-flow aliases
  -> sourcePow2Distribution_total
  -> tailPow2Distribution_total
  -> pow2ChannelFlow_of_pointwise

No.101 finite ratio / retention mass layer
  -> AtMostHalf
  -> AtMostRatioNat
  -> RetentionMass / RecoverySiblingMass / ContinuationSiblingMass
  -> mass-name channel-flow corollaries
```

This is the first distribution layer.  It still avoids importing the heavier
ABC analytic layer-cake file, but it now has a local finite `Nat` count version
of the same idea:

```text
height h contributes once to CountGe 1,
again to CountGe 2,
...
up to CountGe h.
```

The repository already contains `DkMath.ABC.LayerCakeBasic`, but that file is
aimed at real-power / exponential MGF estimates.  The Collatz bridge keeps the
current API local and elementary because the data here is just a finite ordered
list of natural 2-adic heights.  This avoids pulling the ABC analytic stack into
the observation-window layer before a real carrier/radical bridge exists.

The finite channel-flow layer is now visible as a theorem chain:

```text
SourceDistribution:
  CountPow2 over labels 0..k-1

TailDistribution:
  TailCountPow2 over labels 1..k

Conservation:
  total source mass = k
  total tail mass = k

ChannelFlow:
  pointwise source-to-tail transition
    -> source occupation <= tail occupation

Recursive two-adic Petal instances:
  recovery source <= outward-retention tail
  continuation source <= next-retention tail
```

The No.100 entry documents for this layer are:

```text
README.md
docs/Collatz-Overview.md
docs/Collatz-Package-Structure.md
docs/Collatz-FiniteChannelFlow-100.md
docs/Collatz-PetalBridge-Guide.md
../Petal/docs/Petal-CollatzBridge.md
```

The next ratio layer should initially stay in `Nat` inequalities rather than
introducing `ℚ` or `ℝ` frequencies:

```text
FiniteRatioWitness:
  use inequalities such as 2 * count <= k
  instead of count / k at first

Reason:
  avoids zero-window division and coercion overhead
```

This layer has now begun.  Checkpoint 101 adds division-free finite ratio
witnesses and names the main retention/sibling masses:

```text
AtMostHalf:
  2 * count <= k

AtMostRatioNat:
  den * count <= num * k

RetentionMass(depth r):
  CountPow2 r (2^r - 1)

RecoverySiblingMass(parent r):
  CountPow2 (r + 1) (2^r - 1)

ContinuationSiblingMass(parent r):
  CountPow2 (r + 1) (2^(r + 1) - 1)
```

The next theorem target is the depth-refinement split:

```text
CountPow2 depth residue
  = CountPow2 (depth + 1) residue
    + CountPow2 (depth + 1) (residue + 2^depth)
```

For the retention cell this becomes:

```text
RetentionMass(r)
  = RecoverySiblingMass(r) + ContinuationSiblingMass(r)
```

The Collatz-specific floor is now also fixed:

```text
every accelerated odd state has height >= 1
```

Therefore the first layer is not merely an occupation statistic; it is the full
window size:

```text
CountGe 1 = k
```

The two-layer lower bound becomes the practical drift estimate:

```text
k + CountGe 2 <= sumS n k
```

and the same statement is available for prefixes:

```text
r + prefix CountGe 2 <= sumS n r
```

The experimental three-layer theorem also passed:

```text
CountGe 1 + CountGe 2 + CountGe 3 <= sumS n k
```

This evidence has now been upgraded to the general finite layer-cake theorem:

```text
Sum_{t < H} CountGe (t + 1) <= sumS n k
```

The explicit four-layer theorem is retained as a readable experiment witness,
but it is now derived from the general theorem rather than proved by another
hand-written induction.

Since `CountGe 1 = k`, the practical Collatz-facing form is the tail budget:

```text
k + Sum_{t < H} CountGe (t + 2) <= sumS n k
```

This separates the always-present base peeling from the additional peeling
events.  The same structure is also available for prefixes.

Finally, downstream observation layers can now feed the drift estimate by
proving only a lower bound on the second layer:

```text
m <= CountGe 2 -> k + m <= sumS n k
```

Equivalently, after the residue bridge, they may prove only:

```text
m <= orbitWindowResidueCountMod4EqOne n k
```

This changes the practical target from a valuation-count statement into a
finite residue-class occupation statement.

The same reading is now available locally in prefixes:

```text
m <= orbitWindowPrefixResidueCountMod4EqOne n k r
  -> r + m <= sumS n r
```

The first mod `4` partition is also closed at pointwise and count level:

```text
height = 1 <-> oddOrbitLabel % 4 = 3
CountGe 2 = residue mod 4 = 1
CountEq 1 = residue mod 4 = 3
residueCountMod4EqOne + residueCountMod4EqThree = k
```

The mod `8` layer now has a count-level handoff:

```text
CountGe 3 = residue mod 8 = 5
m <= residueCountMod8EqFive
  -> k + CountGe 2 + m <= sumS n k
```

The exact mod `8` height partition is now also visible:

```text
height = 2 <-> oddOrbitLabel % 8 = 1
height = 1 <-> oddOrbitLabel % 8 = 3 or 7
CountEq 2 = residue mod 8 = 1
residueCountMod8EqOne + residueCountMod8EqThree
  + residueCountMod8EqFive + residueCountMod8EqSeven = k
```

The first transition map is now fixed for the exact height-one channels:

```text
oddOrbitLabel % 8 = 3
  -> (T current).val % 4 = 1

oddOrbitLabel % 8 = 7
  -> (T current).val % 4 = 3
```

This has now been lifted to the actual orbit-label sequence:

```text
oddOrbitLabel n i % 8 = 3
  -> oddOrbitLabel n (i + 1) % 4 = 1

oddOrbitLabel n i % 8 = 7
  -> oddOrbitLabel n (i + 1) % 4 = 3
```

The `3 mod 8` channel is a delayed-peeling edge:

```text
current label is 3 mod 8
  -> current height is exactly 1
  -> next label is 1 mod 4
  -> next height is at least 2
```

Thus the first two-step experiment is fixed:

```text
oddOrbitLabel n 0 % 8 = 3
  -> 3 <= sumS n 2
```

At count level, the two exact height-one channels feed shifted tail counts:

```text
residueCountMod8EqThree <= tail residueCountMod4EqOne
residueCountMod8EqSeven <= tail residueCountMod4EqThree
```

The `3 mod 8` source channel has also been returned to the height-count side:

```text
residueCountMod8EqThree
  <= tail CountGe 2
```

Since the tail `1..k` sits inside the ordinary `(k + 1)` window `0..k`, this
feeds the Collatz drift budget:

```text
(k + 1) + tail CountGe 2 <= sumS n (k + 1)

(k + 1) + residueCountMod8EqThree n k <= sumS n (k + 1)
```

This is the first general-window delayed-peeling theorem.  A source count in
the current window now produces a lower bound on accumulated height one step
later.

The `7 mod 8` source channel is now the retention counterpart:

```text
residueCountMod8EqSeven
  <= tail CountEq 1
```

The shifted tail itself has the first exact/threshold partition:

```text
tail CountGe 2 + tail CountEq 1 = k
```

This records the first mod `8` transition split:

```text
3 mod 8 source:
  next tail enters the extra-peeling side

7 mod 8 source:
  next tail remains exact height one
```

A concrete two-step witness is also available:

```text
label 0 = 7 mod 8 and label 1 = 7 mod 8
  -> sumS n 2 = 2
```

The `7 mod 8` retention channel has now been split at mod `16`:

```text
7 mod 16:
  next label is 3 mod 8
  recovery branch

15 mod 16:
  next label is 7 mod 8
  retention-continuation branch
```

Thus the `7 mod 16` subchannel recovers delayed peeling in three steps:

```text
label 0 = 7 mod 16
  -> height at 0 is 1
  -> label 1 = 3 mod 8
  -> height at 1 is 1
  -> height at 2 is at least 2
  -> 4 <= sumS n 3
```

The `15 mod 16` retention-continuation channel has now been split at mod `32`:

```text
15 mod 32:
  next label is 7 mod 16
  recovery branch one level down

31 mod 32:
  next label is 15 mod 16
  retention-continuation branch
```

Thus the `15 mod 32` subchannel recovers delayed peeling in four steps:

```text
label 0 = 15 mod 32
  -> height at 0 is 1
  -> label 1 = 7 mod 16
  -> height at 1 is 1
  -> label 2 = 3 mod 8
  -> height at 2 is 1
  -> height at 3 is at least 2
  -> 5 <= sumS n 4
```

The complementary `31 mod 32` branch is the visible narrowing condition for a
long low-peeling path:

```text
7 mod 8
15 mod 16
31 mod 32
...
```

At this stage the bridge has not proved the general cylinder theorem.  What is
fixed is the verified local pattern: every time the retention branch continues,
the residue condition moves into a thinner power-of-two cylinder; the sibling
branch returns to a delayed-peeling recovery estimate.

The `31 mod 32` retention-continuation channel has now been split at mod `64`:

```text
31 mod 64:
  next label is 15 mod 32
  recovery branch one level down

63 mod 64:
  next label is 31 mod 32
  retention-continuation branch
```

Thus the `31 mod 64` subchannel recovers delayed peeling in five steps:

```text
label 0 = 31 mod 64
  -> height at 0 is 1
  -> label 1 = 15 mod 32
  -> height at 1 is 1
  -> label 2 = 7 mod 16
  -> height at 2 is 1
  -> label 3 = 3 mod 8
  -> height at 3 is 1
  -> height at 4 is at least 2
  -> 6 <= sumS n 5
```

The raw arithmetic anchors have also been checked in Lean up to mod `512`:

```text
7 mod 16    -> 3 mod 8
15 mod 16   -> 7 mod 8

15 mod 32   -> 7 mod 16
31 mod 32   -> 15 mod 16

31 mod 64   -> 15 mod 32
63 mod 64   -> 31 mod 32

63 mod 128  -> 31 mod 64
127 mod 128 -> 63 mod 64

127 mod 256 -> 63 mod 128
255 mod 256 -> 127 mod 128

255 mod 512 -> 127 mod 256
511 mod 512 -> 255 mod 256
```

The Lean theorem layer currently promotes the `mod 64` rung to orbit-label and
drift form.  The `mod 128`, `mod 256`, and `mod 512` rows are raw arithmetic
anchors, kept as evidence for the next generalization step rather than fully
expanded orbit bridges.

The fixed raw anchors have now been lifted to an expanded general raw theorem.
The recursive Petal naming layer is:

```text
twoAdicRetentionResidue r
  = 2^r - 1

twoAdicRecoverySiblingResidue r
  = 2^r - 1

twoAdicContinuationSiblingResidue r
  = 2^(r + 1) - 1
```

The two structural identities are:

```text
RecoverySibling r = RetentionResidue r
ContinuationSibling r = RetentionResidue (r + 1)
```

The second identity is the minimal Lean statement of the nested Petal reading:

```text
continuation branch
  = next retention cell
```

The general raw transition theorems are:

```text
expanded recovery sibling:
  m = 2^(r+2) * t + (2^(r+1) - 1)
  -> T-height-one raw step is 2^r - 1 mod 2^(r+1)

expanded continuation sibling:
  m = 2^(r+2) * t + (2^(r+2) - 1)
  -> T-height-one raw step is 2^(r+1) - 1 mod 2^(r+1)
```

This confirms that the narrowing cylinder is not merely a list of fixed
observations.  At the raw arithmetic layer, it is a recursive two-branch Petal:

```text
parent retention cell
  -> recovery sibling
  -> continuation sibling = next retention cell
```

The expanded raw theorems now also have practical residue-class forms:

```text
m % 2^(r+2) = 2^(r+1) - 1
  -> ((3m + 1) / 2) % 2^(r+1) = 2^r - 1

m % 2^(r+2) = 2^(r+2) - 1
  -> ((3m + 1) / 2) % 2^(r+1) = 2^(r+1) - 1
```

The proof decomposes an arbitrary label by `Nat.mod_add_div`:

```text
m = 2^(r+2) * (m / 2^(r+2)) + m % 2^(r+2)
```

and then reuses the expanded theorem.  This turns the recursive Petal theorem
from a parametric raw expression into a theorem about any label inside the
given residue cell.  The fixed `mod 512` anchors have been rederived from this
general theorem as usability tests.

The source-entry side is also now recorded:

```text
2 <= r
  -> (2^(r+1) - 1) % 8 = 7

1 <= r
  -> (2^(r+2) - 1) % 8 = 7
```

This is the lower-bound condition needed before promoting the practical raw
theorem to an orbit-label theorem: the source label must be in the exact
height-one `7 mod 8` channel so that `T` is the visible `(3m + 1) / 2` step.

That promotion is now closed.  The residue-cell reduction bridge is:

```text
d | M
  -> m % d = (m % M) % d
```

In particular, when `8 | 2^(r+2)`, the large 2-adic address determines the
visible `mod 8` source channel:

```text
m % 2^(r+2) = 2^(r+1) - 1, 2 <= r
  -> m % 8 = 7

m % 2^(r+2) = 2^(r+2) - 1, 1 <= r
  -> m % 8 = 7
```

Therefore the recursive two-adic Petal theorem has reached the orbit-label
layer:

```text
oddOrbitLabel n i % 2^(r+2) = 2^(r+1) - 1, 2 <= r
  -> oddOrbitLabel n (i+1) % 2^(r+1) = 2^r - 1

oddOrbitLabel n i % 2^(r+2) = 2^(r+2) - 1, 1 <= r
  -> oddOrbitLabel n (i+1) % 2^(r+1) = 2^(r+1) - 1
```

This is the first general orbit-level statement of the narrowing retention
cylinder: recovery exits one level outward, while continuation becomes the next
retention cell.

The same recursive rule is now lifted to occupation counts.  Source cells in
the current window inject into target cells in the shifted tail window:

```text
CountPow2 depth (r+2) residue (2^(r+1)-1), 2 <= r
  <= TailCountPow2 depth (r+1) residue (2^r - 1)

CountPow2 depth (r+2) residue (2^(r+2)-1), 1 <= r
  <= TailCountPow2 depth (r+1) residue (2^(r+1)-1)
```

This is the first count-level recursive Petal statistic: individual address
transitions now become source-to-tail occupation inequalities.

At count level, the two exact-height-one source channels also have a source
mass bound:

```text
residueCountMod8EqThree + residueCountMod8EqSeven <= k
```

There are two readings of this bound:

```text
mod 8 partition:
  the two source channels are part of the four odd mod 8 classes

tail partition:
  3 source enters tail CountGe 2
  7 source enters tail CountEq 1
  tail CountGe 2 + tail CountEq 1 = k
```

The next higher-coordinate experiment also passed:

```text
height >= 4 <-> oddOrbitLabel % 16 = 5
```

This is the intended bridge from a future residue/address occupation theorem
to a Collatz drift lower bound.

The bridge theorem

```lean
rawHeightLabel_shift_eq
```

repackages `v2_shift_invariant`: inside a sufficiently large `2^k` shift
block, the raw height label is conserved.  This is the current entry point for
reading Collatz block-shift invariance as a Petal-style address conservation
phenomenon.

This gives a clean place to attach future hypotheses:

```text
orbit labels are usable carrier labels
orbit labels are mapped to prime labels
orbit collision implies a specific fold/cycle condition
2-adic height controls Petal address movement
ordered height profile controls accumulated Collatz drift
height-threshold hypotheses give integer lower bounds for `sumS`
label collisions preserve the next height observation
height occupation counts measure exact and lower-bound regimes
threshold occupation counts give direct lower bounds for `sumS`
```

## Next Candidate Work

The next safe steps are:

```text
1. Connect the ordered height profile to a Petal address/residue reading.
2. Add a window occupation/address transition layer.
3. Refine exact-height counts into distribution estimates for `sumS`.
4. Use threshold occupation lower bounds as the Collatz-side drift input.
5. Test whether an external label transform can turn orbit labels into carrier labels.
6. Only after that, test whether Collatz labels can feed ABC support/rad.
```

The immediate residue candidates are:

```text
general 2^r residue coordinate for height >= r
prefix mod 8 residue occupation
shifted-tail prefix versions of the transition-count inequalities
2-step and 3-step delayed-peeling drift estimates
```

The main caution is that Collatz state labels are not prime labels.  Any bridge
to `ABCBridge` must insert an additional label transform or carrier witness
layer before using the Petal radical lower-bound theorems.
