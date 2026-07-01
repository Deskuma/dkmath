# Collatz PetalBridge Guide

## Why PetalBridge Exists

`DkMath.Collatz.PetalBridge` connects accelerated Collatz dynamics to the
Petal observation style used elsewhere in DkMath.

The Petal side already has language for:

```text
finite ranges
addresses
occupation counts
separation vs collision
boundary and channel behavior
```

The Collatz side has:

```text
odd states
2-adic height
accelerated transition
finite orbit segments
```

`PetalBridge` is the file where these languages meet.

## Basic Objects

### `OrbitWindow`

```lean
OrbitWindow n k
```

This is the finite observation window of length `k`.

It is definitionally:

```text
Finset.range k
```

### `oddOrbitLabel`

```lean
oddOrbitLabel n i
```

This is the natural value of the `i`-th accelerated odd state:

```text
(iterateT i n).val
```

### `orbitWindowHeight`

```lean
orbitWindowHeight n i
```

This is:

```text
v2 (3 * oddOrbitLabel n i + 1)
```

It is the local 2-adic peeling height.

### `orbitWindowHeightSeq`

```lean
orbitWindowHeightSeq n k
```

This is the ordered list of the first `k` height values.

The bridge theorem:

```lean
orbitWindowHeightSeq_sum_eq_sumS
```

connects the ordered list back to the accumulated Collatz height:

```text
(orbitWindowHeightSeq n k).sum = sumS n k
```

## Separation And Collision

The bridge includes a finite split:

```lean
OrbitWindowSeparated n k
OrbitWindowCollision n k
orbitWindowSeparated_or_collision
```

This reads:

```text
either the first k odd orbit labels are separated,
or there is a collision inside the window
```

The Petal reading:

```text
separated labels support independent finite counting
collision is an obstruction to that independent route
```

The Collatz reading:

```text
collision means the accelerated odd state has merged/folded
```

This split is finite.  It is not a global convergence theorem.

## Height Counts

The file defines exact and threshold height counts:

```lean
orbitWindowHeightCountEq
orbitWindowHeightCountGe
orbitWindowHeightCountEqTail
orbitWindowHeightCountGeTail
```

These are finite `Nat` counts.

They support layer-cake style bounds such as:

```lean
orbitWindowHeightSeq_sum_ge_sum_countGe_range
orbitWindowHeightSeq_sum_ge_window_add_sum_countGe_tail
```

The important Collatz floor is:

```lean
orbitWindowHeightCountGe_one_eq_window
```

Every odd accelerated state has height at least `1`.

## Residue Counts

Named residue counts exist for low layers:

```lean
orbitWindowResidueCountMod4EqOne
orbitWindowResidueCountMod4EqThree
orbitWindowResidueCountMod8EqOne
orbitWindowResidueCountMod8EqThree
orbitWindowResidueCountMod8EqFive
orbitWindowResidueCountMod8EqSeven
```

The generic power-of-two count is:

```lean
orbitWindowResidueCountPow2 n k depth residue
```

The shifted-tail version is:

```lean
orbitWindowResidueCountPow2Tail n k depth residue
```

This generic surface is the current preferred route for new residue-channel
work.

## Distribution Conservation

Checkpoint 100 exposes the conservation laws as conceptual aliases:

```lean
sourcePow2Distribution_total
tailPow2Distribution_total
```

These say that every finite source or shifted-tail window is fully partitioned
by its `2^depth` residue cells.

This gives the exact finite analogue of:

```text
total distribution mass = window size
```

but still in `Nat`.

## Channel Flow

The main helper is:

```lean
pow2ChannelFlow_of_pointwise
```

Use it when you have a pointwise theorem of the form:

```text
for all i < k,
  source cell condition at i
    -> target tail cell condition at i + 1
```

The helper returns:

```text
source cell count <= target tail cell count
```

## Depth Refinement

Checkpoint 102 adds the recursive residue-cell split.

The pointwise theorem is:

```lean
mod_pow2_succ_eq_left_or_right_of_mod_pow2_eq
```

It says that a valid residue cell at depth `depth` has exactly two children at
depth `depth + 1`:

```text
residue
residue + 2^depth
```

The count-level theorem is:

```lean
orbitWindowResidueCountPow2_refine_succ
```

It upgrades the pointwise split to finite window occupation counts:

```text
count(parent cell)
  = count(left child) + count(right child)
```

The retention-channel specialization is:

```lean
orbitWindowRetentionMass_split
```

This reads:

```text
retention mass at depth r
  = recovery sibling mass at depth r+1
    + continuation sibling mass at depth r+1
```

Use this theorem when an argument needs to show that recovery and continuation
are not independent extra mass.  They are the two subcells of the previous
retention cylinder.

Checkpoint 103 adds the shifted-tail counterpart:

```lean
orbitWindowResidueCountPow2Tail_refine_succ
orbitWindowRetentionMassPow2Tail_split
```

So the same reading is available in the receiving window:

```text
tail retention mass at depth r
  = tail recovery sibling mass at depth r+1
    + tail continuation sibling mass at depth r+1
```

The useful forcing aliases are:

```lean
orbitWindowContinuationMass_forces_tailRetention
orbitWindowRecoveryMass_forces_tailRecovery
orbitWindowContinuationMass_le_tailRecovery_add_tailContinuation
```

Use these names when the argument is conceptually about mass flow from the
source window into the shifted-tail window.  Use the split theorems when the
argument is about decomposing a retention cylinder into its two child cells.

## Finite Half Criteria

Checkpoint 104 connects the split theorems to `AtMostHalf`.

The source criterion is:

```lean
atMostHalf_continuation_of_continuation_le_recovery
```

The tail criterion is:

```lean
atMostHalf_tailContinuation_of_tailContinuation_le_tailRecovery
```

Both have the same reading:

```text
continuation <= recovery
  -> continuation is at most half of retention
```

There are also recovery-budget variants:

```lean
atMostHalf_continuation_of_retention_le_two_recovery
atMostHalf_tailContinuation_of_tailRetention_le_two_tailRecovery
```

These do not prove the comparison condition.  They make the next target
explicit: find a structural reason why continuation is no larger than recovery,
or why recovery covers at least half of retention.

## Comparison Predicates

Checkpoint 105 names the missing comparison conditions:

```lean
RecoveryDominatesContinuation
TailRecoveryDominatesContinuation
RecoveryCoversHalfRetention
TailRecoveryCoversHalfRetention
RecoveryDominatesOnRange
TailRecoveryDominatesOnRange
```

The predicate-facing half criteria are:

```lean
atMostHalf_continuation_of_recoveryDominates
atMostHalf_tailContinuation_of_tailRecoveryDominates
atMostHalf_continuation_of_recoveryCoversHalf
atMostHalf_tailContinuation_of_tailRecoveryCoversHalf
```

Use these names when a later proof has produced a comparison hypothesis and
wants to consume it without unfolding recovery/continuation counts.

This is the theorem to reach for before writing a custom induction over `k`.

## More-Than-Half Pressure

Checkpoint 106 adds the strict complement to `AtMostHalf`:

```lean
MoreThanHalf
atMostHalf_or_moreThanHalf
```

The comparison predicates now split locally:

```lean
recoveryDominates_or_continuationOutruns
tailRecoveryDominates_or_tailContinuationOutruns
```

The failure branch is not treated as a dead end.  It has a measurable
consequence:

```lean
moreThanHalf_continuation_of_continuationOutruns
moreThanHalf_tailContinuation_of_tailContinuationOutruns
moreThanHalf_continuation_of_outRunsOnRange
moreThanHalf_tailContinuation_of_outRunsOnRange
```

Read this as:

```text
recovery dominates continuation
  -> continuation is at most half of retention

continuation outruns recovery
  -> continuation is more than half of retention
```

This gives the obstruction route a concrete finite signature.  If the desired
dominance condition fails over a range, each failed depth carries strict
continuation pressure inside the corresponding retention cylinder.

## Pressure Profiles

Checkpoint 107 packages repeated more-than-half pressure over a depth range:

```lean
MoreThanHalfOnRange
SourceContinuationPressureOnRange
TailContinuationPressureOnRange
```

The range-failure predicates from checkpoint 106 now promote directly to
pressure profiles:

```lean
sourceContinuationPressure_of_outRunsOnRange
tailContinuationPressure_of_outRunsOnRange
```

Use the extraction theorems when a later proof has a range profile and needs a
single depth:

```lean
moreThanHalf_of_sourceContinuationPressure
moreThanHalf_of_tailContinuationPressure
```

Checkpoint 107 also starts depth-mode counting:

```lean
sourceContinuationPressureDepthCount
tailContinuationPressureDepthCount
sourceContinuationPressureDepthCount_eq_len_of_pressureOnRange
tailContinuationPressureDepthCount_eq_len_of_pressureOnRange
```

This is a different finite distribution from the window residue counts.  It
counts how many depths in `[r, r + len)` are pressure depths.  The first count
theorems only cover the all-pressure case:

```text
pressure at every depth
  -> pressure depth count = len
```

The next natural layer is a mixed depth-mode distribution: controlled depths
versus pressure depths.

## Mixed Depth-Mode Distribution

Checkpoint 108 adds the controlled side of the pressure count:

```lean
sourceContinuationControlledDepthCount
tailContinuationControlledDepthCount
```

Both pressure and controlled counts are bounded by the range length:

```lean
sourceContinuationPressureDepthCount_le_len
tailContinuationPressureDepthCount_le_len
sourceContinuationControlledDepthCount_le_len
tailContinuationControlledDepthCount_le_len
```

The main partition theorems are:

```lean
sourceContinuationControlledDepthCount_add_pressureDepthCount_eq_len
tailContinuationControlledDepthCount_add_pressureDepthCount_eq_len
```

They say:

```text
controlled depth count + pressure depth count = len
```

This is the depth-mode analogue of the finite channel distribution theorem.
Checkpoint 100 counted how orbit-window labels distribute across residue
cells.  Checkpoint 108 counts how depth positions distribute across the two
local modes:

```text
AtMostHalf mode
MoreThanHalf mode
```

This still does not prove that pressure is rare.  It provides the finite budget
surface needed to state such a claim without leaving `Nat`.

## Depth-Pressure Frequency

Checkpoint 109 applies the existing finite half vocabulary to the depth-mode
pressure count itself:

```lean
SourcePressureAtMostHalfOnDepthRange
SourcePressureMoreThanHalfOnDepthRange
TailPressureAtMostHalfOnDepthRange
TailPressureMoreThanHalfOnDepthRange
```

The frequency split is:

```lean
sourcePressureAtMostHalf_or_moreThanHalfOnDepthRange
tailPressureAtMostHalf_or_moreThanHalfOnDepthRange
```

The mixed distribution makes these predicates readable as comparisons between
controlled depths and pressure depths:

```lean
sourcePressureDepthCount_le_controlled_of_atMostHalf
sourcePressureAtMostHalf_of_pressureDepthCount_le_controlled
sourceControlledDepthCount_lt_pressure_of_pressureMoreThanHalf
sourcePressureMoreThanHalf_of_controlledDepthCount_lt_pressure
```

with shifted-tail counterparts.

Checkpoint 109 also proves the reverse local pressure direction:

```lean
continuationOutruns_of_moreThanHalf_continuation
tailContinuationOutruns_of_moreThanHalf_tailContinuation
```

Together with the checkpoint 106 forward direction, this means the local
`MoreThanHalf` pressure mode and the continuation-outruns-recovery mode are now
interderivable.

## Cause-Side Failure Counts

Checkpoint 110 counts the cause-side failure predicate directly:

```lean
sourceContinuationOutrunsDepthCount
tailContinuationOutrunsDepthCount
```

The bridge to the descriptive pressure count is:

```lean
sourceContinuationOutrunsDepthCount_eq_pressureDepthCount
tailContinuationOutrunsDepthCount_eq_pressureDepthCount
```

Thus a pressure depth count can be read as:

```text
descriptive mode:
  MoreThanHalf continuation retention

cause-side mode:
  ContinuationOutrunsRecovery
```

Checkpoint 110 also adds the controlled-side reverse direction:

```lean
recoveryDominates_of_atMostHalf_continuation
tailRecoveryDominates_of_atMostHalf_tailContinuation
```

Together with the existing forward direction, the local modes now align:

```text
RecoveryDominatesContinuation
  <-> AtMostHalf continuation retention

ContinuationOutrunsRecovery
  <-> MoreThanHalf continuation retention
```

This is the point where the depth-mode distribution acquires both a descriptive
reading and a cause-side reading.

## Cause-Side Depth Distribution

Checkpoint 111 completes the dominance side of the cause-side count layer:

```lean
sourceRecoveryDominanceDepthCount
tailRecoveryDominanceDepthCount
```

The local bridge is now explicit in both directions:

```lean
recoveryDominates_iff_atMostHalf_continuation
tailRecoveryDominates_iff_atMostHalf_tailContinuation
```

Therefore the dominance count is exactly the controlled count:

```lean
sourceRecoveryDominanceDepthCount_eq_controlledDepthCount
tailRecoveryDominanceDepthCount_eq_controlledDepthCount
```

Together with the checkpoint 110 failure-count equalities, this gives the
cause-side partition:

```lean
sourceCauseSideDepthCount_add_eq_len
tailCauseSideDepthCount_add_eq_len
```

The same finite depth range now has two aligned presentations:

```text
descriptive:
  controlledDepthCount + pressureDepthCount = len

cause-side:
  dominanceDepthCount + outrunsDepthCount = len
```

The bridge between the two readings is not heuristic.  It is theorem-level:

```text
dominanceDepthCount = controlledDepthCount
outrunsDepthCount = pressureDepthCount
```

Use the descriptive presentation when the proof is about the finite
`AtMostHalf` / `MoreThanHalf` budget.  Use the cause-side presentation when the
proof is about the comparison mechanism:

```text
RecoveryDominatesContinuation
ContinuationOutrunsRecovery
```

## Cause-Side Frequency Alias

Checkpoint 112 gives the failure side its own frequency vocabulary:

```lean
SourceOutrunsAtMostHalfOnDepthRange
SourceOutrunsMoreThanHalfOnDepthRange
TailOutrunsAtMostHalfOnDepthRange
TailOutrunsMoreThanHalfOnDepthRange
```

These predicates are thin aliases around the cause-side outruns counts:

```text
sourceContinuationOutrunsDepthCount
tailContinuationOutrunsDepthCount
```

They have the same finite dichotomy as pressure frequency:

```lean
sourceOutrunsAtMostHalf_or_moreThanHalfOnDepthRange
tailOutrunsAtMostHalf_or_moreThanHalfOnDepthRange
```

The bridge back to the descriptive pressure vocabulary is explicit:

```lean
sourceOutrunsAtMostHalf_iff_pressureAtMostHalf
sourceOutrunsMoreThanHalf_iff_pressureMoreThanHalf
tailOutrunsAtMostHalf_iff_pressureAtMostHalf
tailOutrunsMoreThanHalf_iff_pressureMoreThanHalf
```

So a later proof can state a hypothesis on the mechanism side:

```text
continuation outruns recovery in more than half of the depths
```

and immediately consume the existing pressure-frequency API.

Checkpoint 112 also records the direct count comparison forced by cause-side
more-than-half:

```lean
sourceDominanceDepthCount_lt_outruns_of_outrunsMoreThanHalf
tailDominanceDepthCount_lt_outruns_of_outrunsMoreThanHalf
```

This reads:

```text
if outruns depths occupy more than half of the depth range,
then outruns depths strictly outnumber dominance depths.
```

## Frequency To Height Preparation

Checkpoint 113 starts the bridge from cause-side frequency toward height and
drift data.

The first step is a one-way alias from cause-side high frequency to descriptive
pressure high frequency:

```lean
sourcePressureMoreThanHalf_of_outrunsMoreThanHalf
tailPressureMoreThanHalf_of_outrunsMoreThanHalf
```

The next step consumes the existing pressure-frequency API and produces the
descriptive count imbalance:

```lean
sourceControlledDepthCount_lt_pressure_of_outrunsMoreThanHalf
tailControlledDepthCount_lt_pressure_of_outrunsMoreThanHalf
```

For later existence-style arguments, checkpoint 113 also exposes positivity of
the pressure count:

```lean
sourcePressureDepthCount_pos_of_outrunsMoreThanHalf
tailPressureDepthCount_pos_of_outrunsMoreThanHalf
```

The recovery-side partition consumption test is:

```lean
sourceDominanceDepthCount_pos_of_outrunsAtMostHalf_and_not_all_outruns
tailDominanceDepthCount_pos_of_outrunsAtMostHalf_and_not_all_outruns
```

This records a useful finite reading:

```text
if the outruns side does not fill the range,
then the dominance side has positive count.
```

The direct height/drift hook is not yet proved from pressure frequency.
However, the existing height API already has the likely landing points:

```lean
orbitWindowHeightSeq_sum_eq_sumS
orbitWindowHeightSeq_sum_ge_window_add_of_countGe_two_ge
orbitWindowHeightSeq_sum_ge_window_add_tailCountGe_two
orbitWindowHeightSeq_sum_ge_sum_countGe_range
orbitWindowHeightSeq_sum_ge_window_add_sum_countGe_tail
```

So the next real bridge should convert a pressure-heavy or outruns-heavy range
into a lower bound for a height-count object such as:

```text
orbitWindowHeightCountGe n k 2
orbitWindowHeightCountGeTail n k 2
```

## Tail-Facing Height Bridge

Checkpoint 114 tests the expected bridge from source continuation mass to tail
height counts.

The meaning-name aliases are:

```lean
sourceContinuationMass_le_tailRetentionMass
sourceContinuationMass_le_tailSplitMass
```

The experiment showed an important correction.  At parent depth `2`, source
continuation mass lands in shifted-tail retention depth `2`; this is the
`3 mod 4` tail cell, hence exact height `1`, not height at least `2`.

The theorem-level bridge is:

```lean
tailRetentionMass_depth_two_eq_heightCountEq_one
tailRetentionMass_depth_two_le_heightCountEq_one
sourceContinuationMass_depth_two_le_tailHeightCountEq_one
```

This rules out the tempting route:

```text
source continuation mass at depth 2
  -> tail height >= 2
  -> extra sumS lower bound
```

The correct reading is:

```text
source continuation mass at depth 2
  -> tail exact height 1
  -> base retention / no extra peeling at this layer
```

So the next height-growth attempt should inspect the recovery sibling or a
deeper delayed branch, rather than using depth-2 continuation retention as an
extra-peeling source.

## Recovery And Delayed Branch

Checkpoint 115 follows the correction from checkpoint 114 and separates two
different recovery readings.

At parent depth `1`, shifted-tail recovery is the immediate extra-height cell:

```lean
tailRecoveryMass_depth_one_eq_tailResidueCount_mod4_eq_one
tailRecoveryMass_depth_one_le_heightCountGe_two
```

At parent depth `2`, shifted-tail recovery is not the same object.  It is the
`3 mod 8` color inside the exact-height-one reservoir:

```lean
tailRecoveryMass_depth_two_eq_tailResidueCount_mod8_eq_three
tailRecoveryMass_depth_two_le_tailResidueCount_mod8_eq_three
```

This is the main recovery correction:

```text
tail recovery, parent depth 1
  -> 1 mod 4
  -> immediate height >= 2

tail recovery, parent depth 2
  -> 3 mod 8
  -> exact height 1 now
  -> height >= 2 one step later
```

The exact-height-one reservoir is now split into its two visible colors:

```lean
tailHeightCountEq_one_split_mod8_three_seven
```

with reading:

```text
tail exact height 1
  = tail 3 mod 8 delayed-peeling color
    + tail 7 mod 8 continuing color
```

The delayed-peeling color has its own tail transition:

```lean
tailMod8Three_le_nextTailHeightCountGe_two
tailResidueCountMod8EqThree_delayed_drift
```

Finally, the source-side checkpoint hooks are:

```lean
sourceRecoveryMass_depth_three_le_tailResidueCount_mod8_eq_three
sourceContinuationMass_depth_two_le_tailMod8Three_add_tailMod8Seven
```

The working model is no longer:

```text
pressure-heavy -> immediate extra peeling
```

It is:

```text
pressure or recovery channel
  -> exact-height-one reservoir
  -> 3 mod 8 / 7 mod 8 color split
  -> the 3 mod 8 color supplies delayed extra peeling
```

## Delayed Reservoir Tower

Checkpoint 116 starts the recursive tower above the checkpoint 115 split.

The continuing `7 mod 8` color itself splits at the next resolution:

```lean
orbitWindowResidueCountMod16EqSevenTail
orbitWindowResidueCountMod16EqFifteenTail
tailResidueCountMod8EqSeven_split_mod16_seven_fifteen
```

The reading is:

```text
tail 7 mod 8
  = tail 7 mod 16
    + tail 15 mod 16
```

This is not only a static refinement.  The existing pointwise theorem:

```lean
orbitWindowNextHeight_eq_one_of_mod_eight_eq_seven
```

is now lifted to count level:

```lean
tailMod8Seven_le_nextTailHeightCountEq_one
tailMod8Seven_le_nextTailMod8Three_add_nextTailMod8Seven
```

So the continuing color enters the next exact-height-one reservoir and is then
split again:

```text
tail 7 mod 8 at this step
  -> next tail exact height 1
  -> next tail 3 mod 8 / next tail 7 mod 8
```

The one-step grammar is:

```lean
tailExactHeightOneReservoir_step_grammar
```

which says:

```text
current tail exact height 1
  -> next tail height >= 2
     or
     next tail exact height 1
```

The budget form keeps the continuing part as an explicit remainder:

```lean
tailExactHeightOneReservoir_budget_with_remainder
sourceContinuationMass_depth_two_delayed_budget_with_tailSeven_remainder
```

This is the current strongest finite reading:

```text
the delayed-peeling color pays into sumS;
the continuing color is not discarded, but carried as the next remainder.
```

## Level-2 Remainder

Checkpoint 117 fixes the next concrete tower level.

The level aliases are:

```lean
TailRemainderLevel0
TailRemainderLevel1
TailRemainderLevel2
TailFallingLevel1
TailFallingLevel2
```

They name the first visible pieces of the tower:

```text
level 0 remainder:
  tail exact height 1

level 1 falling:
  tail 3 mod 8

level 1 remainder:
  tail 7 mod 8

level 2 falling:
  tail 7 mod 16

level 2 remainder:
  tail 15 mod 16
```

The level-`2` static split is:

```lean
orbitWindowResidueCountMod32EqFifteenTail
orbitWindowResidueCountMod32EqThirtyOneTail
tailResidueCountMod16EqFifteen_split_mod32_fifteen_thirtyOne
```

The level-`2` recursion edge is:

```lean
tailMod16Fifteen_le_nextTailMod16Seven_add_nextTailMod16Fifteen
```

So the continuing tower now has two concrete levels:

```text
tail 7 mod 8
  -> next tail 3 mod 8 + next tail 7 mod 8

tail 15 mod 16
  -> next tail 7 mod 16 + next tail 15 mod 16
```

Checkpoint 117 also adds the first pressure-facing entrance:

```lean
sourceContinuationMass_depth_two_pos_of_pressure_depth_two
sourcePressureDepthTwo_delayed_budget_with_tailSeven_remainder
```

This does not yet prove that a pressure-heavy range feeds enough mass into the
tower.  It records the local depth-`2` caller shape:

```text
MoreThanHalf continuation pressure at depth 2
  -> positive continuation mass
  -> delayed budget with explicit remainder
```

## Level-3 And Range Pressure Entrance

Checkpoint 118 extends the concrete tower to level `3` and adds the first
range-pressure entrance.

The level-`3` residue counts are:

```lean
orbitWindowResidueCountMod64EqThirtyOneTail
orbitWindowResidueCountMod64EqSixtyThreeTail
```

The static split is:

```lean
tailResidueCountMod32EqThirtyOne_split_mod64_thirtyOne_sixtyThree
```

with reading:

```text
tail 31 mod 32
  = tail 31 mod 64
    + tail 63 mod 64
```

The level-`3` recursion edge is:

```lean
tailMod32ThirtyOne_le_nextTailMod32Fifteen_add_nextTailMod32ThirtyOne
```

so the tower now has:

```text
tail 31 mod 32
  -> next tail 15 mod 32 + next tail 31 mod 32
```

The level aliases are:

```lean
TailRemainderLevel3
TailFallingLevel3
tailRemainderLevel2_static_split
tailRemainderLevel2_step_grammar
```

Checkpoint 118 also connects one-depth range pressure to local depth-`2`
pressure:

```lean
sourcePressureDepthTwo_of_pressureOnRange_two_one
sourceContinuationMass_depth_two_pos_of_pressureOnRange_two_one
```

This is the first bridge from the range profile vocabulary to the delayed
reservoir budget entrance.

## Level-4 And Generic Pressure

Checkpoint 119 extends the concrete tower to level `4`:

```lean
orbitWindowResidueCountMod128EqSixtyThreeTail
orbitWindowResidueCountMod128EqOneHundredTwentySevenTail
tailResidueCountMod64EqSixtyThree_split_mod128_sixtyThree_oneHundredTwentySeven
tailMod64SixtyThree_le_nextTailMod64ThirtyOne_add_nextTailMod64SixtyThree
```

The tower edge is:

```text
tail 63 mod 64
  -> next tail 31 mod 64 + next tail 63 mod 64
```

The alias layer is:

```lean
TailRemainderLevel4
TailFallingLevel4
tailRemainderLevel3_static_split
tailRemainderLevel3_step_grammar
```

Checkpoint 119 also generalizes the pressure entrance:

```lean
sourcePressureAtDepth_of_pressureOnRange
sourceContinuationMass_pos_of_localPressure
sourceContinuationMass_pos_of_pressureOnRange_at
```

Use these names when a proof has a pressure profile over a depth range and
needs a local tower-entry opportunity at a selected depth `r + j`.

## Recursive Petal Residues

The current recursive two-adic Petal channels are:

```lean
twoAdicRetentionResidue
twoAdicRecoverySiblingResidue
twoAdicContinuationSiblingResidue
```

The count-level recursive instances are now available through helper-routed
theorems:

```lean
orbitWindowRecoverySiblingCount_le_tailRetentionResidueCount_via_helper
orbitWindowContinuationSiblingCount_le_tailRetentionResidueCount_via_helper
```

This fixes the intended proof route:

```text
residue formula
  -> pointwise orbit-label transition
  -> finite channel-flow count inequality
```

## How To Add A New Channel Theorem

For a new residue channel:

1. Prove the pointwise transition:

    ```text
    if oddOrbitLabel n i is in source cell A,
    then oddOrbitLabel n (i + 1) is in tail cell B.
    ```

2. Apply:

    ```lean
    pow2ChannelFlow_of_pointwise
    ```

3. State a named theorem for the channel:

    ```text
    sourceChannelCount <= tailChannelCount
    ```

Avoid writing a fresh count induction unless the helper does not fit.

## Next Work

The next layer should probably introduce finite ratio witnesses, but still as
natural-number inequalities:

```text
2 * count <= k
countA + countB <= k
m <= count
```

Only later should this become rational or real frequency.

Checkpoint 101 starts this layer with:

```lean
AtMostHalf
AtMostRatioNat
```

and names the retention-channel masses:

```lean
orbitWindowRetentionMassPow2
orbitWindowRetentionMassPow2Tail
orbitWindowRecoverySiblingMassPow2
orbitWindowContinuationSiblingMassPow2
```

Use these names when a theorem is conceptually about low-peeling retention,
rather than writing the raw residue-count expression every time.
