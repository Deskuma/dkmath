# DkMath.Collatz

`DkMath.Collatz` is the DkMath formalization workspace for the accelerated
Collatz map on odd natural states.

The current package is not only a direct attempt to prove the Collatz
conjecture.  It is a structured observation program:

```text
odd state dynamics
  -> 2-adic height
  -> residue channels
  -> finite observation windows
  -> source/tail distributions
  -> finite channel flow
```

The most recent milestone is the finite channel-flow layer in
`DkMath.Collatz.PetalBridge`.  It turns pointwise residue transitions into
count-level statements over finite windows, without using limits,
probability, or real-valued frequencies.

## Module Entry Points

```text
DkMath.Collatz.Basic
DkMath.Collatz.V2
DkMath.Collatz.Accelerated
DkMath.Collatz.Shift
DkMath.Collatz.PetalBridge
DkMath.Collatz.Collatz2K26
```

### `DkMath.Collatz.Basic`

Defines the basic Collatz surface:

```lean
C
OddNat
threeNPlusOne
```

This is the lowest-level arithmetic layer.

### `DkMath.Collatz.V2`

Provides the local 2-adic valuation vocabulary used by the accelerated map.

Important names include:

```lean
v2
v2_3n_plus_1_ge_1
v2_shift_invariant
```

This file is the arithmetic source of the fact that every odd accelerated
Collatz state peels at least one factor of `2`.

### `DkMath.Collatz.Accelerated`

Defines the accelerated odd-state Collatz map:

```lean
s n = v2 (3 * n + 1)
T n = (3 * n + 1) / 2 ^ s n
iterateT
sumS
driftReal
```

This is the dynamical core.

### `DkMath.Collatz.Shift`

Records the block-shift / petal-cartography approach.

This older approach studies how the valuation signal behaves under shifts by
powers of two:

```text
n -> n + 2^k * m
```

The guiding idea is that many differences do not appear everywhere; they
concentrate around singular 2-adic ridges.

### `DkMath.Collatz.PetalBridge`

This is the current main bridge.

It packages finite windows of the accelerated orbit and connects them to
Petal-style counting:

```lean
OrbitWindow
oddOrbitLabel
orbitWindowHeight
orbitWindowHeightSeq
orbitWindowResidueCountPow2
orbitWindowResidueCountPow2Tail
sourcePow2Distribution_total
tailPow2Distribution_total
pow2ChannelFlow_of_pointwise
orbitWindowResidueCountPow2_refine_succ
orbitWindowRetentionMass_split
```

The central No.100 layer is:

```text
Source distribution:
  sum of all source residue counts = window size

Tail distribution:
  sum of all shifted-tail residue counts = window size

Channel flow:
  pointwise source-to-tail residue transition
    -> source count <= target tail count
```

### `DkMath.Collatz.Collatz2K26`

Integration file for the 2026 Collatz cartography project.

It imports the main Collatz files and marks the package-level surface.

## Main Documentation

Read these in order:

```text
docs/Collatz-Overview.md
docs/Collatz-Package-Structure.md
docs/Collatz-FiniteChannelFlow-100.md
docs/Collatz-FiniteRatioRetention-101.md
docs/Collatz-DepthRefinement-102.md
docs/Collatz-TailDepthRefinement-103.md
docs/Collatz-FiniteHalfCriterion-104.md
docs/Collatz-ComparisonPredicates-105.md
docs/Collatz-MoreThanHalfPressure-106.md
docs/Collatz-PressureProfile-107.md
docs/Collatz-MixedDepthModeDistribution-108.md
docs/Collatz-DepthPressureFrequency-109.md
docs/Collatz-CauseSideFailureCount-110.md
docs/Collatz-CauseSideDepthDistribution-111.md
docs/Collatz-CauseSideFrequencyAlias-112.md
docs/Collatz-FrequencyHeightBridge-113.md
docs/Collatz-TailFacingHeightBridge-114.md
docs/Collatz-RecoveryDelayedBranch-115.md
docs/Collatz-DelayedReservoirTower-116.md
docs/Collatz-Level2Remainder-117.md
docs/Collatz-Level3PressureEntrance-118.md
docs/Collatz-Level4GenericPressure-119.md
docs/Collatz-Level5AndModScan-120.md
docs/Collatz-SelectedWitnessBudget-121.md
docs/Collatz-SelectedPressureDepths-122.md
docs/Collatz-PetalBridge-Guide.md
docs/Collatz-PetalBridge-Status.md
```

Older and experimental notes:

```text
docs/CollatzCartography.md
docs/CollatzCartography-ja.md
docs/IMPLEMENTATION_REPORT_20260130.md
docs/AUXILIARY_LEMMA_COMPLETION_20260130.md
docs/SORRY_CLEANUP_PROGRESS_20260130.md
```

Petal-side companion:

```text
../Petal/docs/Petal-CollatzBridge.md
```

## What Was Achieved At Checkpoint 100?

Checkpoint 100 closes a finite, natural-valued observation layer.

The important Lean aliases are:

```lean
sourcePow2Distribution_total
tailPow2Distribution_total
pow2ChannelFlow_of_pointwise
```

They summarize earlier technical theorems:

```lean
orbitWindowResidueCountPow2_sum_eq_window
orbitWindowResidueCountPow2Tail_sum_eq_window
orbitWindowResidueCountPow2_le_tail_of_pointwise
```

The mathematical point is simple:

```text
Every label in a finite window occupies exactly one residue channel.
If a pointwise transition sends one channel into another channel,
then the occupation count of the source channel is bounded by the
occupation count of the target shifted-tail channel.
```

This is not yet a proof of Collatz termination.  It is a verified framework
for talking about finite channel mass and its movement under the accelerated
map.

## Next Direction

The next natural layer is a finite ratio layer, but still using natural-number
inequalities:

```text
2 * count <= k
countA + countB <= k
m <= count
```

This avoids division by zero and coercion overhead.  Rational or real
frequencies can be introduced later if the finite inequality layer repeatedly
needs them.

Checkpoint 101 begins that layer with:

```lean
AtMostHalf
AtMostRatioNat
orbitWindowRetentionMassPow2
orbitWindowRetentionMassPow2Tail
orbitWindowRecoverySiblingMassPow2
orbitWindowContinuationSiblingMassPow2
```

See:

```text
docs/Collatz-FiniteRatioRetention-101.md
```

Checkpoint 102 then turns the named retention channels into a recursive
two-adic decomposition:

```lean
mod_pow2_succ_eq_left_or_right_of_mod_pow2_eq
pow2ResidueIndicator_refine_succ
orbitWindowResidueCountPow2_refine_succ
orbitWindowRetentionMass_split
orbitWindowRecoverySiblingMassPow2_le_retentionMass
orbitWindowContinuationSiblingMassPow2_le_retentionMass
```

The key reading is:

```text
retention mass at depth r
  = recovery sibling mass at depth r+1
    + continuation sibling mass at depth r+1
```

This is still finite `Nat` counting.  It does not use probability, limits, or
real-valued density.  It gives the next local tool for saying that a long
low-peeling path must keep occupying a nested retention cylinder.

Checkpoint 103 closes the shifted-tail counterpart:

```lean
orbitWindowResidueCountPow2Tail_refine_succ
orbitWindowRetentionMassPow2Tail_split
orbitWindowRecoverySiblingMassPow2Tail_le_retentionMassTail
orbitWindowContinuationSiblingMassPow2Tail_le_retentionMassTail
orbitWindowContinuationMass_forces_tailRetention
orbitWindowRecoveryMass_forces_tailRecovery
orbitWindowContinuationMass_le_tailRecovery_add_tailContinuation
```

The source and shifted-tail windows now both have the same recursive Petal
split.  This makes later mass-flow statements readable as:

```text
source continuation mass
  <= shifted-tail retention mass
  = shifted-tail recovery mass + shifted-tail continuation mass
```

Checkpoint 104 adds the first finite half criterion layer:

```lean
atMostHalf_continuation_of_continuation_le_recovery
atMostHalf_tailContinuation_of_tailContinuation_le_tailRecovery
atMostHalf_continuation_of_retention_le_two_recovery
atMostHalf_tailContinuation_of_tailRetention_le_two_tailRecovery
continuation_atMostRatio_one_one_retention
tailContinuation_atMostRatio_one_one_retention
orbitWindowContinuationMass_tailBudget
```

This still does not prove contraction.  It records exactly what local comparison
is enough to obtain a finite `AtMostHalf` statement.

Checkpoint 105 names that missing local comparison as a first-class predicate:

```lean
RecoveryDominatesContinuation
TailRecoveryDominatesContinuation
RecoveryCoversHalfRetention
TailRecoveryCoversHalfRetention
RecoveryDominatesOnRange
TailRecoveryDominatesOnRange
```

These are deliberately hypothesis packages.  They mark the exact gap between
the current finite budget calculus and a future structural contraction
argument.

Checkpoint 106 adds the complementary failure-pressure layer:

```lean
MoreThanHalf
atMostHalf_or_moreThanHalf
recoveryDominates_or_continuationOutruns
tailRecoveryDominates_or_tailContinuationOutruns
moreThanHalf_continuation_of_continuationOutruns
moreThanHalf_tailContinuation_of_tailContinuationOutruns
```

This turns each local comparison into a finite case split:

```text
recovery dominates continuation
  -> continuation is at most half of retention

continuation outruns recovery
  -> continuation is more than half of retention
```

The new layer still does not assert that either branch is globally preferred.
It makes the failure branch measurable: if dominance fails, the obstruction is
not vague; it is strict more-than-half continuation pressure inside the
retention cylinder.

Checkpoint 107 packages repeated pressure over a finite depth range:

```lean
MoreThanHalfOnRange
SourceContinuationPressureOnRange
TailContinuationPressureOnRange
sourceContinuationPressure_of_outRunsOnRange
tailContinuationPressure_of_outRunsOnRange
sourceContinuationPressureDepthCount
tailContinuationPressureDepthCount
```

The added count theorems show that an all-pressure range fills the whole
depth-mode count:

```lean
sourceContinuationPressureDepthCount_eq_len_of_pressureOnRange
tailContinuationPressureDepthCount_eq_len_of_pressureOnRange
```

This moves the observation from local mass pressure to finite depth-profile
counting.

Checkpoint 108 closes the mixed depth-mode distribution:

```lean
sourceContinuationControlledDepthCount
tailContinuationControlledDepthCount
sourceContinuationControlledDepthCount_add_pressureDepthCount_eq_len
tailContinuationControlledDepthCount_add_pressureDepthCount_eq_len
```

The reading is:

```text
controlled depth count + pressure depth count = depth range length
```

This is the depth-mode analogue of the finite residue distribution from
checkpoint 100.

Checkpoint 109 adds finite depth-pressure frequency predicates:

```lean
SourcePressureAtMostHalfOnDepthRange
SourcePressureMoreThanHalfOnDepthRange
TailPressureAtMostHalfOnDepthRange
TailPressureMoreThanHalfOnDepthRange
```

The frequency predicates are connected back to the mixed distribution:

```text
pressure is at most half
  <-> pressureDepthCount <= controlledDepthCount

pressure is more than half
  <-> controlledDepthCount < pressureDepthCount
```

The checkpoint also closes the reverse local direction:

```lean
continuationOutruns_of_moreThanHalf_continuation
tailContinuationOutruns_of_moreThanHalf_tailContinuation
```

Checkpoint 110 connects descriptive pressure counts to cause-side failure
counts:

```lean
sourceContinuationOutrunsDepthCount
tailContinuationOutrunsDepthCount
sourceContinuationOutrunsDepthCount_eq_pressureDepthCount
tailContinuationOutrunsDepthCount_eq_pressureDepthCount
```

It also records local equivalences:

```text
ContinuationOutrunsRecovery
  <-> MoreThanHalf continuation retention

RecoveryDominatesContinuation
  <-> AtMostHalf continuation retention
```

Checkpoint 111 closes the dominance side:

```lean
sourceRecoveryDominanceDepthCount
tailRecoveryDominanceDepthCount
sourceRecoveryDominanceDepthCount_eq_controlledDepthCount
tailRecoveryDominanceDepthCount_eq_controlledDepthCount
sourceCauseSideDepthCount_add_eq_len
tailCauseSideDepthCount_add_eq_len
```

The depth-mode distribution now has both presentations:

```text
descriptive:
  controlledDepthCount + pressureDepthCount = len

cause-side:
  dominanceDepthCount + outrunsDepthCount = len
```
