# Report Petal 113

## Summary

Checkpoint 113 begins the bridge from cause-side frequency toward height and
drift data in `DkMath.Collatz.PetalBridge`.

The checkpoint does not yet prove a new `sumS` lower bound.  It closes the
front half of the route:

```text
outruns-heavy
  -> pressure-heavy
  -> controlled/pressure count imbalance
  -> positive pressure count
```

This gives later height arguments a small API surface that avoids unfolding
the frequency predicates.

## Lean Additions

Cause-side high frequency to descriptive pressure high frequency:

```lean
sourcePressureMoreThanHalf_of_outrunsMoreThanHalf
tailPressureMoreThanHalf_of_outrunsMoreThanHalf
```

Cause-side high frequency to descriptive count imbalance:

```lean
sourceControlledDepthCount_lt_pressure_of_outrunsMoreThanHalf
tailControlledDepthCount_lt_pressure_of_outrunsMoreThanHalf
```

Positive pressure-count consequences:

```lean
sourcePressureDepthCount_pos_of_outrunsMoreThanHalf
tailPressureDepthCount_pos_of_outrunsMoreThanHalf
```

Partition-consumption tests for the recovery side:

```lean
sourceDominanceDepthCount_pos_of_outrunsAtMostHalf_and_not_all_outruns
tailDominanceDepthCount_pos_of_outrunsAtMostHalf_and_not_all_outruns
```

## Implementation Note

The review suggested a dominance-positive lemma with an explicit `0 < len`
hypothesis.  Lean showed that this hypothesis is unnecessary once we assume:

```text
outrunsDepthCount < len
```

That assumption already rules out the empty-range obstruction.  The final
theorem names therefore use `not_all_outruns` rather than `len_pos`.

This is a small API improvement: callers only need to prove the operational
condition that the failure side does not fill the range.

## Search Findings

The existing height and `sumS` bridge hooks are concentrated in
`DkMath.Collatz.PetalBridge`.

Direct height-sum bridge:

```lean
orbitWindowHeightSeq_sum_eq_sumS
```

Finite layer-cake and count lower bounds:

```lean
orbitWindowHeightSeq_sum_ge_countGe_mul_threshold
orbitWindowHeightSeq_sum_ge_countGe_one_add_countGe_two
orbitWindowHeightSeq_sum_ge_sum_countGe_range
orbitWindowHeightSeq_sum_ge_window_add_sum_countGe_tail
```

Practical second-layer lower bounds:

```lean
orbitWindowHeightSeq_sum_ge_window_add_of_countGe_two_ge
orbitWindowHeightSeq_sum_ge_window_add_tailCountGe_two
orbitWindowHeightSeq_sum_ge_succ_window_add_tailCountGe_two
```

Residue-to-height hooks:

```lean
orbitWindowHeightCountGe_two_eq_residueCount_mod4_eq_one
orbitWindowHeightCountGeTail_two_eq_tailResidueCount_mod4_eq_one
orbitWindowHeightCountGe_three_eq_residueCount_mod8_eq_five
orbitWindowHeightSeq_sum_ge_window_add_of_residue_mod4_count_ge
orbitWindowHeightSeq_sum_ge_window_add_countGe_two_add_of_residue_mod8_count_ge
```

## Mathematical Reading

Checkpoint 113 proves that a cause-side failure-heavy range is already visible
as a descriptive pressure-heavy range, and that it forces pressure depths to
outnumber controlled depths.

This is still a depth-mode statement.  The next missing bridge is:

```text
pressure-heavy depth range
  -> lower bound on source or tail height-count mass
```

Once that bridge exists, the current height API can turn it into a `sumS`
lower bound.

## Documentation Updates

Updated:

```text
DkMath/Collatz/README.md
DkMath/Collatz/docs/Collatz-PetalBridge-Guide.md
DkMath/Collatz/docs/Collatz-PetalBridge-Status.md
```

Added:

```text
DkMath/Collatz/docs/Collatz-FrequencyHeightBridge-113.md
```

## Verification

Passed:

```text
lake build DkMath.Collatz.PetalBridge
lake build DkMath.Collatz.Collatz2K26
rg -n "\bsorry\b" DkMath/Collatz/PetalBridge.lean
git diff --check
```

The no-sorry check returned no matches in `DkMath/Collatz/PetalBridge.lean`.

```text
Known upstream warning during the integration build:
DkMath.NumberTheory.ZsigmondyCyclotomicResearch.lean:152:6 uses sorry.
```

## Next Candidate

The next checkpoint should try a tail-facing height bridge.

Candidate target:

```text
pressure or continuation mass
  -> tail retention / tail residue mass
  -> orbitWindowHeightCountGeTail n k 2 lower bound
  -> sumS n (k + 1) lower bound
```

Relevant existing hooks:

```lean
orbitWindowContinuationMass_forces_tailRetention
orbitWindowContinuationMass_le_tailRecovery_add_tailContinuation
orbitWindowHeightCountGeTail_two_eq_tailResidueCount_mod4_eq_one
orbitWindowHeightSeq_sum_ge_window_add_tailCountGe_two
```

The first experiment should stay in `Nat` and should avoid real drift
estimates until a clean height-count lower bound is available.
