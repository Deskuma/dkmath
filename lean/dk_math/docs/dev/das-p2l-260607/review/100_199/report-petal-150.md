# Report Petal 150

## Checkpoint

Checkpoint 150 implemented the family-constructor layer for explicit source
pressure accounting and added the scaled `1 -> 4 -> 2 -> 1` one-cycle
obstruction as a separate Collatz/PetalBridge file.

The pressure-family work remains intentionally local:

- no maximality,
- no uniqueness,
- no coverage,
- no prefix behavior,
- no union accounting,
- no Collatz convergence.

Disjointness is still an explicit field or hypothesis.

## PressureAccounting additions

File:

```text
DkMath/Collatz/PetalBridge/PressureAccounting.lean
```

Added family constructors:

```lean
def sourcePressureAccountedIntervalFamily_nil
def sourcePressureAccountedIntervalFamily_singleton
def sourcePressureAccountedIntervalFamily_cons
```

These are thin constructors over:

```lean
SourcePressureAccountedIntervalFamily
SourcePressureAccountedIntervalListPairwiseDisjoint
```

The `cons` constructor requires an explicit head-disjointness hypothesis:

```lean
∀ B ∈ F.items, SourcePressureAccountedIntervalsDisjoint A B
```

This keeps the API honest: accounting data alone is not treated as
disjointness evidence.

## Budget corollaries

Added:

```lean
theorem sourcePressureAccountedIntervalFamily_singleton_sum_le_neg_one
theorem sourcePressureAccountedIntervalFamily_cons_sum_le_neg_length
```

The singleton theorem exposes the one-interval `≤ -1` budget at family level.
The cons theorem is a named specialization of the existing family budget:

```lean
sourcePressureAccountedIntervalFamily_sum_le_neg_length
```

## Sorted / before skeleton

Added:

```lean
theorem NatIntervalBefore.trans_like
theorem SourcePressureAccountedIntervalBefore.trans_like
def sourcePressureAccountedIntervalFamily_pair_of_before
```

The pair constructor builds a two-item family from ordered non-overlap:

```lean
[A, B]
```

where `A` lies before `B`.  This is only a sorted-family seed.  It does not
claim that the pair covers a pressure region.

## OneCycle

Created:

```text
DkMath/Collatz/PetalBridge/OneCycle.lean
```

and imported it from:

```text
DkMath/Collatz/PetalBridge.lean
```

Accepted theorem:

```lean
theorem collatz_scaled_one_cycle_eq_one
    {n h : ℕ}
    (hn : 0 < n)
    (hcycle : 3 * n + 1 = 2 ^ h * n) :
    n = 1 ∧ h = 2
```

Supporting and boundary facts were also added:

```lean
theorem collatz_scaled_one_cycle_h_not_ge_three
theorem collatz_scaled_one_cycle_h_ne_zero
theorem collatz_scaled_one_cycle_h_ne_one
theorem collatz_one_four_two_one_scaled_boundary_unique
theorem collatz_one_four_two_one_scaled_boundary_exists
```

Interpretation:

```text
The familiar one-cycle boundary exists at n = 1, h = 2.
It has no positive scaled copy satisfying one accelerated odd step
back to the same odd state.
```

Non-claim:

```text
This does not rule out arbitrary nontrivial Collatz cycles.
This does not prove Collatz convergence.
```

## Verification

Commands run from `lean/dk_math`:

```text
lake build DkMath.Collatz.PetalBridge.PressureAccounting
lake build DkMath.Collatz.PetalBridge.OneCycle
lake build DkMath.Collatz.PetalBridge
```

All passed.

No local sorry hits:

```text
rg -n "\bsorry\b" lean/dk_math/DkMath/Collatz/PetalBridge/PressureAccounting.lean
rg -n "\bsorry\b" lean/dk_math/DkMath/Collatz/PetalBridge/OneCycle.lean
```

Both returned no matches.

Whitespace check:

```text
git diff --check
```

passed.

Known unrelated build warning:

```text
DkMath.NumberTheory.ZsigmondyCyclotomicResearch.lean: declaration uses `sorry`
```

This is pre-existing and outside the checkpoint files.

## Inference for next checkpoint

The safe next move is not coverage.  The next useful Lean surface is an
ordered-family layer that remains explicit:

```text
list is sorted by NatIntervalBefore
sorted adjacent intervals imply pairwise disjointness
sorted accounted interval list can become SourcePressureAccountedIntervalFamily
```

The likely minimal API:

```lean
def SourcePressureAccountedIntervalListSortedBefore

theorem sourcePressureAccountedIntervalListPairwiseDisjoint_of_sortedBefore

def sourcePressureAccountedIntervalFamily_of_sortedBefore
```

This would let future code build larger explicit families from an ordered list
without saying those intervals are maximal or cover the positive region.

For OneCycle, the next small obstruction can be phrased as a negative theorem:

```text
No positive n satisfies 3*n + 1 = 2^h*n for h != 2.
```

This is already derivable from `collatz_scaled_one_cycle_eq_one`; it may be
worth adding only if callers want a contradiction-style API.
