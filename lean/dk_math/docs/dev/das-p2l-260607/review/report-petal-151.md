# Report Petal 151

## Checkpoint

Checkpoint 151 thickened the explicit sorted-family side of source-pressure
accounting and added contradiction-style API around the scaled
`1 -> 4 -> 2 -> 1` one-cycle obstruction.

The implementation continues to avoid the unsafe jumps:

- no maximality,
- no uniqueness of pressure families,
- no coverage,
- no prefix behavior,
- no union accounting,
- no Collatz convergence.

## Sorted-before predicate

File:

```text
DkMath/Collatz/PetalBridge/PressureAccounting.lean
```

Added a recursive adjacent-order predicate:

```lean
def SourcePressureAccountedIntervalListSortedBefore
```

Shape:

```lean
[]              => True
[_]             => True
A :: B :: rest  =>
  SourcePressureAccountedIntervalBefore A B ∧
    SourcePressureAccountedIntervalListSortedBefore (B :: rest)
```

This was chosen instead of `List.Sorted` because it keeps the local adjacent
meaning explicit and matches the project vocabulary around interval addresses.

## Sorted-before to pairwise-disjoint

Added small cases:

```lean
theorem sourcePressureAccountedIntervalListSortedBefore_nil
theorem sourcePressureAccountedIntervalListSortedBefore_singleton
theorem sourcePressureAccountedIntervalListPairwiseDisjoint_of_sortedBefore_nil
theorem sourcePressureAccountedIntervalListPairwiseDisjoint_of_sortedBefore_singleton
theorem sourcePressureAccountedIntervalListPairwiseDisjoint_of_sortedBefore_pair
```

Added the bridge lemma:

```lean
theorem SourcePressureAccountedIntervalBefore.before_all_of_sorted_tail
```

This turns:

```text
A before B
B :: rest is adjacent-sorted
```

into:

```text
A before every element of B :: rest
```

Then the full theorem was proved:

```lean
theorem sourcePressureAccountedIntervalListPairwiseDisjoint_of_sortedBefore
```

Meaning:

```text
adjacent sorted-before list
  -> pairwise disjoint accounted-interval list
```

Non-meaning:

```text
sorted-before does not imply coverage of all positive pressure depths.
```

## Family from sorted-before

Added:

```lean
def sourcePressureAccountedIntervalFamily_of_sortedBefore
```

This packages a sorted explicit list as:

```lean
SourcePressureAccountedIntervalFamily
```

using the derived pairwise-disjoint theorem.

Added budget wrapper:

```lean
theorem sourcePressureAccountedIntervalFamily_of_sortedBefore_sum_le_neg_length
```

This is still only the explicit list budget.  The sorted hypothesis is used to
construct the family, not to claim global decomposition.

## OneCycle contradiction API

File:

```text
DkMath/Collatz/PetalBridge/OneCycle.lean
```

Added:

```lean
theorem collatz_scaled_one_cycle_no_wrong_height
theorem collatz_scaled_one_cycle_no_wrong_base
theorem collatz_scaled_one_cycle_iff
theorem one_four_two_one_petal_scaled_cycle_unique
```

The iff theorem accepted:

```lean
theorem collatz_scaled_one_cycle_iff
    {n h : ℕ}
    (hn : 0 < n) :
    3 * n + 1 = 2 ^ h * n ↔ n = 1 ∧ h = 2
```

This remains only a theorem about the equation:

```text
3 * n + 1 = 2^h * n
```

It does not prove general Collatz cycle uniqueness and does not prove
Collatz convergence.

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

This is outside the checkpoint files.

## Inference for next checkpoint

The next safe family-side target is still not coverage.  A useful next layer
would be sorted-family convenience constructors that preserve explicitness:

```lean
sourcePressureAccountedIntervalFamily_sorted_pair
sourcePressureAccountedIntervalFamily_sorted_cons
sourcePressureAccountedIntervalListSortedBefore_cons_of_before_all
```

A second possible route is to expose contradiction-style APIs for sorted
families:

```text
if adjacent sortedness fails at some neighbor, the list cannot use
sourcePressureAccountedIntervalFamily_of_sortedBefore
```

That would keep failure evidence first-class, matching the obstruction style
used elsewhere in PetalBridge.

On the OneCycle side, the next thin alias could be a "no scaled boundary except
unit" theorem that presents `collatz_scaled_one_cycle_iff` in Petal language.
This is only worthwhile if downstream files start preferring prose-facing names
over the raw equation name.
