# report-petal-152

Checkpoint: 152

Subject: return to the main root, `PressureAccounting`, after closing the
OneCycle valuation-flow interruption.

## Summary

The main-root implementation advanced the explicit accounted-interval API.

The new surface keeps the current design deliberately narrow:

```text
explicit intervals
  -> adjacent sorted-before predicate
  -> pairwise disjoint family
  -> budget wrapper
```

It also adds a first-class obstruction window:

```text
not adjacent-sorted
  -> sorted-before failure witness
```

This gives later checkpoints a place to attach negative evidence without
claiming coverage, maximality, or global Collatz behavior.

## Implemented Additions

### Sorted Constructor

Added a direct cons constructor for adjacent sorted-before lists:

```lean
theorem sourcePressureAccountedIntervalListSortedBefore_cons
```

This makes recursive sorted-family construction easier to use.

### Sorted Family Constructors

Added named family constructors:

```lean
def sourcePressureAccountedIntervalFamily_sorted_nil
def sourcePressureAccountedIntervalFamily_sorted_singleton
def sourcePressureAccountedIntervalFamily_sorted_cons
```

These are wrappers around the existing explicit family constructors.  They do
not generate intervals and do not assert coverage.

### Tail Disjointness

Added:

```lean
theorem sourcePressureAccountedInterval_before_all_tail_of_sortedBefore
```

This records that the head interval of an adjacent-sorted explicit list is
disjoint from every tail interval.

### Failure API

Added:

```lean
def SourcePressureAccountedIntervalListSortedBeforeFailsAt
def SourcePressureAccountedIntervalListHasSortedBeforeFailure
```

The failure predicate is an obstruction tool for explicit lists.  It says that
some neighboring pair fails the sorted-before condition.

### Pair-Level Obstruction Facts

Added:

```lean
theorem sourcePressureAccountedIntervalListHasSortedBeforeFailure_pair
theorem sourcePressureAccountedIntervalListSortedBefore_pair_iff
theorem sourcePressureAccountedIntervalListHasSortedBeforeFailure_pair_iff
```

For a two-element list, sortedness and failure are exact negations of the same
neighboring relation.

### Explicit List Dichotomy

Added:

```lean
theorem sourcePressureAccountedIntervalList_sorted_or_failure
```

Every explicit list is either adjacent-sorted or carries a first-class
sorted-before failure.

This is a local list-level dichotomy only.  It is not a coverage theorem.

### Budget Wrappers

Added:

```lean
theorem sourcePressureAccountedIntervalFamily_sorted_singleton_sum_le_neg_one
theorem sourcePressureAccountedIntervalFamily_sorted_cons_sum_le_neg_length
```

These preserve the existing pressure-budget bounds through the new sorted
family constructors.

## Mathematical Reading

The pressure-accounting layer now has two complementary modes:

```text
sorted mode:
  intervals are explicitly ordered by before-relations
  -> pairwise disjoint family
  -> additive negative budget bound

failure mode:
  some adjacent before-relation fails
  -> obstruction evidence is visible
```

This matches the current Petal/Collatz workflow: prove what can be cleanly
budgeted, and make failure conditions explicit when the clean route breaks.

## Non-Claims

This checkpoint does not prove maximality of an interval family.

This checkpoint does not prove uniqueness of sorted representations.

This checkpoint does not prove that the intervals cover an orbit prefix.

This checkpoint does not prove global convergence or cycle exclusion beyond
the already isolated one-cycle boundary facts.

## Verification

Passed:

```text
lake build DkMath.Collatz.PetalBridge.PressureAccounting
lake build DkMath.Collatz.PetalBridge
rg -n "\bsorry\b" lean/dk_math/DkMath/Collatz/PetalBridge/PressureAccounting.lean
git diff --check
```

The `rg` check returned no matches.

The build still reports the existing unrelated warning from:

```text
DkMath.NumberTheory.ZsigmondyCyclotomicResearch
```

That warning is outside this checkpoint.

## Next Implementation Direction

The next stable target is to connect this explicit-list obstruction API to the
next Collatz pressure object:

```text
adjacent failure
  -> overlapping / non-before interval evidence
  -> obstruction comment or theorem near the caller
```

If this closes cleanly, the following step should be a small bridge from sorted
explicit families to the orbit-window objects already present in the Collatz
PetalBridge tree.
