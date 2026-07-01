# Collatz Tail-Facing Height Bridge 114

## Purpose

Checkpoint 114 tests the first direct bridge from source continuation mass to
tail height counts.

The initial target was:

```text
source continuation mass
  -> tail retention
  -> tail height >= 2
  -> sumS lower bound
```

Lean showed that the middle interpretation needs correction.

At parent depth `2`, source continuation mass flows into shifted-tail retention
depth `2`.  That cell is:

```text
3 mod 4
```

and therefore corresponds to:

```text
tail exact height 1
```

not:

```text
tail height >= 2
```

## Meaning-Name Aliases

The checkpoint adds readable aliases for existing mass-flow theorems:

```lean
sourceContinuationMass_le_tailRetentionMass
sourceContinuationMass_le_tailSplitMass
```

These preserve the existing theorem order and make future arguments easier to
read.

## Correct Tail Height Bridge

The safe bridge is:

```lean
tailRetentionMass_depth_two_eq_heightCountEq_one
tailRetentionMass_depth_two_le_heightCountEq_one
sourceContinuationMass_depth_two_le_tailHeightCountEq_one
```

The mathematical reading is:

```text
source continuation mass at parent depth 2
  -> shifted-tail retention at depth 2
  -> shifted-tail 3 mod 4
  -> shifted-tail exact height 1
```

This is a retention/base-layer result, not an extra-peeling result.

## Ruled-Out Route

The tempting route was:

```text
source continuation mass at parent depth 2
  -> shifted-tail height >= 2
  -> k + continuationMass <= sumS n (k + 1)
```

This route is not correct at depth `2`.

The reason is the residue:

```text
tail retention depth 2 = 3 mod 4
```

while:

```text
tail height >= 2 = 1 mod 4
```

So this checkpoint does not produce a new extra `sumS` lower bound.  It
clarifies which tail side the continuation-retention channel occupies.

## Consequence

Checkpoint 114 redirects the next search.

To obtain extra height, the likely routes are:

```text
3 mod 8 delayed-peeling source
recovery sibling channels
deeper continuation branches that later move into a peeling cell
```

The already-proved theorem:

```lean
orbitWindowResidueCountMod8EqThree_delayed_drift
```

is still the model: find a source channel that maps into shifted-tail
`height >= 2`, then consume:

```lean
orbitWindowHeightSeq_sum_ge_window_add_tailCountGe_two
```

## Next Candidate

The next checkpoint should inspect recovery-side or delayed continuation
channels.

Candidate search:

```text
source recovery mass
  -> tail recovery sibling
  -> tail residue 1 mod 4?
  -> tail height >= 2?
```

or:

```text
deeper continuation residue
  -> exact height 1 now
  -> delayed transition later
  -> eventual height >= 2
```

The important outcome of checkpoint 114 is that depth-2 continuation retention
is not the extra-peeling bridge.
