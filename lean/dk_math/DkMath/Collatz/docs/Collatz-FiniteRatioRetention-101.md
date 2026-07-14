# Collatz Finite Ratio And Retention Mass

## Checkpoint 101 Summary

Checkpoint 101 starts the next layer after finite channel flow.

Checkpoint 100 closed:

```text
source distribution
tail distribution
pointwise transition -> count-level flow
```

Checkpoint 101 introduces the first ratio vocabulary, but deliberately keeps it
inside `Nat` inequalities.

The central decision is:

```text
do not define count / k yet
```

Instead, finite ratio statements are represented as multiplication
inequalities.

## Division-Free Ratio Witnesses

The basic half-window witness is:

```lean
AtMostHalf count k
```

meaning:

```text
2 * count <= k
```

The general finite ratio witness is:

```lean
AtMostRatioNat num den count k
```

meaning:

```text
den * count <= num * k
```

This reads like:

```text
count / k <= num / den
```

but no division appears in Lean.

## Why Not Use `ℚ` Or `ℝ` Yet?

The Nat form is intentionally conservative.

It avoids:

```text
k = 0 division problems
coercion overhead
unnecessary imports
premature analytic interpretation
```

This is aligned with the current PetalBridge layer, which is still finite:

```text
finite window
finite count
finite channel-flow inequality
```

## Retention Mass

The all-ones residue cell at depth `r` is the retention cell:

```text
2^r - 1
```

The source retention mass is:

```lean
orbitWindowRetentionMassPow2 n k r
```

definitionally:

```text
orbitWindowResidueCountPow2 n k r (2^r - 1)
```

The shifted-tail retention mass is:

```lean
orbitWindowRetentionMassPow2Tail n k r
```

definitionally:

```text
orbitWindowResidueCountPow2Tail n k r (2^r - 1)
```

Both are bounded by the window size:

```lean
orbitWindowRetentionMassPow2_le_window
orbitWindowRetentionMassPow2Tail_le_window
```

## Recovery And Continuation Sibling Mass

At parent depth `r`, the next deeper layer has two child cells relevant to the
retention branch:

```text
recovery child:
  depth r + 1, residue 2^r - 1

continuation child:
  depth r + 1, residue 2^(r+1) - 1
```

The source masses are:

```lean
orbitWindowRecoverySiblingMassPow2
orbitWindowContinuationSiblingMassPow2
```

The shifted-tail recovery and continuation masses are:

```lean
orbitWindowRecoverySiblingMassPow2Tail
orbitWindowContinuationSiblingMassPow2Tail
```

Window bounds are currently fixed for the source sibling masses:

```lean
orbitWindowRecoverySiblingMassPow2_le_window
orbitWindowContinuationSiblingMassPow2_le_window
```

## Mass-Name Channel Flow

The existing recursive two-adic channel-flow theorems now have mass-name
readings.

Recovery:

```lean
orbitWindowRecoverySiblingMass_succ_le_tailRecoverySiblingMass
```

Continuation:

```lean
orbitWindowContinuationSiblingMass_succ_le_tailRetentionMass
```

The continuation theorem says:

```text
source continuation sibling at parent depth r + 1
  <= shifted-tail retention mass at depth r + 1
```

This is the first named bridge from channel flow into retention mass language.

## Deferred Split Theorem

The desired parent-to-children split is:

```text
RetentionMass(r)
  = RecoverySiblingMass(r) + ContinuationSiblingMass(r)
```

More generally, a residue cell at depth `d` should refine into two child cells
at depth `d + 1`:

```text
Count(d, residue)
  = Count(d+1, residue)
    + Count(d+1, residue + 2^d)
```

This is not added in checkpoint 101.  It is the next natural theorem target.

The expected proof route is:

```text
prove a pointwise residue refinement lemma
lift by induction over k using count successor formulas
specialize to residue = 2^r - 1
```

## Next Direction

The next checkpoint should attempt:

```lean
orbitWindowResidueCountPow2_refine_succ
```

or directly:

```lean
orbitWindowRetentionMass_split
```

If the general refinement theorem is too heavy, the retention-specific split
with hypothesis `1 <= r` is the better first target.
