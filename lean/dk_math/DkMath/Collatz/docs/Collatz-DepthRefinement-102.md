# Collatz Depth Refinement 102

Checkpoint 102 closes the first recursive residue-cell split in
`DkMath.Collatz.PetalBridge`.

The previous checkpoints established:

```text
100:
  finite source/tail residue distributions
  pointwise channel flow -> count inequality

101:
  division-free ratio predicates
  named retention/recovery/continuation masses
```

Checkpoint 102 adds the missing local fact:

```text
a residue cell modulo 2^r splits into exactly two residue cells modulo 2^(r+1)
```

This is the finite Petal recursion layer for Collatz residue observations.

## Pointwise Split

The basic pointwise theorem is:

```lean
mod_pow2_succ_eq_left_or_right_of_mod_pow2_eq
```

For a valid residue `residue < 2^depth`, if

```text
x % 2^depth = residue
```

then at the next depth:

```text
x % 2^(depth+1) = residue
```

or

```text
x % 2^(depth+1) = residue + 2^depth
```

The reverse direction is also available:

```lean
mod_pow2_eq_of_mod_pow2_succ_eq_left_or_right
```

Together these identify the parent cell with the two child cells.

## Indicator Split

The pointwise split is converted into a `0/1` indicator equality:

```lean
pow2ResidueIndicator_refine_succ
```

This theorem is the small API hinge used to lift pointwise residue logic to
finite `countP` statements.

## Count Split

The count-level theorem is:

```lean
orbitWindowResidueCountPow2_refine_succ
```

It states:

```text
count(depth, residue)
  =
count(depth+1, residue)
  + count(depth+1, residue + 2^depth)
```

inside the finite source window.

This is still purely finite `Nat` arithmetic.  It does not use density,
probability, or limits.

## Retention Split

The retention residue at depth `r` is:

```text
2^r - 1
```

The two child residues are:

```text
recovery:
  2^r - 1

continuation:
  2^(r+1) - 1
```

The specialized theorem is:

```lean
orbitWindowRetentionMass_split
```

It states:

```text
orbitWindowRetentionMassPow2 n k r
  =
orbitWindowRecoverySiblingMassPow2 n k r
  + orbitWindowContinuationSiblingMassPow2 n k r
```

This is the main mathematical result of checkpoint 102.

## Immediate Corollaries

Both child masses are bounded by the parent retention mass:

```lean
orbitWindowRecoverySiblingMassPow2_le_retentionMass
orbitWindowContinuationSiblingMassPow2_le_retentionMass
```

The shifted-tail sibling masses also have window bounds:

```lean
orbitWindowRecoverySiblingMassPow2Tail_le_window
orbitWindowContinuationSiblingMassPow2Tail_le_window
```

## Interpretation

The recovery and continuation channels are not independent masses.

They are the two child cells of the same parent retention cylinder:

```text
retention_r
  = recovery_r + continuation_r
```

This is important for later low-peeling arguments.  If a long Collatz segment
keeps avoiding large 2-adic peeling, then its mass must remain inside nested
retention cylinders.  Checkpoint 102 provides the exact finite split needed to
measure that nesting.

## Next Candidate

The next useful layer is a finite contraction or obstruction statement, still
without real-valued frequencies.

Candidate shapes:

```lean
AtMostHalf (orbitWindowContinuationSiblingMassPow2 n k r)
  (orbitWindowRetentionMassPow2 n k r)
```

or a weaker theorem saying that large continuation mass forces a large
shifted-tail retention mass through the existing channel-flow lemmas.

The key strategic point is that such a theorem should now use:

```lean
orbitWindowRetentionMass_split
```

instead of unfolding raw residue counts.
