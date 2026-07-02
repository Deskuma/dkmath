# Collatz Gnomon Evaluation - Checkpoint 125

Checkpoint 125 changes the subject of the Collatz reading.

The previous working surface often spoke directly about `3n+1`, height,
retention, continuation, and pressure.  Those theorems remain valid, but the
low-level interpretation is now finer:

```text
Odd gnomon correction
  n -> n + (2n+1) = 3n+1

Power-of-two alignment evaluation
  height = v2 (3n+1)

Residual shape extraction
  residual = (3n+1) / 2^height

Relative scale update
  the residual odd shape becomes the next accelerated odd state
```

The new module is:

```text
DkMath.Collatz.GnomonEvaluation
```

`DkMath.Collatz.PetalBridge` is deliberately not used as the home for this
low-level vocabulary.  `PetalBridge` is already the finite observation window
and pressure/margin surface.  New gnomon and residual-shape primitives should
start in `GnomonEvaluation` unless they explicitly depend on finite windows or
Petal counts.

## Implemented Vocabulary

```lean
OddGnomonLayer n = 2 * n + 1
RawGnomonStep n = n + OddGnomonLayer n
RawGnomonHeight n = v2 (RawGnomonStep n)
RawGnomonResidualShape n = RawGnomonStep n / 2 ^ RawGnomonHeight n
RawGnomonRemainderAtDepth n j = RawGnomonStep n % 2 ^ j
FirstFailedPow2Depth n = RawGnomonHeight n + 1
```

The module keeps the layer integer-valued.  It does not introduce `Real.log`
or real drift estimates.  Those belong to a later translation layer after the
integer shape/margin surface stabilizes.

## Implemented Theorems

The raw gnomon step is the usual Collatz numerator:

```lean
rawGnomonStep_eq_three_mul_add_one
rawGnomonStep_eq_threeNPlusOne
```

The odd layer is the square gnomon:

```lean
square_succ_eq_square_add_oddGnomonLayer
sum_oddGnomonLayer_eq_square
sum_odd_eq_square
square_add_eq_square_add_gnomon_sum
```

The existing accelerated height agrees with the new alignment name:

```lean
rawGnomonHeight_eq_s
```

The remainder profile is zero up to the alignment height:

```lean
rawGnomonRemainderAtDepth_eq_zero_of_le_height
```

This last theorem is the first formal expression of:

```text
j <= height:
  the raw gnomon value is fully aligned with 2^j

j = height + 1:
  the first unresolved residual-shape bit becomes visible
```

## PetalBridge Correction

Checkpoint 125 also records a warning in `PetalBridge`:

```text
carrier nesting is not pressure-prefix nesting
```

Continuation and retention carriers can be nested, but pressure compares two
changing masses:

```text
retention(depth) < 2 * continuation(depth)
```

The selected depths are therefore governed by the sign of the integer margin:

```text
SourcePressureMarginInt = 2 * continuation - retention
```

The new diagnostic predicate is:

```lean
SourcePressurePrefixFailure
```

with bridge:

```lean
sourcePressurePrefixFailure_iff_margin
```

It records the pattern:

```text
shallow margin <= 0
deep margin > 0
```

This is not a contradiction.  It is a pressure island or pressure obstruction:
a deeper residual-shape channel can stand up before a shallower pressure
prefix exists.

## Next Work

The next natural implementation direction is either:

```text
GnomonEvaluation -> residual-shape bridge to T
```

or:

```text
PetalBridge -> pressure failure classification
```

For the second route, Python experiments should classify failures by:

```text
first_failure_pair
shallow_margin
deep_margin
margin_jump
retention_shallow
retention_deep
continuation_shallow
continuation_deep
retention_drop
continuation_drop
```

The Lean side now has a place to store those observations as exact predicates,
without pretending that pressure selection is automatically prefix-shaped.

## Checkpoint 126 Follow-up

Checkpoint 126 closes the first residual-shape bridge.

New theorem:

```lean
rawGnomonResidualShape_eq_T_val
```

The residual shape is now formally identical to the value of the existing
accelerated map:

```text
RawGnomonResidualShape n.val = (T n).val
```

Additional consequences:

```lean
rawGnomonResidualShape_odd
rawGnomonStep_eq_pow_height_mul_residualShape
two_pow_succ_rawGnomonHeight_not_dvd
rawGnomonRemainderAtDepth_firstFailed_ne_zero
```

The exact alignment boundary is now:

```text
j <= RawGnomonHeight n:
  remainder at depth j is zero

j = RawGnomonHeight n + 1:
  remainder is nonzero
```

See:

```text
Collatz-GnomonResidualShape-126.md
```
