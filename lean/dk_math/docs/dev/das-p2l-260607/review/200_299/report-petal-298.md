# Petal Checkpoint 298 Report

## Result

The diagnosis-free atomic two-spacing layer is complete.

Added to `PressureState/FiniteWindowPacking.lean`:

```lean
sourcePressureLocalIslandWitness_two_le_val_gap_of_val_lt
sourcePressureLocalIslandWitness_twoSeparated_of_ne
```

Both declarations compile without `sorry`, axioms, new imports, or changes to
the existing canonical/failure API.

## Fact established by Lean

For any two local-island witnesses at the same pressure parameters:

```text
W.val < W'.val  ->  W.val + 2 <= W'.val
```

Consequently, two distinct witnesses satisfy exactly one of the two reusable
separation alternatives:

```text
W.val + 2 <= W'.val
or
W'.val + 2 <= W.val
```

The proof uses only the margin form of `SourcePressureLocalIsland`.
The left witness has nonpositive margin immediately after its center, while
the right witness has positive margin at its center.  If the centers were
consecutive, these statements would concern the same coordinate and
contradict each other.

This is stronger than the earlier sorted-adjacent route.  Two-spacing is not a
property supplied by list sortedness, adjacency, diagnosis, failure resolution,
canonical packing, or finite-window coverage.  It is already intrinsic to the
local-island predicate.

## Subtype equality

The symmetric wrapper closed directly with `Subtype.ext`: equality of witness
values determines equality of the witness subtypes.  No alternate carrier or
extensionality lemma was required.

## Verification

Passed:

```text
lake build DkMath.Collatz.PetalBridge.PressureState.FiniteWindowPacking
lake build DkMath.Collatz.PetalBridge.PressureState
lake build DkMath.Collatz.PetalBridge
git diff --check
```

Confirmed for the edited Lean file:

```text
no new sorry
no new axiom
no new import
no unrelated source modification
```

## Next checkpoint

The next nonvacuous packing layer can now be finite-set based:

1. image `sourcePressurePositiveWitnessesInWindow` under
   `W |-> r + W.val`;
2. prove image cardinality equals witness cardinality by subtype-value
   injectivity;
3. transport the direct two-spacing theorem to center coordinates;
4. apply `finset_card_le_half_window_add_one_of_twoSeparated`.

That route should produce the direct half-window density bound with no
sortedness, diagnosis, canonical family, or unresolved-family term.

## Autonomous continuation completed

The instruction explicitly permitted continuing until the route closed or met
a genuine obstruction.  The implementation therefore continued beyond the
atomic cp-298 theorem.

### Diagnosis-free finite-window local Big

Added:

```lean
sourcePressurePositiveWitnessCentersInWindow
sourcePressurePositiveWitnessCentersInWindow_card_eq
sourcePressurePositiveWitnessCentersInWindow_twoSeparated
sourcePressurePositiveWitnesses_card_le_half_window_add_one_direct
sourcePressurePositiveWitness_next_nonpos
sourcePressurePositiveWitnesses_card_le_nonposPositions_add_one_direct
sourcePressurePositiveWitnesses_localBig_direct
```

The resulting direct local Big has no sortedness, adjacency, diagnosis,
canonical-family, coverage, or unresolved-family hypothesis.  Its two bounds
are:

```text
positive centers <= (hi - lo) / 2 + 1
positive centers <= nonpositive positions + 1
```

The `+1` is exactly the possible center at the right endpoint `hi`; every
strictly earlier center injects into its nonpositive successor coordinate.

### Upper/Float/Dyadic module tree

New public modules:

```text
DkMath.Collatz.PetalBridge.UpperWindow
DkMath.Collatz.PetalBridge.FloatWindow
DkMath.Collatz.PetalBridge.FloatWindow.Core
DkMath.Collatz.PetalBridge.FloatWindow.WidthBalance
DkMath.Collatz.PetalBridge.FloatWindow.DyadicFloat
DkMath.Collatz.PetalBridge.FloatWindow.OrbitBalance
DkMath.Collatz.PetalBridge.FloatWindow.PatternLedger
```

`UpperWindow` is a searchable public facade.  `FloatWindow` is the aggregate
entry point.  `DyadicFloat` is an exact natural-number observation and does not
use IEEE floating-point arithmetic.

### Exact upper-window core

Implemented:

```text
bitWidth
upperCarry3n1
lowerWindow3n1
stateUpperCarry
threeNPlusOne_eq_upperCarry_mul_add_lower
lowerWindow3n1_lt_pow
stateUpperCarry_one_or_two
bitWidth_threeNPlusOne_eq_bitWidth_add_upperCarry
```

Thus a positive state has own-width carry exactly `1` or `2`, and the raw
`3*n+1` word gains exactly that many binary-width positions.

### Exact width balance

The central theorem now exists:

```text
bitWidth n + stateUpperCarry n
  = s(n) + bitWidth (T n)
```

The factorization through the accelerated map and the power-of-two width law
are separately exposed.  Width growth is completely classified:

```text
bitWidth n < bitWidth (T n)
  <-> stateUpperCarry n = 2 and s(n) = 1
```

Height at least two therefore prevents width growth.

### Orbit ledger

The one-step identity telescopes exactly:

```text
sumS(n,k) + bitWidth(iterateT k n)
  = bitWidth(n) + sumUpperCarry(n,k)
```

Since each carry is one or two:

```text
sumUpperCarry(n,k) = k + carryTwoCount(n,k)
```

Combining them gives the finite exact ledger:

```text
sumS(n,k) + finalWidth
  = initialWidth + k + carryTwoCount(n,k)
```

### Dyadic observation and residue ledger

`DyadicFloatObservation` records exact width, upper prefix, lower suffix,
middle Gap, carry, and lower height.  The middle Gap is zero whenever the upper
and lower window sizes cover the word width, and its raw candidate capacity is
then one.

The first pattern bridge is also fixed:

```text
width growth -> n mod 8 = 3 or n mod 8 = 7
```

Consequently the `1 mod 8` and `5 mod 8` channels cannot increase width.

## New frontier

The immediate algebraic route is no longer blocked.  The next independent
mountains are:

1. symbolic Mersenne/all-ones boundary formulas;
2. delayed-payment accounting for the `3 mod 8` growth branch;
3. isolation and counting of the continuing `carry 2 and 7 mod 8` reservoir;
4. compatibility/cardinality theorems for upper/lower windows, beyond the
   current zero-Gap capacity observation.

These require new quantitative bridges rather than another thin wrapper, so
they form the next coherent checkpoint.

## Extended validation

Additionally passed:

```text
lake build DkMath.Collatz.PetalBridge.FloatWindow.Core
lake build DkMath.Collatz.PetalBridge.FloatWindow.WidthBalance
lake build DkMath.Collatz.PetalBridge.FloatWindow.DyadicFloat
lake build DkMath.Collatz.PetalBridge.FloatWindow.OrbitBalance
lake build DkMath.Collatz.PetalBridge.FloatWindow.PatternLedger
lake build DkMath.Collatz.PetalBridge.FloatWindow
lake build DkMath.Collatz.PetalBridge
```

All newly added Lean files are free of `sorry` and `axiom` declarations.
