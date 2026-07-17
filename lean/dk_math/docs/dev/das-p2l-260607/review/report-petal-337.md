# Petal / Collatz Implementation Report cp-337

## Status

`COMPLETE WITH EXPLICIT BOUNDARY`

The source-age horizon arithmetic requested by cp-337 is now implemented in:

- `DkMath.Collatz.PetalBridge.FloatWindow.CanonicalSourceAgeHorizon`
- `python/Collatz/PetalBridge/source_age_frontier_audit.py`

No `sorry` was added.  The public `FloatWindow` import surface includes the new
Lean module.

## Lean results

### Concrete obstruction at horizon zero

The bounded search found `(n,m) = (59,0)`, and Lean independently verifies:

```text
CanonicalSaturatedBorderBlock fiftyNineSaturatedOdd 0
```

Consequently the previously conditional obstruction is now unconditional:

```text
not_forall_sourceAgeFrontierIncrement_zero_nonpos
```

Thus horizon-zero pointwise nonpositivity is formally false.

### Exact queue compatibility

At `H = 0`, frontier flow is both:

```text
demand - actual consumed service
queueBeforeBlock (m+1) - queueBeforeBlock m
```

A saturated block raises the queue by exactly one.

### Finite-facing certificate

`CanonicalFiniteSourceAgeFrontierPotentialCertificate` replaces the old
all-time prefix assumption by a finite-state initial maximum:

```text
forall s : Signature, potential s <= potential (signature 0)
```

It forgets to the compatibility certificate and preserves the exact chain to
uniform source age, queue bounds, and endpoint-width bounds.  Signature,
transition, and potential remain externally supplied and cannot be defined
from the target deficit without circularity.

### Exact horizon derivative

The carry indicator is connected to singleton carrier cardinality in both
`Nat` and `Int` forms.  In the mature regime `H < blockStart m`:

```text
oldCarrier (H+1) m = erase (blockStart m - H - 1) (oldCarrier H m)

deficit (H+1) m
  = deficit H m - carryIndicator (blockStart m - H - 1)
```

The early cutoff regime is separate: both carriers are empty and the deficit
is unchanged.

For crossing flow, sliding the horizon exchanges exactly two boundaries:

```text
card crossing(H+1,m) - card crossing(H,m)
  = indicator(blockStart m - H - 1)
      - indicator(blockStart (m+1) - H - 1)
```

The same identity holds for frontier increments because actual consumption is
independent of the horizon.

### Horizon-one audit

For positive block start, `crossing(1,m)` decomposes exactly into:

```text
predecessor source
union
current block claims with the final source erased
```

Hence a mature saturated block satisfies:

```text
frontierIncrement 1 m = indicator(blockStart m - 1)
```

The positivity hypothesis is necessary.  The checked root `59` proves that at
the origin the frontier is zero while the Nat-subtracted predecessor indicator
is one.  The unrestricted candidate is therefore formally false; this is a
real Nat-boundary alias, not a proof artifact.

### Origin-to-crossing assignment and window sums

`canonicalAgeCrossingBlockOfSource n H i` uses the existing unique canonical
block coverage of `i + H`.  Under the exact non-underflow condition, a
carry-two source belongs to that block's age crossing carrier.

Finite frontier windows telescope exactly:

```text
windowSum H q L = deficit H (q+L) - deficit H q
```

Length zero, one, and two interfaces are available.

### New successor fact

A saturated block leaves one queued claim.  Since every successor has at least
one service slot, Lean proves:

```text
CanonicalSaturatedBorderBlock.successor_queueConsumed_pos
```

If successor endpoint drift is strictly negative, the extra service is
actually consumed and the exact horizon-zero two-block window is nonpositive:

```text
sourceAgeFrontierWindowSum_zero_two_nonpos_of_successor_negative
```

This cannot currently be weakened to nonpositive successor drift.  Zero drift
may consume only current demand and leave the preceding saturated unit unpaid.

## Numerical discovery audit

The deterministic audit covered odd roots through `4095`, at most `256`
canonical blocks, horizons `0..4`, and window lengths `1..8`.

| H | max increment | max prefix | saturated return range | two-block counterexample |
| --- | ---: | ---: | --- | --- |
| 0 | 6 at `(1819,1)` | 7 at `(1819,3)` | 2..9 | `(123,0): [1,0]` |
| 1 | 5 at `(1819,1)` | 6 at `(1819,3)` | 1 | `(927,3): [0,1]` |
| 2 | 6 at `(1819,1)` | 6 at `(1819,3)` | 1 | `(927,3): [0,1]` |
| 3 | 5 at `(1819,1)` | 5 at `(1819,3)` | 1 | `(927,3): [0,1]` |
| 4 | 6 at `(1915,4)` | 5 at `(1819,3)` | 1 | `(927,3): [0,1]` |

These values are finite evidence only.  The `H=0`, root-123 pattern directly
rejects the tempting claim that every saturated `+1` is repaid in two blocks.

## Exact stopping boundary

The conditional positive route is now explicit and intact:

```text
finite noncircular structural certificate for some H
  -> every frontier prefix <= 0
  -> uniform actual source age H
  -> uniform queue bound H
  -> endpoint-width bound bitWidth(n) + H
```

What remains absent is the first item: no structural signature/certificate and
no successful universal horizon have been constructed.  The current successor
grammar proves positive actual consumption and strict-negative two-block
repayment, but its zero-drift and positive-pressure branches do not supply a
uniform short-window actual-consumption lower bound.

## Next implementation

The next honest checkpoint should isolate the unresolved successor branches:

1. characterize the zero-drift successor's exact retained queue unit;
2. search for an actual-consumption lower bound in the positive-pressure
   branch, without replacing consumption by capacity;
3. formulate a finite window certificate only if both branches admit a common
   noncircular potential or repayment invariant.

If no common invariant appears, retain the present exact split and treat the
root-123 zero-drift pattern as the obstruction witness.
