# cp-305 Universal Payment Coordinates

## Implemented

The accepted cp-304 payment-block ledger was retained and its generic shifted
ledger theorem was moved before the specialized block theorem, so the latter
now reuses the public shifted statement directly.

`PaymentBlockBridge.lean` now also provides an integer API:

- `paymentBlockSignedDrift = complete claim card - endpoint capacity`;
- this equals signed width-after minus width-before;
- positive, zero, and negative drift characterize overload, balance, and
  strict capacity surplus respectively.

The height/depth interface is now explicit:

```text
height = 1   iff exact all-ones depth >= 2
height >= 2  iff exact all-ones depth = 1
```

## Universal target layer

Added `DkMath.Collatz.PetalBridge.FloatWindow.UniversalPaymentBlock`.

`orbitPaymentTarget n i = i + orbitExactDepth n i - 1` is defined for every
orbit time.  The pre-existing debt-facing target is definitionally equal to
it.  Lean proves:

- height-one sources target strictly later times;
- extra-height sources target themselves;
- every source targets an actual extra-height slot;
- the finite source fiber at an endpoint has a membership API and a minimum;
- every target has a nonempty source fiber;
- a nonempty source fiber has an extra-height endpoint;
- every delayed growth-debt source lies in the universal source fiber with the
  same target, so the universal start is no later than the debt-supported
  block start.

## Boundary Found

The universal fiber has not been claimed to be a contiguous interval yet.
The remaining mathematical bridge is a reverse exact-depth staircase theorem:
given a source targeting `j`, every intermediate time must be shown to have
the decremented exact depth and the same target.  This is a substantive
closure lemma, not an `Ico` normalization issue.  The source code records this
boundary beside the new API.

## No overclaim

No final allocation of first claims, universal block-family coverage, pressure
conclusion, or convergence conclusion has been added.
