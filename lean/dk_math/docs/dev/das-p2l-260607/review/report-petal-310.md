# cp-310 Universal Signed Drift Classification

## Result

The proof-independent universal endpoint drift now has complete local sign
classification for every nonempty universal payment block.

```text
drift > 0  iff width(start) < width(after endpoint)
drift = 0  iff width(start) = width(after endpoint)
drift < 0  iff width(after endpoint) < width(start)
```

The same signs have direct finite-ledger readings:

```text
drift > 0  iff capacity < complete claim card
drift = 0  iff complete claim card = capacity
drift < 0  iff complete claim card < capacity
```

## Meaning

The universal block ledger can now be used through either of two equivalent
surfaces:

- geometric/orbit surface: width growth, preservation, or decay;
- finite accounting surface: overload, balance, or capacity surplus.

The drift definition itself remains proof-independent, so it can be summed
over future endpoint families without carrying a `Nonempty` witness in the
data.

## Next Boundary

The direct ledger and sign API are complete.  The next substantive branch is
the no-delayed-debt classification and then the canonical endpoint sequence.
The latter must represent adjacent completed blocks explicitly before any
finite-prefix telescope is claimed.

## Validation

```text
lake build DkMath.Collatz.PetalBridge.FloatWindow.UniversalPaymentBlock
```

completed successfully; no new `sorry` or `axiom` was introduced.
