# Report: Canonical Universal Payment Family, cp-312

## Outcome

The endpoint-aligned universal payment family is now formalized. The new
family layer proves that canonical blocks form a cofinal, disjoint, exhaustive
partition of orbit time, and that their signed ledgers telescope exactly.

This is a complete finite accounting theorem. It is not yet a proof that the
cumulative drift is always nonpositive.

## Local block results

`UniversalPaymentBlock.lean` now proves:

- positive universal signed drift implies a nonempty delayed growth-debt fiber;
- strict bit-width growth across a universal block implies the same;
- the complete carry-two claim fiber is the disjoint union of the delayed
  growth-debt fiber and one optional immediate endpoint claim;
- the corresponding claim-card and signed-drift decompositions are exact;
- universal and debt-supported starts have equal bit width;
- every point between those starts has height one and upper carry one.

Thus the earlier universal prefix is proven to be a zero-width-drift prefix,
not merely inferred from aggregate equality.

## Canonical family layer

Added `UniversalPaymentFamily.lean` and exposed it through the FloatWindow
entry point. It proves:

- `paymentEndpointSeq` is strictly monotone;
- `paymentEndpointSeq n 0 + k <= paymentEndpointSeq n k`, hence cofinality;
- each canonical block equals the universal target fiber of its endpoint;
- distinct canonical blocks are disjoint;
- the recursive union through block `m` is exactly
  `Icc 0 (paymentEndpointSeq n m)`;
- every orbit time belongs to exactly one canonical block;
- extra-height endpoints are exactly and uniquely the values of
  `paymentEndpointSeq`;
- the sum of signed block drifts telescopes to final bit width minus initial
  bit width;
- the same telescope is exposed in delayed-debt, endpoint-claim, and endpoint
  capacity coordinates through `endpointAccountingTerm`.

## Exact mathematical picture

The orbit-time axis now has a Lean-proven canonical partition:

```text
[0 .. e_0], [e_0 + 1 .. e_1], [e_1 + 1 .. e_2], ...
```

where `e_k = paymentEndpointSeq n k`. Every block consists precisely of all
sources sharing target `e_k`. Its endpoint is the unique extra-height point in
that block; all strict interior points have height one.

For every finite endpoint prefix:

```text
sum(block drift)
  = final bit width - initial bit width
  = sum(delayed debt + immediate endpoint claim - endpoint capacity).
```

Therefore the remaining global sign question is isolated exactly: one must
control cumulative delayed-debt multiplicity against cumulative endpoint
capacity. The partition and telescope themselves are no longer missing.

## Genuine obstruction

Stage J asks for block-length pressure contributions of the forms `1` and
`L - d`. Existing pressure modules describe residue-family recovery and
continuation masses, but no current definition identifies those masses with
the canonical endpoint-block staircase. Introducing a function already
defined to equal `if d <= L then 1 else 0` would only restate the requested
formula.

The next honest bridge must first define a pressure contribution by counting
members of `canonicalPaymentBlock` satisfying an existing exact-depth or
continuation predicate. Only then should the `1` / `L - d` formulas be proved.

## Verification

The new and modified modules contain no `sorry` or axioms. Verification gates:

```text
lake build DkMath.Collatz.PetalBridge.FloatWindow.UniversalPaymentBlock
lake build DkMath.Collatz.PetalBridge.FloatWindow.UniversalPaymentFamily
lake build DkMath.Collatz.PetalBridge.FloatWindow
lake build DkMath.Collatz.PetalBridge
lake build DkMath
git diff --check
```
