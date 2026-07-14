# Petal / Collatz implementation report: cp-314

## Result

Checkpoint cp-314 establishes a repayment-aware endpoint accounting layer in
`DkMath.Collatz.PetalBridge.FloatWindow.UniversalPaymentRepayment`.

The strategic correction is now formal rather than documentary:

- prefix capacity dominance is a no-overdraft condition;
- temporary positive endpoint balance is possible;
- later endpoint capacity must therefore be represented by a distinct forward
  repayment relation.

No theorem in this checkpoint asserts convergence or universal repayment.

## Regression fact: the orbit from seven

Lean proves the first canonical endpoints to be `2` and `3`, and proves their
signed accounting terms to be `+1` and `-1`. Their two-block sum is zero.

Consequently, the first endpoint is a genuine positive excursion and the next
endpoint repays it to the preceding baseline. This is a concrete counterexample
to using global all-prefix no-overdraft as the intended general target.

## Balance and sliding telescope

The new `canonicalEndpointBalanceInt n m` is the signed sum through block `m`.
It is proved equal to

```text
bitWidth(after endpoint m) - bitWidth(initial state).
```

Terminal capacity dominance is equivalent both to nonpositive terminal balance
and to terminal bit width being at most the initial bit width.

For every `q <= m`, the sum over blocks `q..m` telescopes to endpoint width
minus width at the start of block `q`. A claims-minus-capacity form is also
available. This is the finite algebra needed to describe repayment by future
blocks rather than prohibiting an earlier overload.

## Matching directions

The former ordered matching is retained under the explicit compatibility name
`CanonicalEndpointBackwardCreditMatching`. Its slot satisfies

```text
payment block <= claim block.
```

Lean now proves that such a matching implies
`CanonicalEndpointPrefixCapacityDominance`. Thus its exact meaning is fixed: it
is a no-overdraft certificate using capacity already available at the claim's
deadline.

The separate `CanonicalEndpointForwardRepaymentMatching n q r` has distinct
claim and payment horizons and requires

```text
q <= r
claim block <= payment block.
```

Its existence is intentionally not asserted. If supplied, Lean proves that
claims through `q` do not exceed capacity through `r`. The global open property
is stated as `EveryFiniteCanonicalClaimPrefixEventuallyRepayable`.

Carrier equivalences to finite dependent sums were added, with exact `Nat.card`
formulas for cumulative claims and cumulative capacity.

## Depth-coordinate incidence

The canonical source at depth `d` is fixed as

```text
paymentEndpointSeq n k + 1 - d.
```

The following exact facts are proved:

- every canonical block has positive length;
- depth one is the endpoint;
- the depth-one mark is exactly the optional immediate endpoint claim;
- every valid positive recovery fiber is exactly the singleton containing its
  canonical source;
- complete marked claim depths are the depth-image of the complete claim fiber;
- their cardinality is delayed claims plus the optional immediate claim;
- delayed marked depths lie in `Icc 2 blockLength`;
- delayed marked depths equal the existing marked debt-depth carrier;
- their cardinality is exactly the delayed growth-debt count;
- levelled capacity slots are `Icc 2 endpointHeight`, with cardinality exactly
  equal to endpoint extra capacity.

This closes the pressure-fiber to claim-accounting incidence bridge. Claims and
capacity are now both available in depth coordinates.

## Excursion and boundedness surfaces

The implementation adds predicates for positive endpoint excursions, repayment
to the prior baseline, and eventual repayment of every positive excursion.
The seven regression proves one concrete excursion and repayment pair.

A separate uniform balance ceiling is shown to imply the corresponding uniform
canonical endpoint bit-width ceiling. This is a boundedness implication only;
it is not identified with convergence.

## Exact frontier

The remaining obstruction is no longer counting or reindexing. It is the
eligibility rule needed to construct a forward payment map.

The finite data suggests that a delayed claim at depth `d` may use a depth-`d`
capacity slot at its own or a later endpoint, with the immediate claim using a
lowest local level. That rule has not yet been derived from an orbit invariant.
It is therefore not exported as a relation and no forward repayment matching is
claimed.

The next checkpoint should investigate this local invariant against exact
canonical blocks. A valid result must explain both eligibility and injectivity;
cardinality alone is insufficient.

## Verification

Completed during implementation:

```text
lake build DkMath.Collatz.PetalBridge.FloatWindow.UniversalPaymentRepayment
lake build DkMath.Collatz.PetalBridge.FloatWindow
lake build DkMath.Collatz.PetalBridge
lake build DkMath
```

The new module contains no `sorry`. Existing unrelated project warnings remain
outside this checkpoint.
