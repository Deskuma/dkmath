# Petal / FloatWindow implementation report - checkpoint 334

## Result

This checkpoint replaces scalar source-coverage language by an actual
source-bearing FIFO queue and audits the first upper-boundary refinement of the
fixed low signature.

The two routes now have precise boundaries:

1. the source-age route has a temporally coherent owned queue whose cardinality
   agrees exactly with the existing scalar queue;
2. the fixed-low signature remains impossible under every finite coarsening,
   and the first top-two-bit refinement is also rejected by an exact positive
   projected cycle at depth `r = 1`.

The positive conclusion remains conditional.  Lean proves that a uniform
actual source-age bound implies uniform queue and endpoint-width bounds.  It
does not prove that such a uniform age bound exists.

## Cardinal-only correction from checkpoint 333

The cp-333 predicate has been given the precise name

```text
CanonicalOutstandingQueueCardCoveredByRecentSourceClaims n H.
```

It states only that the scalar outstanding count is no larger than the number
of recent carry-two source addresses.  It does not match outstanding claims to
those sources and does not preserve source identity.  The former name

```text
CanonicalOutstandingQueueCoveredByRecentSourceClaims
```

remains as a compatibility abbreviation, with this limitation documented at
the definition site.

The existing scalar consequences are unchanged:

```text
card coverage
  -> canonical queue upper bound H
  -> endpoint-width upper bound bitWidth(n) + H.
```

## Exact block source carriers

`canonicalBlockClaimSourceCarrier n k` is the set of carry-two source times in
the exact canonical block interval

```text
[canonicalBlockStartTime n k, canonicalBlockStartTime n (k + 1)).
```

Lean proves:

```text
card block carrier = canonicalQueueDemand n k;
every member is in the exact block interval;
every member satisfies CarryTwoDebtAt n;
distinct block carriers are disjoint.
```

This carrier supplies source identities to the recursive queue instead of
rematching an endpoint count against an unrelated historical window.

## Generic oldest-first queue

The new `OldestFirstQueue.lean` is independent of Collatz.  For a finite set of
natural-number source times, `eraseOldestN c s` removes at most `c` least
members and `consumedOldestN c s` records exactly the removed members.

The generic API proves:

```text
eraseOldestN c s subset s;
card (eraseOldestN c s) = card s - c;
card (consumedOldestN c s) = min c s.card;
consumed and remaining sets are disjoint;
consumed union remaining = s;
every consumed source <= every remaining source.
```

The comparison theorem

```text
exists_le_of_card_eq_card_eraseOldestN
```

also proves the required finite minimax statement.  If `t` is any subset of
the original carrier with the same cardinality as the FIFO remainder, then for
every FIFO-retained source `y`, `t` contains a source `x <= y`.  Therefore a
different same-capacity policy cannot make every retained source strictly
newer than FIFO.

## Canonical owned queue

`CanonicalOwnedQueue.lean` defines the recursive source-bearing realization

```text
ownedQueue 0 = empty

ownedQueue (k + 1)
  = eraseOldestN (service k) (ownedQueue k union blockCarrier k).
```

The accompanying consumed set is the set difference between the available
claims and this oldest-first remainder.  Source time itself is the claim
identity.

Lean proves the temporal and ownership invariants:

```text
every outstanding source before block k is earlier than block start k;
every outstanding source remains a CarryTwoDebtAt source;
old outstanding claims and current block arrivals are disjoint;
consumed claims and the next outstanding queue are disjoint;
consumed union next outstanding reconstructs all available claims;
a consumed source never appears in any later owned queue.
```

Most importantly, the concrete queue agrees exactly with the pre-existing
scalar recurrence:

```text
card ownedQueue(k) = canonicalOutstandingClaimQueueBeforeBlock n k;
card ownedConsumed(k) = canonicalQueueConsumed n k.
```

Thus the owned queue is not merely an alternative model.  It is a
source-preserving realization of the scalar queue already used by the endpoint
accounting theorems.

## Genuine source-age bridge

The predicate

```text
CanonicalOwnedOutstandingClaimsHaveSourceAgeAtMost n H
```

requires every actual source `i` retained before every block `m` to satisfy

```text
canonicalBlockStartTime n m - i <= H.
```

Using temporal support and preserved `CarryTwoDebtAt`, Lean proves that such an
owned source belongs to `canonicalRecentSourceClaimCarrier n H m`.  Exact
cardinality agreement then gives the complete implication chain

```text
uniform actual source age H
  -> actual owned queue embeds in the recent-source carrier
  -> scalar cardinal coverage
  -> uniform scalar queue bound H
  -> uniform endpoint-width bound bitWidth(n) + H.
```

No theorem in this checkpoint asserts

```text
exists H, CanonicalOwnedOutstandingClaimsHaveSourceAgeAtMost n H.
```

That existence statement is the remaining positive problem on this route.

## Generic closed-signature obstruction

`FiniteSignedTransition.lean` now isolates the logical one-edge obstruction:
if a realized related edge has positive actual weight, equal endpoint
signatures, and is covered by the certificate step relation, then the
certificate is contradictory.  Equal signatures force zero potential change,
while soundness requires it to dominate a positive weight.

The previous all-ones theorem is now a corollary of this generic result.

The factor-through theorem strengthens the negative boundary.  For any finite
map

```text
f : FixedLowRawSignature r -> Sigma,
```

no certificate that uses `f (fixedLowRawSignature r x)` and covers every raw
odd transition can exist.  Therefore post-processing, merging, or otherwise
coarsening the four fixed-low coordinates cannot repair their information
loss.  This does not reject strict refinements that retain new information.

## Top-two-bit refinement

The normalized top-two-bit observation distinguishes the cp-333 all-ones
edge.  For every `r >= 1`, its source has normalized bits `11`, while its
successor has normalized bits `10`.  Consequently the old positive projected
self-loop is absent after adding this coordinate.

This is only a local repair.  It does not imply that the enriched signature
admits a bounded potential.

## Exact enriched-signature obstruction

The first enriched candidate is

```text
fixedLowUpperBoundarySignature r x
  = (fixedLowRawSignature r x, normalizedTopTwoBits x).
```

Exploratory enumeration found no positive projected self-loop in the sampled
range, but it found positive projected cycles.  Numerical search was used only
to locate witnesses; it was not promoted to a global claim.

For `r = 1`, the exact witnesses were then proved in Lean:

```text
55 -> 83, raw signed-width weight = +1;
39 -> 59, raw signed-width weight =  0;

signature(83) = signature(39);
signature(59) = signature(55).
```

The two realized signature edges therefore form a projected two-cycle with
total weight `+1`.  Summing the two potential inequalities gives a strict
positive demand around a closed signature cycle, which is impossible.  The
concrete states do not need to form one orbit cycle: a projected certificate
assigns potential to signatures, so any closed cycle in the realized
signature-pair graph is sufficient.

Lean consequently proves

```text
not_coversAllRawOddTransitionsWithFixedLowUpperBoundarySignature.
```

This is the genuine Stage L stopping obstruction.  The top-two coordinate
removes the old one-edge collision but does not contain enough information to
support a global bounded potential even at depth one.

## Route decision

The owned-source route remains open at one honest theorem:

```text
existence of a uniform actual source-age bound H
  -> uniform queue and endpoint-width bounds.
```

The audited signature route has advanced from a positive self-loop obstruction
to a positive projected-cycle obstruction.  A next signature candidate must
separate at least one side of the exact `55/39` cycle, and it must be audited
again for all positive projected cycles rather than only self-loops.

## Verification

The following build gates passed:

```text
lake build DkMath.Collatz.PetalBridge.FloatWindow.OldestFirstQueue
lake build DkMath.Collatz.PetalBridge.FloatWindow.CanonicalOwnedQueue
lake build DkMath.Collatz.PetalBridge.FloatWindow.RawLowSignatureObstruction
lake build DkMath.Collatz.PetalBridge.FloatWindow
lake build DkMath.Collatz.PetalBridge
lake build DkMath
git diff --check
```

The changed FloatWindow implementation files contain no `sorry` or `admit`.
The full top-level `DkMath` build completed successfully.
