# review-000 — LGF-000 exact support turnover

## Verdict

**APPROVED — Outcome A: EXACT TURNOVER LAW ESTABLISHED.**

LGF-000 strengthens the GNIP successor firewall from a one-way divisibility obstruction to an exact adjacent-shell support identity.

## Exact new content

For the canonical threshold-skipping reindex, the lower support intersection is exactly

```text
squareOffsetPrimeSupport n r ∩
  squareOffsetPrimeSupport (n+1) (successorThresholdInsert n r)
=
(squareOffsetPrimeSupport n r).filter
  (fun q => q ∣ oddGnomon n)
```

under the lower-region condition `r < n+1`.

For the upper region it is exactly

```text
squareOffsetPrimeSupport n r ∩
  squareOffsetPrimeSupport (n+1) (successorThresholdInsert n r)
=
(squareOffsetPrimeSupport n r).filter
  (fun q => q ∣ 2*(n+1)).
```

These are true Finset equalities, not merely one-way firewall implications.

Under `Nat.Prime (n+1)`, every old prime divisor of `2*(n+1)` is exactly `2`, so the upper intersection collapses to the old support filtered by `q = 2`.

## Why this is genuinely new

`GnomonSuccessor` proved only that common support must divide the displacement.  LGF-000 proves the converse as well: an old support prime dividing the displacement is reconstructed as successor support.  Therefore the support turnover law is exact.

The existing `OldSupportGcd` / `FreshCollisionMatching` layers concern two distinct seats in one fixed shell.  LGF-000 instead compares canonically paired seats across adjacent shells, so it adds a distinct axis of structure.

## 30 -> 31 regression

The lower half is completely support-disjoint because `oddGnomon 30 = 61` is prime and all old support primes are at most `30`.

In the upper half, any common support prime is `2`.

This confirms that the previously observed coverage mismatches are instances of a general adjacent-shell turnover law rather than isolated arithmetic accidents.

## Scope judgment

No theorem here proves:

```text
¬ SquareOffsetsFullyCovered n
```

or gives a new prime witness.

A two-shell turnover ledger is not yet justified.  To obtain new leverage over the existing full-cover frontier one first needs a quantitative statement of the form:

```text
simultaneous full cover
-> sufficiently many forced support changes / fresh incidences
```

with a lower bound strong enough to conflict with an existing capacity bound.

LGF-000 itself supplies only the local exact intersection rule; it does not supply that aggregate lower bound.

## Recommendation

Close the current LGF campaign at LGF-000 and merge the exact support-turnover API.

Do not create LGF-001 merely to package support changes into another ledger without a concrete inequality target.

Future Legendre work should reopen from this theorem only after a candidate charging principle is identified.  The natural consumer would be the existing collision/capacity frontier rather than a new generic gnomon layer.
