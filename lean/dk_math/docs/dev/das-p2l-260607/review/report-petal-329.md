# Petal / FloatWindow implementation report - checkpoint 329

## Result

The local saturated-successor program is closed at the abstract dyadic level.
The block-core claim API, rigid successor profiles, unified local discharge,
and a noncircular conditional global interface are now formalized.

## Block-core API

`canonicalBlockCoreWordAtDepth` packages

```text
2^d * 3^(L-d) * u - 1.
```

The source state equals this word at every valid depth, and claim membership
is exactly own-width carry two at this word.  Adjacent depths satisfy

```text
3 * (word (d+1) + 1) = 2 * (word d + 1),
source (d+1) + 1 = source d.
```

## Rigid successor collapse

For a saturated predecessor:

- every successor misses its deepest depth;
- a zero-carrier balanced successor is forced to `L=2`, terminal valuation
  one, claim count one, claims `{1}`, and holes `{2}`;
- the full-balanced zero-carrier branch is impossible;
- a tight valuation-one positive successor has holes `{L}` and claims
  `Icc 1 (L-1)`.

## Unified local discharge

`CanonicalSaturatedSuccessorAbstractDischarge` has exactly three constructors:

- negative successor drift with scalar cancellation;
- zero successor drift with `L >= 2` and a `Fin 2` abstract embedding;
- positive nonsaturated successor with disjoint saturated-unit and demand
  embeddings.

Every saturated predecessor has this certificate.  It is explicitly not an
allocation of actual orbit bits or a globally reusable resource.

Length-one successors now have the definitive repayment surface:

- claim count zero;
- successor drift at most `-1`;
- predecessor plus successor drift at most zero;
- residue `11 mod 16` gives exact cancellation;
- residue `3 mod 16` gives total drift at most `-1`.

## Claim-transition audit

The adjacent recurrence does not imply monotone carries.  Lean verifies the
exact recurrence witness `53, 35, 23`, whose own-width carries are `2, 1, 2`.
Thus recurrence alone cannot provide the required uniform claim-hole density.

## Abstract global interface (corrected by checkpoint 330)

The first version of `UniversalPaymentAmortizedResource.lean` introduced a
scalar transition state and finite-prefix conservation.  Checkpoint 330 found
that its potential could be chosen as `C - queue`, so the certificate was not
noncircular.  The generic telescope remains valid, but the interpretation in
the original checkpoint result is withdrawn.

A uniform potential ceiling together with a cumulative replenishment ceiling
implies a uniform queue bound, which then implies the existing endpoint-width
bound.  A merely pointwise replenishment bound is correctly rejected because
it permits linear cumulative growth.

## Genuine obstruction

Checkpoint 330 proves that existence of the former abstract amortization law
is equivalent to existence of a uniform queue bound.  A genuine replacement
must assign negative drift or width decrease to concrete resource atoms with
temporal ownership and prove a cumulative replenishment ceiling.  Existing
scalar facts allow the same event to be reused across blocks unless a
multiplicity bound is added.

Route 1 therefore does not obtain monotonicity from recurrence alone, although
additional canonical residue or width data may still support a density bound.
Route 2 stops at the absence of a concrete owned carrier and temporal nonreuse.

## Verification

All required gates passed:

```text
lake build DkMath.Collatz.PetalBridge.FloatWindow.UniversalPaymentAmplitude
lake build DkMath.Collatz.PetalBridge.FloatWindow.UniversalPaymentAmortizedResource
lake build DkMath.Collatz.PetalBridge.FloatWindow
lake build DkMath.Collatz.PetalBridge
lake build DkMath
git diff --check
```

The changed Lean files contain no `sorry` or local `maxHeartbeats` override.
