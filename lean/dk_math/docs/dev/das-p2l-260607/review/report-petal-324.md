# Petal / FloatWindow implementation report - checkpoint 324

## Scope

This checkpoint separates causal queue semantics from the unordered residual
carrier introduced at cp-323.  It completes the generic finite queue, the
fixed-depth specialization, source-bearing temporal matching, and the first
all-depth causal carrier.  No unordered classical complement is reinterpreted
as a recursively updated queue.

## Implemented modules

### `FiniteReflectedQueue.lean`

The new Collatz-independent module provides:

- a Nat-valued reflected queue on a finite closed interval;
- signed arrivals-minus-service window balances;
- the finite Lindley suffix-maximum identity;
- queue-zero iff all suffix balances are nonpositive;
- unordered total residual bounded by the causal queue;
- an early-service regression where unordered residual is `0` but the causal
  queue is `1`;
- finite arrival and service carriers retaining block coordinates;
- the interval-order Hall equivalence between suffix inequalities and a
  forward injective matching.

The regression is the semantic guardrail: service before a claim cannot pay
that future claim, even when total arrivals and total service are equal.

### `UniversalPaymentScalarQueue.lean`

The existing scalar queue API is preserved.  Two compatibility theorems show
that canonical claim count and capacity count instantiate the generic signed
balance and reflected queue.

### `UniversalPaymentAmplitude.lean`

The fixed-depth layer now contains:

- proof-independent selected-drift arrival counts;
- a depth-restricted actual source-image carrier;
- equality between local image cardinality and numeric arrival count;
- equality between bucket cardinality and the blockwise arrival sum;
- exact-length service counts and their finite-set cardinality theorem;
- the fixed-depth causal queue and Lindley maximum form;
- equality between the old unordered drift residual count and the generic
  whole-window positive balance;
- the theorem that unordered residual count is at most causal queue size;
- a block-preserving equivalence from actual source-bearing arrival fibers to
  numeric `Fin` fibers;
- queue-zero iff an actual source-bearing forward matching exists;
- an all-depth sigma carrier and cardinal/embedding comparison from unordered
  residual incidences to independent causal queue fibers;
- one-unit spare selected-incidence slack for positive nonsaturated blocks
  whose terminal valuation is at least two.

The former dependent-sigma definition
`selectedPressureBucketWindowEmbedding` was removed.  Its only use was a
cardinality bound that follows directly from the existing blockwise bucket
sum and `Finset.sum_le_sum_of_subset`.  This replacement preserves the theorem
surface while reducing a clean `UniversalPaymentAmplitude` rebuild from about
70 seconds to about 10 seconds on this workspace.

## Facts established

1. The causal queue is not an alternate presentation of the cp-323 unordered
   complement.  It is the maximum positive suffix imbalance.
2. The unordered residual can underestimate causal outstanding work; the
   early-service example proves strict inequality can occur.
3. At fixed depth, queue zero has an exact finite Hall interpretation: every
   actual source incidence can be injected into a service token at the same or
   a later block.
4. Classical choice is confined to realizing finite source images and
   equivalences.  Numeric arrivals are defined solely from drift positivity,
   nonsaturation, selected depth, and `Int.toNat endpointAccountingTerm`.
5. Summing independent depthwise inequalities gives an all-depth finite
   incidence certificate.  It does not authorize token sharing across depths.
6. For positive nonsaturated terminal valuation at least two, selected
   pressure contains the drift image plus at least one extra incidence.

## Honest stopping boundary

The next unresolved branches are:

- a saturated block followed by a zero-drift successor;
- a positive successor whose terminal valuation is one;
- any theorem sharing exact-length service across distinct depths;
- a canonical causal residual subset obtained from a maximal forward
  matching.

The current theorems do not supply these claims.  The all-depth object is a
disjoint package of independent queues, not a global repayment allocation.

## Verification

Completed targeted builds during implementation:

```text
lake build DkMath.Collatz.PetalBridge.FloatWindow.FiniteReflectedQueue
lake build DkMath.Collatz.PetalBridge.FloatWindow.UniversalPaymentScalarQueue
lake build DkMath.Collatz.PetalBridge.FloatWindow.UniversalPaymentAmplitude
lake build DkMath.Collatz.PetalBridge.FloatWindow
lake build DkMath.Collatz.PetalBridge
lake build DkMath
git diff --check
```

All commands passed.  The changed Lean files contain no `sorry`.

## Suggested next checkpoint

Investigate the two excluded successor branches before adding any cross-block
charge.  A useful next theorem must produce a local source incidence or an
explicit obstruction in the zero-drift and valuation-one cases.  If neither
exists, record a negative theorem or counterexample rather than weakening the
causal matching contract.
