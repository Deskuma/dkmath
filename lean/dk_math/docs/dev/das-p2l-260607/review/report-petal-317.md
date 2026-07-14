# cp-317 Implementation Report

## Status

**Completed to the first genuine obstruction.**

The finite queue-accounting layer was not extended with more matching variants.
This checkpoint instead exposed the exact arithmetic transition of a complete
canonical block, separated endpoint drawup from in-block burst, formalized
finite primitive repayment excursions, and built a sound generic
finite-transition certificate surface.

All new Lean files are `no-sorry`.

## 1. Endpoint-width drawup

`UniversalPaymentScalarQueue.lean` now defines:

- `canonicalEndpointWidth`
- `canonicalEndpointRunningWidthMinimum`
- `CanonicalEndpointWidthUniformUpperBound`

The exact identity is proved:

```text
canonicalOutstandingClaimQueue n m
  = canonicalEndpointWidth n m
      - canonicalEndpointRunningWidthMinimum n m
```

Consequences include:

- queue zero iff the current endpoint width attains the running minimum;
- a completed endpoint whose next state is `1` has queue zero;
- uniform queue boundedness iff uniform completed-endpoint-width boundedness.

Thus the cp-316 observation "state one had queue zero" is structurally forced,
not independent numerical evidence.

The experimental candidate

```text
queue n m <= bitWidth n.1
```

is named by `CanonicalOutstandingClaimQueueLeInitialWidth`, but is not asserted.
Only its valid conditional consequence is proved:

```text
candidate -> canonicalEndpointWidth n m <= 2 * bitWidth n.1
```

## 2. Exact canonical block normal form

New module:

```text
DkMath.Collatz.PetalBridge.FloatWindow.UniversalPaymentBlockNormalForm
```

For canonical block `k`, it defines the start time/state, block length `L`, odd
core `u`, endpoint state, terminal carrier, terminal valuation, and next start.

The following exact arithmetic is proved:

```text
x + 1 = 2^L * u
u % 2 = 1

2^t * (state(start+t) + 1) = 3^t * (x + 1),  t < L

endpoint + 1 = 2 * 3^(L-1) * u
3 * endpoint + 1 = 2 * (3^L * u - 1)

capacity = v2 (3^L * u - 1)
next start = (3^L * u - 1) / 2^v2(3^L * u - 1)
```

Therefore the complete block transition is now a Lean theorem:

```text
(L, u) -> oddPart (3^L * u - 1)
```

No logarithmic or asymptotic approximation occurs in this layer.

## 3. Drift and in-block burst

The normal-form module also proves:

- block claim count is at most block length;
- signed block drift is at most `L - capacity`;
- positive drift implies `capacity < L`;
- equivalently, positive drift implies `v2(3^L*u-1) < L`;
- positive drift requires a nonempty delayed-debt fiber.

Within a canonical block, bit width is nondecreasing before endpoint payment,
so the endpoint-before-payment width is the block maximum.  The exact burst is:

```text
endpointWidthBeforePayment - blockStartWidth
  = card (floatGrowthDebtFiberAt n endpoint)
```

This separates two coordinates:

```text
completed-endpoint drawup = canonicalOutstandingClaimQueue
current in-block burst     = delayed-debt cardinality
```

A conditional all-state bound is proved for every state in a named canonical
block when both coordinates have uniform bounds.  No global block-coverage
claim was inserted into that theorem.

## 4. Primitive queue excursions

New module:

```text
DkMath.Collatz.PetalBridge.FloatWindow.UniversalPaymentPrimitiveExcursion
```

It defines a finite primitive positive excursion `q..r` by:

- queue before `q` is zero;
- queue after every block in `[q,r)` is positive;
- queue after `r` is zero.

The queue presentation is proved equivalent to the signed partial-sum form:

- every proper prefix drift from `q` is positive;
- total drift through `r` is nonpositive.

The module exposes excursion length, maximum queue, exact signed block word,
first repayment endpoint, and uniqueness of the repayment block for a fixed
start.

The important separation is now formal:

```text
finite repayment endpoint -> unique
future repayment endpoint exists -> not yet proved
```

Therefore the unconditional statement that every positive queue position lies
in a finite primitive excursion is intentionally not exported.

## 5. Generic finite signed-transition certificate

New module:

```text
DkMath.Collatz.PetalBridge.FloatWindow.FiniteSignedTransition
```

`FiniteSignedTransitionPotentialCertificate` requires:

- a finite signature type;
- a concrete-to-signature map;
- concrete and projected edge weights;
- proof that projected weight bounds concrete drift;
- a bounded potential whose difference bounds every projected edge.

Lean proves:

- projected path weight bounds concrete path weight;
- projected path weight telescopes below endpoint potential difference;
- every concrete path weight is uniformly bounded by the certificate bound;
- a path returning to the same signature has nonpositive projected and concrete
  weight.

This is a sound, stronger potential form of the desired nonpositive-cycle
certificate.  The converse weighted-graph theorem from cycle conditions alone
remains separate work.

## 6. Finite audit

New executable audit:

```text
python/Collatz/PetalBridge/canonical_block_normal_form_audit.py
```

Recorded outputs:

```text
python/Collatz/PetalBridge/results/canonical_block_normal_form_audit_317.json
python/Collatz/PetalBridge/results/canonical_block_normal_form_audit_317.md
```

Range:

- all 65,536 odd roots through `131071`;
- 1,280 deterministic random odd roots of widths 64, 128, 256, 512, and 1024;
- exact block-normal-form traces for 9,472 roots (8,192 small plus all random roots);
- up to 4,096 canonical blocks per root;
- random seed `54039`.

Every audited block passed the exact normal-form assertions.  No counterexample
to `queue <= initial bitWidth` was observed.  The largest observed queue was
`15`, at a 512-bit random root.  These are finite observations only.

## 7. Candidate signature result

The candidate finite signatures used:

- capped block length;
- low `w` bits of odd core `u`;
- high `w` bits of start state;
- capped terminal valuation;
- capped claim count.

For every tested width `w = 5,6,7,8`, equal signatures had conflicting drift
or successor behavior.  The audit also found realized positive-weight segments
between repeated signatures:

| w | drift collisions | nondeterministic successors | positive repeated segments |
| --- | --- | --- | --- |
| 5 | 514 | 2477 | 419 |
| 6 | 363 | 8411 | 103 |
| 7 | 369 | 24807 | 10 |
| 8 | 476 | 65724 | 5 |

This does not prove that no finite abstraction can work.  It does prove that
the tested projection cannot be treated as an exact deterministic automaton,
and the data gives no basis for constructing its required Lean soundness field.

## 8. Existing bridge audit and stopping point

The existing `FloatStepLedger`, mod-eight reservoir, canonical block histogram,
pressure margin, finite-window packing, `OneCycle`, and NoLift-facing surfaces
were inspected.

The exact missing bridge agrees with the source comment already present in
`DriftBridge.lean`:

```text
Float/payment data is indexed by orbit time.
SourcePressureMarginInt is indexed by source depth.
No proved map currently identifies these slots while preserving contribution.
```

Without this index-preserving map, a positive primitive queue excursion cannot
be sent to a pressure separator or NoLift obstruction.  Likewise, the tested
finite signatures cannot instantiate `actual_le_projected` in the generic
certificate.

This is the first genuine cp-317 obstruction.  Continuing with more queue
algebra would not address it.

## 9. Verified builds

Passed:

```text
lake build DkMath.Collatz.PetalBridge.FloatWindow.UniversalPaymentPrimitiveExcursion
lake build DkMath.Collatz.PetalBridge.FloatWindow.FiniteSignedTransition
lake build DkMath.Collatz.PetalBridge.FloatWindow
lake build DkMath.Collatz.PetalBridge
lake build DkMath
git diff --check
```

No `sorry` occurs in the changed Float-window files.

## Next implementation

Do not enlarge the coarse signature blindly.  The next productive checkpoint
must prove one of these missing contracts:

1. an orbit-index to pressure-depth map preserving claim/payment contribution;
2. a different finite signature with a theorem proving concrete drift is bounded
   by projected edge weight;
3. an eventually-zero or finite-repayment theorem for the scalar queue;
4. an initial upper-boundary resource theorem implying
   `CanonicalOutstandingClaimQueueLeInitialWidth`.

The first option is the most direct bridge to the existing pressure and NoLift
infrastructure.  The fourth is the most direct route to the surviving initial
width candidate.
