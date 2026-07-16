# Petal / FloatWindow implementation report - checkpoint 330

## Result

The circularity audit succeeded.  The former scalar “noncircular” law is now
proved existentially equivalent to the desired uniform queue bound, so it is
not a reduction of the global problem.  Its valid generic telescope has been
separated from Collatz, and the canonical reflected queue now has explicit
demand, service, consumption, and exact one-block conservation observables.

## Circularity regression

Given a queue ceiling `C`, Lean constructs the finite amortized transition

```text
queue k         = canonicalOutstandingClaimQueue n k
potential k     = C - queue k
consumed k      = 0
replenishment k = 0.
```

Both `queue k + potential k` and its successor reduce to `C`.  Therefore:

```text
exists P R, CanonicalAbstractAmortizationCertificate n P R
  <->
exists C, CanonicalOutstandingClaimQueueUniformUpperBound n C.
```

This is a mandatory semantic regression: an arbitrary complement potential
can encode the target bound rather than explain it.

## Generic telescope

`FiniteAmortizedResource.lean` is Collatz-independent and has no phantom state
field.  It records only queue, potential, consumed mass, replenishment, and
one-step conservation.

The sharp finite-prefix theorem is:

```text
queue m <= queue 0 + potential 0 + cumulativeReplenishment m.
```

Only the initial potential is needed.  The old uniform-potential version is
retained as a stronger compatibility corollary.

## Exact canonical queue transition

The canonical observables are now explicit:

```text
demand k   = canonicalBlockClaimCount n k
service k  = canonicalBlockCapacityCount n k
consumed k = min (queueBeforeBlock k + demand k) (service k).
```

Lean proves exact reflected conservation for every block:

```text
canonicalOutstandingClaimQueue n k + consumed k
  = queueBeforeBlock k + demand k.
```

This handles block zero and successor blocks uniformly through the explicit
`queueBeforeBlock` observable.

## Canonical carry-alternation regression

The arithmetic witness `53,35,23` is realized by the first canonical block of
the odd root `23`.  Lean proves:

```text
block length = 3
odd core = 3
core words at depths 1,2,3 = 53,35,23
claim depths = {1,3}
claim holes = {2}.
```

Thus adjacent core-word recurrence alone does not imply monotone carry inside
canonical blocks.  This does not rule out bounded-gap or density theorems that
also use canonical residue classes, odd core, or block width.

## Genuine stopping point

No concrete initial upper-resource carrier has yet been identified.  A genuine
owned transition must define carriers from the initial odd state and prove an
identity of the form

```text
Available (k+1) ≃ (Available k \ Consumed k) Sum Replenished k
```

together with disjoint ownership, injective consumption, unique temporal
origin, and temporal nonreuse.  Without those data, local saturated-successor
discharge is not formally connected to global amortization.

The next admissible step is therefore carrier discovery, not another scalar
potential predicate.  Any proposed owned law must be audited against the same
reverse construction before it is accepted.

## Verification

All required gates passed:

```text
lake build DkMath.Collatz.PetalBridge.FloatWindow.UniversalPaymentAmplitude
lake build DkMath.Collatz.PetalBridge.FloatWindow.UniversalPaymentAmortizedResource
lake build DkMath.Collatz.PetalBridge.FloatWindow
lake build DkMath
git diff --check
```

The changed Lean files contain no `sorry` or local heartbeat override.
