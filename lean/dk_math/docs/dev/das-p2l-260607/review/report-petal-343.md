# Petal / FloatWindow implementation report: checkpoint 343

## Status

Checkpoint 343 is implemented without adding `sorry`.

This checkpoint replaces the remaining indirect presentations of cumulative
canonical width by exact prefix-drift, reflected-queue, and absorption-deficit
surfaces.  These are equivalences or quantitative translations of the same
open fixed-root boundedness question.  They do not prove that the bound exists.

The correct relation to the pointwise branch is:

```text
cumulative width boundedness implies pointwise drift boundedness;
no converse is currently available.
```

No canonical separation theorem is claimed.

## Strong zero-reserve obstruction

Lean now proves the stronger statement

```text
0 < endpointAccountingTerm n 0
  -> not exists C : SignedCounterCertificate,
       C.credit = canonicalEndpointCounterCredit n.
```

The former weight hypothesis is unnecessary.  A signed-counter certificate
already requires every credit value to be nonnegative, while positive initial
drift makes zero-reserve credit negative at time one.

The optional recurrence rigidity statement also closes:

```text
C.credit = canonicalEndpointCounterCredit n
  -> C.weight = endpointAccountingTerm n.
```

Thus the credit function alone determines the weight through the certificate's
exact successor equation.  The old theorem with both equalities remains as a
compatibility corollary.

## Direct prefix-drift surface

The exact width telescope now gives the public equivalence

```text
CanonicalWidthWithinReserve n B
  iff
forall M, sum m in range M, endpointAccountingTerm n m <= B.
```

Its existential form is

```text
RootwiseCanonicalWidthBound n
  iff
exists B, forall M,
  sum m in range M, endpointAccountingTerm n m <= B.
```

This is the direct cumulative target.  It no longer needs to be inferred from
the conditional signed-counter construction.

## Quantitative queue translations

The constants in the queue/width bridge are now explicit:

```text
CanonicalWidthWithinReserve n B
  -> CanonicalOutstandingClaimQueueUniformUpperBound
       n (bitWidth n.1 + B)

CanonicalOutstandingClaimQueueUniformUpperBound n C
  -> CanonicalWidthWithinReserve n C.
```

Consequently, existential fixed-root width boundedness and existential queue
boundedness are equivalent.  No same-constant parameterwise equivalence is
stated: the width-to-queue direction pays the root-width offset.

## Half-open absorption deficit

The new integer-valued ledger is

```text
canonicalAbsorptionDeficitWindow n q M
  = blockLengthWindow n q M
      - claimHolesWindow n q M
      - terminalValuationWindow n q M.
```

Lean proves the exact chain

```text
absorptionDeficitWindow n q M
  = endpointDriftWindowSum n q M
  = bitWidth (blockStartState n (q + M))
      - bitWidth (blockStartState n q).
```

The empty and singleton windows are fixed explicitly.  For `q <= m`, the
half-open window of length `m - q + 1` is also proved equal to the existing
inclusive drift window `canonicalWindowDriftInt n q m`.  This removes the
inclusive/half-open convention risk from downstream queue proofs.

## Queue maximum is an attained deficit

Using the existing maximum-positive-suffix theorem, Lean proves:

```text
0 < canonicalOutstandingClaimQueue n m
  -> exists q <= m,
       (canonicalOutstandingClaimQueue n m : Int)
         = canonicalAbsorptionDeficitWindow n q (m - q + 1).
```

Therefore a positive queue value is not merely an abstract recurrence value.
It is attained by a concrete finite suffix whose excess block length over
claim holes plus terminal valuation equals that queue value.  This theorem
assumes no queue bound.

## Exact all-window target

The new predicate

```text
CanonicalAbsorptionDeficitWindowUniformUpperBound n C
```

requires every finite shifted half-open block window to have deficit at most
`C`.  Its quantitative translations are:

```text
CanonicalWidthWithinReserve n B
  -> deficitWindowBound n (bitWidth n.1 + B)

deficitWindowBound n C
  -> CanonicalWidthWithinReserve n C.
```

Hence Lean proves

```text
RootwiseCanonicalWidthBound n
  iff
exists C, CanonicalAbsorptionDeficitWindowUniformUpperBound n C.
```

The predicate is also equivalent to the cumulative block-budget inequality

```text
lengthWindow
  <= claimHolesWindow + terminalValuationWindow + C
```

for every shifted finite window.

## Pointwise versus cumulative targets

Both surfaces remain public and deliberately distinct.

Pointwise:

```text
blockLength m
  <= claimHoles m + terminalValuation m + B.
```

Cumulative:

```text
forall q M,
  blockLengthWindow q M
    <= claimHolesWindow q M + terminalValuationWindow q M + C.
```

The cumulative statement is the one equivalent to rootwise canonical width
boundedness and suitable for a finite-state reduction.  The pointwise target
alone is not used as though it supplied the cumulative estimate.

## Independent discharge search

The existing bounded-repayment-lag and source-age surfaces are conditional.
They require the lag, horizon, future zero, or related repayment property that
would discharge the queue; they do not prove such a property independently.

The finite signed-transition surfaces can express a graph reduction, but the
canonical bridge currently supplies no theorem excluding every reachable
positive-deficit cycle.  Claim-hole incidence and terminal-valuation ledgers
provide exact conservation, not an independent cumulative lower bound.

The honest missing arithmetic statement is therefore one of:

1. a uniform cumulative absorption estimate;
2. an independently proved bounded repayment lag or regular queue zero;
3. a finite canonical transition grammar together with exclusion of every
   reachable positive-deficit cycle.

The implementation stops at the exact maximum-deficit characterization rather
than defining another equivalent credit or assuming the desired conclusion.

## Finite audit

The new script

```text
python/Collatz/PetalBridge/canonical_absorption_deficit_audit.py
```

records, for each audited odd root, a window attaining every newly observed
reflected-queue record.  The generated CSV includes:

- root;
- terminal and witness-start blocks;
- number of blocks in the witness window;
- cumulative block length;
- cumulative claim holes;
- cumulative terminal valuation;
- resulting absorption deficit and queue maximum.

The audit covered all 8192 odd roots in `1..16383`, with a limit of 4096
canonical blocks per root.  All reached a state-one canonical endpoint within
the audited range.  There were 6709 roots with a positive observed maximum,
and the largest observed queue/deficit was 8.  Every positive record passed the
exact identity

```text
maximum queue = length - holes - terminal valuation.
```

These values are explicitly observational.  They prove neither a uniform
all-root bound nor eventual discharge.

Generated artifacts:

```text
python/Collatz/PetalBridge/results/canonical_absorption_deficit_audit_343.csv
python/Collatz/PetalBridge/results/canonical_absorption_deficit_audit_343.md
```

## Facts fixed by Lean

1. Positive initial drift excludes any certificate using zero-reserve credit.
2. That credit function would force the canonical endpoint-drift weight.
3. A width reserve is exactly a uniform upper bound on every drift prefix sum.
4. Width reserves and queue ceilings translate with the stated constants.
5. Half-open absorption deficit is exactly window drift and width change.
6. Every positive reflected queue is attained by a finite absorption window.
7. Rootwise width boundedness is existentially equivalent to uniform
   all-window absorption-deficit boundedness.
8. None of these equivalences proves the missing cumulative bound exists.

## Next implementation direction

The next productive checkpoint should add genuinely independent arithmetic,
not another reformulation.  The preferred order is:

1. isolate the finite canonical transition state needed to compute block
   deficit and queue discharge;
2. prove that every reachable positive-deficit cycle is impossible, or prove a
   bounded-lag/regular-zero theorem directly;
3. transport that theorem through the all-window absorption predicate to a
   rootwise width reserve.

If step 2 cannot be proved, retain the finite graph obstruction as the precise
open theorem rather than weakening the theorem boundary.

## Verification

The checkpoint is validated with targeted module builds, aggregate bridge
builds, the finite Python audit, `git diff --check`, and a no-`sorry` scan over
the modified Lean files.
