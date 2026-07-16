# Petal / FloatWindow Report - Checkpoint 325

## Status

Accepted implementation target completed through the first honest conversion
boundary.  All new declarations in the touched FloatWindow files are
`no-sorry`.

## Implemented

### Total closed-window queue

`FiniteReflectedQueue.lean` now provides `finiteReflectedQueueOnIcc`.  It
agrees with the compatibility queue on nonempty closed intervals and is zero
when the interval is empty.  Its zero characterization quantifies over every
suffix of the possibly-empty window.

### Explicit all-depth embedding

`UniversalPaymentAmplitude.lean` now contains an explicit depth-preserving
embedding from the all-depth actual residual carrier into the all-depth causal
queue carrier.  The depth coordinate is preserved definitionally.  The old
cardinality-only existence theorem remains available.

### Spare selected incidences

The selected pressure carrier is split into the chosen drift image and its
finite complement, `canonicalSelectedDriftSpareCarrier`.  Positive
nonsaturated blocks with terminal valuation at least two have a concrete spare
incidence, including an explicit `Fin 1` embedding.

### Exact no-spare classes

For positive nonsaturated valuation-one blocks, spare emptiness is equivalent
to `claimCount = length - 1`.  The named tight predicate exposes valuation,
depth, drift, carrier cardinality, and no-spare data.

For zero drift, claims equal terminal valuation.  Empty selected carriers are
classified separately at valuation one and valuation at least two.  The rigid
zero-carrier balanced predicate records the remaining no-source case.

### Saturated-successor correction

The requested five-way successor split is not derivable from the current API.
It omitted a possible branch:

```text
positive nonsaturated + terminal valuation one + nonempty spare carrier
```

Lean validates an exhaustive six-way classification including this branch.
The two easy source-bearing cases expose actual source incidences:

1. zero drift with nonempty selected carrier;
2. positive nonsaturated drift with terminal valuation at least two.

The five-way theorem must not be introduced unless a future theorem proves
that every positive valuation-one successor of a saturated block is tight.

### Dyadic potential

For positive nonsaturated blocks with selected depth `d` and length `L`:

```text
Int.toNat drift <= L - d - 1
Int.toNat drift * 2^d <= 2^(L - 1)
```

The saturated length-two unit satisfies the corresponding exact identity.

## Proven Facts

1. Fixed-depth queue accounting is total, exact, causal, and explicitly
   embeddable without changing depth.
2. The all-depth construction is conservative: no source token is shared
   across depths.
3. Spare incidence is a concrete finite source carrier, not merely a cardinal
   slack inequality.
4. Terminal valuation at least two guarantees spare incidence in the positive
   nonsaturated branch.
5. Valuation-one no-spare is exactly the near-full claim condition.
6. Zero drift alone is not an incidence; a nonempty selected carrier is the
   required source witness.
7. A block-width dyadic denomination numerically dominates its selected drift
   mass.

## Boundary and Next Work

The dyadic inequality is not a cross-depth matching theorem.  A valid
conversion layer must represent one high-depth token by lower-depth units
while preserving both temporal order and nonduplication.  Candidate models
remain a finite binary refinement tree, weighted Hall capacity, or a monotone
potential certificate.

The immediate focused audit should examine the two rigid no-spare classes and
the newly exposed valuation-one spare branch.  In particular, determine
whether saturated successors can enter the valuation-one spare branch and
whether either rigid class can persist indefinitely.  No global repayment or
convergence conclusion is claimed at this checkpoint.
