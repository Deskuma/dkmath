# Petal / FloatWindow implementation report: checkpoint 344

## Status

Checkpoint 344 is implemented without adding `sorry`.

The reflected scalar queue and the conservation-facing absorption deficit are
now identified at the same constant, at each finite maximum, at zero/positive
states, and on finite primitive excursions.  The finite-transition branch was
also audited.  It stops at a precise missing theorem rather than assuming
cycle nonpositivity.

## Audit wording correction

The finite audit now checks the active-window deficit identity at every
positive queue state, not only when a new record is set.  The CSV still stores
only the final maximum witness for each root.  The cp-343 report and generated
summary state this distinction explicitly.

The finite range and observed values are unchanged:

```text
8192 odd roots in 1..16383
6709 roots with a positive observed maximum
largest observed queue/deficit: 8
```

These remain finite observations.

## Same-constant equivalence

Lean proves the parameterwise theorem

```text
CanonicalOutstandingClaimQueueUniformUpperBound n C
  iff
CanonicalAbsorptionDeficitWindowUniformUpperBound n C.
```

No root-width offset is needed between these two surfaces.  The proof handles
the empty half-open window separately and converts each nonempty interval
`[q, q + M)` into the inclusive suffix `q .. q + M - 1`.

This differs from the width-reserve translation.  Width to queue still uses
the root-width offset because width is an absolute level, while queue and
deficit both measure positive finite-window increments.

## Exact suffix maximum

The new finite carrier is

```text
canonicalAbsorptionDeficitSuffixMaximum n m
  = sup q in range (m + 1),
      Int.toNat
        (canonicalAbsorptionDeficitWindow n q (m - q + 1)).
```

Lean proves exactly

```text
canonicalOutstandingClaimQueue n m
  = canonicalAbsorptionDeficitSuffixMaximum n m.
```

Thus the reflected recurrence does not merely produce some deficit witness.
At every terminal block it computes the maximum positive absorption deficit
among all finite suffixes ending there.

Two direct consequences are now public:

```text
queue n m = 0
  iff every suffix absorption deficit ending at m is nonpositive

0 < queue n m
  iff some suffix absorption deficit ending at m is positive.
```

## Primitive positive-deficit excursions

The new predicate

```text
CanonicalPrimitivePositiveAbsorptionDeficitExcursion n q r
```

records:

- queue before block `q` is zero;
- every proper prefix from `q` has positive absorption deficit;
- the total deficit through the supplied endpoint `r` is nonpositive.

Lean proves it equivalent to the existing finite primitive queue excursion:

```text
CanonicalPrimitivePositiveQueueExcursion n q r
  iff
CanonicalPrimitivePositiveAbsorptionDeficitExcursion n q r.
```

The future discharge endpoint remains an input.  No theorem claiming that
every open excursion has a future zero was added.

## Finite-transition audit

One block deficit is exactly

```text
block length - claim holes - terminal valuation.
```

A finite control graph must therefore either retain enough information to
recover these terms or prove a common upper bound for all realized weights in
each projected edge fiber.

The candidate coordinates currently have the following status:

| coordinate | finite as stated | sufficient weight control |
| --- | --- | --- |
| full carry/claim word | no, length is unbounded | exact but not finite |
| block length | no | exact component |
| claim-hole count | no | exact component |
| terminal valuation | no | exact component |
| queue zero/nonzero | yes | no magnitude control |
| excursion phase | yes | no magnitude control |
| bounded low residue | yes | exact-weight collisions already observed |

Reducing an unbounded coordinate modulo or into a finite class does not yet
bound the omitted quotient contribution.  The missing canonical theorem is:

```text
for every projected finite edge,
all realized canonical block deficits in that edge fiber
have a common finite upper bound.
```

Without that theorem, a finite weighted edge table cannot be defined soundly.
Consequently, reachable positive-cycle exclusion cannot yet be formulated as
a canonical theorem rather than an assumption.

This obstruction is recorded in the source commentary of
`FiniteSignedTransition.lean`.

## Independent discharge search

The existing relevant surfaces remain conditional:

- bounded repayment lag requires a supplied lag property;
- source-age horizon requires a supplied horizon or future payment;
- primitive excursion closure requires a supplied future queue zero;
- potential certificates require a supplied sound finite projection and
  bounded potential;
- the reverse finite certificate built from an assumed queue bound is
  explicitly circular.

No unconditional theorem in the current source database supplies regular
queue discharge, bounded source age, cumulative terminal-valuation absorption,
or positive-cycle exclusion from canonical arithmetic alone.

## Facts fixed by Lean

1. Queue boundedness and all-window deficit boundedness are equivalent with
   exactly the same constant.
2. The queue at each block is the exact maximum positive suffix deficit.
3. Queue zero is exactly universal nonpositivity of ending suffix deficits.
4. Queue positivity is exactly existence of a positive ending suffix deficit.
5. Finite repaid primitive queue excursions are exactly primitive
   absorption-deficit excursions.
6. None of these theorems supplies a future discharge endpoint or a uniform
   bound independently.

## Next implementation direction

The next noncircular branch must attack the bounded-edge-fiber theorem before
cycle elimination.  A useful candidate should:

1. choose a structurally predefined finite signature;
2. prove every canonical transition maps to a projected edge;
3. prove each projected edge's realized deficit fiber is bounded above;
4. only then audit or prove nonpositivity of reachable projected cycles.

If no such signature controls the edge fiber, the alternative arithmetic
route is an independent regular-discharge or cumulative absorption theorem.
Further queue/credit reformulations alone will not advance the open target.

## Verification

The checkpoint is checked by the targeted reserve build, the strengthened
finite Python audit, aggregate FloatWindow/PetalBridge builds, top-level
`DkMath`, `git diff --check`, and a no-`sorry` scan of modified Lean files.
