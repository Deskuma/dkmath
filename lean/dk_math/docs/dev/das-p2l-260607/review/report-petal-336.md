# Report Petal 336: Canonical Source-Age Signed Flow

## Status

- Checkpoint: cp-336
- Result: implemented
- Lean status: no new `sorry`
- Main module: `DkMath.Collatz.PetalBridge.FloatWindow.CanonicalSourceAgeFlow`

## What Was Implemented

The static source-age deficit from cp-335 is now an exact local signed flow.
The new frontier increment is

```text
crossing carry-two sources - actual FIFO consumption.
```

For every horizon `H` and prefix length `m`, Lean proves

```text
sourceAgeDeficit(H, m)
  = sum_{k < m} sourceAgeFrontierIncrement(H, k).
```

The proof keeps the accumulator in `Int`. Negative repayment credit is not
truncated between blocks.

## Exact Carrier Results

The implementation adds the actual expired-outstanding carrier and proves:

```text
i is expired
  <-> i is outstanding and its actual source age is greater than H.
```

More strongly,

```text
card(expired outstanding claims)
  = Int.toNat(sourceAgeDeficit).
```

Thus the signed deficit is not merely an upper estimate. Its positive part is
exactly the number of currently outstanding identities beyond the horizon.

The moving old-source carrier also has the exact disjoint recurrence

```text
old(H, m + 1) = old(H, m) union crossing(H, m).
```

This includes the early Nat-subtraction regime without an additional side
condition.

## Uniform Age Equivalences

Lean now identifies three equivalent readings:

```text
all outstanding sources have age <= H
<-> every signed frontier prefix is <= 0
<-> every expired-outstanding carrier is empty.
```

This is the principal positive target for subsequent arithmetic work. It also
sharpens the conditional repayment theorem: a claim born in block `k` is
consumed in some block strictly before `k + H + 1`.

## FIFO Facts

The oldest-first finite-set API now proves threshold dominance. Among all
historical subsets with the same cardinality, the FIFO remainder retains the
largest possible number of source indices at or above every cutoff.

This is a static assignment theorem. It does not compare complete recursive
alternative queue policies.

The same module contains a Collatz-independent regression: a queue can retain
one fixed source forever, have cardinality exactly one at every time, and still
have unbounded source age. Uniform source age is therefore sufficient for queue
boundedness here, but is not generically necessary.

## Conditional Structural Certificate

`CanonicalSourceAgeFrontierPotentialCertificate` wraps an externally supplied
finite transition signature and bounded potential. Its realized successor
weight must equal the frontier increment, and its prefix potential changes must
be nonpositive.

The wrapper then yields, without defining the signature or potential from the
deficit:

```text
uniform source age H
uniform queue bound H
uniform endpoint-width bound bitWidth(n) + H.
```

This keeps the certificate route noncircular. Existence of such a structural
certificate remains an arithmetic obligation.

## Saturated-Branch Audit

The first exact obstruction is now formalized. For every saturated border block
at horizon zero:

```text
crossing source count = 2
actual consumed count = 1
frontier increment = +1.
```

Therefore horizon-zero pointwise nonpositivity is false on this classified
subclass. Any successful argument must use a positive horizon, or amortize the
positive saturated increment against later negative flow over a longer window.
The existing fact that consecutive blocks cannot both be saturated does not by
itself prove that the two-block frontier sum is nonpositive.

## Additional Exact Residual Split

The sign of the source-age deficit determines the inclusion direction:

```text
deficit > 0  -> cumulative consumed sources are contained in old sources
deficit <= 0 -> old sources are contained in cumulative consumed sources.
```

This lower-tail/upper-tail split is what closes the exact expired-cardinality
formula.

## Next Arithmetic Target

The next useful attack is not another static queue identity. It is a local or
short-window classification of

```text
card(crossing(H, m)) - consumed(m).
```

Recommended order:

1. Relate crossing carriers for small positive `H` to the existing canonical
   block grammar.
2. Audit saturated-successor subclasses over the shortest window for which
   actual consumption can be bounded from below.
3. Search for a finite signature whose potential is defined from block grammar,
   never from the deficit or its prefix sums.
4. Only after such a signature exists, instantiate the conditional certificate.

Top-four normalized-prefix experiments remain paused unless they directly
encode this frontier arithmetic.

## Verification

The following gates passed:

```text
lake build DkMath.Collatz.PetalBridge.FloatWindow.OldestFirstQueue
lake build DkMath.Collatz.PetalBridge.FloatWindow.CanonicalSourceAgeFlow
lake build DkMath.Collatz.PetalBridge.FloatWindow
lake build DkMath.Collatz.PetalBridge
lake build DkMath
git diff --check
```

Neither changed Lean file contains `sorry`.
