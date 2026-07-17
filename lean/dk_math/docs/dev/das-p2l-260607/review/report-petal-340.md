# Petal / Collatz implementation report: checkpoint 340

Date: 2026-07-17

## Status

Checkpoint 340 attacked the endpoint-drift arithmetic boundary isolated by
cp-339.  The requested exact normal forms, the cross-root all-ones family, the
finite-potential counterexample, and the alternative finite-control counter
surface are implemented without `sorry`.

The new modules are:

```text
DkMath/Collatz/PetalBridge/FloatWindow/CanonicalEndpointDrift.lean
DkMath/Collatz/PetalBridge/FloatWindow/CanonicalAllOnesDrift.lean
DkMath/Collatz/PetalBridge/FloatWindow/FinitePotentialIncompleteness.lean
DkMath/Collatz/PetalBridge/FloatWindow/FiniteControlCounter.lean
```

All four are exported by `DkMath.Collatz.PetalBridge.FloatWindow`.

## Exact canonical endpoint ledger

Lean now proves directly that every endpoint term is the signed binary-width
change between consecutive canonical block starts:

```text
endpointAccountingTerm n m
  = bitWidth (canonicalBlockNextStartState n m)
      - bitWidth (canonicalBlockStartState n m).
```

The prefix telescope is also exposed under canonical names:

```text
sum_{k < m+1} endpointAccountingTerm n k
  = bitWidth (canonicalBlockNextStartState n m) - bitWidth n.
```

Thus endpoint accounting is not an auxiliary approximation.  It is the exact
width ledger of the canonical block process.

## Rootwise and global boundedness

Two predicates now prevent an invalid change of quantifiers:

```text
RootwiseEndpointDriftBound n
  := exists B, forall m, endpointAccountingTerm n m <= B

GlobalEndpointDriftBound
  := exists B, forall n m, endpointAccountingTerm n m <= B.
```

The cp-339 fixed-horizon theorem is proved equivalent to the first predicate
for the same fixed root `n`.  A global bound implies each rootwise bound, but
no converse is asserted.

## Odd all-ones root family

For the root `2^L - 1`, Lean proves the exact first-block chain:

```text
block length       = L
odd core           = 1
terminal carrier   = 3^L - 1
```

For odd `L = 2*r+1` it additionally proves:

```text
v2 (3^(2*r+1) - 1) = 1
next start = (3^(2*r+1) - 1) / 2.
```

The elementary exponential estimates in the module give:

```text
r <= endpointAccountingTerm (allOnesOdd (2*r+1)) 0.
```

Consequently, for every integer threshold `B`, there is an odd root whose
initial endpoint drift exceeds `B`:

```text
exists_endpointAccountingTerm_gt (B : Int) :
  exists n, B < endpointAccountingTerm n 0.
```

This proves:

```text
not_globalEndpointDriftBound : not GlobalEndpointDriftBound.
```

This is cross-root unboundedness.  The root depends on the threshold.  It does
not prove `not (RootwiseEndpointDriftBound n)` for any fixed `n`.

## Exact claim and valuation forms

The endpoint term has the exact normal form:

```text
endpointAccountingTerm
  = canonicalBlockClaimCount - canonicalBlockTerminalValuation.
```

It therefore satisfies the coarse estimate:

```text
endpointAccountingTerm
  <= canonicalBlockLength - canonicalBlockTerminalValuation.
```

The exact loss from that ceiling is the finite claim-hole count:

```text
endpointAccountingTerm + card canonicalBlockClaimHoles
  = canonicalBlockLength - canonicalBlockTerminalValuation.
```

This is the sharper universal statement requested in Stage E.  A large block
with low terminal valuation creates only capacity; missing claim depths are
the exact obstruction to realizing the full coarse drift.

## Sufficient fixed-root conditions

Three implications are now public:

1. A uniform block-length bound implies rootwise endpoint-drift boundedness.
2. A uniform bound on `blockLength - terminalValuation` implies it.
3. A uniform additive bound on next-start width above start width implies it.

These theorems do not claim that any hypothesis holds for a canonical orbit.
They identify three honest arithmetic routes to the fixed-root goal.

## Finite numerical audit

For each listed root, the canonical recurrence was evaluated for at most 1000
blocks, stopping earlier when a state repeated.  The table records the maximum
observed endpoint drift and one block attaining it.

| root | states | max drift | block | length | odd core | terminal v2 | claims | start width | next width |
|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| 3 | 2 | 0 | 1 | 1 | 1 | 1 | 1 | 1 | 1 |
| 7 | 4 | 1 | 0 | 3 | 1 | 1 | 2 | 3 | 4 |
| 27 | 18 | 2 | 1 | 5 | 1 | 1 | 3 | 5 | 7 |
| 31 | 17 | 2 | 0 | 5 | 1 | 1 | 3 | 5 | 7 |
| 47 | 17 | 1 | 0 | 4 | 3 | 1 | 2 | 6 | 7 |
| 59 | 7 | 1 | 0 | 2 | 15 | 1 | 2 | 6 | 7 |
| 123 | 10 | 1 | 0 | 2 | 31 | 1 | 2 | 7 | 8 |
| 255 | 8 | 0 | 0 | 8 | 1 | 5 | 5 | 8 | 8 |
| 511 | 11 | 5 | 0 | 9 | 1 | 1 | 6 | 9 | 14 |
| 1023 | 10 | 3 | 0 | 10 | 1 | 3 | 6 | 10 | 13 |
| 2047 | 28 | 6 | 0 | 11 | 1 | 1 | 7 | 11 | 17 |
| 4095 | 27 | 4 | 0 | 12 | 1 | 4 | 8 | 12 | 16 |

The data visibly separates long block length from realized drift: root `255`
has length eight but drift zero because valuation and missing claims absorb the
capacity, while odd all-ones lengths with terminal valuation one can produce
large initial drift.  No tested finite orbit is evidence for either rootwise
boundedness or fixed-root unboundedness.

## Finite-potential incompleteness witness

The explicit signed sequence

```text
w (2*k)     = -(k+1)
w (2*k + 1) =  (k+1)
```

is now formalized.  Lean proves:

```text
sum_{m < 2*k} w m     = 0
sum_{m < 2*k+1} w m   = -(k+1)
sum_{m < M} w m       <= 0
```

while its positive individual terms exceed every integer bound.  Therefore no
finite signature can carry a sound finite successor upper-weight table for
this sequence.

This is a formal counterexample to completeness of the present finite-table
method, not a counterexample to the desired prefix inequality.

## Finite control with an unbounded counter

`FiniteControlSignedCounterCertificate` separates finite control from an
unrestricted integer credit.  Its obligations are:

```text
credit 0 = 0
credit (m+1) = credit m - weight m
0 <= credit m -> weight m <= credit m.
```

Lean derives nonnegative credit at every step, the exact telescope, and every
nonpositive weight prefix.  The alternating witness is instantiated with a
one-state finite control and an unbounded parity-dependent credit.

The canonical source-age deficit is deliberately not instantiated.  Such an
instance requires an independently proved arithmetic transition guard; using
the desired prefix result as the guard would be circular.  Macro transitions
were likewise not introduced, so no intermediate-prefix condition is hidden.

## Facts now fixed

1. Endpoint accounting is exactly canonical next-width minus start-width.
2. Its prefixes telescope to the total canonical width change.
3. Fixed-root and root-uniform boundedness are different public predicates.
4. No endpoint-drift ceiling is uniform over all odd roots.
5. The odd all-ones family proves this global failure symbolically.
6. Cross-root failure does not decide any fixed-root bound.
7. Claim holes exactly measure the loss from `length - valuation` capacity.
8. Several useful arithmetic hypotheses are sufficient for a fixed-root bound.
9. Nonpositive prefixes can coexist with unbounded positive increments and no
   finite successor upper-weight table.
10. Finite control plus an unbounded, independently guarded counter can still
    certify all prefix inequalities.

## Branch decision and honest boundary

Stage C reached only global-across-roots unboundedness.  Per Stage K, the
branch remains at the fixed-root investigation:

```text
RootwiseEndpointDriftBound n
```

is neither proved nor refuted for a general fixed root.  The all-ones roots
cannot be reused to refute it because they vary with the requested threshold.

The next meaningful attack must therefore prove one of:

```text
uniform block-length control for one fixed root;
uniform control of blockLength - terminalValuation;
uniform control of next-start width increments;
or a symbolic repeated high-drift family inside one fixed root.
```

In parallel, the alternative counter route may proceed only after deriving a
canonical exact recurrence and its nonnegativity-preservation guard directly
from block arithmetic.  The diagnostic finite signature remains available,
but no projected upper table should be claimed before the rootwise ceiling is
proved.

## Verification

Passed during implementation:

```text
lake build DkMath.Collatz.PetalBridge.FloatWindow.CanonicalEndpointDrift
lake build DkMath.Collatz.PetalBridge.FloatWindow.CanonicalAllOnesDrift
lake build DkMath.Collatz.PetalBridge.FloatWindow.FinitePotentialIncompleteness
lake build DkMath.Collatz.PetalBridge.FloatWindow.FiniteControlCounter
lake build DkMath.Collatz.PetalBridge.FloatWindow
lake build DkMath.Collatz.PetalBridge
lake build DkMath
rg -n "\bsorry\b|\badmit\b" \
  DkMath/Collatz/PetalBridge/FloatWindow/CanonicalEndpointDrift.lean \
  DkMath/Collatz/PetalBridge/FloatWindow/CanonicalAllOnesDrift.lean \
  DkMath/Collatz/PetalBridge/FloatWindow/FinitePotentialIncompleteness.lean \
  DkMath/Collatz/PetalBridge/FloatWindow/FiniteControlCounter.lean
git diff --check
```

The `rg` check returned no matches.  `DkMath.Collatz` is not a build target
because this workspace has no aggregate `DkMath/Collatz.lean`; the actual
top-level `DkMath` target passed instead.
