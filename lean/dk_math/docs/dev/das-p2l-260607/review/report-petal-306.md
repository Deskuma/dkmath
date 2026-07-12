# cp-306 Universal Payment Block Closure

## Closed result

The cp-305 boundary was not a logical obstruction.  Applying the existing
forward exact-depth staircase theorem to the minimum source in a nonempty
universal fiber proves interval closure.

For a nonempty `orbitPaymentSourceFiberAt n j`, Lean now proves:

```text
fiber(j) = Icc (universalPaymentBlockStart n j h) j
```

Every strict interior point has height one.  The endpoint has height at least
two.  The exact-depth profile throughout the closed block is:

```text
orbitExactDepth n i = j - i + 1
```

for every `i` in that interval.

## Target dynamics

The target map has also been strengthened:

- `i <= orbitPaymentTarget n i`;
- targets are fixed points under a second target application;
- fixed points are exactly extra-height times;
- a height-one step preserves its target;
- an extra-height step moves to a strictly later target.

These facts establish the canonical target as a retraction onto its
extra-height endpoint image.

## Scope

The new result is a single universal payment-block geometry theorem.  It does
not yet provide finite-family coverage, a cumulative block ledger, or a
pressure conclusion.  Those require explicit handling of successive target
fibers and unfinished boundary suffixes.
