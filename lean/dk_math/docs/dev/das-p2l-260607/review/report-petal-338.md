# Petal / Collatz implementation report: checkpoint 338

Date: 2026-07-17

## Status

Checkpoint 338 is complete.  Every requested local arithmetic stage closed in
Lean without `sorry`, including the predecessor-carry obstruction that had
previously been supported only by the bounded audit.

The implementation is in:

```text
DkMath/Collatz/PetalBridge/FloatWindow/CanonicalSourceAgeHorizon.lean
```

## Implemented results

### Crossing-block boundary removal

`mem_crossingClaims_canonicalAgeCrossingBlockOfSource` now requires only
`CarryTwoDebtAt n i`.  The proof uses the exact block containing `i + H` and
the natural subtraction equivalences directly.  It also covers the origin and
underflow regime; the former auxiliary boundary hypothesis was unnecessary.

### Exact horizon-zero reflected normal form

The new theorem

```text
canonicalSourceAgeFrontierIncrement_zero_eq_max
```

proves

```text
frontier(0,m) = max (-queueBefore(m)) endpointDrift(m).
```

It yields the exact trichotomy:

- negative drift and a nonempty queue give frontier at most `-1`;
- zero drift gives frontier exactly `0`;
- positive drift is transmitted unchanged.

Thus one-step actual consumption cannot erase positive endpoint drift at
horizon zero.  Such repayment needs a longer window, a positive horizon, or a
separate potential.

### Saturated two-block trichotomy and root 123

For a saturated block, the exact two-block expression is

```text
1 + max (-queueBefore(successor)) endpointDrift(successor).
```

The strict branches are now formal:

- successor drift `< 0` implies a nonpositive two-block sum;
- successor drift `= 0` gives sum exactly `1`;
- successor drift `> 0` gives `1 + drift`.

Root 123 was reconstructed entirely in Lean.  The implementation proves:

```text
CanonicalSaturatedBorderBlock oneTwentyThreeSaturatedOdd 0
endpointAccountingTerm oneTwentyThreeSaturatedOdd 1 = 0
canonicalSourceAgeFrontierWindowSum oneTwentyThreeSaturatedOdd 0 0 2 = 1
```

Consequently, the universal claim with merely nonpositive successor drift is
formally false.  The negative theorem is sharp at `< 0`.

### Mature saturated horizons

For `H <= canonicalBlockStartTime n m`, a saturated length-two block has the
exact carrier decomposition into two shifted singleton boundaries.  Therefore

```text
frontier(H,m)
  = indicator(start-H) + indicator(start-H+1) - 1.
```

The `H > start` regime remains explicitly separate because natural
subtraction would otherwise alias underflowed addresses.

### Predecessor-carry obstruction

The bounded observation has become a general theorem:

```text
CanonicalSaturatedBorderBlock.predecessor_not_carryTwo
```

For every mature saturated block, the immediately preceding source is not a
carry-two source.  The proof is not a residue-only argument.  Saturation first
places the start state strictly above three quarters of its binary window.
Assuming a carry-two predecessor, the exact predecessor transition

```text
3*y + 1 = 2^(s y) * x
```

and the one-step binary-width balance place `y` in an incompatible window.
This contradiction proves the obstruction.

The direct consequence is:

```text
CanonicalSaturatedBorderBlock.sourceAgeFrontierIncrement_one_eq_zero
```

Every mature saturated block is exactly neutral at horizon one.  This is now
a theorem, not numerical evidence.

### Horizon-one successor balance

The successor of a saturated block satisfies an exact four-term identity:

```text
successor frontier at H=1
  = predecessor boundary unit
      + successor demand
      - successor final-source indicator
      - successor actual consumption.
```

The predecessor unit is always present, but successor actual consumption is
positive and cancels that unit.  Therefore a remaining successor value `+1`
requires at least one nonfinal current-block carry.  It is not caused by the
inherited predecessor boundary alone.

### Horizon telescope and finite carrier

`canonicalRecentCarryMassBeforeStart` gives the reverse-offset finite sum of
carry indicators.  In the mature regime:

```text
deficit(H,m) = deficit(0,m) - recentCarryMass(H,m)
             = queueBefore(m) - recentCarryMass(H,m).
```

The corresponding frontier identity is the exact coboundary formula:

```text
frontier(H,m)
  = frontier(0,m)
      + recentCarryMass(H,m)
      - recentCarryMass(H,m+1).
```

`canonicalPreBlockCarryCarrier` exposes the existing recent source carrier
under the requested name.  Uniform source age is exactly equivalent to

```text
forall m, queueBefore(m) <= card (preBlockCarryCarrier H m).
```

No anonymous queue elements were identified with source addresses; this is
the existing FIFO/cardinality theorem, reused through an honest bridge.

## Facts now fixed

1. Horizon-zero frontier flow is a reflected maximum, not raw endpoint drift.
2. Zero successor drift does not repay a saturated unit.
3. Mature saturated blocks are always neutral at horizon one.
4. A horizon-one successor `+1` comes from nonfinal successor carry mass after
   actual consumption, not from the predecessor unit alone.
5. Positive horizon changes frontier flow by an exact finite carry
   coboundary.
6. The source-age target can be stated entirely as finite recent-carrier
   cardinal coverage at each block.

## Honest boundary

This checkpoint does not prove that some uniform horizon exists.  It also does
not construct a finite structural potential certificate.  A finite signature
makes only the potential-maximum field finite-state checkable; transition
realization and actual-weight soundness remain all-time arithmetic
obligations.

The source-age target and one sufficient certificate method remain distinct.
Later global work still includes endpoint-to-all-time width transport,
finite-state periodicity, nontrivial-cycle elimination, and translation to the
raw challenge.

## Suggested next implementation

The local horizon algebra is now sufficiently normalized.  The next useful
checkpoint should work at the certificate-construction boundary rather than
add more aliases:

1. define a genuinely finite reachable signature carrier for the frontier
   state;
2. separate finite reachability from all-time step realization;
3. test whether the horizon coboundary and pre-block carry carrier determine
   enough state to make the actual frontier weight local;
4. if not, produce the exact pair of histories with equal proposed signature
   and different next frontier weight as an obstruction theorem.

The failure mode should be formalized rather than hidden by adding deficit or
future-prefix data to the signature, because either would make the proposed
certificate circular.

## Verification

Passed:

```text
lake build DkMath.Collatz.PetalBridge.FloatWindow.CanonicalSourceAgeHorizon
lake build DkMath.Collatz.PetalBridge
rg -n "\bsorry\b|admit|axiom" \
  DkMath/Collatz/PetalBridge/FloatWindow/CanonicalSourceAgeHorizon.lean
git diff --check
```

The `rg` check returned no matches.
