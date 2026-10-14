# DRC-008 — Current FLT7 finite aggregation

## Result: Outcome A

The current FLT7 route now has a checked **degree-six oriented exact cutoff**,
complete finite ideal factorization, explicit seventh-power factors with their
complementary ideals retained, and a conditional element receiver. Unconditional
FLT7 and strict descent have not been reached. The first remaining obligation
is complete-support seventh-divisibility for a fixed current linear carrier.

Branch: `research/DkMath-ResearchConnections-261003-v0`.
Baseline: `784bf2af3`; Lean/Mathlib: `v4.34.1`.

## Canonical stack selected

The public `DkMath.FLT.Seven` stack is:

1. `CounterexamplePack x y z`: positive natural coordinates, coprimality,
   and the actual equation `x^7 + y^7 = z^7`.
2. `PrimitiveCounterexampleRamifiedProvenance source`, the direct chosen
   cyclotomic quotient/root and `DirectRealCubicRootPacket source r`.
3. `DirectOrbitCanonicalCommonFactorPacket p`: positive `c,u,v`, canonical gcd,
   square refinement, norm powers, coprimality, and the existing height inequality.
4. `CurrentCommonPrimeCyclotomicPacket h q`: selected real prime `Q`, phase,
   and `CurrentMuSevenResidueAddress q` for each rational prime dividing `h.c`.
5. `SevenRealCubicCurrentPhaseCorrectedCarrier`,
   `SevenRealCubicCurrentSelectedFactorFiber`, and
   `SevenRealCubicCurrentSelectedFactorUniqueness`: the actual current carrier,
   its star conjugate, the real-prime fibre product, and real multiplicity `14e`.

The public facade now imports `CurrentFiniteAggregation`, which imports the new
`CurrentCarrierCutoff`. The old `SevenRamifiedFusionOrientedCarrierValuationOwnership`
uses a different carrier and is not used as an identification bridge. The
existing `SevenRamifiedFusionCyclotomicDegreeSixPID` is reused only for its
checked PID instance and receiver on the very same explicit quadratic algebra.
No scalar norm equality is used to identify elements. DRC-007's QR embedding
is not silently identified with this current carrier either.

The earlier direct chosen cyclotomic quotient's seventh-power results concern
that quotient, not the later phase-corrected linear carrier of the real root.
They do not supply its missing complete-support exponent theorem.

## New local endpoint

For a current packet `c`, put

- `A = currentLinearCarrier c`, `Abar = star A`;
- `P = c.address.currentKernel`, `Pbar = c.address.conjugate.currentKernel`;
- `e = currentIdealPrimeMultiplicity c.residue.Q (currentPrincipalIdeal S)`,
  where `S = h.squareRefinement.quotientSquareRoot` and the existing stack proves `e > 0`.

`CurrentCarrierCutoff.lean` proves, using these current objects:

```text
A ∈ P^k  ↔  k ≤ 14e.
```

The lower bound maps the selected real factor's membership in `Q^(14e)` through
`ofReal`, uses the checked fibre equality and `A*Abar = ofReal selectedFactor`,
and cancels `Abar` using its exclusion from `P`. The upper cutoff transports
membership by star to `Pbar`, multiplies, and contracts the fibre power through
the faithfully flat quadratic algebra. This contradicts the existing exact real
cutoff at `Q^(14e+1)`. Thus the previously deferred current upper-cutoff step is
now discharged without reverting to a historical carrier.

## Complete finite aggregation

`DkMath.Lib.NumberTheory.FiniteIdealPowerAggregation` exposes the actual full
height-one support of any nonzero ideal and its exact Associates-count exponents:

```text
I = ∏ v ∈ support I, v.asIdeal ^ exponent I v.
```

It also proves support membership, exact principal exponents from membership
plus cutoff, partition into a selected support and its complement, and power
extraction when every selected exponent is divisible by the exponent sought.
No completeness assumption on a separately chosen list of primes is hidden.

`CurrentFiniteAggregation.lean` implements:

- `commonRow`: an existing current packet for **each** member of the complete
  rational finite set `h.c.primeFactors`.
- `knownCommonPrime_exponent`: each chosen real row has exact positive exponent
  `14e` in the current real quotient ideal.
- `common_prime_aggregation`: the real quotient ideal equals
  `commonPowerRoot^7 * commonRemainder`. The remainder includes every unselected
  prime with its exact exponent. One chosen real prime per rational prime is
  not claimed to enumerate every real prime above it.
- `quotientIdeal_axis_cube_seventh_power`: independently, the existing element
  identity gives the stronger full real identity
  `quotientIdeal = principalIdeal(axis)^3 * (principalIdeal(S)^2)^7`.
  The axis cube remains present.
- `carrier_full_factorization`: the fixed current degree-six carrier ideal's
  complete support, including primes with no identified current row.
- `current_orientation`: the four current/conjugate membership and exclusion facts.
- `carrier_local_exponent`: the current oriented prime's exact exponent in that
  complete support is `14e`.
- `carrier_local_aggregation`: the identified oriented prime contributes a
  seventh-power factor; every other degree-six prime remains in the explicit
  complementary product.

Different `commonRow` packets can choose different phases and hence different
linear carriers. Their exponents are not combined as though they all belonged
to one fixed carrier ideal.

## Ideal and element receiver; precise frontier

For a fixed `c`, the first unresolved theorem is exactly:

```lean
∀ v ∈ support (carrierIdeal c) (carrierIdeal_ne_zero c),
  7 ∣ exponent (carrierIdeal c) v
```

This needs proof for **all** primes of the fixed current carrier, including the
complement of its identified oriented row. Current local membership, the exact
cutoff at the selected row, and the real quotient decomposition do not alone
identify or control every remaining degree-six prime.

Under this explicit hypothesis `hdiv`, `carrier_ideal_seventh_power` proves

```text
carrierIdeal c = powerRoot (carrierIdeal c) ... 7 ^ 7.
```

The existing checked PID instance for this degree-six ring then supplies
`carrier_element_receiver`:

```text
∃ u beta, IsUnit u ∧ A = u * beta^7 ∧ Fermat7Equation x y z.
```

No additional class-group hypothesis is needed in this ring: principalization
is already proved by its existing PID infrastructure. The unit is retained
explicitly; it has not been shown to be a seventh power or to lie in a sector
that permits its removal. The original Fermat equation is carried unchanged
from `source.hEq`. It is **not** an additive seventh-power relation for extracted
coordinates of `beta`. Such a coordinate relation, positive primitive successor,
and strict decrease remain subsequent obligations, not consequences asserted
by this receiver. No unconditional FLT7 theorem is exposed.

## Files and validation

New implementation:

- `DkMath/Lib/NumberTheory/FiniteIdealPowerAggregation.lean`
- `DkMath/FLT/Seven/CurrentCarrierCutoff.lean`
- `DkMath/FLT/Seven/CurrentFiniteAggregation.lean`
- `DkMathTest/FLT/CurrentFiniteAggregation.lean`

Facade imports: `DkMath.Lib`, `DkMath.FLT.Seven`, and `DkMathTest`.
Regression cases check empty selections, `h.c = 1` preserving the entire
remainder, current orientation/exact cutoff for every rational common-support
row, and the explicit exponent/unit/source-equation boundary of the receiver.

- Focused current cutoff/aggregation build: passed (9187 jobs).
- Combined regression and public facade build:
  `lake build DkMathTest.FLT.CurrentFiniteAggregation DkMath.FLT.Seven DkMath.FLT.Prime DkMath.Lib`:
  passed (9338 jobs).
- Full `lake build`: passed (10347 jobs).
- Full `lake build DkMathTest`: passed (10937 jobs).
- All 23 new public theorem endpoints were audited by the regression module's
  `#print axioms`: only `propext`, `Classical.choice`, and `Quot.sound`.
- New implementation/test files contain no `sorry`, `sorryAx`, `admit`,
  `axiom`, `unsafe`, or `native_decide`; tracked and new-file whitespace checks passed.
- The full build replays pre-existing incomplete research declarations elsewhere
  in the repository. None appears in the new endpoints' axiom dependencies.

Validation logs are under
`/tmp/drc-008-current-final.log`, `/tmp/drc-008-validated.log`,
`/tmp/drc-008-full-build.log`, and `/tmp/drc-008-full-test.log`.
