# FLT7TC-005R20 — Archimedean bridge and smaller-norm frontier

## Scope

Instruction-026 asks for the production height layer over the current direct
`DirectOrbitPowerSplitPacket`.  The implementation was kept algebraic and
receiver-free.  No successor state, infinite-descent claim, floating-point
embedding argument, or historical routing packet was introduced.

## Implemented results

The new production module
`DkMath.FLT.Seven.PrimeTraceOneDirectRealCubicOrbitHeight` defines
`H7` and proves the two exact real inequalities:

```text
7 * (s*t)^3 <= H7 s t       for 0 <= s and 0 <= t
(l-r)^6 <= 64 * H7 l r     for arbitrary real l,r.
```

The proofs use the explicit sum-of-squares identities from the Astra scratch
certificate and do not use numerical approximation.  The module is exported
from `DkMath.FLT.Seven`, with dedicated API and axiom tests.

## Precise production frontier

The current direct API proves

```text
rho = QuadraticAlgebra.norm gammaNorm
directChosenQuotientRealSource = rho^7
SevenRealCubicInt.norm rho = residualRoot.
```

It does not yet provide the required map from `SevenRealCubicInt` into the
three real embeddings of `SevenRealCubic.Field`, nor an explicit theorem that
each embedding of the relative norm is `z * conjugate z > 0`.  Consequently,
the following dependent results were not asserted:

- total positivity of the three images of `rho`;
- the lower bound `norm H >= 7^3 * B^6`;
- the stripped-gap absolute norm identity;
- `G^7 * B^6 <= a^42`;
- `A^42 < B^7`;
- `0 < G < a <= A`;
- a `DirectOrbitSmallerNormPacket` constructor.

This is **Outcome C — the real-embedding / total-positivity bridge is the
precise frontier**.  The unresolved projective unit classes `(2,4)` and
`(5,1)` are not used and are not a prerequisite for the height route.  The
production source records this as a TODO: the smaller-norm argument needs unit
norm `abs(norm unit) = 1`, not a projective unit-class classification.

## Successor-state data still required

Even after the strict integer inequality is available, a successor constructor
would need a new positive primitive endpoint triple, its exact seventh-power
equation and gcd data, the corresponding ramified provenance packet, and a
fresh normalized cyclotomic/real-cubic root packet.  The current smaller norm
datum alone is not such a successor state.

## Verification log

The following Lean commands were run sequentially:

```text
lake env lean DkMath/FLT/Seven/PrimeTraceOneDirectRealCubicOrbitHeight.lean
lake build DkMath.FLT.Seven.PrimeTraceOneDirectRealCubicOrbitHeight
lake build DkMathTest.FLT.SevenPrimeTraceOneDirectRealCubicOrbitHeightApi
lake build DkMathTest.FLT.SevenPrimeTraceOneDirectRealCubicOrbitHeightAxiom
lake build DkMath.FLT.Seven
```

All commands completed successfully.  The axiom audit for the two
production inequalities reports only `propext`, `Classical.choice`, and
`Quot.sound`.  The decisive source and tests contain no `sorry`, `sorryAx`,
`admit`, `unsafe`, or project `axiom` declaration.

## Boundary

This checkpoint productionizes the real polynomial inequalities and isolates
the exact missing field/embedding bridge.  It does not claim a strict smaller
norm, a successor, infinite descent, or unconditional FLT7 closure.
