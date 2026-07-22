# FLT7-012 implementation report

## Outcome

Outcome B. The hidden cubic split, primitive root coordinates, pairwise-coprime
root factors, endpoint/root product comparison, and explicit `3 × 3` routing
grid are complete. The FLT7-011 depth drop becomes a strict recursive step
under an `AwayDescentClosureProvider`, but this checkpoint does not construct
that provider or a new primitive `CounterexamplePack`.

## Files changed

- `DkMath/FLT/Seven/CubicSecondCoordinateSplit.lean`
- `DkMath/FLT/Seven/CoprimeTripleRouting.lean`
- `DkMath/FLT/Seven/DescentClosureAudit.lean`
- `DkMath/FLT/Seven.lean`
- `DkMathTest/FLT/SevenCubicSecondCoordinateSplit.lean`
- `DkMathTest/FLT/SevenDescentClosureAudit.lean`
- `docs/feature/FLT7-magic-core-260722/report-flt7-012.md`

## Hidden cubic factorization

The second-coordinate core factors integrally as

```text
SndCore(u,v) = P(u,v) * Q(u,v),
P = u^3 - 2u^2v - uv^2 + v^3,
Q = u^3 + 5u^2v + 6uv^2 + v^3.
```

Theorems `seventhPowerSndCore_factor`, `seventhPowerSnd_cubic_sub`, and
`seventhPowerSnd_cubic_add` prove the factorization and the identities

```text
Q - P = 7uv(u+v),
P + Q = (2u+v) * norm(u,v).
```

Combined with the FLT7-011 load identity this gives

```text
y*z*(y+z) = 7*|v|*|P(u,v)|*|Q(u,v)|.
```

## Primitive coordinates and root triple

`AwayCoordinateNormalForm.root_coordinates_isCoprime` proves that the two
integer coordinates of the seventh-power root are coprime. A common prime
would divide both seventh-power coordinates and hence both primitive
cyclotomic coordinates, contradicting the existing Bezout certificate. Its
natural absolute-value form is also exposed.

The inherited away theorem `root_norm_not_seven_dvd` supplies the required
condition `7 ∤ norm(root)` without reproving the FLT7-011 argument.

The two cubics are nonzero because their product is the nonzero second core.
Theorems `coprime_rootSnd_leftCubic` and
`coprime_rootSnd_rightCubic` reduce the cubics modulo `v`. For
`coprime_leftCubic_rightCubic`, a common prime divides
`7uv(u+v)`; root primitivity eliminates the three coordinate factors. The
remaining prime `7` is excluded using the cubic sum and the norm modulo seven.

`AwayRootCoprimeTriple` packages positivity and all three pairwise
coprimality results for `|v|, |P|, |Q|`.

## Endpoint product and routing grid

`AwayEndpointCoprimeTriple` packages positivity and pairwise coprimality of
`y, z, y+z` directly from primitive endpoint coprimality.
`AwayCubicProductPacket` combines this triple, the root triple, the selected
valuation carrier, and the exact four-factor identity.

`CoprimeTripleRouting` records nine cells `cij`, all three row products, all
three column products, and pairwise disjointness within every row and column.
`nonempty_coprimeTripleRouting` constructs the cells canonically as
`gcd(ai,bj)`. `AwayCubicRoutingPacket` specializes it to

```text
(y, z, y+z)  versus  (7*|v|, |P|, |Q|).
```

Pairwise coprimality on both sides does not force a permutation: a row factor
may contain distinct prime components routed to different columns. The nine
gcd cells retain exactly this possibility, so no diagonalization claim has
been made.

## Closure audit

`AwayDescentClosureProvider` states the missing recursive data explicitly:
naturals `nextX,nextY,nextZ`, a new primitive
`CounterexamplePack nextX nextY nextZ`, an away valuation route for that new
packet, and the exact carrier equation

```text
nextRoute.carrier = |oldRoot.snd|.
```

Given this data, `away_depth_descent_of_closureProvider` reuses FLT7-011 to
prove the new selected carrier has strictly smaller `7`-adic depth.
`MissingClosureProviderStatement` records `Nonempty
(AwayDescentClosureProvider ...)` as the precise unproved reconstruction
obligation; it does not assert a negation.

`AwayClosureAuditResult` separates a genuinely closed provider from an open
routing result. The theorem `nonempty_awayClosureAuditResult_open` constructs
the honest open result. `ClosureAuditCounterexampleRoute` preserves the
ramified branch and has `awayClosed` and `awayOpen` branches;
`closureAuditCounterexampleRoute_of_pack` uses `awayOpen`, because no provider
has been constructed.

## Verification

The focused module, facade, and focused test builds passed. Axiom audits on the
new public theorems report only Lean/Mathlib foundations (`propext`,
`Classical.choice`, and `Quot.sound`). No `sorry`, `admit`, custom axiom, or
`native_decide` was introduced.

## Recommended FLT7-013 boundary

Attack the routing grid with the first-coordinate equation and the four
mod-seven sectors. The next target is to eliminate off-diagonal routing cells
or use the surviving cells to construct the missing new Fermat packet with
carrier `|root.snd|`. The completed valuation transfer should be reused, not
repeated.
