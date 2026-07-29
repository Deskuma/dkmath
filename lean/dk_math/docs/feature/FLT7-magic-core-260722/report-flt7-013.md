# FLT7-013 implementation report

## Outcome

Outcome B.

```text
7-primary routing: completely localized
non-7 prime routing: explicit local systems, still open
```

The first-coordinate equations identify the unique `7` pivot and attach an
explicit congruence to every routing cell. They do not yet eliminate all
off-permutation cells or construct a new primitive FLT7 packet.

## Files changed

- `DkMath/FLT/Seven/FirstCoordinateRemainders.lean`
- `DkMath/FLT/Seven/RoutingSevenPivot.lean`
- `DkMath/FLT/Seven/FirstCoordinateRoutingAudit.lean`
- `DkMath/FLT/Seven/CoprimeTripleRouting.lean`
- `DkMath/FLT/Seven.lean`
- `DkMathTest/FLT/SevenRoutingSevenPivot.lean`
- `DkMathTest/FLT/SevenFirstCoordinateRoutingAudit.lean`
- `docs/feature/FLT7-magic-core-260722/report-flt7-013.md`

## First-coordinate identities

The endpoint coordinate `A(z,y)` satisfies

```text
A-z^3 = y(z-y)(z+y),
A+y^3 = z^2(z+y).
```

The corresponding divisibility theorems expose the row residues for `y`, `z`,
and `y+z`.

For the root first coordinate `F(u,v)`, the following exact divisions are
proved by `ring`:

```text
F = u^7 + v^2 * VResidual,
F = P * leftFstQuotient - 49*v^5*leftFstCorrection,
F = Q * rightFstQuotient + 49*v^5*rightFstCorrection.
```

Their divisibility consequences form the three root-column remainders.

## Root sector and seven pivot

`AwayRootResidueSector` combines each away endpoint sector with the collapsed
root coordinate `u+4v` modulo seven. In the three branches it proves

```text
Y carrier:   u+4v =  t^3,
Z carrier:   u+4v = -t^3,
sum carrier: u+4v = -t^3,
```

with `t ≠ 0`. Consequently `rootLinear_ne_zero` agrees with the inherited norm
nondivisibility.

`AwayRoutingSevenPivot` proves exactly one of:

```text
Y carrier:   7 | c11,
Z carrier:   7 | c21,
sum carrier: 7 | c31,
```

and records nondivisibility by `7` for the other eight cells. Columns `P,Q`
are outside the seven channel by the second-core theorem; the two
nonexceptional rows exclude the other cells in column `7|v|`.

`AwayRoutingPivotDepth` proves that the pivot carries all exceptional depth:

```text
v7(pivot) = v7(carrier) = 1 + v7(|root.snd|).
```

This reuses the FLT7-011 transfer equality. It does not repeat its proof.

The FLT7-012 product packet now stores `normal_eq`, preserving the already true
fact that its transfer and root triple arise from the same normal form. This
provenance equality is necessary to state the depth identity without an
unrecorded definitional assumption.

## Nine first-coordinate constraints

`AwayFirstCoordinateRoutingConstraints` packages the root sector, unique pivot,
six full integer constraints in the `P,Q` columns, and three prime-level
non-seven constraints in the `7|v|` column.

For `P`, the three values are

```text
z^3 + 49*v^5*leftCorrection,
49*v^5*leftCorrection - y^3,
49*v^5*leftCorrection - y^3.
```

For `Q`, they are

```text
z^3 - 49*v^5*rightCorrection,
y^3 + 49*v^5*rightCorrection,
y^3 + 49*v^5*rightCorrection.
```

For any prime `q != 7` in the first column, the row constraints are

```text
u^7-z^3, u^7+y^3, u^7+y^3.
```

## Local-prime extraction

`EndpointRoutingRow`, `RootRoutingColumn`, `routingCell`, and
`routingFirstCoordinateValue` give stable labels to the grid.
`routingPrimeWitness_of_cell_ne_one` chooses a prime divisor of every
nontrivial cell and records:

- divisibility of the corresponding endpoint factor;
- divisibility of the root factor when `q != 7` (or the distinguished
  `q = 7` case);
- divisibility of the cell's exact first-coordinate constraint when
  `q != 7`;
- the unique seven-pivot certificate when `q = 7`.

Thus every surviving non-seven cell gives an explicit finite-field local
solution after translating integer divisibility into `ZMod q` zero equations.

No off-permutation cell was eliminated unconditionally. The obstruction is
now precise: for some non-seven prime, one of the nine endpoint/root systems
together with its displayed first-coordinate polynomial may remain soluble.

## Conditional closure and audit route

`AwayFirstCoordinateClosureResolution` is not an alias for the desired
provider. It stores genuinely reconstructed naturals, a new
`CounterexamplePack`, its away route, and the signed carrier compatibility.
`awayDescentClosureProvider_of_firstCoordinateResolution` converts these data
to the FLT7-012 closure provider.

No unconditional resolution was constructed. Therefore
`firstCoordinateClosureAuditResult_of_pack` uses `awayConstrained` in the away
branch and retains the ramified branch explicitly.

## Verification

Focused module and test builds, the `DkMath.FLT.Seven` facade, and the full
`DkMath.FLT` target passed. Public axiom audits report only Lean/Mathlib
foundations (`propext`, `Classical.choice`, and `Quot.sound`). No `sorry`,
`admit`, custom axiom, or `native_decide` was introduced.

## Recommended FLT7-014 boundary

Classify the finite-field local-prime systems by the nine row/column positions.
Use resultants or proved residue restrictions for the three root columns
`v,P,Q`, split across rows `y,z,y+z`. The goal is to prove selected systems
impossible, force a permutation-compatible grid, or derive the signed data
needed for `AwayFirstCoordinateClosureResolution`. Do not repeat the routing
or valuation construction.
