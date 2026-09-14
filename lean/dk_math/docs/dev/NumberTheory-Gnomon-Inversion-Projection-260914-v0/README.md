# NumberTheory Gnomon Inversion / Projection 260914 v0

## Objective

Recover the already-proved square-gnomon arithmetic from application-owned modules, promote it to a neutral reusable layer, and then test whether that layer gives a sharper Legendre formulation before returning to the ABC branch.

This campaign is intentionally narrower than the older roadmap:

```text
docs/not_implements/260730-gnomon-prime-petal-pascal-polyomino-roadmap.md
```

The old roadmap remains the broad source design.  This branch first implements only the part needed for square growth, Cosmic Formula degree two, and the Legendre square shell.

## Existing production anchors

```text
DkMath.Collatz.GnomonEvaluation
DkMath.Lib.Cosmic.GTail
DkMath.NumberTheory.StructuralArithmetic.CosmicSquareScaling
DkMath.NumberTheory.Legendre.Basic
DkMath.NumberTheory.Legendre.MultiGaugeBridge
DkMath.NumberTheory.Legendre.Frontier
```

Already production-proved in the Collatz package:

```text
OddGnomonLayer n = 2*n+1
(n+1)^2 = n^2 + OddGnomonLayer n
sum_{i<n} OddGnomonLayer i = n^2
(P+u)^2 = P^2 + sum_{i<u} (2*(P+i)+1)
```

The problem is architectural: these basic facts are application-owned and are not yet the neutral source of truth for Cosmic / Legendre work.

## Core interpretation

For anchor `x` and side-thickness `u`, define the square gnomon band by

```text
squareGnomonBand x u = u * (2*x + u).
```

Then

```text
(x+u)^2 = x^2 + squareGnomonBand x u.
```

The unit-thickness specialization is

```text
squareGnomonBand x 1 = 2*x+1.
```

Thus the `+1` is a one-unit side growth, not an area increment of one.  Its induced area layer is the odd gnomon `2*x+1`.

The intended degree-two Cosmic bridge is

```text
oddGnomon x = GTail 2 1 1 x
squareGnomonBand x u = u * GTail 2 1 u x.
```

## Legendre target interpretation

Production currently defines

```text
SquareOffset n r := 1 <= r and r <= 2*n.
```

Since `oddGnomon n = 2*n+1`, the square-cell offsets are exactly the open interior of one unit gnomon:

```text
SquareOffset n r
<->
1 <= r and r < oddGnomon n.
```

The excluded final offset `r = oddGnomon n` is the next square `(n+1)^2` itself.

This branch will test whether that exact gnomon-interior formulation exposes a genuine projection/preservation law.  It does not assume such a law in advance.

## Phases

```text
GNIP-000  recover neutral gnomon algebra + arbitrary-thickness growth
GNIP-001  connect neutral gnomon algebra to GTail/GN degree two
GNIP-002  refactor Collatz GnomonEvaluation onto the neutral layer without API breakage
GNIP-003  express the Legendre square cell as open unit-gnomon interior
GNIP-004  audit/analyze the 30 -> 31 prime-gauge boundary and decide whether a nontrivial inversion/projection theorem exists
```

## Non-goals for the recovery phase

```text
no Legendre proof claim
no prime-existence provider
no Pascal bridge yet
no Polyomino/tromino geometry yet
no PetalAtom prime equivalence yet
no analytic real-valued projection theorem unless GNIP-004 justifies one
no duplicate GN definition
no breaking rename of Collatz public theorem names
```
