# CODEX — Gnomon Inversion / Projection 260914 v0

Branch:

```text
wip/number-theory-gnomon-inversion-projection-260914-v0
```

## Read first

```text
docs/not_implements/260730-gnomon-prime-petal-pascal-polyomino-roadmap.md
DkMath/Collatz/GnomonEvaluation.lean
DkMath/Lib/Cosmic/GTail.lean
DkMath/NumberTheory/StructuralArithmetic/CosmicSquareScaling.lean
DkMath/NumberTheory/Legendre/Basic.lean
DkMath/NumberTheory/Legendre/MultiGaugeBridge.lean
DkMath/NumberTheory/Legendre/Frontier.lean
```

## Architecture rules

1. `DkMath.Gnomon.Algebra` is neutral pure arithmetic.
2. It must not import Collatz, Legendre, MultiGauge, Pascal, Polyomino, FLT, ABC, or application modules.
3. Do not duplicate or redefine `GTail`/`GN` in the algebra layer.
4. Cosmic identities belong in a bridge module after the pure layer is stable.
5. Existing public Collatz theorem names must remain available when refactored later.
6. Do not state a Legendre existence theorem from a gnomon rewrite alone.
7. Distinguish the full unit gnomon size `2*n+1` from the open Legendre interior offsets `1..2*n`.
8. Prefer additive Nat identities over subtraction when possible.
9. No `sorry`, `admit`, new `axiom`, or decorative provider predicates.

## Mathematical normal form

```text
oddGnomon n = 2*n+1
squareGnomonBand x u = u*(2*x+u)

x^2 + squareGnomonBand x u = (x+u)^2
squareGnomonBand x 1 = oddGnomon x

squareGnomonBand x (u+v)
=
squareGnomonBand x u + squareGnomonBand (x+u) v

squareGnomonBand x u
=
sum_{i<u} oddGnomon (x+i)
```

The intended interpretation is: `u` is side-thickness.  In particular `u=1` is the atomic lattice growth step; the induced area increment is `2*x+1`.

## Validation

For each implementation checkpoint:

```text
lake build <focused-module>
lake build <changed-facade-if-any>
git diff --check
```

Scan changed Lean files for:

```text
sorry
admit
axiom
```

Report exact theorem names and any scope deviation.
