# review-000 — GNIP-000 neutral gnomon algebra recovery

## Verdict

**APPROVED — Outcome A: RECOVERY + GENERALIZATION COMPLETE**

The implementation matches `instruction-000.md` and establishes the neutral gnomon algebra needed before any Cosmic, Collatz, or Legendre bridge is added.

## What is now production-proved

The new neutral module `DkMath.Gnomon.Algebra` provides:

```text
oddGnomon n = 2*n+1
squareGnomonBand x u = u*(2*x+u)
petalMul a b = 2*a*b+a+b
```

and kernel-checks the requested algebraic laws, including:

```text
oddGnomon (petalMul a b) = oddGnomon a * oddGnomon b
x^2 + squareGnomonBand x u = (x+u)^2
squareGnomonBand x 1 = oddGnomon x
squareGnomonBand x (u+v)
  = squareGnomonBand x u + squareGnomonBand (x+u) v
squareGnomonBand x u
  = sum_{i<u} oddGnomon (x+i)
sum_{i<n} oddGnomon i = n^2
```

The arbitrary-thickness composition theorem is the important new structural result.  It packages square growth as an exact path-composition law rather than only a unit successor identity.

## Dependency audit

`DkMath.Gnomon.Algebra` remains application-neutral.  It imports no Collatz, Legendre, MultiGauge, Cosmic/GTail, Polyomino, FLT, or ABC module.  This is the correct dependency direction for later bridge modules.

The Collatz API remains untouched, as required.  Compatibility refactoring is still deferred to GNIP-002.

## Concrete regressions

The requested anchors are present, including:

```text
oddGnomon 30 = 61
oddGnomon 31 = 63
squareGnomonBand 30 1 = 61
squareGnomonBand 30 2 = 124 = 61+63
```

These are arithmetic regressions only and make no prime-existence or Legendre claim.

## Next justified checkpoint

GNIP-001 is justified.

The existing Cosmic Formula orientation is:

```text
(x + u)^d = x * GTail d 1 x u + u^d.
```

Therefore, when `x` is the current square side and `u` is the growth thickness, the exact degree-two bridge uses the **reversed GTail coordinate order**:

```text
squareGnomonBand x u
  = u * GTail 2 1 u x
```

with the normalized shell identity:

```text
GTail 2 1 u x = 2*x + u.
```

The unit specialization is:

```text
GTail 2 1 1 x = oddGnomon x.
```

This agrees with the already-approved Legendre successor-increment orientation `GTail 2 1 1 n = 2*n+1`.

GNIP-001 should add only this neutral Cosmic bridge and its exact square-growth consequences.  It must not yet refactor Collatz or add Legendre claims.
