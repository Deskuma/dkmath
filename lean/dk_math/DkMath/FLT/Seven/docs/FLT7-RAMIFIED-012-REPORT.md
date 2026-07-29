# FLT7-RAMIFIED-011U / 012 implementation report

## Outcome

**Outcome A: the projective global unit-class criterion and exact source
seventh powers are complete.**

This checkpoint closes both the deferred RAMIFIED-011U unit obstruction and
the advertised RAMIFIED-012 pure source equation.

## Local theta-coordinate logarithm

`SevenRealCubicUnitClass.lean` reduces the translated basis
`1, theta, theta^2` modulo seven through:

```text
A(x) = fst + 3*snd + 9*thd
B(x) = snd + 6*thd
C(x) = thd.
```

The verified multiplication laws are:

```text
A(xy) = A(x)A(y)
B(xy) = A(x)B(y) + B(x)A(y)
C(xy) = A(x)C(y) + B(x)B(y) + C(x)A(y).
```

For a global unit, `A` cannot vanish. The normalized coordinates
`X=B/A`, `Y=C/A` therefore define:

```text
projectiveLog(u) = (X, Y - X^2/2).
```

Lean proves this is a homomorphism from the multiplicative unit group to the
additive group `ZMod 7 × ZMod 7`, and hence:

```text
projectiveLog(u^7) = 0
projectiveLog(-1) = 0.
```

The two explicit units give:

```text
projectiveLog(alpha)     = (5,5)
projectiveLog(1 + alpha) = (2,5)
det = 5*5 - 2*5 = 1.
```

Thus their images span the complete two-dimensional local target.

## Global unit quotient

The logarithm is transported through
`SevenRealCubicInt ≃+* O_K`, kills the torsion subgroup, and descends to:

```text
UnitClassModSeven =
  (O_K^x / torsion) / 7*(O_K^x / torsion).
```

The global cardinal calculation uses only established Mathlib surfaces:

```text
unit rank K = 2
torsion units = {1,-1}
Nat.card UnitClassModSeven = 7^2 = 49.
```

The explicit determinant proves surjectivity of the descended logarithm.
Since both finite types have cardinality `49`, Lean obtains bijectivity.

Unpacking a zero `ModN` class produces a seventh-power representative modulo
torsion. The remaining torsion unit is `1` or `-1`; because the exponent
seven is odd, either sign can be absorbed into the root. This proves:

```text
(exists v, u = v^7)
  <-> projectiveLog(u) = 0.
```

No assertion that `alpha` and `1+alpha` generate the full integral unit group
is needed. They only generate the quotient modulo seventh powers, which is
the exact required statement.

## Source bridge and exact packet

For a primitive loaded source `a+b*alpha` with `7 | b`, Lean proves its
constant theta coordinate is nonzero modulo seven. It also proves that the
linear and quadratic theta coordinates of every seventh power vanish.

If:

```text
a+b*alpha = u*root^7,
```

comparison of the three theta coordinates forces both nilpotent coordinates
of `u` to vanish. Therefore `projectiveLog(u)=0`, and the global criterion
makes `u` a seventh power.

This argument applies independently to the left and right source units.
Their roots are absorbed into the previous source roots, producing
`RamifiedRealCubicExactPowerPacket`:

```text
etaL = leftRoot^7
etaR = rightRoot^7

rightRoot^7 - leftRoot^7 =
  normalizedAxis^6 * normalizedWitness^7.
```

Every `RamifiedRealCubicNormPacket` now constructs a nonempty exact-power
packet through the existing up-to-unit packet.

## Axiom and implementation audit

The exported checkpoint theorems depend only on:

```text
propext
Classical.choice
Quot.sound
```

There is no `sorryAx`, new axiom, or `native_decide`.

## Inference and next prediction

RAMIFIED-012 is the final **unit-elimination and exact-source-power**
checkpoint, but it is not the final ramified checkpoint and not the final
FLT7 theorem.

The next natural input is now exact and cleaner than before:

```text
XR^7 - XL^7 = varpi^6*Z^7.
```

RAMIFIED-013 should prove the exact depth ledger:

```text
RHS depth                  = 13
XR - XL depth              = 10
cyclotomic quotient depth  = 3.
```

The recommended implementation remains a small exact-divisibility packet,
not a general valuation theory for the cubic ring. The first reusable lemma
should be the reduction fact that the Eisenstein axis divides
`x^7 - x`. This permits the initial gap divisibility; the exact quotient
depth then requires the binomial expansion and the nonvanishing scalar
coordinate of the roots.

The independent RAMIFIED-009B signed-root-gap routing and the construction
of a recursive smaller Fermat counterexample are still open. Consequently,
the pure equation must not yet be reported as a terminal contradiction or a
completed descent.

## Stop boundary

This checkpoint does not claim:

- the RAMIFIED-013 depth `13/10/3` split;
- an exact axis exponent drop;
- a new primitive Fermat counterexample;
- an inhabited recursive descent provider;
- the unconditional FLT7 theorem.
