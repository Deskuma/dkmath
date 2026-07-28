# FLT7-RAMIFIED-010 implementation report

## Outcome

**Outcome A: the planned maximal-order and class-number-one bridge is
complete.**

The implementation also fixes the stronger concrete comparison needed by
the next checkpoint: the RAMIFIED-009 coordinate ring itself is explicitly
ring-equivalent to the full ring of integers.

## Lean implementation

`SevenRealCubicEisenstein.lean` fixes the translated ramified coordinate
`theta = alpha - 3` and proves:

```text
theta^3 + 7*theta^2 + 14*theta + 7 = 0
theta^3 = -7*(theta + 1)^2
IsUnit (theta + 1)
Associated ramifiedAxis theta.
```

For

```text
f(X) = X^3 + 7*X^2 + 14*X + 7
```

Lean proves monicity, degree three, discriminant `49`, the Eisenstein
criterion at `(7)`, irreducibility over `Z`, and irreducibility after mapping
to `Q`.

The same file defines the cyclic coordinate automorphism and verifies:

```text
sigma(alpha) = alpha^2 - 2*alpha
sigma^2(alpha) = -alpha^2 + alpha + 2
sigma^3 = id.
```

`SevenRealCubicNumberField.lean` defines the number field as the
`AdjoinRoot` of `f` over `Q`. It constructs the rational power basis,
proves its discriminant is `49`, and uses the Eisenstein prime-power
membership theorem to show that every algebraic integer lies in
`Z[theta]`. Therefore:

```text
IsIntegralClosure Z[theta] Z K
Z[theta] ≃ₐ[Z] O_K.
```

An integral power basis then gives:

```text
disc K = 49
nrComplexPlaces K = 0
IsTotallyReal K
Minkowski class bound = 14/9
Minkowski class bound < 2
IsPrincipalIdealRing O_K
classNumber K = 1.
```

Finally, the original coordinate model maps its generator `alpha` to
`theta + 3`. Surjectivity follows from the integral power basis. Injectivity
is proved by comparing the three basis coordinates. This yields:

```text
modelEquivRingOfIntegers :
  SevenRealCubicInt ≃+* O_K

modelIsDomain :
  IsDomain SevenRealCubicInt.
```

Conjugating the coordinate rotation through this equivalence gives an
order-three automorphism of `O_K` with the same formulas.

## Proof-engineering note

The maximal-order comparison creates several plausible but definitionally
different algebra and scalar-tower instances. The implementation avoids an
instance diamond by passing the relevant `IsIntegralClosure`,
`IsScalarTower`, torsion-free, and localization arguments explicitly when
constructing the comparison equivalence, integral power basis, and field
discriminant transport.

No index formula or unproved local-maximality shortcut is assumed. The
maximality proof uses the existing discriminant membership bound together
with the Eisenstein prime-power removal theorem.

## Axiom audit

The exported checkpoint theorems report only the standard foundations used
throughout this development:

```text
propext
Classical.choice
Quot.sound
```

There is no `sorryAx`; no new axiom and no `native_decide` is used.

## Inference and prediction

RAMIFIED-011 now has all ambient algebraic-number-theory infrastructure it
needs:

```text
RAMIFIED-009 source elements
  -> modelEquivRingOfIntegers
  -> principal ideals in O_K
  -> transported cyclic rotation
  -> conjugate-ideal coprimality
  -> seventh-divisible prime-ideal exponents
  -> principal seventh-root ideals.
```

The first genuinely new obligation is not class-group theory. It is the
pairwise coprimality of the three conjugate source ideals. The expected proof
should use
`sigma(alpha) - alpha = alpha*(alpha - 3)`, the fact that `alpha` is a unit,
the unique ramified axis represented by `theta`, and the existing primitive
integer coprimality ledger.

After ideal extraction, a relative unit remains. Class number one does not
remove it. RAMIFIED-011U must separately prove that the relevant local
depth-six unit class injects into global units modulo seventh powers. The
finite `49`-class audit and proof that the proposed units generate the full
unit group are still missing inputs.

RAMIFIED-009B is an independent integer route and can be developed without
changing this maximal-order API.

## Stop boundary

This report stops at RAMIFIED-010. It does not begin RAMIFIED-011 ideal
extraction, RAMIFIED-011U unit classification, or RAMIFIED-012 element-level
seventh-power extraction and depth descent.
