# FLT5 cp-004f+ rolling report

Date: 2026-07-20
Branch: `hackathon/feature-gn5-flt5-260719-v0`

## cp-004f certified endpoint

The explicit `GoldenInt` coordinate model now carries a verified `CommRing`
instance.  Its operations and natural powers remain definitionally compatible
with `goldenAdd`, `goldenMul`, and `goldenPow`.  No integral-domain, gcd, UFD,
PID, or Euclidean instance has been declared.

`GoldenDivisibility.lean` certifies divisibility transport through the norm,
conjugation compatibility, norm formulas for powers, and both directions
needed between golden units and norm `1` or `-1`.

The power-split packet now retains its construction-time theorem
`coprime_a_b`.  It also publishes:

```lean
Nat.Coprime (5^15 * a^20) (b^5)
Nat.Coprime (b^5) (5^15 * a^20)
```

For every ramifier-stripped packet, the following theorem is certified:

```lean
SignedGoldenRamifierStrippedPacket.beta_relPrime_conj :
  GoldenRelPrime beta (goldenConj beta)
```

The proof sends a common golden divisor through the norm.  Its norm divides
both `b^5` and `-5^15*a^20`; natural absolute values and the recovered
coprimality force absolute norm one, so the explicit conjugate supplies an
inverse.

The public packet `SignedGoldenConjugateCoprimePacket` retains this result and
has constructors and receivers for the signed Branch-A and routed Branch-B
layers.

## Active next attack

cp-004g investigates fifth-power extraction up to a unit.  The certified input
is now packet-specific conjugate coprimality, but no factorization theorem is
assumed.  Routes through generic factor splitting, packet-specific extraction,
a norm-Euclidean algorithm, and ideals will be audited in that order.

This remains an FLT5 reduction campaign, not a completed proof of FLT5.

## cp-004g route audit and exact blocker

The packet now certifies the precise power equation

```lean
beta * goldenConj beta = goldenPow (goldenOfInt b) 5.
```

The narrowest missing next theorem is published as the full proposition
`GoldenCoprimeFactorOfFifthPower`:

```lean
∀ x y z : GoldenInt,
  GoldenRelPrime x y →
  goldenMul x y = goldenPow z 5 →
  ∃ epsilon gamma : GoldenInt,
    GoldenUnit epsilon ∧
    x = goldenMul epsilon (goldenPow gamma 5)
```

`signedGoldenFifthPowerUpToUnitCore_of_coprimeFactor` proves that this one
theorem is sufficient to inhabit the previously published packet-specific
core.

The investigated routes stop as follows:

- Generic factor split: Mathlib's theorem requires genuine unique
  factorization or equivalent gcd infrastructure.  The new honest
  `CommRing` alone is intentionally insufficient.  A subsequent doubled
  embedding `a+b*phi |-> (2a+b)+b*sqrt(5)` into `Zsqrtd 5` certifies
  `NoZeroDivisors` and `IsDomain` without confusing the two orders.  Thus the
  remaining missing structure is factorization/GCD, not domainhood.
- Packet-specific prime exponents: conjugate coprimality is now available, but
  existence and uniqueness of irreducible decompositions in `Z[phi]` would be
  the same missing input in a less reusable form.
- Euclidean order: no quotient/remainder API for `Z[phi]` is present.  A valid
  implementation would require nearest-lattice division and a certified norm
  decrease; no instance was fabricated.
- Ideals: `Zsqrtd 5` is `Z[sqrt 5]`, not the full ring `Z[phi]`.  The repository
  has no exact ring-of-integers bridge plus principal-ideal/class-number-one
  result for this order.

## cp-004h unconditional coordinate progress

`GoldenFifthPowerCoordinates.lean` certifies the exact two coordinate
polynomials of `(p+q*phi)^5`.  It also certifies the second coordinate after
multiplication by each representative `1, phi, phi^2, phi^3, phi^4`; negating
the representative negates that coordinate.  `goldenPhi`, its powers, their
products, and their negatives are explicitly certified units.

These formulas permit finite unit-class work after factorization, but do not
bypass existence of `epsilon` and `gamma`.  Consequently descent and final
assembly cannot be soundly entered from the current unconditional hypotheses.

Mathlib's closest reusable endpoint is
`exists_associated_pow_of_mul_eq_pow`, available under a genuine `GCDMonoid`.
No `GCDMonoid GoldenInt` can be declared without constructing gcds (for
example through a verified norm-Euclidean division algorithm).  The proposition
`GoldenCoprimeFactorOfFifthPower` remains narrower than asking for that global
instance and is therefore the final exact blocker for the next packet step.
