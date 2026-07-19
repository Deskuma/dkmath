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
