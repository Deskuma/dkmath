# LUNA-015 — primitive Pell support packet

## Scope and files

This checkpoint freezes the primitive local arithmetic of the LUNA-014
square-cube and Pell coordinates. It adds exact divisibility, support
congruence, coprimality, gcd, and square-divisibility statements. It does not
count Pell solutions, estimate shells or fibers, introduce a provider, or use
`abc_main_axiom`.

Changed files:

- `DkMath/ABC/GNExcessCubicPrimitivePell.lean`
- `DkMath/ABC.lean` (public import after LUNA-014)
- `README.md`, `ROADMAP.md`, `validation-015.txt`, and this report.

## Squareful divisibility hierarchy

For nonzero squareful `M`, the module exposes:

```text
oddPart M ∣ evenPart M
GNExcessCubicSquarefulQuotient M ∣ evenPart M
evenPart M ∣ M
oddPart M ∣ M
GNExcessCubicSquarefulQuotient M ∣ M.
```

The proofs consume the LUNA-013 odd/even packet and the LUNA-014 canonical
quotient reconstruction; no factorization calculation is repeated.

## Prime support congruence

The following coordinate consumers are proved for every realized large
modulus:

```text
q ∣ oddPart M       -> q % 3 = 1
q ∣ evenPart M      -> q % 3 = 1
q ∣ squarefulQuotient M -> q % 3 = 1
```

Each is a short divisibility transport into the existing realized-modulus
theorem `GNExcessCubicRealizedLargeModulusSpace_prime_mod_three_eq_one`.

## Pell `y` coprimality

`GNExcessCubicRealizedLargeModulusShellWitness_coprime_pellY_modulus` proves

```text
Nat.Coprime (2*a+3) (FullRepeatedModulus a).
```

The proof extracts a common prime divisor, transports it through the canonical
product equation and the discriminant identity, forces that prime to divide
`3`, and contradicts the realized support congruence `q % 3 = 1`.

The packet
`GNExcessCubicRealizedLargeModulusShellWitness_pellY_coordinate_coprime_packet`
then inherits coprimality with `oddPart M`, `evenPart M`, and the canonical
squareful quotient using the divisibility hierarchy.

## Complement and Pell-parameter gcd boundary

For a represented pair,
`GNExcessCubicRealizedLargeModulusShellIncidencePair_squareCube_coprime_packet`
proves both

```text
Nat.Coprime (evenPart M) S
Nat.Coprime (squarefulQuotient M) S.
```

The theorem
`GNExcessCubicRealizedLargeModulusShellIncidencePair_gcd_pellY_pellParameter_dvd_three`
freezes the exact exceptional-prime boundary:

```text
Nat.gcd (2*a+3) (oddPart M*S) ∣ 3.
```

The optional classification `gcd = 1 ∨ gcd = 3` was intentionally not added;
the divisibility statement is the stable consumer needed by the fixed-
parameter packet.

## Square divisibility and local root packets

The production Pell identity yields:

```text
(evenPart M)^2 ∣ (2*a+3)^2 + 3
```

through
`GNExcessCubicRealizedLargeModulusShellIncidencePair_evenPart_sq_dvd_pellValue`.
The corresponding squareful-quotient square divisibility theorem is also
provided.

For a prime divisor of `evenPart M`,
`GNExcessCubicRealizedLargeModulusShellIncidencePair_evenPart_prime_packet`
packages a represented witness together with

```text
q % 3 = 1,
q^2 ∣ (2*a+3)^2 + 3.
```

The quotient-prime packet is provided by transporting quotient divisibility to
the even-part packet. These are exact local root conditions, not rarity
claims.

## Fixed-`T` primitive conic packet

For every witness in
`GNExcessCubicRealizedLargeModulusShellPellParameterFiber X D T`,
`GNExcessCubicRealizedLargeModulusShellPellParameterFiber_primitive_packet`
exposes:

```text
0 < evenPart M
0 < squarefulQuotient M
(2*a+3)^2 + 3 = 4*T*(evenPart M)^2
Nat.Coprime (2*a+3) (evenPart M)
Nat.Coprime (2*a+3) (squarefulQuotient M)
Nat.gcd (2*a+3) (oddPart M * S) ∣ 3
(evenPart M)^2 ∣ (2*a+3)^2 + 3
q ∣ evenPart M -> q % 3 = 1 ∧ q^2 ∣ (2*a+3)^2+3.
```

The optional integer-valued Pell equation was not duplicated; the exact natural
equation already present in LUNA-014 is the primary production interface.

## Verification and trust boundary

Focused module:

```text
lake build DkMath.ABC.GNExcessCubicPrimitivePell  PASS
```

The public `DkMath.ABC` aggregator was rebuilt after adding the import. Changed
Lean sources contain no `sorry`, `admit`, new `axiom`, `abc_main_axiom`, or
`native_decide`. Audited declarations remain within the standard boundary
`propext`, `Classical.choice`, and `Quot.sound` (or a subset).

## Remaining research boundary

The new packets do not imply Pell-solution rarity, fixed-`T` fiber bounds,
shell counts, incidence sparsity, Hensel density decay, paired relative-height
exclusion, or ABC quality coupling. In particular, `q^2 ∣ y^2+3`,
`q % 3 = 1`, and `gcd(y,T) ∣ 3` are exact local conditions only.
