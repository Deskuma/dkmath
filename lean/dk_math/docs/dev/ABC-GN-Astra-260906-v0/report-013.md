# LUNA-013 — squareful parity / Pell-shell coordinates

## Scope and files

This checkpoint freezes the generic odd/even squareful decomposition and its
application to every represented LUNA-012 shell pair. It adds exact conic
coordinates only: no Pell solution count, shell estimate, fiber estimate,
provider assumption, or use of `abc_main_axiom` is introduced.

Changed files:

- `DkMath/ABC/GNExcessCubicSquarefulPell.lean`
- `DkMath/ABC.lean` (public import after the LUNA-012 module)
- `README.md`, `ROADMAP.md`, `validation-013.txt`, and this report.

## Generic odd/even arithmetic

`squarefree_oddPart` proves directly from the factorization support that
`oddPart n` is squarefree. The proof bounds each odd exponent by one and uses
the squarefree product of distinct prime support elements.

`oddPart_dvd_evenPart_of_squarefull` proves, for nonzero squareful `n`,

```text
oddPart n ∣ evenPart n.
```

At every support prime, squarefullness gives factorization exponent at least
two; the odd-exponent contribution is therefore absorbed by the floor-half
exponent in `evenPart`.

`squareful_oddEven_packet` packages

```text
n = oddPart n * (evenPart n)^2,
Squarefree (oddPart n),
oddPart n ∣ evenPart n.
```

The optional classical representation was also proved:
`exists_sq_mul_cube_of_squarefull` gives `n = u^2 * r^3` with `Squarefree r`.

## Realized modulus bridge and pair packet

`GNExcessCubicRealizedLargeModulusSpace_squarefull` consumes the existing
prime-square divisor theorem for realized cubic moduli and exposes the
project's generic `squarefull M` predicate without duplicating factorization
reasoning.

For a represented incidence pair,
`GNExcessCubicRealizedLargeModulusShellIncidencePair_squareful_packet` gives

```text
M = oddPart M * (evenPart M)^2
Squarefree (oddPart M)
oddPart M ∣ evenPart M
Squarefree S
Nat.Coprime M S
Nat.Coprime (oddPart M) S
D ≤ M < 2D
X+1 < M
1 ≤ S ≤ X.
```

The last coprimality fact is the divisor consumer of `oddPart M ∣ M`.

## Squarefree Pell parameter and exact shell identity

`GNExcessCubicRealizedLargeModulusShellIncidencePair_squarefree_pellParameter`
proves that the combined parameter

```text
T = oddPart M * S
```

is squarefree. The odd parity factor is retained explicitly; it must not be
collapsed to `S` when an odd repeated exponent occurs in `M`.

For any concrete shell witness `a` representing `(M,S)`,
`GNExcessCubicRealizedLargeModulusShellIncidencePair_pell_identity` proves the
exact natural identity

```text
(2*a + 3)^2 + 3
  = 4 * (oddPart M * S) * (evenPart M)^2.
```

The proof combines the existing cubic discriminant identity, the LUNA-012
pair equation `M*S = a^2 + 3*a + 3`, and `decomp_oddPart_evenPart`. No
subtraction in `Nat` is used.

`GNExcessCubicRealizedLargeModulusShellIncidencePair_pell_packet` exposes all
coordinates simultaneously: `y = 2*a+3`, `d = evenPart M`, `r = oddPart M`,
`T = r*S`, the squareful decomposition, squarefree data, divisibility, shell
bounds, and

```text
y^2 + 3 = 4*T*d^2.
```

It also records `0 < y`, odd parity of `y`, and `3 ≤ y`.

The optional coprimality theorem `Nat.Coprime (2*a+3) M` was left deferred
because it is not needed for the exact coordinate packet. An additional
finite Pell-parameter image space was likewise not added; the parameter is
already exposed in the packet and no count is required here.

## Verification and trust boundary

Focused build:

```text
lake build DkMath.ABC.GNExcessCubicSquarefulPell  PASS
```

The public `DkMath.ABC` aggregator was rebuilt after adding the import. The
new production file contains no `sorry`, `admit`, new `axiom`,
`abc_main_axiom`, or `native_decide`. The generic squareful lemmas, realized
bridge, pair packet, squarefree parameter, Pell identity, and Pell packet
audit to the standard boundary `propext`, `Classical.choice`, and
`Quot.sound` (or a subset).

## Remaining research boundary

The exact lattice view from LUNA-012 and the exact negative-Pell view now
coexist:

```text
M*S = a^2 + 3*a + 3
(2*a+3)^2 + 3 = 4*(oddPart M*S)*(evenPart M)^2.
```

The remaining question is still arithmetic incidence: no theorem here counts
fixed-`T`, fixed-`S`, or fixed-`M` solutions, bounds a shell, or couples the
coordinates to ABC quality. Squareful parameterization is recorded as an
exact representation only.
