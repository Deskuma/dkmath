# LUNA-016 — exceptional-three sector normalization

## Scope and files

This checkpoint resolves the exceptional prime `3` in the LUNA-015 fixed-`T`
Pell packet. It adds exact divisibility, gcd classification, quotient
reconstruction, and two-sector normal forms. It does not count either sector,
estimate a fiber, introduce a provider, or use `abc_main_axiom`.

Changed files:

- `DkMath/ABC/GNExcessCubicThreeSector.lean`
- `DkMath/ABC.lean` (public import immediately after `GNExcessCubicPrimitivePell`)
- `README.md`, `ROADMAP.md`, `validation-016.txt`, and this report.

## Exact factor-three layer

`three_dvd_cubicQuadratic_iff` proves

```text
3 ∣ a² + 3a + 3  ↔  3 ∣ a.
```

`three_dvd_pellY_iff` transports the same sector condition to `2a+3`.
`cubicQuadratic_three_exact_depth_one` combines the divisibility with the
existing `¬ 9 ∣ a²+3a+3` theorem, so the cubic quadratic has exact depth one.

Every realized large modulus is prime to `3`; coordinate consumers expose the
corresponding non-divisibility for its odd part, even part, and squareful
quotient.

## Complement, Pell parameter, and gcd boundary

For a shell witness, the new equivalences are:

```text
3 ∣ Complement a       ↔ 3 ∣ a
3 ∣ (oddPart M * S)    ↔ 3 ∣ a.
```

The complement cannot be divisible by `9`. For an incidence pair, the exact
gcd classification is

```text
gcd (2a+3) (oddPart M*S) = 1 ∨ gcd (2a+3) (oddPart M*S) = 3,
```

with `gcd = 3` equivalent to each of `3 ∣ a`, `3 ∣ S`, and
`3 ∣ oddPart M*S`.

## The two normalized sectors

The theorem
`GNExcessCubicRealizedLargeModulusShellPellParameterFiber_nonThree_primitive_packet`
gives the non-three sector:

```text
¬ 3 ∣ a,  ¬ 3 ∣ (2a+3),  ¬ 3 ∣ T,
gcd (2a+3) T = 1,  Coprime (2a+3) T,
(2a+3)²+3 = 4*T*(evenPart M)²,
Coprime (2a+3) (evenPart M),  Squarefree T.
```

For the exceptional sector, the named quotient coordinates are
`GNExcessCubicThreeSectorY a`,
`GNExcessCubicThreeSectorComplement a`, and
`GNExcessCubicThreeSectorPellParameter T`. Reconstruction proves

```text
2a+3 = 3*y3,  S = 3*S3,  T = 3*T3,
¬ 3 ∣ S3,  ¬ 3 ∣ T3.
```

The normalized conic is exactly

```text
3*y3² + 1 = 4*T3*(evenPart M)²,
```

and the normalized coordinates satisfy `Coprime y3 T3` and inherit
`Coprime y3 (evenPart M)`. No `Coprime T3 d` claim is made.

`GNExcessCubicRealizedLargeModulusShellPellParameterFiber_threeSector_cases`
packages every fiber witness into exactly one of these two normal forms.

## Verification and trust boundary

Focused and aggregator builds both pass:

```text
lake build DkMath.ABC.GNExcessCubicThreeSector  PASS
lake build DkMath.ABC                              PASS
```

The changed production Lean module contains no `sorry`, `admit`, new `axiom`,
`abc_main_axiom`, or `native_decide`. The audited declarations use only the
standard `propext`, `Classical.choice`, and `Quot.sound` boundary (or a
subset).

The optional finite-set sector partition was not added. The remaining frontier
is solution counting, fiber/shell sparsity, Hensel density, relative-height
exclusion, ABC quality coupling, and any asymptotic conclusion.
