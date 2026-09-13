# LUNA-017 — finite three-sector incidence ledger

## Scope and files

This checkpoint converts the LUNA-016 exceptional-three normalization into
exact finite filters, images, fibers, and cardinality identities. It makes no
sector sparsity, density, or multiplicity claim.

Changed files:

- `DkMath/ABC/GNExcessCubicThreeSectorIncidence.lean`
- `DkMath/ABC.lean` (public import immediately after `GNExcessCubicThreeSector`)
- `README.md`, `ROADMAP.md`, `validation-017.txt`, and this report.

## Fixed-`T` sector ledger

The module defines
`GNExcessCubicRealizedLargeModulusShellPellParameterFiberNonThree` and
`GNExcessCubicRealizedLargeModulusShellPellParameterFiberThree` as filters of
the existing fixed-`T` Pell-parameter fiber. Their membership theorems expose
the expected conjunctions with `¬ 3 ∣ a` and `3 ∣ a`.

The exact finite identities are proved:

```text
PellParameterFiber T = NonThreeFiber T ∪ ThreeFiber T
Disjoint (NonThreeFiber T) (ThreeFiber T)
fiber.card = nonThree.card + three.card.
```

The non-three consumer is a direct wrapper around the LUNA-016 primitive
packet. It exposes `¬3 ∣ a`, `¬3 ∣ y`, `¬3 ∣ T`, `Coprime y T`, the Pell
equation, coprimality with the even-part coordinate, and `Squarefree T`.

The three-sector consumer exposes `3 ∣ a`, the reconstruction of `y=3*y3`
and `T=3*T3`, `¬3 ∣ T3`, `Coprime y3 T3`, the normalized conic, and
coprimality with the even-part coordinate.

## Normalized `T3` incidence

The normalized parameter image is
`GNExcessCubicRealizedLargeModulusShellThreeSectorParameterSpace`. Its
membership theorem is an exact existential image description over shell
witnesses satisfying `3 ∣ a`.

For every represented `T3`, the support packet proves:

```text
0 < T3
Squarefree T3
¬ 3 ∣ T3.
```

The normalized witness fiber
`GNExcessCubicRealizedLargeModulusShellThreeSectorParameterFiber` has an exact
membership theorem and is nonempty for every represented `T3`.

The normalized primitive packet and equation consumer expose, for every
fiber witness,

```text
3*y3² + 1 = 4*T3*(evenPart M)²
Coprime y3 T3
Coprime y3 (evenPart M).
```

The exact finite reindexing is frozen by the bi-union theorem and its card
identity:

```text
ThreeSectorWitnessSpace
  = ⋃ T3 ∈ ThreeSectorParameterSpace, ThreeSectorParameterFiber T3

ThreeSectorWitnessSpace.card
  = ∑ T3 ∈ ThreeSectorParameterSpace,
      (ThreeSectorParameterFiber T3).card.
```

## Shell-level split

The module also defines non-three and three shell witness spaces, proves their
exact union and disjointness, and proves

```text
shellWitnessCount = nonThreeShell.card + threeShell.card.
```

The optional original-`T` to normalized-`T3` image corollary was not added;
the normalized parameter image and fibers already provide the required exact
ledger.

## Verification and trust boundary

Focused and aggregator builds pass:

```text
lake build DkMath.ABC.GNExcessCubicThreeSectorIncidence  PASS
lake build DkMath.ABC                                   PASS
```

Changed production Lean sources contain no `sorry`, `admit`, new `axiom`,
`abc_main_axiom`, or `native_decide`. Audited declarations remain within the
standard `propext`, `Classical.choice`, and `Quot.sound` boundary (or a
subset).

The remaining frontier is sector cardinality bounds, fixed-`T` or fixed-`T3`
multiplicity, Pell/conic counting, density, sparsity, relative-height
exclusion, and ABC quality coupling.
