# LUNA-009 — Pell and incidence-obstruction fact freeze

## Scope and files

This checkpoint freezes the two stable ASTRA-007 fact families requested by
`instruction-009`. It does not pursue the missing global incidence estimate,
paired relative-height exclusion, or ABC closure.

Changed production files:

- `DkMath/ABC/GNExcessCubicComplementPell.lean`
- `DkMath/ABC/GNExcessCubicIncidenceObstruction.lean`
- `DkMath/ABC.lean` (public imports)

Changed documentation and tests:

- `DkMathTest/ABC/GNCubicPellRegression.lean`
- `README.md`, `ROADMAP.md`, and this report/validation record.

## Pell and quadratic declarations

`cubicQuadratic_discriminant_identity` proves

```text
4 * (a^2 + 3*a + 3) = (2*a+3)^2 + 3.
```

`cubicQuadratic_ne_square` proves that the quadratic is never a natural
square, using the strict inequalities between `(a+1)^2` and `(a+2)^2`.

`repeatedPrimePowerPart_three_mul_sq` proves that, for `d ≠ 0` and `3 ∤ d`,
the full repeated prime-power part of `3*d^2` is exactly `d^2`.
`GNNonExceptionalRepeatedPart_three_one_eq_sq_of_quadratic_eq_three_sq`
transports this through the LUNA-008 prime-three/full-part theorem.

## Explicit recurrence and constant complement

`GNCubicComplementPell` is defined by

```text
(a₀,d₀) = (0,1)
aₙ₊₁ = 7*aₙ + 12*dₙ + 9
dₙ₊₁ = 4*aₙ + 7*dₙ + 6.
```

`GNCubicComplementPell_invariant` proves for every `n`:

```text
aₙ² + 3*aₙ + 3 = 3*dₙ²,
aₙ % 3 = 0,
dₙ % 3 = 1.
```

The production theorems `GNCubicComplementPell_repeatedPart` and
`GNCubicComplementPell_complement_eq_three` then prove respectively
`M(aₙ)=dₙ²` and `GNExcessCubicComplement aₙ = 3`.
`GNCubicComplementPell_strictMono` proves strict growth. The corollary
`exists_large_cubic_point_complement_eq_three` gives, for every `B`, a point
`a > B` with complement exactly `3`.

This is a negative boundary result: small complement does not imply bounded
witness multiplicity. In particular, no theorem saying that a fixed small
complement has only `O(1)` canonical points can follow from smallness alone.
No asymptotic multiplicity estimate is asserted.

The two exact paired identities are also frozen:
`cubicOrientation_product_identity_one` and
`cubicOrientation_linear_difference_one`. No paired relative-height claim is
made.

## Membership, injectivity, and block obstruction

`mem_GNExcessCubicRealizedLargeModulusSpace_of_fullRepeatedPart` is the safe
converse bridge from an actual full repeated part at `a ≤ X` with `X+1 < M`
to realized modulus-space membership. It does not accept arbitrary squareful
divisors.

`cubicQuadratic_injective` proves injectivity of `a ↦ a²+3a+3`.
`cubicSquarefullBlock_card_mul_weight_le_realizedModulusMoment` proves the
exact necessary inequality: if every `a ∈ A` lies in `[X,2X]` and its whole
quadratic value is repeated, then

```text
(A.card : ℝ) * ((X : ℝ)^2)^(3/8)
  ≤ ∑ M ∈ realizedModulusSpace (2*X), (M : ℝ)^(3/8).
```

The proof uses only the full-repeated membership bridge, quadratic
injectivity, image-sum reindexing, monotonicity of `Real.rpow`, and nonnegative
subset summation. The theorem assumes no bound on the right-hand side. It is a
necessary obstruction, not an incidence theorem.

## Regression and verification

The optional Pell regression module checks the first values
`(0,1)`, `(21,13)`, `(312,181)`, and `(4365,2521)` and checks complement `3`.
The prior LUNA-008 collision regression remains unchanged and is not
duplicated.

Focused builds:

```text
lake build DkMath.ABC.GNExcessCubicComplementPell                  PASS
lake build DkMath.ABC.GNExcessCubicIncidenceObstruction            PASS
lake build DkMath.ABC                                               PASS
lake env lean DkMathTest/ABC/GNCubicPellRegression.lean             PASS
```

The principal new declarations audit to the expected
`propext`, `Classical.choice`, and `Quot.sound` boundary, or a subset of it.
No `sorry`, `admit`, new axiom, `abc_main_axiom`, or `native_decide` was added.

## Remaining frontier

The durable negative lessons are now:

1. complement `3` occurs at arbitrarily large canonical witnesses;
2. any linear realized-modulus moment closure would force strong sparsity of
   squarefull quadratic values in dyadic blocks.

Neither fact supplies that sparsity. The remaining research frontier is still
global incidence control for `F(a)=M*S` with `M>X`, `S≤X`, squarefree `S`, and
`gcd(M,S)=1`, strong enough to control the realized modulus `3/8` moment.
