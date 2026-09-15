# LUNA-008 — canonical repeated/complement foundation

## Scope

This checkpoint freezes the stable arithmetic from ASTRA-007. It does not
attempt an incidence estimate, paired relative-height theorem, or ABC closure.
The production module is [GNExcessCubicComplement.lean](../../../DkMath/ABC/GNExcessCubicComplement.lean), with collision regressions in
[GNCubicComplementRegression.lean](../../../DkMathTest/ABC/GNCubicComplementRegression.lean).

## Declarations added

The new module exports the following layers.

* `not_nine_dvd_GN_three_one` proves `¬ 9 ∣ a^2 + 3*a + 3`; the direct
  `GN 3 a 1` form is `not_nine_dvd_GN_three_one_value`.
* `GNNonExceptionalRepeatedPart_three_one_eq_repeatedPrimePowerPart` identifies
  the canonical non-exceptional repeated part with the full repeated
  prime-power part. The proof shows that prime 3 cannot have depth two.
* `repeatedPrimePowerComplement n := n / repeatedPrimePowerPart n` is the
  generic residual coordinate. Its multiplication, squarefree, and coprime
  theorems are `repeatedPrimePowerPart_mul_complement`,
  `squarefree_repeatedPrimePowerComplement`, and
  `coprime_repeatedPrimePowerPart_complement`.
* `GNExcessCubicComplement a` is the canonical cubic residual. The product
  theorem and explicit quadratic theorem are
  `GNNonExceptionalRepeatedPart_mul_GNExcessCubicComplement` and
  `GNNonExceptionalRepeatedPart_mul_GNExcessCubicComplement_eq_quadratic`.
  Its squarefree and coprime consumers are exported directly.
* `GNExcessCubicRealizedLargeModulusSpace_exists_complement_packet` gives a
  positive witness `a ≤ X` and `S ≤ X` with
  `M*S = a^2 + 3*a + 3`, `M` equal to the full repeated part, `S` squarefree,
  and `Nat.Coprime M S`.
* `cubicQuadratic_commonDivisor_dvd_rootDifference` and
  `cubicQuadratic_commonDivisor_le_spacingProduct` give the exact integer
  divisibility and natural spacing inequalities for any two roots.

The complement is intentionally the full quotient by all valuation depths at
least two. It is not the parity squarefree kernel; odd repeated exponents stay
in the repeated part.

## Proof notes

The prime-three exclusion uses residues modulo 9 and the existing explicit
formula `GN_three_dual_explicit`. The full-part equality compares each prime
factorization coordinate with the existing support/factorization API. For a
nonzero `n`, `Nat.factorization_div` gives the quotient valuation as a
difference. A valuation of at least two is removed completely, so every
remaining quotient valuation is at most one; the same coordinate calculation
proves coprimality.

The sharp bound is proved in two stages. First `S > X+1` contradicts the
quadratic height and `M > X+1`. If `S = X+1`, integrality forces `a = X`; the
cases `M = X+2` and `M ≥ X+3` contradict the exact quadratic product. Thus
the realized certificate retains the sharp `S ≤ X`, with `X > 0` explicit.

## Negative regressions

The test module preserves exact factorization certificates for

```text
M(21) = M(145) = 169
M(2173) = M(3018) = M(5260) = M(6105) = 8281.
```

These remain test-side examples so that future work cannot silently reintroduce
point-to-modulus injectivity or an at-most-two witness shortcut.

## Verification

Focused production build:

```text
lake build DkMath.ABC.GNExcessCubicComplement   PASS
```

Public aggregator build:

```text
lake build DkMath.ABC                            PASS
```

Regression module:

```text
lake env lean DkMathTest/ABC/GNCubicComplementRegression.lean  PASS
```

The principal theorem axiom audit reports only the expected kernel boundary:
`propext`, `Classical.choice`, and `Quot.sound` (the spacing divisibility
theorem itself needs only the corresponding subset). No `sorry`, `admit`, new
axiom, `abc_main_axiom`, or `native_decide` was added by this checkpoint.
Existing unrelated repository warnings are outside the changed modules.

## Remaining frontier

The durable result is the coordinate system

```text
F(a) = M*S,  M > X,  S ≤ X,  Squarefree S,  gcd(M,S)=1.
```

The remaining ABC–GN problem is global incidence control for these pairs strong
enough to bound the distinct realized modulus `3/8` moment. ASTRA-007's
research conjectures, Pell obstruction, and squarefull counting target remain
deferred and are not production assumptions here.
