# LUNA-006 — neutral Eisenstein-coordinate core and cubic bridge

This checkpoint adds a neutral Eisenstein coordinate presentation backed by
`TraceOneInt (-1)` and a thin ABC bridge for the cubic quadratic. It records
exact ring identities only; it does not assert factorization existence or
counting.

## 1. Files changed

Added [EisensteinCoordinates.lean](../../../DkMath/NumberTheory/EisensteinCoordinates.lean)
and [GNExcessCubicEisensteinCoordinates.lean](../../../DkMath/ABC/GNExcessCubicEisensteinCoordinates.lean).
The ABC bridge is imported from `DkMath/ABC.lean` immediately after
`GNExcessCubicMordellIncidence`. Build logs are retained in
[lean-006-numbertheory-output.txt](lean-006-numbertheory-output.txt),
[lean-006-abc-output.txt](lean-006-abc-output.txt), and
[build-006-abc-output.txt](build-006-abc-output.txt). The validation record
is [validation-006.txt](validation-006.txt).

## 2. Neutral dependency direction

`DkMath.NumberTheory.EisensteinCoordinates` imports only
`DkMath.NumberTheory.TraceOneQuadratic`. It does not depend on ABC, FLT, or
Petal. The ABC module depends on this neutral module and on the existing
LUNA-005 Mordell incidence API.

## 3. Coordinate embedding

`eisensteinCoord m n : TraceOneInt (-1)` is defined as `<m,-n>`. This is
the standard `m+n*ω` presentation under `τ = -ω`; the coordinate
projections have simp lemmas.

## 4. Norm theorem

`norm_eisensteinCoord` proves, using the existing TraceOneQuadratic norm,

```text
norm (eisensteinCoord m n) = m² - m*n + n².
```

No alternate norm function is introduced.

## 5. Multiplication formula

`eisensteinCoord_mul` proves

```text
eisensteinCoord a b * eisensteinCoord c d
  = eisensteinCoord (a*c-b*d) (a*d+b*c-b*d).
```

The proof unfolds the existing TraceOneInt ring multiplication.

## 6. Square formula

`eisensteinCoord_sq` proves

```text
(eisensteinCoord m n)²
  = eisensteinCoord (m²-n²) (2*m*n-n²).
```

## 7. Beta-times-square formula

`eisensteinCoord_mul_sq` gives the ASTRA-001 coordinates for
`eisensteinCoord b c * (eisensteinCoord m n)^2`:

```text
A = b*(m²-n²) - c*(2*m*n-n²)
B = b*(2*m*n-n²) + c*(m²-2*m*n).
```

## 8. Norm product identity

`norm_eisensteinCoord_mul_sq` applies the existing multiplicative norm theorem
to prove the square-product identity. The additional
`norm_eisensteinCoord_mul_sq_polynomial` theorem exposes the explicit
`A²-A*B+B²` corollary without creating a second norm API.

## 9. Coefficient-one coprimality

`eisenstein_square_coefficient_coprime` turns

```text
b*(2*m*n-n²) + c*(m²-2*m*n) = 1
```

directly into `IsCoprime (2*m*n-n²) (m²-2*m*n)` by Bezout's definition.
No counting consequence is derived.

## 10. Cubic quadratic norm bridge

The ABC theorem `cubicQuadratic_eq_eisensteinNorm` proves over `ℤ` that

```text
(a² + 3*a + 3 : ℕ : ℤ)
  = norm (eisensteinCoord ((a : ℤ)+2) 1).
```

This is the fixed neutral norm identity for the cubic polynomial.

## 11. Shell witness product norm bridge

`GNExcessCubicRealizedLargeModulusShellWitness_product_eq_eisensteinNorm`
combines the existing shell complement packet
`M(a)*S(a)=a²+3*a+3` with the cubic norm bridge. It makes no claim that the
neutral element factors as `beta*gamma²`.

## 12. Optional coefficient-one implication status

Skipped. The generic Bezout theorem in the neutral module is available; no
additional implication from an explicit factor equality was needed for this
checkpoint.

## 13. Compatibility with existing FLT/Petal API

Skipped. Existing FLT and Petal theorem statements were not changed, and the
new neutral module remains below those packages. A larger API promotion is a
separate refactor.

## 14. Explicit no-factorization-existence boundary

PROVED:

- neutral coordinates in `TraceOneInt (-1)`;
- norm, multiplication, square, and `beta*gamma²` coordinate identities;
- norm multiplicativity and the explicit polynomial corollary;
- coefficient-one Bezout coprimality;
- cubic quadratic and shell product norm bridges.

NOT PROVED:

- existence or uniqueness of `beta` and `gamma` for production witnesses;
- UFD factor extraction for the ABC shell;
- represented-pair sparsity or integral-point counts;
- balanced-box power saving;
- ABC.

## 15. Focused neutral build

The required command passed:

```text
lake build DkMath.NumberTheory.EisensteinCoordinates
```

The output is retained in [lean-006-numbertheory-output.txt](lean-006-numbertheory-output.txt),
ending with `Build completed successfully (8657 jobs).`.

## 16. Focused ABC bridge build

The required command passed:

```text
lake build DkMath.ABC.GNExcessCubicEisensteinCoordinates
```

The output is retained in [lean-006-abc-output.txt](lean-006-abc-output.txt),
ending with `Build completed successfully (8802 jobs).`.

## 17. ABC aggregator build

The required command passed:

```text
lake build DkMath.ABC
```

The output is retained in [build-006-abc-output.txt](build-006-abc-output.txt),
ending with `Build completed successfully (8866 jobs).`.

## 18. Forbidden scan

The two changed production modules were scanned for
`sorry`, `admit`, `axiom`, `abc_main_axiom`, `native_decide`, and
`unsafe`. No occurrences were found.

## 19. Axiom audit

The audited principal declarations report only the expected trust boundary
`propext`, `Classical.choice`, and `Quot.sound`, or subsets thereof. The
focused logs contain no `sorryAx` for the new declarations.

## 20. Remaining research frontier

The production graph now has a reusable neutral Eisenstein coordinate core and
the exact identity

```text
a² + 3*a + 3 = Norm((a+2)+ω).
```

Factorization existence, factor counting, Mordell integral-point bounds,
balanced-box estimates, and ABC remain outside this checkpoint. LUNA-007 is
not opened automatically.

