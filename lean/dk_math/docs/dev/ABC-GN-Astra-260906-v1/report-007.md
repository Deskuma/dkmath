# LUNA-007 — explicit Eisenstein square-factor consequence bridge

This checkpoint freezes the exact consequences of an explicitly supplied
Eisenstein equality. It does not prove that the equality exists, search for
factors, or count factors.

## 1. Files changed

Extended EisensteinCoordinates.lean with conditional coordinate, coprimality,
norm, and polynomial consequences. Added
GNExcessCubicEisensteinFactorConsequences.lean and imported it from
DkMath/ABC.lean immediately after GNExcessCubicEisensteinCoordinates. Build
logs are retained in lean-007-numbertheory-output.txt,
lean-007-abc-output.txt, and build-007-abc-output.txt. The validation record is
validation-007.txt.

## 2. Exact factor-equality hypothesis

All conditional consequences use an explicit hypothesis of the form

    eisensteinCoord b c * (eisensteinCoord m n)^2
      = eisensteinCoord (a + 2) 1

with integer coordinates. No weaker norm equality is treated as a factor
equality.

## 3. First coordinate consequence

eisenstein_mul_sq_eq_cubicCoord_fst proves

    b*(m²-n²) - c*(2*m*n-n²) = a+2.

It is obtained by applying the first-coordinate projection to the explicit
factor equality and consuming eisensteinCoord_mul_sq.

## 4. Coefficient-one consequence

eisenstein_mul_sq_eq_cubicCoord_snd proves

    b*(2*m*n-n²) + c*(m²-2*m*n) = 1.

The sign from the neutral <m,-n> representation is handled in the coordinate
projection proof.

## 5. Coprimality consequence

eisenstein_mul_sq_eq_cubicCoord_coefficients_isCoprime consumes the
coefficient-one equation and eisenstein_square_coefficient_coprime to prove

    IsCoprime (2*m*n-n²) (m²-2*m*n).

This is only a conditional Bezout consequence.

## 6. Norm factor consequence

eisenstein_mul_sq_eq_cubicCoord_norm uses the explicit equality and the
existing multiplicative norm theorem to prove

    Norm(eisensteinCoord (a+2) 1)
      = Norm(eisensteinCoord b c) * Norm(eisensteinCoord m n)^2.

No polynomial re-expansion is needed.

## 7. Polynomial norm consequence

eisenstein_mul_sq_eq_cubicCoord_polynomial_norm derives over Int

    a² + 3*a + 3
      = (b²-b*c+c²) * (m²-m*n+n²)^2.

It is a direct norm-form consequence of the same explicit factor equality.

## 8. Shell witness bridge

Added three thin ABC theorems:

- GNExcessCubicRealizedLargeModulusShellWitness_eisensteinFactor_coeff_one;
- GNExcessCubicRealizedLargeModulusShellWitness_eisensteinFactor_coefficients_isCoprime;
- GNExcessCubicRealizedLargeModulusShellWitness_eisensteinFactor_norm.

The norm theorem combines the existing shell product norm bridge with the
neutral conditional norm theorem. The first two retain the explicit shell
witness and factor-equality hypotheses.

## 9. Optional conjunction packet status

Skipped. The separate public theorems expose the coordinate equation,
coprimality, and norm consequence without introducing a new packet structure.

## 10. Explicit no-converse boundary

No theorem infers an element factorization from a norm factorization. Norm
equality does not recover unit or associate data, so the converse remains
outside the API.

## 11. Explicit no-existence boundary

No theorem asserts

    ∃ b c m n,
      eisensteinCoord b c * (eisensteinCoord m n)^2
        = eisensteinCoord ((a:Int)+2) 1.

No factor search, Classical.choose, axiom, provider, UFD extraction, or
factor-counting result was added.

## 12. Focused neutral build

The required command passed:

    lake build DkMath.NumberTheory.EisensteinCoordinates

The output is retained in lean-007-numbertheory-output.txt, ending with
Build completed successfully (8657 jobs).

## 13. Focused ABC bridge build

The required command passed:

    lake build DkMath.ABC.GNExcessCubicEisensteinFactorConsequences

The output is retained in lean-007-abc-output.txt, ending with
Build completed successfully (8803 jobs).

## 14. ABC aggregator build

The required command passed:

    lake build DkMath.ABC

The output is retained in build-007-abc-output.txt, ending with
Build completed successfully (8867 jobs).

## 15. Forbidden scan

The changed production modules were scanned for sorry, admit, axiom,
abc_main_axiom, native_decide, and unsafe. No occurrences were found.

## 16. Axiom audit

The principal coordinate and shell declarations report only the expected
trust boundary propext, Classical.choice, and Quot.sound, or subsets thereof.
The focused logs contain no sorryAx for the new declarations.

## 17. Remaining research frontier

Production Lean now states:

    IF beta * gamma² = (a+2)+omega,
    THEN the exact coordinate equations hold,
    the square coefficients are coprime,
    and a²+3a+3 = Norm(beta)*Norm(gamma)².

The existence and counting of such factorizations, integral-point bounds,
balanced-box estimates, and ABC remain open. LUNA-008 is not opened
automatically.

