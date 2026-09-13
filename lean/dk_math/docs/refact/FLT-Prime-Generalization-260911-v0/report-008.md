# FLT prime-generalization Phase 8 — QR/QNR polynomial lift and abstract Galois action

## Scope and outcome

This report implements the bounded contract in `instruction-008.md`. The
existing Phase-7 QR/QNR product API is lifted to genuine two-variable
`MvPolynomial (Fin 2) K` factors, and the square/nonsquare exponent action is
proved for an explicitly supplied ring automorphism. The work stops before
the existence of all cyclotomic automorphisms, coefficient descent,
integral Gaussian coordinates, class-group arguments, and any FLT
contradiction.

The resulting classification is:

```text
PGEN-GAUSS-ACTION-GREEN
```

## A. Production polynomial lift

The neutral production module is:

```text
DkMath/NumberTheory/CyclotomicQRGaloisAction.lean
```

It imports only `DkMath.NumberTheory.CyclotomicQRProduct` and does not import
`DkMath.FLT.*`.

For a field `K`, prime `p`, and `a : ZMod p`, the definitions are:

```text
rootFactorPoly ζ a = X₀ - C (ζ ^ a.val) * X₁
qrFactorPoly ζ      = ∏ a in qrFinset p, rootFactorPoly ζ a
qnrFactorPoly ζ     = ∏ a in qnrFinset p, rootFactorPoly ζ a
```

The theorems `eval_rootFactorPoly`, `eval_qrFactorPoly`, and
`eval_qnrFactorPoly` give the exact evaluation compatibility with the
Phase-7 `rootFactor`, QR product, and QNR product APIs.

The optional A1 polynomial identity was not added: the mandatory evaluated
C3 shell bridge is already available and is tested through the new
polynomial evaluator. This keeps the phase at the requested action boundary.

## B. Arbitrary-prime exponent classes

The production file proves:

```text
mulBy_t_nonzero_bijective
mulBy_t_permutes_nonzeroResidues
isSquare_mul_iff
mulBy_t_maps_qr_of_square
mulBy_t_maps_qnr_of_square
mulBy_t_maps_qr_to_qnr_of_nonsquare
mulBy_t_maps_qnr_to_qr_of_nonsquare
```

These statements use the pinned quadratic-character API and hold for an
arbitrary prime `p`; they are not established by small-prime enumeration.
The square case also covers `p = 2`. A nonsquare nonzero exponent does not
occur at `p = 2`, so the nonsquare branch is vacuous there rather than being
silently strengthened by an odd-prime assumption.

## C. Abstract automorphism action

For

```text
σ : K ≃+* K
t : ZMod p
hσζ : σ ζ = ζ ^ t.val
```

with `t ≠ 0`, `map_rootFactorPoly` proves the factor action

```text
map σ (rootFactorPoly ζ a) = rootFactorPoly ζ (t * a).
```

The exponent representative mismatch is handled explicitly by primitive-root
periodicity (`IsPrimitiveRoot.pow_eq_one`) and a `ZMod` natural-cast
calculation. The product-level theorem family is:

```text
map_qrFactorPoly_of_square
map_qnrFactorPoly_of_square
map_qrFactorPoly_to_qnr_of_nonsquare
map_qnrFactorPoly_to_qr_of_nonsquare
```

The first two preserve QR and QNR factors; the latter two swap them. No
existence or surjectivity theorem for an automorphism realizing a prescribed
`t` is assumed.

## D. Symmetric and antisymmetric axes

The production definitions are:

```text
Rpoly ζ := qrFactorPoly ζ + qnrFactorPoly ζ
Dpoly ζ := qrFactorPoly ζ - qnrFactorPoly ζ
```

The following are proved for both square and nonsquare actions:

```text
map_Rpoly_of_square
map_Rpoly_of_nonsquare
map_Dpoly_of_square
map_Dpoly_of_nonsquare
map_Dpoly_sq_of_square
map_Dpoly_sq_of_nonsquare
```

Thus `Rpoly` is invariant, `Dpoly` has sign `+1` or `-1`, and `Dpoly ^ 2`
is invariant under every supplied action satisfying the primitive-root power
condition.

## E. Regression and Phase-7 compatibility

New focused test files are:

```text
DkMathTest/FLT/Prime/CyclotomicQRGaloisActionProbe.lean
DkMathTest/FLT/Prime/CyclotomicQRGaloisActionCompatibility.lean
DkMathTest/FLT/Prime/CyclotomicQRGaloisActionAxiomAudit.lean
```

The probe checks polynomial evaluation using the existing concrete complex
primitive roots for `p = 3, 5, 7, 11, 13`, and specializes the abstract
square/nonsquare action API. The compatibility file checks that evaluating
the new `p=11` and `p=13` polynomial factors reaches the existing
cyclotomic shell and the existing `TraceOneInt` norm identities. Individual
QR/QNR factors are not identified with `A11/B11` or `A13/B13`.

## F. Pinned Mathlib audit and next boundary

The audit module records these declarations from the pinned checkout:

```text
IsPrimitiveRoot.autToPow
IsPrimitiveRoot.autToPow_spec
IsPrimitiveRoot.autToPow_injective
IsPrimitiveRoot.autToPow_eq_modularCyclotomicCharacter
IsCyclotomicExtension.autEquivPow
galCyclotomicEquivUnitsZMod
galXPowEquivUnitsZMod
IntermediateField.mem_fixedField_iff
IsGalois.fixedField_fixingSubgroup
IsCyclotomicExtension.integral
IsCyclotomicExtension.isGalois
IsCyclotomicExtension.ringOfIntegers
```

The automorphism-to-power APIs are available, but the useful forms require
an algebra automorphism (`AlgEquiv`) and, for the full cyclotomic
equivalences, cyclotomic-extension and irreducibility hypotheses. The exact
next missing theorem is therefore an instantiation bridge from a prescribed
nonzero `t : ZMod p` to an automorphism of the selected cyclotomic extension
with `σ ζ = ζ ^ t.val`.

The fixed-field declarations provide general fixed-field membership and
finite Galois correspondence, but no direct theorem was used here that
turns the fixed polynomial action into coefficient descent to `ℚ`. The
integrality and ring-of-integers declarations are likewise only audited;
they do not establish integer coefficients for `Rpoly` or `Dpoly` in this
phase.

The next boundary is consequently:

```text
abstract QR/QNR Galois action       [GREEN]
existence of all cyclotomic actions [NEXT]
coefficient descent to ℚ/ℤ          [OPEN]
integral Gaussian coordinates       [OPEN]
```

## G. Verification and axiom audit

The new public declarations have focused `#print axioms` coverage in the
probe and audit files. The reported dependencies are only Lean kernel
support (`propext`, `Classical.choice`, and `Quot.sound` where finite-set
decidability is involved); no `sorryAx` is present. The new source files
contain no `sorry` and no explicit `axiom`.

The final focused builds are recorded below:

```text
lake build DkMath.NumberTheory.CyclotomicQRProduct
lake build DkMath.NumberTheory.CyclotomicQRGaloisAction
lake build DkMath.NumberTheory.QuadraticConjugateFactor
lake build DkMath.NumberTheory.TraceOneDiscriminantAxis
lake build DkMathTest.FLT.Prime.CyclotomicQRGaloisActionProbe
lake build DkMathTest.FLT.Prime.CyclotomicQRGaloisActionCompatibility
lake build DkMathTest.FLT.Prime.CyclotomicQRGaloisActionAxiomAudit
lake build DkMathTest.FLT.Prime.CyclotomicQRProductCompatibility
lake build DkMath.FLT.Seven
```

`git diff --check` and the final source scans for `sorry`, `sorryAx`, and
explicit `axiom` are part of the closeout validation.
