# FLT prime-generalization Phase 7 — QR/QNR cyclotomic product identification

## Scope and outcome

This report implements the bounded contract in `instruction-007.md`. The
full nonzero primitive-root product is identified with the homogeneous prime
cyclotomic shell in a typed field, and the QR/QNR product is connected to that
shell. The work stops before conjugation, coefficient descent, integral
Gaussian-period coordinates, and any FLT contradiction.

The resulting classification is:

```text
PGEN-GAUSS-FACTOR-GREEN
```

## A. Ambient assumptions

The promoted module is:

```text
DkMath/NumberTheory/CyclotomicQRProduct.lean
```

The main theorems use only:

```text
K : Type* with [Field K]
p : ℕ with [Fact p.Prime]
ζ : K with IsPrimitiveRoot ζ p
X Y x u z y : K as theorem endpoints
```

`rootFactor` itself has the local `[NeZero p]` requirement needed to use
`ZMod p`; every theorem using it gets this from the prime fact. No separate
`CharZero K`, algebraic-closure, cyclotomic-field, or integral-domain
assumption was added. The endpoint theorem is stated in `(x,u)` coordinates
and also in the clean `(z-y,y)` form, so no division by `Y`, `X`, or `X-Y` is
used.

The test-first implementation remains at:

```text
DkMathTest/FLT/Prime/CyclotomicQRProductProbe.lean
```

It uses the Phase-6 QR/QNR definitions and specializes the Phase-6 weak
product recombination. The production module carries the same finite
QR/QNR API locally so that it depends only on `DkMath.Basic`,
`DkMath.Lib.Cosmic.GTailCyclotomic`, and Mathlib primitives; it does not
depend on `DkMath.FLT.*` or on a test module.

## B. Pinned APIs and C1

The primitive-root route was selected after auditing the pinned Mathlib
sources. The proof uses:

- `IsPrimitiveRoot.pow_inj`, `pow_of_coprime`, `pow_iff_coprime`, and
  `eq_pow_of_pow_eq_one`;
- `mem_primitiveRoots`, `primitiveRoots`, and
  `IsPrimitiveRoot.card_primitiveRoots`;
- `Nat.coprime_of_lt_prime`, `ZMod.val_lt`, `ZMod.val_ne_zero`,
  `ZMod.val_cast_of_lt`, and `ZMod.val_injective`;
- `Polynomial.cyclotomic_eq_prod_X_sub_primitiveRoots`;
- `Polynomial.cyclotomic_prime`;
- `Polynomial.homogenize_finsetProd`, `homogenize_finsetSum`,
  `homogenize_X_pow`, and `MvPolynomial.eval`;
- `GTailCyclotomicShell` from `DkMath.Lib.Cosmic.GTailCyclotomic`.

The audited nth-root and zmod-power API families are available in the pinned
checkout, but the clean proof uses the primitive-root factorization directly.

The C1 results are:

```text
C1a  rootPowerMap_injective_on_nonzero
C1b  rootPowerSet_eq_primitiveRoots
     rootPowerSet_card
C1c  not separately stated as nthRootsFinset p 1 \ {1}
```

`rootPowerSet_eq_primitiveRoots` is the stronger usable image statement for
the product proof: the nonzero canonical exponent representatives map exactly
to `primitiveRoots p K`. `rootPowerMap_injective_on_nonzero` prevents any
silent duplicate removal in the finite product. The nth-root-minus-one
formulation was not needed after C1b and is intentionally not introduced as a
second redundant bridge.

## C. C2 polynomial/product bridge

The theorem

```text
primitiveRoots_product_eq_shell
```

first uses the pinned primitive-root factorization of the prime cyclotomic
polynomial. It then homogenizes the factor product and the prime coefficient
sum, evaluates at `(X,Y)`, and obtains:

```text
∏ μ ∈ primitiveRoots p K, (X - μ * Y)
  = ∑ k ∈ Finset.range p, X^k * Y^(p-1-k)
```

The theorem

```text
nonzeroRoot_product_eq_shell
```

transports the product over `a ∈ nonzeroResidues p` through the injective
power image and applies the preceding identity. The proof is division-free
and remains valid at zero endpoints.

## D. C3 DkMath shell bridge

The production declarations are:

```text
qr_product_mul_qnr_product
rootFactor
qr_qnr_product_eq_shell
qr_qnr_product_eq_shell_endpoint
```

They establish:

```text
(∏ a ∈ QR, rootFactor ζ a (x+u) u) *
  (∏ a ∈ QNR, rootFactor ζ a (x+u) u)
  = GTailCyclotomicShell p x u
```

and the endpoint form with `X = (z-y)+y` and `Y = y`. The QR/QNR step is
the finite disjoint-union product identity; the root-product step is the C1/C2
bridge above. No coefficient descent is hidden in this equality.

## E. Finite regressions and promotion

The test probe instantiates C3 over `ℂ` for:

```text
p = 3, 5, 7, 11, 13
```

using `Complex.isPrimitiveRoot_exp` for the concrete primitive root
`exp (2*pi*I/p)`. A separate compatibility module checks the promoted
product at `p=11` and `p=13` against the existing integer TraceOne norm
coordinates:

```text
DkMathTest/FLT/Prime/CyclotomicQRProductCompatibility.lean
```

The checked chains are:

```text
QRProduct * QNRProduct = shell = norm11
QRProduct * QNRProduct = shell = norm13
```

The explicit `A11/B11` and `A13/B13` coordinates are not rebuilt or changed.

Because arbitrary-prime C3 is green with field-only assumptions and the
production file has no FLT imports, the neutral theorem was promoted to:

```text
DkMath/NumberTheory/CyclotomicQRProduct.lean
```

## F. First remaining C4 theorem

The next bounded theorem is a genuine coefficient-descent bridge: define and
prove the relevant conjugation/Galois action on the primitive-root factors,
show that it swaps the QR and QNR products, and then establish descent of the
symmetric combination (and subsequently the discriminant-square difference)
to an integral or quadratic coefficient ring.

This phase does not prove any of the following:

- Galois conjugation swaps QR and QNR products;
- `QRProduct + QNRProduct` has integral coefficients;
- an integral `S_p` with a discriminant-square identity;
- arbitrary-prime `TraceOneInt` coordinates;
- FLT3, FLT5, FLT7, or general FLT.

## G. Verification and axiom audit

Added audit module:

```text
DkMathTest/FLT/Prime/CyclotomicQRProductAxiomAudit.lean
```

The production and test modules print axioms for every new public theorem.
The focused `#print axioms` output contains only Lean kernel support:
`propext`, `Classical.choice`, and `Quot.sound` where finite-set
decidability requires it. No `sorryAx` is present.

Focused builds passed:

```text
lake build DkMath.Lib.Cosmic.GTailCyclotomic
lake build DkMath.NumberTheory.QuadraticConjugateFactor
lake build DkMath.NumberTheory.TraceOneDiscriminantAxis
lake build DkMath.NumberTheory.CyclotomicQRProduct
lake build DkMathTest.FLT.Prime.CyclotomicQRProductProbe
lake build DkMathTest.FLT.Prime.CyclotomicQRProductCompatibility
lake build DkMathTest.FLT.Prime.CyclotomicQRProductAxiomAudit
lake build DkMathTest.FLT.Prime.GaussianPeriodFactorizationCompatibility
lake build DkMathTest.FLT.Prime.QuadraticCyclotomicBridgeProbe
lake build DkMath.FLT.Seven
```

`git diff --check` and the source scan for `sorry` / explicit `axiom` are
part of the final verification. No existing FLT endpoint was modified.
