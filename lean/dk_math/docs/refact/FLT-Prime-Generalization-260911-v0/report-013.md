# FLT prime-generalization Phase 13 — arbitrary-prime TraceOne bridge

## Scope and outcome

This report records the bounded implementation requested by
`instruction-013.md`.  The Phase-12 Gauss-normalized antisymmetric factor is
combined with the Phase-11 integral symmetric factor, reduced modulo two, and
converted into an integral half-coordinate.

The resulting classification is:

```text
PGEN-TRACEONE-PRIME-BRIDGE-GREEN
```

For every odd prime `p`, the production endpoint supplies integral polynomial
coordinates in `TraceOneInt (signedPrimeParameter p)` whose norm is the
homogeneous prime cyclotomic / `GTail` shell.

## A. Polynomial shell and C3 lift

The production shell is defined in:

```text
DkMath/NumberTheory/CyclotomicQRTraceOneBridge.lean
```

It provides:

```text
primeCyclotomicShellPoly
eval_primeCyclotomicShellPoly
map_primeCyclotomicShellPoly_eq_qr_mul_qnr
```

The polynomial C3 lift is proved through a typed homogenized cyclotomic
product identity, not by uniqueness from pointwise field evaluations.  The
reusable product-level theorem is:

```text
primitiveRoots_product_poly_eq_shell
```

in `CyclotomicQRProduct.lean`.  The QR/QNR partition then identifies the
mapped integral shell polynomial with
`qrFactorPoly ζ * qnrFactorPoly ζ`.

## B. Integral Gauss-form packet

The production theorem

```text
exists_integral_gauss_form
```

selects independent `RZ` and `SZ` witnesses from the existing Phase-11 and
Phase-12 existential APIs.  It proves:

```lean
map RZ = Rpoly

C 4 * primeCyclotomicShellPoly p =
  RZ ^ 2 - C (signedPrimeDiscriminant p) * SZ ^ 2

C (quadraticGauss ζ hζ) * map SZ = Dpoly
```

The proof maps the integer identity to the cyclotomic field, uses the typed
C3 lift and `quadraticGauss_sq`, and returns through injectivity of the
integer-to-field polynomial map.

## C. Mod-two parity and half-coordinate

The signed discriminant modulo-four theorem is converted to the explicit
`ZMod 2` equality needed by the mapped Gauss form.  The polynomial ring over
`ZMod 2` is used as a reduced domain: equality of squares yields equality of
the two mapped coordinates in characteristic two.

The production parity theorem is:

```text
map_modTwo_eq_of_integral_gauss_form
```

From its coefficient consequences, `exists_half_difference` constructs an
integer polynomial `AZ` coefficientwise, without rational division, and proves
the exact identity:

```lean
RZ = MvPolynomial.C 2 * AZ + SZ
```

## D. Arbitrary-prime TraceOne endpoint

The mandatory endpoint is:

```text
exists_prime_traceOne_coordinates
```

For arbitrary odd prime `p`, the evaluated coordinates satisfy:

```lean
norm
  (⟨eval ![z,y] AZ, eval ![z,y] SZ⟩ :
    TraceOneInt (signedPrimeParameter p))
  = GTailCyclotomicShell p (z - y) y
```

The final step uses `discr_signedPrimeParameter` and the existing neutral
adapter `norm_eq_of_gauss_coordinates`.  The optional natural-number cast
wrapper was not needed for the canonical shell endpoint.

## E. Compatibility and trust audits

The focused tests are:

```text
DkMathTest/FLT/Prime/CyclotomicQRTraceOneBridgeProbe.lean
DkMathTest/FLT/Prime/CyclotomicQRTraceOneBridgeCompatibility.lean
DkMathTest/FLT/Prime/CyclotomicQRTraceOneBridgeAxiomAudit.lean
```

The probe instantiates the arbitrary-prime endpoint at `p = 3, 5, 7, 11, 13`
and checks:

```text
s_3  = -1
s_5  =  1
s_7  = -2
s_11 = -3
s_13 =  3
```

The compatibility module replays the existing `p=3,5,7` TraceOne targets and
the existing exact `norm11` / `norm13` shell targets.  The new existential
witnesses are intentionally not identified with the old explicit coordinate
witnesses.

The axiom audit covers the polynomial C3 lift, integral Gauss form, mod-two
parity, half-coordinate extraction, and arbitrary-prime TraceOne endpoint.
Their reported dependencies are only the inherited kernel dependencies
`propext`, `Classical.choice`, and `Quot.sound`; no `sorryAx`, new `sorry`, or
explicit `axiom` is introduced by this phase.

## Verification

The final focused build includes the production Phase-9/10/11/12 chain, the
new Phase-13 production module, all three Phase-13 tests, the prior TraceOne
and explicit quadratic compatibility probes, and `DkMath.FLT.Seven`.

A fresh warning scan is run against the final build log with the standard
`declaration uses \`sorry\`` diagnostic filtered separately.  `git diff --check`
and a direct `sorry`/`axiom` scan of the Phase-13 source set are also part of
the closeout.

## Boundary

This closes the quadratic-cyclotomic front-end only.  It does not add a
general FLT contradiction, Euclidean/PID/UFD or class-group results, unit
classification, principalization, Kummer regular-prime arguments, or changes
to the existing FLT3/FLT5/FLT7 proof towers.

