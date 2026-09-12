# FLT prime-generalization Phase 24 — universal `RZ` transport and common-prime support

## Scope and outcome

This report records the bounded implementation requested by
`instruction-024.md`.  The universal `RZ` transport, arbitrary primitive-root
specialization, odd and characteristic-two common-prime support, and the
conditional FLT-side coordinate-coprimality endpoint are implemented and
kernel-checked.

The verified statuses are:

~~~text
PGEN-PRIME-RPOLY-UNIVERSAL-TRANSPORT-GREEN
PGEN-PRIME-COORDINATE-COMMON-PRIME-SUPPORT-GREEN
PGEN-PRIME-COORDINATE-COPRIME-FLT-GREEN
~~~

The stretch ideal-power bridge is not claimed in this phase.

## A. Universal carrier and API audit

`DkMathTest/FLT/Prime/PrimeTraceOneUniversalTransportApiAudit.lean` records
the pinned declarations used by the implementation.  The selected carrier is

~~~text
AdjoinRoot (Polynomial.cyclotomic p ℤ)
~~~

with `AdjoinRoot.root`, `AdjoinRoot.lift`, `AdjoinRoot.lift_root`,
`AdjoinRoot.lift_of`, `AdjoinRoot.lift_comp_of`, and the `modByMonic` degree
API.  The audit also covers the primitive-root cyclotomic-root theorem,
`MvPolynomial.map`/`eval`, product mapping, product-zero, primitive-root power
injectivity, and `ZMod`/`CharP` cast-zero lemmas.

## B. Universal QR/QNR `R` transport

`DkMath/NumberTheory/CyclotomicQRUniversalTransport.lean` defines:

- `universalCyclotomicCarrier` and `zetaU`;
- `universalRootFactorPoly`, `universalQrFactorPoly`,
  `universalQnrFactorPoly`, and `universalRpoly`;
- primitive-root quotient specializations in arbitrary fields;
- characteristic-zero anchor injectivity, proved by cyclotomic minimal-polynomial
  divisibility and the degree bound from `AdjoinRoot.modByMonic`;
- positive-characteristic specialization when `q ≠ p`; and
- functorial QR/QNR/R mapping.

`DkMath/NumberTheory/CyclotomicQRUniversalTraceOneAnchor.lean` proves that a
Phase-22 packet satisfies

~~~text
map (AdjoinRoot.of (cyclotomic p ℤ)) P.RZ = universalRpoly p
~~~

and derives `packet_RZ_map_eq_Rpoly_of_primitive_root` for any primitive
`p`-th root in a field of characteristic `q ≠ p`.  No universal `SZ` or Gauss
transport object was introduced.

## C. Common-prime support

`DkMath/NumberTheory/CyclotomicQRCommonPrimeSupport.lean` implements the
residue argument without Gauss transport:

- a common coordinate divisor forces the homogeneous prime shell to vanish;
- shell-zero and `Nat.Coprime z y` imply `y ≠ 0` modulo `q`;
- `z / y` is directly shown to be a primitive `p`-th root in `ZMod q`;
- the QR factor has its exponent-one zero, so the QNR factor must vanish;
- primitive-root power injectivity contradicts QNR membership of that exponent;
- characteristic two is handled independently by the three parity cases.

The public endpoints are `not_common_coordinate_prime_of_odd_ne`,
`not_common_coordinate_prime_two`,
`common_coordinate_prime_eq_exponent`, and
`common_coordinate_prime_eq_exponent_or_two`.

## D. Conditional FLT-side endpoint

`DkMath/FLT/Prime/PrimeTraceOneCoordinateCoprime.lean` consumes the existing
`PrimeAdicFactorPacket`.  At the endpoint `(g + u, u)`, it derives
`Nat.Coprime (g + u) u`, applies the common-prime support theorem, and rules
out the remaining prime `p` using `PrimeAdicFactorPacket.residual_not_prime_sq`
and the packet norm identity.  The resulting theorem is
`prime_packet_coordinate_isCoprime`.

This remains conditional on the existing Phase-1 packet, as required; it does
not assert general FLT or any class-group conclusion.

## E. Regressions and audits

`DkMathTest/FLT/Prime/PrimeTraceOneUniversalTransportProbe.lean` covers:

- p=3 universal-R transport while preserving the Eisenstein exception;
- p=5 common-prime support;
- p=7 generic FLT-side coprimality alongside the existing specialized
  `cyclotomicSeven_coordinates_isCoprime` theorem;
- p=11 and p=13 universal-R carrier probes.

`DkMathTest/FLT/Prime/PrimeTraceOneUniversalTransportAxiomAudit.lean` prints
axioms for the universal transport, specialization, common-prime, and
FLT-side coprimality endpoints.  The new declarations use only the ordinary
Lean foundational axioms reported by the audit (`propext`,
`Classical.choice`, and `Quot.sound`); no `sorry`, `sorryAx`, `admit`,
`axiom`, or `unsafe` source was added.

## F. Focused validation

From `lean/dk_math`, the following combined focused build completed
successfully:

~~~text
lake build DkMath.NumberTheory.CyclotomicQRProduct \
  DkMath.NumberTheory.CyclotomicQRTraceOneBridge \
  DkMath.NumberTheory.CyclotomicQRUniversalTransport \
  DkMath.NumberTheory.CyclotomicQRUniversalTraceOneAnchor \
  DkMath.NumberTheory.CyclotomicQRCommonPrimeSupport \
  DkMath.FLT.Prime.AdicPowerSplit \
  DkMath.FLT.Prime.PrimeTraceOneCoordinateCoprime \
  DkMath.NumberTheory.TraceOneConjugateCoprime \
  DkMath.Lib.NumberTheory.IdealPowerFactor \
  DkMath.FLT.Seven \
  DkMathTest.FLT.Prime.PrimeTraceOneUniversalTransportApiAudit \
  DkMathTest.FLT.Prime.PrimeTraceOneUniversalTransportProbe \
  DkMathTest.FLT.Prime.PrimeTraceOneUniversalTransportAxiomAudit
~~~

`git diff --check` completed successfully.  A fresh source scan over the
Phase-24 production and test files found no forbidden `sorry`, `sorryAx`,
`admit`, `axiom`, or `unsafe` token.

## G. Stop boundaries

No stretch ideal-power endpoint, principalization, class-group torsion claim,
regular-prime theorem, real-sector elimination, or general FLT theorem is
included.
