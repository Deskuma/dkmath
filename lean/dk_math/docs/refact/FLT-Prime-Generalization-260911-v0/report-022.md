# FLT prime-generalization Phase 22 — arbitrary-prime coordinate provenance

## Scope and outcome

This report records the bounded implementation requested by
`instruction-022.md`. The Phase-13 arbitrary-prime QR/QNR/Gauss construction
now retains its proof provenance in a public packet and the old norm-only
endpoint is derived from that packet.

The phase status is:

~~~text
PGEN-PRIME-TRACEONE-COORDINATE-PACKET-GREEN
PGEN-PRIME-COORDINATE-COPRIME-STILL-OPEN
~~~

No receiver field or theorem hypothesis postulating coordinate coprimality was
added. The general primitive-coordinate/cyclotomic common-prime bridge, and
therefore the Phase-15 composition for arbitrary primes, remains open.

## A. Pinned API audit

`DkMathTest/FLT/Prime/PrimeTraceOneCoordinateApiAudit.lean` records the
checkout-local signatures for the requested APIs. In particular, the
resultant equivalence available in this Mathlib checkout is:

~~~lean
Polynomial.isUnit_resultant_iff_isCoprime
~~~

It requires the first polynomial to be monic. There is no declaration named
`Polynomial.isCoprime_iff_resultant_isUnit`. `Ideal.Quotient` is a namespace;
the audit pins `Ideal.Quotient.mk` and
`Ideal.Quotient.mk_eq_mk_iff_sub_mem`.

The existing DkMath declarations requested by the instruction, including the
Phase-21 axis and terminal-normalization endpoints, are also pinned.

## B. Preserved arbitrary-prime construction

`DkMath/NumberTheory/CyclotomicQRTraceOneBridge.lean` adds:

~~~lean
PrimeTraceOneCoordinatePacket
PrimeTraceOneCoordinatePacket.coord
PrimeTraceOneCoordinatePacket.coord_norm_eq
exists_prime_traceOne_coordinate_packet
~~~

The packet retains `RZ`, `SZ`, and `AZ`, together with:

~~~lean
map_RZ
gauss_form
gauss_difference
half_relation
norm_eq
~~~

`exists_prime_traceOne_coordinate_packet` is constructed directly from
`exists_integral_gauss_form`, `map_modTwo_eq_of_integral_gauss_form`, and
`exists_half_difference`; the Gauss descent is not duplicated. The previous
`exists_prime_traceOne_coordinates` theorem is now a compatibility corollary
of the packet.

Thus the raw arbitrary-prime result proved in this phase is:

~~~text
the QR/QNR/Gauss construction produces integral AZ,SZ polynomials,
and their evaluated TraceOne norm is GTailCyclotomicShell.
~~~

It does not yet prove `Nat.Coprime z y -> IsCoprime A(z,y) S(z,y)`.

## C. Resultant and finite regressions

The p=3, 5, 7, 11, and 13 packet regressions are in
`DkMathTest/FLT/Prime/PrimeTraceOneCoordinatePacketProbe.lean`.

- p=3 preserves the Eisenstein parameter without forcing generic axis
  stripping.
- p=5 exercises the `TraceOneInt 1` packet endpoint at a concrete input.
- p=7 compares the generic packet norm endpoint with the existing specialized
  cyclotomic-seven coordinate endpoint and replays specialized coordinate
  coprimality.
- p=11 and p=13 compare the generic packet norm endpoint with the existing
  explicit `A11/B11` and `A13/B13` formulas.

These comparisons identify the common exact shell norm, but do not identify
the existential packet polynomials with the specialized formulas. The
resultant API is audited, while a general unit-resultant proof for the
existential packet polynomials has not been added.

## D. What additionally uses the FLT-side p-adic input

No new theorem in this phase consumes
`PrimeAdicFactorPacket.residual_exact_one` or
`PrimeAdicFactorPacket.residual_not_prime_sq`. Consequently no theorem is
claimed that eliminates the remaining common prime `p` from arbitrary-prime
packet coordinates.

The exact p-adic input remains available through the audited existing API:

~~~lean
PrimeAdicFactorPacket.residual_exact_one
PrimeAdicFactorPacket.residual_not_prime_sq
PrimeAdicPowerSplit.residual_eq
~~~

The missing step is still the theorem that a common coordinate prime is
either the exponent prime or is impossible, followed by the residual
`p^2` contradiction.

## E. Axis-stripped and ideal endpoints

The Phase-21 production theorem

~~~lean
ideal_isCoprime_span_conj_of_coordinate_coprime_of_axis_terminal
~~~

remains the available neutral endpoint once coordinate coprimality and axis
terminality are supplied. The Phase-21 theorem

~~~lean
PrimeDiscriminantPacket.exists_terminal_discrAxis_mul_of_natAbs_norm_eq_prime_mul_pow
~~~

still provides conditional one-axis stripping from a norm equality of the
form `p * c^p` with `p ∤ c`. This Phase-22 change does not claim that the new
packet supplies those hypotheses, and it does not add the requested
parent-coordinate-to-stripped-residual ideal wrapper.

## F. Open boundary

The smallest precise open boundary is:

~~~text
PGEN-PRIME-COORDINATE-COPRIME-STILL-OPEN
~~~

The missing production theorem must connect the retained `RZ/SZ/AZ`
provenance to either a unit resultant/Bézout statement or the weaker
common-prime support statement. The audited APIs alone do not provide that
connection, so no resultant, residue-field, or cyclotomic ideal fact was
assumed in its place.

## G. Axiom and source audit

`DkMathTest/FLT/Prime/PrimeTraceOneCoordinatePacketAxiomAudit.lean` prints the
axioms of the new public packet declarations. They use only the standard
inherited `propext`, `Classical.choice`, and `Quot.sound` dependencies from
the existing QR/Gauss construction.

The fresh Phase-22 production/test source scan found no new `sorry`,
`sorryAx`, `admit`, `axiom`, or `unsafe` occurrence after excluding the
intentional `#print axioms` directives in the axiom-audit source itself.

## H. Focused validation

The following commands were run successfully from `lean/dk_math`:

~~~text
lake build DkMath.NumberTheory.CyclotomicQRTraceOneBridge
lake build DkMathTest.FLT.Prime.PrimeTraceOneCoordinateApiAudit
lake build DkMathTest.FLT.Prime.PrimeTraceOneCoordinatePacketProbe
lake build DkMathTest.FLT.Prime.PrimeTraceOneCoordinatePacketAxiomAudit
git diff --check
~~~

The Phase-21 focused TraceOne conjugate-coprime regressions were preserved and
remain green from their prior focused validation.

## I. Non-goals

This phase does not prove arbitrary-prime coordinate coprimality, the
common-prime support theorem, the FLT-side p-adic elimination for the new
coordinates, the parent-coordinate stripped-ideal wrapper, class-group
principalization, unit-sector elimination, or FLT.
