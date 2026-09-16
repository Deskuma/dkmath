# FLT prime-generalization Phase 23 — residue transport audit and blocker

## Scope and outcome

This report records the bounded implementation requested by
`instruction-023.md`.  The phase adds the requested API audit and isolates the
positive-characteristic Gauss input.  The characteristic-independent packet
transport itself remains open, so the common-prime-support and subsequent
FLT-side endpoints are not claimed.

The verified status is:

~~~text
PGEN-PRIME-COORDINATE-GAUSS-NONZERO-CHAR-NE-GREEN
PGEN-PRIME-COORDINATE-RESIDUE-TRANSPORT-STILL-OPEN
PGEN-PRIME-COORDINATE-COMMON-PRIME-SUPPORT-STILL-OPEN
~~~

The requested `PGEN-PRIME-COORDINATE-RESIDUE-TRANSPORT-GREEN` status was not
assigned.

## A. Pinned API audit

`DkMathTest/FLT/Prime/PrimeTraceOneResidueTransportApiAudit.lean` records the
checkout-local declarations for:

- `PrimeTraceOneCoordinatePacket`, `.coord`, and the fields
  `map_RZ`, `gauss_form`, `gauss_difference`, `half_relation`, and `norm_eq`;
- the QR/QNR factor sets, root factors, product identity, root-power
  injectivity, `Rpoly`, `Dpoly`, `qrFactorPoly`, and `qnrFactorPoly`;
- `quadraticGauss`, the existing `quadraticGauss_sq` and
  `quadraticGauss_ne_zero` theorems, and Mathlib's generic
  `gaussSum_sq`/`gaussSum_ne_zero_of_nontrivial` APIs;
- `Polynomial.isRoot_cyclotomic_iff`, its char-zero comparison theorem,
  `IsAlgClosed.exists_root`, `primitiveRoots`, `IsPrimitiveRoot`, the
  resultant equivalence and resultant base-change theorem;
- `CyclotomicRing`, `AdjoinRoot`, `AdjoinRoot.mk`, and
  `IsPrimitiveRoot.adjoinEquivRingOfIntegers`;
- the existing GTail, p-adic, Phase-21 axis/ideal, and Phase-15 ideal-power
  endpoints.

The exact audit shows that
`IsPrimitiveRoot.adjoinEquivRingOfIntegers` has `[CharZero K]` and a
cyclotomic extension over `ℚ`, while `quadraticGauss_sq` has the same
characteristic-zero shape.  The generic `isRoot_cyclotomic_iff` is available
under `NeZero (p : K)` and is not the char-zero-only comparison theorem.

## B. Positive-characteristic Gauss nonvanishing

`DkMath/NumberTheory/CyclotomicQRGaussNormalization.lean` adds:

~~~lean
quadraticGauss_ne_zero_of_char_ne
~~~

For a field `K` of prime characteristic `q`, odd primes `p` and `q`, and
`q ≠ p`, the theorem proves that the existing `quadraticGauss` attached to a
primitive `p`-th root in `K` is nonzero.  The proof uses:

1. the nontriviality of the integer-valued quadratic character after mapping
   `ℤ` to `K`, using `q ≠ 2`;
2. `CharP.cast_eq_zero_iff` and `q ∤ p` to show the source cardinality does
   not vanish in `K`;
3. `AddChar.zmodChar_primitive_of_primitive_root`; and
4. Mathlib's `gaussSum_ne_zero_of_nontrivial`.

No positive-characteristic square identity was postulated.  The new theorem's
signature and its inherited axioms are checked by
`PrimeTraceOneResidueTransportProbe.lean` and
`PrimeTraceOneResidueTransportAxiomAudit.lean`.

## C. Exact residue-transport blocker

The Phase-22 packet currently has the following shape:

~~~text
map (algebraMap ℤ L) RZ = Rpoly ζ
C (quadraticGauss ζ) * map (algebraMap ℤ L) SZ = Dpoly ζ
~~~

where `L` is one characteristic-zero cyclotomic extension of `ℚ`.  The
existing `Rpoly` and `Dpoly` declarations are parameterized by the target
field and root.  The existing integer descents are existential constructions
for that selected `L`; they do not produce either of the following missing
objects:

1. a universal `AdjoinRoot (cyclotomic p ℤ)` or `CyclotomicRing` identity whose
   coefficient image is `RZ`/`SZ`; or
2. a coefficientwise divisibility theorem showing that the differences from
   the packet polynomials are multiples of the cyclotomic polynomial over
   `ℤ`, ready for specialization to characteristic `q`.

Consequently, the available `map_RZ` and `gauss_difference` equalities cannot
be rewritten in an algebraic closure of `ZMod q` by transport alone.  The
available `Polynomial.resultant_map_map` theorem only transports a resultant
after universal polynomials and their identity have already been supplied; it
does not establish this missing packet identity.  Likewise,
`IsPrimitiveRoot.adjoinEquivRingOfIntegers` is a characteristic-zero integral
closure equivalence and cannot serve as the residue-characteristic bridge.

No theorem asserting `packet.map_RZ_in_any_primitive_root`,
`packet.gauss_difference_in_any_primitive_root`, or the common-prime-support
conclusion was added in place of this missing proof.

## D. Downstream boundary

Because Part B is not closed, this phase stops before the odd-residue QR/QNR
contradiction in Part C, the separate `q = 2` argument, the
`residual_not_prime_sq` elimination, axis stripping, and ideal p-th-power
extraction.  The Phase-22 p=3, 5, 7, 11, and 13 packet regressions remain in
`PrimeTraceOneCoordinatePacketProbe.lean`; they continue to check the existing
characteristic-zero norm endpoint and do not assert residue transport.

## E. Focused validation

The following builds were run successfully from `lean/dk_math`:

~~~text
lake build DkMath.NumberTheory.CyclotomicQRGaussNormalization
lake build DkMathTest.FLT.Prime.PrimeTraceOneResidueTransportApiAudit
lake build DkMathTest.FLT.Prime.PrimeTraceOneResidueTransportProbe
lake build DkMathTest.FLT.Prime.PrimeTraceOneResidueTransportAxiomAudit
~~~

The final Phase-23 focused replay and source audits are recorded in the
handoff response.  No `sorry`, `sorryAx`, `admit`, `axiom`, or `unsafe` was
introduced by the Phase-23 production or test sources, apart from intentional
`#print axioms` audit directives.

## F. Non-goals

This phase does not prove the universal packet transport, arbitrary-prime
coordinate coprimality, the common-prime-support theorem, arbitrary-prime FLT,
class-group p-torsion-freeness, a class-number theorem, regular-prime theory,
real-sector elimination, or an unproved resultant identity.
