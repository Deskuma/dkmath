# FLT prime-generalization Phase 20 — real TraceOne signature bridge and Dirichlet sectors

## Scope and outcome

This report records the bounded implementation requested by
`instruction-020.md`.  The real prime-discriminant branch is now connected
directly to the explicit quadratic equation.  No field-discriminant equality
was used as the primary route, and no class-group torsion-freeness, sector
elimination, regular-prime theory, or FLT contradiction was added.

The phase statuses are:

~~~text
PGEN-TRACEONE-REAL-SIGNATURE-GREEN
PGEN-TRACEONE-REAL-DIRICHLET-SECTOR-GREEN
~~~

## A. Test-first API audit

The pinned API audit is
`DkMathTest/FLT/Prime/TraceOneRealSignatureApiAudit.lean`.  It compiles
against the current Mathlib checkout and records the exact declarations used
for totally real fields, infinite-place signatures, Dirichlet units, complex
coordinates, integer powers, and unit transport.  In particular, the audit
confirms:

~~~lean
NumberField.isTotallyReal_iff
NumberField.IsTotallyReal.nrComplexPlaces_eq_zero
NumberField.IsTotallyReal.finrank
NumberField.InfinitePlace.card_add_two_mul_card_eq_rank
NumberField.Units.rank
NumberField.Units.fundSystem
NumberField.Units.exist_unique_eq_mul_prod
NumberField.Units.torsion
NumberField.RingOfIntegers.equiv
RingEquiv.toMonoidHom
Units.map
Units.val_zpow_eq_zpow_val
NumberField.ComplexEmbedding.isReal_iff
NumberField.InfinitePlace.isReal_iff
Complex.conj_eq_iff_im
QuadraticAlgebra.omega_mul_omega_eq_add
QuadraticAlgebra.mk_eq_add_smul_omega
zpow_add
zpow_mul
~~

The current checkout exposes `NumberField.isTotallyReal_iff_ofRingEquiv`,
`NumberField.maximalRealSubfield`, and the maximal-real-subfield membership
lemmas as well.  The implementation uses the shorter direct infinite-place
route.

## B. Direct `TraceOneRat` total reality

The production module is
`DkMath/NumberTheory/TraceOnePrimeUnitSectors.lean`.

The private neutral complex lemma proves that if

~~~text
z^2 = z + s,  1 + 4*s > 0,
~~~

then `z.im = 0`.  It takes real and imaginary parts, obtains
`z.im * (2 * z.re - 1) = 0`, and shows that the nonzero-imaginary branch
would contradict the positive discriminant.

For `K = TraceOneRat (signedPrimeParameter p)`, the generator relation is
transported through an arbitrary ring homomorphism `K →+* ℂ`.  The
`p % 4 = 1` hypothesis rewrites `1 + 4*s` to `p`, so the image of `omega` is
real.  `QuadraticAlgebra.mk_eq_add_smul_omega` then makes every image real.
The public theorem is:

~~~lean
traceOneRat_isTotallyReal_of_prime_mod_four_eq_one
    (hp : Nat.Prime p) (hmod : p % 4 = 1) :
    NumberField.IsTotallyReal (TraceOneRat (signedPrimeParameter p))
~~~

It is proved from `NumberField.InfinitePlace.isReal_iff` and
`NumberField.ComplexEmbedding.isReal_iff`; no `NumberField.discr K = ...`
bridge is assumed.

## C. Signature and unit rank

`traceOnePrimeReal_signature` derives, in one kernel-checked theorem,

~~~text
Module.finrank ℚ K = 2
nrComplexPlaces K = 0
nrRealPlaces K = 2
NumberField.Units.rank K = 1.
~~~

The two-dimensional fact comes from `QuadraticAlgebra.finrank_eq_two`.
Total reality gives the zero complex-place count.  The infinite-place degree
identity then gives two real places, and the definition of
`NumberField.Units.rank` reduces the rank to one.

## D. Dirichlet rank-one decomposition

For `u : (NumberField.RingOfIntegers K)ˣ`, the implementation calls
`NumberField.Units.exist_unique_eq_mul_prod`.  A local `Unique (Fin 1)`
instance reduces the finite product to one fundamental unit
`ε = NumberField.Units.fundSystem K j` and one integer exponent `n`.

The torsion component is handled by
`traceOneReal_torsion_eq_one_or_neg_one`.  If its order were greater than
two, `IsPrimitiveRoot.orderOf` and the real-place root-of-unity theorem would
force `nrRealPlaces K = 0`, contradicting the derived value two.  The order
one/two cases give `1` or `-1` explicitly.

## E. Torsion absorption and exponent reduction

For the odd prime `p`, `1` and `-1` are both p-th powers.  The proof uses
`hp.odd_of_ne_two` and the audited unit power APIs.

For `n : ℤ`, it sets `q := n / p` and `r := n % p`, proves

~~~text
0 ≤ r < p,  n = r + p*q,
~~~

and converts `r` to `i : Fin p`.  The exact group identity `zpow_add`,
followed by `zpow_mul` and the natural-cast rewrite, yields

~~~text
ε^n = ε^i * (ε^q)^p.
~~~

Combining this with the absorbed torsion component gives the genuine
ring-of-integers unit completeness statement with sectors `Fin p`.

## F. Ring-of-integers `Fin p` sector system

The public definition is:

~~~lean
traceOnePrimeRealFinSectorSystem
    {p : ℕ} (hp : Nat.Prime p) (hmod : p % 4 = 1) :
    UnitPowerSectorSystem (TraceOneInt (signedPrimeParameter p)) p
~~~

Its structure field is explicitly `Sector := Fin p`, with representatives
given by the transported fundamental unit raised to `(i : ℕ)`.  The
completeness field is proved rather than postulated.

## G. Transport to `TraceOneInt`

The Phase-17 result
`traceOneRat_ringOfIntegers_equiv` supplies

~~~text
e : NumberField.RingOfIntegers K ≃+* TraceOneInt (signedPrimeParameter p).
~~~

The production proof transports units with
`Units.map e.toMonoidHom` and pulls them back with
`Units.map e.symm.toMonoidHom`.  The inverse-unit identity is checked by
`Units.ext` and the ring-equivalence simp lemmas.  No unsupported
`RingEquiv.unitsEquiv` construction is introduced.

## H. Phase-18 conditional sector endpoint

The public theorem
`traceOnePrimeReal_exists_sector_mul_pow_of_span_eq_pow` uses
`exists_sector_mul_pow_of_span_eq_pow_of_classGroupPTorsionFreeAt` directly.
Under

~~~text
I ∈ (Ideal R)⁰
classGroupPTorsionFreeAt R p
Ideal.span ({a} : Set R) = I^p
~~~

it returns

~~~text
∃ i : Fin p, ∃ delta : R,
  a = (traceOnePrimeRealFinSectorSystem hp hmod).rep i * delta^p.
~~~

The theorem is conditional and does not eliminate `i` or prove the class-group
hypothesis.

## I. Finite regressions

The new focused probe is
`DkMathTest/FLT/Prime/TraceOneRealUnitSectorProbe.lean`.

~~~text
p=5:  signedPrimeParameter 5 = 1, total reality/rank, and a TraceOneInt 1 sector system
p=13: signedPrimeParameter 13 = 3, unit rank, and a TraceOneInt 3 sector system
~~~

The existing probe
`DkMathTest/FLT/Prime/TraceOnePrimeUnitSectorProbe.lean` was extended with
the p=5/p=13 real sector regressions while retaining:

~~~text
p=3:  existing Eisenstein exception
p=7:  imaginary singleton sector
p=11: imaginary singleton sector
~~~

The old p=5 `GoldenUnitClassesModFifth` check remains separate from the new
`TraceOneInt 1` construction; no carrier identification is claimed.

## J. Axiom and forbidden-construct audit

`DkMathTest/FLT/Prime/TraceOnePrimeUnitSectorAxiomAudit.lean` prints axioms
for the total-reality theorem, signature theorem, real sector definition, and
conditional endpoint, in addition to the Phase-19 imaginary declarations.
The new declarations report only the standard inherited
`propext`, `Classical.choice`, and `Quot.sound` dependencies from the
number-field/choice APIs.  No fresh `sorry`, `sorryAx`, `admit`, `axiom`, or
`unsafe` occurrence was found in the Phase-20 production and test files.
The forbidden scan also found no `NumberField.discr` use in the new real
bridge.

## K. Focused validation

The following focused builds were run successfully from `lean/dk_math`:

~~~text
lake build DkMath.NumberTheory.TraceOneQuadraticField
lake build DkMath.NumberTheory.TraceOnePrimeUnitSectors
lake build DkMath.Lib.NumberTheory.UnitPowerSector
lake build DkMathTest.FLT.Prime.TraceOneRealSignatureApiAudit
lake build DkMathTest.FLT.Prime.TraceOneRealUnitSectorProbe
lake build DkMathTest.FLT.Prime.TraceOnePrimeUnitSectorProbe
lake build DkMathTest.FLT.Prime.TraceOnePrimeUnitSectorAxiomAudit
lake build DkMath.FLT.Seven
git diff --check
~~~

A fresh warning scan leaves the pre-existing
`DkMath/NumberTheory/ZsigmondyCyclotomicResearch.lean:147` `sorry` warning
outside this phase.  The Phase-20 declarations themselves have no
`sorry`-declaration warning.

## L. Remaining non-goals

This phase does not prove `classGroupPTorsionFreeAt`, does not eliminate any
nonzero sector, and does not establish FLT.  It only supplies the real
TraceOne signature and finite Dirichlet sector bridge needed by the
conditional Phase-18 endpoint.
