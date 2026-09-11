# FLT prime-generalization Phase 14 — arithmetic frontier audit

## Scope and outcome

This report records the bounded implementation requested by
instruction-014.md. The Phase-13 arbitrary-prime TraceOne bridge is kept
unchanged. This phase audits the existing FLT7 arithmetic layer, adds the
small exponent-independent factor-extraction and unit-absorption helpers, and
does not assert an arbitrary-prime FLT theorem.

The required outcome is:

    Outcome A — ABSTRACT-ARITHMETIC-FRONTIER
    PGEN-ARITHMETIC-FRONTIER-AUDITED

The first reusable step is now abstract over the exponent and over the ring:
coprime factors of a p-th power are associated to p-th powers. The first
prime-dependent obstruction after that step is the unit class modulo p-th
powers, followed in the non-PID/non-UFD route by principalization and the
p-torsion of the class group.

## A. FLT7 declaration audit

The audit was performed in the requested import order. The labels below use
the six classifications from the instruction.

### QuadraticResidualPacket.lean

| Public declaration or family | Classification | Boundary |
|---|---|---|
| SevenQuadraticResidualPacket | P7-ARITHMETIC | Uses SevenAdicPowerSplit, cyclotomicSevenToTraceOne, sevenAxis, and the exact exponent 7. |
| nonempty_sevenQuadraticResidualPacket_of_powerSplit | P7-ARITHMETIC | The terminal core is obtained from the p=7 split and the p=7 cyclotomic identity. |
| sevenQuadraticResidualPacket_of_powerSplit, sevenQuadraticResidualPacket_of_counterexample | P7-ARITHMETIC | Choice wrappers around the same specialized packet. |
| SevenQuadraticResidualPacket.norm_is_seventh_power, .norm_positive | P7-ARITHMETIC | The norm source and positivity are specialized to the seventh-power packet. |

The packet is not a consequence of the Phase-13 coordinate bridge alone: it
also needs the specialized adic split, terminality, and the p=7 norm identity.

### QuadraticEuclidean.lean

| Public declaration or family | Classification | Boundary |
|---|---|---|
| traceOneNegTwo_eq_zero_or_eq_zero_of_mul_eq_zero, traceOneNegTwoNoZeroDivisors, traceOneNegTwoNontrivial, traceOneNegTwoIsDomain | P7-ARITHMETIC | Proves the domain structure from the positive-definite discriminant -7 norm. |
| SevenRat, sevenRatNorm, rounding, quotient, remainder, and size declarations | P7-ARITHMETIC | The nearest-lattice division proof is a concrete -7 geometry argument. |
| seven_remainder_size_lt | P7-ARITHMETIC | This is the strict Euclidean decrease; it is not supplied by the generic TraceOne front-end. |
| traceOneNegTwoEuclideanDomain | P7-ARITHMETIC | A concrete Euclidean-domain instance for TraceOneInt (-2). |

The quotient/remainder declarations are public support for the Euclidean
instance; downstream factor extraction consumes the instance rather than a
generic arbitrary-discriminant Euclidean theorem.

### QuadraticUnits.lean

| Public declaration | Classification | Boundary |
|---|---|---|
| isUnit_iff_norm_eq_one, isUnit_iff_eq_one_or_neg_one | P7-ARITHMETIC | The norm-one shell is exactly {1,-1} for discriminant -7. |
| exists_seventh_power_eq_of_isUnit | PGEN-UNIT-SECTOR | It is the unit-absorption step, but its proof uses the p=7 unit classification and odd exponent. |

This is stronger than a finite unit-sector statement for this order: every
unit is itself a seventh power. No corresponding assertion is made for
TraceOneInt (signedPrimeParameter p) at arbitrary p.

### QuadraticCoprimeFactor.lean

| Public declaration | Classification | Boundary |
|---|---|---|
| traceOneNegTwoGCDMonoid | PGEN-GCD-UFD | Obtained from the specialized Euclidean domain. |
| associated_seventh_power_of_coprime_mul_eq_pow | PGEN-ABSTRACT-RING | The proof is the pinned Mathlib theorem with exponent 7; the new neutral wrapper removes the fixed exponent. |
| exists_eq_seventh_power_of_coprime_mul_eq_pow | PGEN-UNIT-SECTOR | Adds p=7 unit-power absorption to associated extraction. |
| seventh_power_factor_split_traceOneNegTwo | PGEN-UNIT-SECTOR | Repeats the same associated-extraction and unit-absorption argument for both factors. |

The file does not need a separately declared UFD in these theorem statements.
Mathlib packages the element factorization behind GCDMonoid; the concrete
source of the instance here is still the p=7 Euclidean proof.

### QuadraticConjugateCoprime.lean

| Public declaration or family | Classification | Boundary |
|---|---|---|
| irreducible_sevenAxis, prime_sevenAxis | P7-ARITHMETIC | Uses sevenAxis_norm = 7, p=7 prime divisors, and the domain instance. |
| isUnit_of_dvd_sevenAxis_of_dvd_terminal | P7-ARITHMETIC | Uses irreducibility of the p=7 axis and the terminal non-divisibility certificate. |
| cyclotomicSeven_gcd_conj_isUnit_of_not_seven_dvd_gap | P7-ARITHMETIC | Uses the p=7 coordinate common-divisor theorem and the p=7 gap test. |
| exists_cyclotomicSeven_eq_seventh_power_of_away | P7-ARITHMETIC | Combines the away branch, conjugate gcd certificate, and the seventh-power factor split. |
| SevenQuadraticResidualPacket.gcd_residual_conj_isUnit | P7-ARITHMETIC | Transfers the p=7 cyclotomic gcd certificate through sevenAxis * residualCore. |
| SevenQuadraticResidualPacket.exists_residualCore_eq_seventh_power | P7-ARITHMETIC | Uses the residual conjugate product and the p=7 unit-absorption layer. |

The gcd certificates need GCDMonoid only where an actual gcd is formed; the
axis irreducibility and the common-divisor-to-unit argument are logically
weaker than a Euclidean-domain construction.

### QuadraticSeventhPowerNormalForm.lean

| Public declaration or family | Classification | Boundary |
|---|---|---|
| SevenQuadraticSeventhPowerPacket and its constructors | P7-ARITHMETIC | Packages the specialized seventh-power residual normal form. |
| QuadraticCounterexampleRoute, quadraticCounterexampleRoute_of_pack | P7-ARITHMETIC | Routes the p=7 gap branch into away or ramified specialized packets. |

The route shape is reusable as a design pattern, but these declarations are
not arbitrary-prime theorems: both branches contain p=7-specific input.

## B. Generic coprime-power extraction

The test-first probe is:

    DkMathTest/FLT/Prime/AssociatedPrimePowerAuditProbe.lean

It first checked the target directly against the pinned Mathlib theorem
exists_associated_pow_of_mul_eq_pow. The production wrapper is now in:

    DkMath/Lib/NumberTheory/PowerFactor.lean

with declaration:

    DkMath.Lib.NumberTheory.associated_prime_power_of_coprime_mul_eq_pow

Its actual pinned contract is:

    {R : Type*} [CommMonoidWithZero R] [GCDMonoid R]
    {p : ℕ} {x y z : R}
    (hcop : IsUnit (gcd x y)) (hpow : x * y = z ^ p) :
    ∃ gamma : R, Associated x (gamma ^ p)

The instruction's name CommCancelMonoidWithZero is not a declaration in the
pinned Mathlib 4.32.2. GCDMonoid itself extends the required
IsCancelMulZero, so [CommMonoidWithZero R] [GCDMonoid R] is the weakest
available practical contract used here.

The result is PGEN-ABSTRACT-RING: the exponent is a parameter and there is
no TraceOne, discriminant, Euclidean, unit, or class-group assumption.

## C. Unit absorption boundary

The same production module also exports:

    DkMath.Lib.NumberTheory.eq_pow_of_associated_pow_of_unit_pow_surjective

under [CommMonoidWithZero R], with the neutral unit-group hypothesis

    ∀ u : Rˣ, ∃ e : Rˣ, u = e ^ p

and conclusion

    Associated x (gamma ^ p) → ∃ delta, x = delta ^ p.

This is the exact separation needed by the FLT7 proof: associated extraction
is generic, while equality is a unit-sector statement. The unit-group form
also avoids silently adding an inverse operation to an arbitrary monoid.

For TraceOneInt (-2), QuadraticUnits.lean proves the stronger concrete fact
that every unit is a seventh power through isUnit_iff_eq_one_or_neg_one and
exists_seventh_power_eq_of_isUnit. The helper is not specialized to, and does
not assume, arbitrary TraceOneInt (signedPrimeParameter p).

## D. Euclidean/GCD/UFD dependency audit

| Declaration | Actual required arithmetic boundary |
|---|---|
| irreducible_sevenAxis | Concrete -7 norm and ring arithmetic; no EuclideanDomain, GCDMonoid, UFD, or PID theorem is used as an input. |
| prime_sevenAxis | The IsDomain (TraceOneInt (-2)) instance plus Mathlib's irreducible_iff_prime; no Euclidean theorem is used directly. |
| isUnit_of_dvd_sevenAxis_of_dvd_terminal | Irreducibility of sevenAxis, divisibility, units, and terminality; no gcd is needed. |
| SevenQuadraticResidualPacket.gcd_residual_conj_isUnit | GCDMonoid for gcd and its two divisor projections, plus the p=7 axis argument. |
| associated_seventh_power_of_coprime_mul_eq_pow | GCDMonoid and Mathlib's generic associated-power extraction. |
| exists_eq_seventh_power_of_coprime_mul_eq_pow | The preceding GCDMonoid extraction plus p=7 unit-power absorption. |

Thus the current Euclidean instance is stronger than the immediate extraction
theorems require. It supplies the concrete GCDMonoid instance, but the first
generic replacement should ask only for GCD/UFD structure where it is
available. If a prime-discriminant order is not a proved GCD/UFD, the honest
replacement is ideal-theoretic coprime factorization followed by class-group
control, not an unproved arbitrary TraceOne Euclidean instance.

## E. Discriminant-axis comparison

The p=7 axis is the specialization

    sevenAxis = discrAxis (-2)

by the definitions in TraceOneQuadratic.lean and
TraceOneDiscriminantAxis.lean. For the packet
PrimeDiscriminantPacket 7 (-2), the generic Phase-4 declarations provide the
same arithmetic backbone:

    discrAxis_sq
    norm_discrAxis
    PrimeDiscriminantPacket.discrAxis_dvd_iff_prime_dvd_natAbs_norm
    PrimeDiscriminantPacket.discrAxis_pow_dvd_iff_pow_prime_dvd_natAbs_norm
    PrimeDiscriminantPacket.exists_terminal_discrAxis_core

In particular, sevenAxis_sq and sevenAxis_norm are p=7 presentations of
discrAxis_sq and norm_discrAxis; the specialized form exposes the exact
integer -7 and 7 values used by the FLT7 code. The generic terminal core also
explains the shape of the specialized axis-depth APIs.

The existing Seven API was not rewritten. SevenQuadraticResidualPacket
contains extra p=7 data—SevenAdicPowerSplit, a seventh-power norm, and the
cyclotomic coordinate identity—so it is not merely a rename of
exists_terminal_discrAxis_core. Likewise, the conjugate-coprime module uses
p=7 theorems such as sevenAxis_dvd_cyclotomicSevenToTraceOne_iff and
common_divisor_cyclotomic_conj_dvd_sevenAxis.

## F. Class-group frontier and pinned API audit

The natural arbitrary-prime replacement is the following. If the principal
ideals generated by alpha and conj alpha are coprime and

    (alpha) * (conj alpha) = (beta)^p,

ideal factorization gives (alpha) = A^p for an ideal A. To return from A^p
to an element equation alpha = unit * gamma^p, one must principalize A. The
obstruction is the p-torsion class [A] in the relevant class group. Unit
classes modulo p-th powers remain a separate obstruction even after
principalization.

The actual pinned Mathlib declarations inspected for this design are:

    Mathlib.RingTheory.DedekindDomain.Ideal.Basic
      Ideal.uniqueFactorizationMonoid

    Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
      Ideal.prod_normalizedFactors_eq_self
      Ideal.count_normalizedFactors_eq_multiplicity
      Ideal.normalizedFactorsEquivSpanNormalizedFactors

    Mathlib.RingTheory.DedekindDomain.Factorization
      Ideal.finprod_heightOneSpectrum_factorization
      FractionalIdeal.finprod_heightOneSpectrum_factorization
      FractionalIdeal.finprod_heightOneSpectrum_factorization_principal

    Mathlib.RingTheory.ClassGroup.Basic
      FractionalIdeal.mk0
      ClassGroup.mk0
      ClassGroup.mk0_eq_one_iff
      ClassGroup.mk0_eq_mk0_iff
      ClassGroup.mk0_surjective
      ClassGroup.mk_eq_one_iff
      Submodule.IsPrincipal.generator

    Mathlib.RingTheory.DedekindDomain.PID
      IsPrincipalIdealRing.of_isDedekindDomain_of_uniqueFactorizationMonoid

The ideal factorization APIs are concrete, but they require a proved
IsDedekindDomain/fractional-ideal setting. No such setting or class-group
p-torsion theorem was added to the TraceOne prime bridge in this phase. The
existing DkMath Kummer declaration CyclotomicClassGroupPTorsionFreeTarget
remains a separate conditional design route and is not silently imported as a
proof of the present TraceOne arithmetic frontier.

## G. Finite specialization audit

The Phase-13 bridge probes all five parameters. The arithmetic status below
is stricter: it records only declarations or instances actually present in
DkMath/Mathlib for the stated carrier.

| p, s_p | IsDomain | EuclideanDomain | GCDMonoid / UFD | unit classes modulo p-th powers | axis irreducible / prime | conjugate-coprime extraction |
|---|---|---|---|---|---|---|
| 3, -1 | AVAILABLE: traceOneNegOneIsDomain | AVAILABLE: traceOneNegOneEuclideanDomain | AVAILABLE: traceOneNegOneGCDMonoid; Euclidean consequences supply factorization | AVAILABLE: EisensteinUnitSectors, especially exists_sector_mul_cube_of_unit and eisensteinUnit_cases | NOT FORMALIZED for generic discrAxis (-1) | AVAILABLE up to unit/sector: associated_cube_of_coprime_mul_eq_cube and exists_unit_mul_cube_of_coprime_mul_eq_cube; no unconditional exact cube theorem at this layer |
| 5, 1 | NOT FORMALIZED for TraceOneInt 1 | NOT FORMALIZED for TraceOneInt 1 | NOT FORMALIZED for TraceOneInt 1 | AVAILABLE on parallel GoldenInt model: goldenUnitClassesModFifth; no proved transport to TraceOneInt 1 | NOT FORMALIZED for discrAxis 1 | AVAILABLE on GoldenInt up to unit through goldenCoprimeFactorOfFifthPower; not a TraceOne carrier theorem |
| 7, -2 | AVAILABLE: traceOneNegTwoIsDomain | AVAILABLE: traceOneNegTwoEuclideanDomain | AVAILABLE: traceOneNegTwoGCDMonoid; Euclidean consequences supply factorization | AVAILABLE, stronger than classes: exists_seventh_power_eq_of_isUnit | AVAILABLE: irreducible_sevenAxis, prime_sevenAxis | AVAILABLE: away and residual extraction, including exists_eq_seventh_power_of_coprime_mul_eq_pow |
| 11, -3 | NOT FORMALIZED for TraceOneInt (-3) | NOT FORMALIZED | NOT FORMALIZED | NOT FORMALIZED | NOT FORMALIZED | NOT FORMALIZED |
| 13, 3 | NOT FORMALIZED for TraceOneInt 3 | NOT FORMALIZED | NOT FORMALIZED | NOT FORMALIZED | NOT FORMALIZED | NOT FORMALIZED |

For p=11 and p=13, the existing A11/B11 and A13/B13 identities are
test-side bridge probes in
DkMathTest/FLT/Prime/QuadraticCyclotomicBridgeProbe.lean; they do not provide
the missing ring arithmetic instances. The Phase-13 generic endpoint is
therefore green only for the TraceOne norm front-end, not for this arithmetic
layer.

## H. Verification

The test-first probe and the production axiom audit are:

    DkMathTest/FLT/Prime/AssociatedPrimePowerAuditProbe.lean
    DkMathTest/FLT/Prime/AssociatedPrimePowerAuditAxiomAudit.lean

The new neutral declarations build with the probe. The Phase-14 focused
production replay is:

    lake build DkMath.NumberTheory.CyclotomicQRTraceOneBridge
    lake build DkMath.FLT.Seven.QuadraticResidualPacket
    lake build DkMath.FLT.Seven.QuadraticEuclidean
    lake build DkMath.FLT.Seven.QuadraticUnits
    lake build DkMath.FLT.Seven.QuadraticCoprimeFactor
    lake build DkMath.FLT.Seven.QuadraticConjugateCoprime
    lake build DkMath.FLT.Seven.QuadraticSeventhPowerNormalForm
    lake build DkMath.FLT.Seven

The final closeout also includes the new neutral module and both audit tests,
git diff --check, a fresh warning scan with the standard
declaration uses \`sorry\` diagnostic separated, and a direct source scan for
new sorry, sorryAx, or explicit axiom declarations. The new production
declarations are wrappers/proofs only; no new axiom or sorry is introduced.

## Boundary

This phase closes the audited arithmetic frontier and exposes the reusable
abstract/unit-sector split. It does not add an arbitrary TraceOne
Euclidean/PID/UFD theorem, prove unit p-th-power surjectivity for arbitrary
prime discriminants, prove class groups vanish or have no p-torsion, enter a
Kummer route, or prove general FLT.
