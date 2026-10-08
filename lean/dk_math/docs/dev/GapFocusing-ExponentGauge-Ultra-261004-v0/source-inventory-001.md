# Source inventory — Gap focusing

Date: 2026-10-04. Toolchain: Lean 4.34.1 / Mathlib v4.34.1.
The following names and hypotheses were read from the current workspace.
`GN d x u` is the existing abbreviation for `GTail d 1 x u`.

## Existing exact algebra

| Declaration | Typed setting and content | Source |
| --- | --- | --- |
| `DkMath.CosmicFormula.GN` | `[CommSemiring R]`; canonical abbreviation for `GTail d 1 x u` | [Defs](../../../DkMath/CosmicFormula/Defs.lean) |
| `DkMath.CosmicFormula.add_pow_eq_mul_GTail_one_add_gap` | `[CommSemiring R]`, all `d,x,u`; `(x+u)^d = x*GTail d 1 x u + u^d` | [GTail](../../../DkMath/Lib/Cosmic/GTail.lean) |
| `DkMath.CosmicFormula.GN_zero_eval` | `[CommSemiring R]`; `GTail d 1 0 u = choose(d,1)*u^(d-1)` | [GTail](../../../DkMath/Lib/Cosmic/GTail.lean) |
| `DkMath.CosmicFormula.map_GN` | Semiring homomorphisms between commutative semirings preserve GN | [GNProductDegree](../../../DkMath/Lib/Cosmic/GNProductDegree.lean) |
| `DkMath.CosmicFormula.GN_mul_degree` | `[CommSemiring R]`; generic composition at degrees `a*b`, including zero gap and zero divisors | [GNProductDegree](../../../DkMath/Lib/Cosmic/GNProductDegree.lean) |
| `DkMath.CosmicFormula.GTail_one_eq_GTailCyclotomicShell` | `[CommSemiring R]`; GN equals `∑k<d (x+u)^k*u^(d-1-k)` without cancellation | [GTailCyclotomic](../../../DkMath/Lib/Cosmic/GTailCyclotomic.lean) |
| `DkMath.Lib.NumberTheory.prod_cyclotomicEval_eq_geomSum` | `[CommRing R]`, `0<d`; product over `d.divisors.erase 1` equals the evaluated geometric sum | [GTailCyclotomic](../../../DkMath/Lib/Cosmic/GTailCyclotomic.lean) |
| `DkMath.CosmicFormula.GTailCyclotomicHomEval_prime_eq_shell` | `[CommRing R]`, prime `p`; homogeneous `Φ_p` evaluation equals the GN shell | [GTailCyclotomic](../../../DkMath/Lib/Cosmic/GTailCyclotomic.lean) |
| `DkMath.NumberTheory.one_lt_factors_of_composite_degree` | Natural numbers; `2≤a,b`, `0<x,u`; both GN factors exceed one | [GNDegreeFactorization](../../../DkMath/NumberTheory/GNDegreeFactorization.lean) |
| `DkMath.NumberTheory.prime_degree_of_prime_GN` | Natural numbers; `2≤d`, `0<x,u`, prime GN value implies prime degree | [GNDegreeFactorization](../../../DkMath/NumberTheory/GNDegreeFactorization.lean) |

The existing prime homogeneous shell API already has a commutative-ring
statement; its older field/nonzero compatibility wrapper is not the strongest
available theorem. The new modules retain the existing kernel definition.

## Mathlib polynomial and phase APIs

| Declaration | Typed setting and content | Source |
| --- | --- | --- |
| `Polynomial.X_dvd_iff` | `[Semiring R]`; divisibility by formal `X` iff constant coefficient vanishes | [Polynomial/Div](../../../.lake/packages/mathlib/Mathlib/Algebra/Polynomial/Div.lean) |
| `Polynomial.prod_cyclotomic_eq_X_pow_sub_one` | `[CommRing R]`, positive degree; divisor product for `X^d-1` | [Cyclotomic/Basic](../../../.lake/packages/mathlib/Mathlib/RingTheory/Polynomial/Cyclotomic/Basic.lean) |
| `Polynomial.prod_cyclotomic_eq_geom_sum` | `[CommRing R]`, positive degree; divisor product after removing `Φ_1` | [Cyclotomic/Basic](../../../.lake/packages/mathlib/Mathlib/RingTheory/Polynomial/Cyclotomic/Basic.lean) |
| `Polynomial.cyclotomic_prime` | `[CommRing R]`, `[Fact p.Prime]`; `Φ_p` is the geometric sum | [Cyclotomic/Basic](../../../.lake/packages/mathlib/Mathlib/RingTheory/Polynomial/Cyclotomic/Basic.lean) |
| `Polynomial.cyclotomic.irreducible` | Positive index, polynomial over `ℤ` | [Cyclotomic/Roots](../../../.lake/packages/mathlib/Mathlib/RingTheory/Polynomial/Cyclotomic/Roots.lean) |
| `Polynomial.taylorEquiv` | `[CommRing R]`; translation is a polynomial ring automorphism | [Taylor](../../../.lake/packages/mathlib/Mathlib/Algebra/Polynomial/Taylor.lean) |
| `Polynomial.IsPrimitive.Int.irreducible_iff_irreducible_map_cast` | Primitive integer polynomial; Gauss lemma transfers irreducibility to `ℚ[X]` | [GaussLemma](../../../.lake/packages/mathlib/Mathlib/RingTheory/Polynomial/GaussLemma.lean) |
| `IsPrimitiveRoot.pow_sub_pow_eq_prod_sub_mul` | `[CommRing R] [IsDomain R]`, `0<d`, primitive `d`th root; difference of powers is the product over `nthRootsFinset d 1` | [Cyclotomic/Basic](../../../.lake/packages/mathlib/Mathlib/RingTheory/Polynomial/Cyclotomic/Basic.lean) |
| `IsPrimitiveRoot.geom_sum_isUnit` | `[CommRing R] [IsDomain R]`, primitive root of order `n`, `2≤n`, `j.Coprime n`; geometric sum is a unit | [CyclotomicUnits](../../../.lake/packages/mathlib/Mathlib/RingTheory/RootsOfUnity/CyclotomicUnits.lean) |
| `mul_neg_geom_sum` | Ring geometric-sum identity; `(1-zeta)*∑i<j zeta^i = 1-zeta^j` | Used by [UnitGauge](../../../DkMath/NumberTheory/GapFocusing/UnitGauge.lean) |

The phase theorem has no characteristic-zero hypothesis, but it does require
a domain containing a primitive root of the specified order. An arbitrary
root set in an arbitrary ring cannot replace these splitting hypotheses.

## Unit-power and actual FLT carriers

| Declaration | Typed setting / extra input | Source |
| --- | --- | --- |
| `FLT357CrossInvariantAudit.unitPowerClass_independent` | Integrally closed commutative domain; `n≠0`, same nonzero normalized element, two unit-times-`n`th-power extractions | [Prior audit](../FLT357-CrossInvariant-Ultra-261004-v0/checks/UnitPowerClassAudit.lean) |
| `FLT357CrossInvariantAudit.fixedRamifier_unitPowerClass_independent` | Same assumptions plus fixed nonzero source and ramifier | [Prior audit](../FLT357-CrossInvariant-Ultra-261004-v0/checks/UnitPowerClassAudit.lean) |
| `DkMath.Lib.NumberTheory.exists_unit_mul_pow_of_span_eq_pow_of_isPrincipal` | Domain; ideal root is principal and `(a)=I^p`; concludes `a=u*gamma^p` with unit retained | [PrincipalIdealPower](../../../DkMath/Lib/NumberTheory/PrincipalIdealPower.lean) |
| `DkMath.Lib.NumberTheory.exists_unit_mul_pow_of_span_eq_pow_of_classGroupPTorsionFreeAt` | Dedekind domain; nonzero ideal root, class-group torsion hypothesis, ideal-power equality | [PrincipalIdealPower](../../../DkMath/Lib/NumberTheory/PrincipalIdealPower.lean) |
| `DkMath.Lib.NumberTheory.exists_eq_pow_of_span_eq_pow_of_classGroupPTorsionFreeAt` | Above plus surjectivity of `p`th powers on the actual unit group | [PrincipalIdealPower](../../../DkMath/Lib/NumberTheory/PrincipalIdealPower.lean) |
| `DkMath.Lib.NumberTheory.UnitPowerSectorSystem` | Representative coverage in `Rˣ`; does not assert uniqueness, finiteness, or power surjectivity | [UnitPowerSector](../../../DkMath/Lib/NumberTheory/UnitPowerSector.lean) |
| `DkMath.FLT.Seven.SevenRealCubic.CurrentCarrierPower.currentCarrier_ramified_element_receiver` | Actual current packet; builds ideal seventh power, principal generator, then `A=lambda*u*beta^7` | [CurrentCarrierNormalizedPower](../../../DkMath/FLT/Seven/CurrentCarrierNormalizedPower.lean) |
| `DkMath.FLT.Seven.SevenRealCubic.CurrentCarrierRamification.phaseCarrier_eq_uniformizer_mul_quotient` | Actual current real-cubic roots in the degree-six ring; proof explicitly rewrites `R-zeta^j*L` as `(R-L)+(1-zeta^j)*L` before ramifier extraction | [CurrentCarrierRamifiedObstruction](../../../DkMath/FLT/Seven/CurrentCarrierRamifiedObstruction.lean) |

The audited actual carriers are:

- `DkMath.FLT.Three.EisensteinInt := TraceOneInt (-1)`;
- `DkMath.FLT.Five.GoldenInt`, the quadratic golden coordinate ring;
- `DkMath.FLT.Seven.SevenCyclotomicDegreeSixInt.Ring :=
  QuadraticAlgebra SevenRealCubicInt (-1) (alpha - 1)`.

These rings are used as their actual typed carriers. The prior audit checks
their integrally-closed instances and exponent `3/5/7` specializations.
It was rerun in this workspace; see [validation](evidence/MANIFEST.md#log-2a85498f28567ebe).
No ring or element equality is inferred from matching scalar norms.

The two historical normalization identities are
`FLT357CrossInvariantAudit.three_ramifier_normalization` and
`FLT357CrossInvariantAudit.five_ramifier_normalization` in
[EndpointAudit](../FLT357-CrossInvariant-Ultra-261004-v0/checks/EndpointAudit.lean).
The new production API makes the corresponding general load-weighted
normalization law explicit rather than identifying phase factors with unit
classes.

The actual p=7 coordinate bridge and the fixed-extraction specialization of
the new production unit-class theorem are independently checked in
[SevenCarrierBridge](checks/SevenCarrierBridge.lean), retaining the same
`CurrentCommonPrimeCyclotomicPacket` and original Fermat equation.
