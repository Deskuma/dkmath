# FLT prime-generalization Phase 18 — generic unit-power sectors

## Scope and outcome

This report records the bounded implementation requested by
`instruction-018.md`.  The implementation remains neutral: it does not
assert that every unit is a p-th power, classify arbitrary unit groups, prove
class-group torsion-freeness, or eliminate any concrete FLT sector.

The requested production layers are green:

~~~
PGEN-UNIT-SECTOR-GREEN
PGEN-IDEAL-TO-SECTOR-POWER-GREEN
~~~

## A. Neutral sector API

The production module is:

~~~
DkMath/Lib/NumberTheory/UnitPowerSector.lean
~~~

It defines `UnitPowerSectorSystem R p` with an unconstrained sector type,
unit representatives, and the completeness statement

~~~
∀ u : Rˣ, ∃ s, ∃ e : Rˣ, u = rep s * e ^ p
~~~

The module imports only the neutral Phase-16 principal-ideal bridge and has
no `DkMath.FLT.*` import.

## B. Generic normalization

The main normalization theorem is:

~~~
exists_sector_mul_pow_of_unit_mul_pow
~~~

It absorbs the unit `e` into the displayed factor using
`(e * gamma)^p = e^p * gamma^p`.  An associated-element wrapper is also
provided as `exists_sector_mul_pow_of_associated_pow`.

## C. Phase-16 composition and singleton recovery

The Phase-16 endpoint is composed by:

~~~
exists_sector_mul_pow_of_span_eq_pow_of_classGroupPTorsionFreeAt
~~~

The existing class-group hypothesis still supplies only an element times a
unit p-th power.  The theorem explicitly converts the returned `IsUnit`
carrier into `Rˣ` before applying the sector API.

For the separate hypothesis

~~~
∀ u : Rˣ, ∃ e : Rˣ, u = e ^ p
~~~

`singletonUnitPowerSectorSystem` constructs the singleton representative
`1`, and
`exists_eq_pow_of_span_eq_pow_of_classGroupPTorsionFreeAt_of_unit_pow_surjective`
recovers the exact-power endpoint.  No surjectivity assumption is built into
the base structure.

## D. Specialized compatibility audit

The focused probe is:

~~~
DkMathTest/FLT/Prime/UnitPowerSectorAuditProbe.lean
~~~

The carrier distinctions are explicit:

| exponent | carrier and result |
|---:|---|
| 3 | `EisensteinIntˣ`, adapted from `exists_sector_mul_cube_of_unit`; the existing six-unit proof is not duplicated |
| 5 | `GoldenInt` with predicate `GoldenUnit`; `goldenUnitClassesModFifth` is checked, but no unsupported `GoldenIntˣ` bridge is introduced |
| 7 | `TraceOneInt (-2)ˣ`, adapted to a singleton sector from `exists_seventh_power_eq_of_isUnit` |

Thus the p=5 result is an audit classification, not a fabricated unit-group
adapter.  The remaining bridge obligation is an honest `GoldenUnit` to
`GoldenIntˣ` API, if a later phase requires it.

A pinned Mathlib search for a canonical generic quotient of units by p-th
powers did not reveal a directly reusable API in the searched group/ring
theory areas; the explicit sector-system abstraction is retained.

## E. Axiom and forbidden-construct audit

The audit file is:

~~~
DkMathTest/FLT/Prime/UnitPowerSectorAuditAxiomAudit.lean
~~~

The new public production theorems use only the standard inherited
`propext`, `Classical.choice`, and `Quot.sound` axioms.  The fresh scan of the
new production and test files found no `sorry`, `sorryAx`, `admit`, explicit
`axiom`, or `unsafe` occurrence.

## Verification

The exact focused build requested by `instruction-018.md` passed:

~~~
lake build DkMath.Lib.NumberTheory.PowerFactor \
  DkMath.Lib.NumberTheory.IdealPowerFactor \
  DkMath.Lib.NumberTheory.PrincipalIdealPower \
  DkMath.Lib.NumberTheory.UnitPowerSector \
  DkMathTest.FLT.Prime.UnitPowerSectorAuditProbe \
  DkMathTest.FLT.Prime.UnitPowerSectorAuditAxiomAudit \
  DkMath.FLT.Seven
~~~

`git diff --check` passed.  The fresh warning scan had no warning other than
the pre-existing `ZsigmondyCyclotomicResearch.lean:147` declaration using
`sorry`; excluding that known `sorry` warning left the scan empty.

The stop boundary remains: concrete class-group torsion-freeness, a concrete
sector system for each target order, and elimination of the resulting FLT
sectors are future obligations.
