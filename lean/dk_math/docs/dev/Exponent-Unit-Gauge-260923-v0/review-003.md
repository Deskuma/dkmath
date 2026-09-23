# Review-003 — GAGE-003 ValueGauge / local power residue

Result: APPROVED — Outcome A

## 1. Judgment

GAGE-003 correctly implements the value-side gauge as a semantic facade over the existing StructuralArithmetic prime-coordinate projection.

The design boundary is sound:

~~~text
ExponentGauge
  = Pascal-side observation of the exponent itself

ValueGauge
  = prime-valuation residue vector of a value modulo the exponent period
~~~

No competing valuation or modulo engine was introduced.

## 2. Zero and boundary handling

`ValueGaugePure` explicitly requires a != 0. This correctly prevents the conventional value of padicValNat at zero from being interpreted as ordinary perfect-power factorization data.

The boundary theorems for period 0 and period 1 are also correct:

~~~text
period 0 -> retain raw valuation coordinates
period 1 -> collapse all residue coordinates
~~~

The implementation therefore preserves the intended distinction between an unprojected value spectrum and a trivial period-one observation.

## 3. Conservation law

The central theorem:

~~~text
valueGaugeCoordinates n (a * b^n)
  = valueGaugeCoordinates n a
~~~

is exactly the value-side conservation law required by the campaign. Reusing StructuralArithmetic.projectPrimeCoordinates_mul_pow is the right implementation choice.

## 4. Converse reconstruction

The perfect-power converse was correctly deferred.

Mathlib provides the raw factorization reconstruction ingredients, but exposing:

~~~text
all prime valuations divisible by n
  -> exists b, a = b^n
~~~

would require a genuine factorization reconstruction proof rather than a thin facade. It is not required before the dyadic/midpoint calibration.

## 5. GAGE-004 design freeze

GAGE-004 should introduce a denominator-free midpoint defect as its production core.

Preferred quantity over a commutative ring:

~~~text
M_d(x,u)
  = 2^(d-1) * ((x+u)^d - x^d)
    - d*u*(2*x+u)^(d-1)
~~~

with the natural-number exponent d cast into the carrier.

The first exact calibrations are:

~~~text
M_2(x,u) = 0
M_3(x,u) = u^3
M_4(x,u) = 4*u^3*(2*x+u)
~~~

The d = 2 theorem is the production form of the half-unit midpoint identity. Over a characteristic-zero field it corresponds to:

~~~text
(x+u)^2 - x^2 = 2*u*(x + u/2).
~~~

## 6. Existing assets to reuse

Inspect before coding:

~~~text
DkMath.CosmicFormula.PowerGapBeam
DkMath.CosmicFormula.HalfUnitZeroConjugate
DkMath.Algebra.DiffPow
~~~

`PowerGapBeam` already has the d = 2,3,4 difference-quotient calibrations. `HalfUnitZeroConjugate` already fixes the semantic real half-unit q/2. Do not duplicate those modules merely for naming symmetry.

Proceed to instruction-004.md.
