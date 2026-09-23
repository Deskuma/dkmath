# Review-004 — GAGE-004 dyadic midpoint gauge

Result: APPROVED — Outcome A

## 1. Judgment

GAGE-004 introduces the first genuinely new production quantity in the campaign and keeps the implementation appropriately small.

The division-free definition:

~~~text
scaledMidpointDefect d x u
  = 2^(d-1) * ((x+u)^d - x^d)
    - d*u*(2*x+u)^(d-1)
~~~

is the correct production core for the midpoint-correction idea because it avoids introducing division by 2 into the generic ring-level API.

## 2. Calibration quality

The exact low-degree theorems are correct and sufficient for v0:

~~~text
M_2(x,u) = 0
M_3(x,u) = u^3
M_4(x,u) = 4*u^3*(2*x+u)
~~~

The implementation does not overclaim generic positivity or uniqueness.

The d=2 identity is correctly interpreted as exact midpoint closure, not as an FLT2 theorem.

## 3. Half-unit bridge

The characteristic-zero field theorem:

~~~text
(x+u)^2 - x^2 = 2*u*(x+u/2)
~~~

and the real bridge to the existing HalfUnitZeroConjugate.halfUnit are both clean. No competing half-unit implementation was introduced.

## 4. PowerGapBeam bridge

The endpoint specializations:

~~~text
powerGap x (x+u) = u
powerBeam 2 x (x+u) = 2*x+u
~~~

and the resulting square-difference factorization correctly connect GAGE-004 to the existing PowerGapBeam machinery that GAGE-005 will consume.

## 5. Deferred generic work

The generic odd-correction expansion and positivity/uniqueness theorems were correctly deferred.

They are not required to calibrate the exponent-2 landing mechanism. Their absence does not block GAGE-005.

## 6. GAGE-005 design freeze

GAGE-005 should be FLT-specific and must not be imported back into DkMath.NumberTheory.Gauge.

Preferred owner:

~~~text
DkMath/FLT/Two/GaugeCalibration.lean
~~~

The dependency direction should be:

~~~text
Gauge.Dyadic
PowerGapBeam
PowerGapBeamGcd
PowerFactor
    |
    v
FLT.Two.GaugeCalibration
~~~

not the reverse.

The production proof should expose the arithmetic gauge mechanism directly rather than shortcut through Mathlib's final Pythagorean-triple classification.

Proceed to instruction-005.md.