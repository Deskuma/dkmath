# GAGE-005 — FLT2 gauge calibration

Branch: `research/Exponent-Unit-Gauge-260923-v0`

Checkpoint: GAGE-005

Result: **Outcome A — implemented**

## 1. Outcome

The exponent-2 arithmetic calibration is implemented in a FLT-specific owner.
For every positive primitive natural square solution, the two legs can be
oriented so that `x` is even and `y` is odd. In that orientation, the
PowerGapBeam factors of `z^2 - y^2` have exact common gauge `2`; after dividing
both factors by `2`, they are coprime and their product is the square
`(x / 2)^2`. `power_factor_split` then produces two square carriers.

This is a square-landing calibration, not an impossibility theorem. No
general FLT statement and no final Pythagorean-triple classification theorem
were used.

## 2. Production owner and public API

Production owner:

```text
DkMath/FLT/Two/GaugeCalibration.lean
```

Namespace: `DkMath.FLT.Two`

Public declarations:

```text
PrimitiveSquareSolution
PrimitiveSquareLandingGaugeSplit

primitiveSquareSolution_parity
primitiveSquareSolution_z_odd
primitiveSquareSolution_gap_beam_gcd_eq_two
primitiveSquareSolution_gap_beam_sq
primitiveSquareSolution_gauge_split
primitiveSquareSolution_oriented_gauge_split
```

The module is not imported from `DkMath.NumberTheory.Gauge`. No unnecessary
`DkMath/FLT/Two.lean` facade was created.

`PrimitiveSquareSolution` stores only positive `x`, `y`, `z`, the square
equation, and `Nat.Coprime x y`. The principal result is the Prop-valued
existential packet `PrimitiveSquareLandingGaugeSplit`, containing the stripped
carriers `A`, `B`, normalized body `X`, and square roots `r`, `s`.

## 3. Primitive parity and orientation

`primitiveSquareSolution_parity` proves:

```text
(Even x ∧ Odd y) ∨ (Odd x ∧ Even y)
```

The proof excludes the even-even case using primitive coprimality and excludes
the odd-odd case by reducing odd squares modulo `4`; it does not invoke
Mathlib's final classification theorem.

`primitiveSquareSolution_z_odd` proves `Odd z` in the oriented case from the
even square plus odd square parity. The symmetric public theorem
`primitiveSquareSolution_oriented_gauge_split` swaps the legs when the other
orientation is observed.

## 4. Gap/Beam square body

For the oriented positive data, natural arithmetic first establishes:

```text
x^2 = (z-y) * (z+y)
```

The public theorem `primitiveSquareSolution_gap_beam_sq` exposes the same
identity through the existing integer PowerGapBeam vocabulary:

```text
(x : ℤ)^2
  = powerGap (y : ℤ) (z : ℤ) * powerBeam 2 (y : ℤ) (z : ℤ)
```

It reuses `powerGap_eq_sub`, `powerBeam_two`, and
`gcd_powerGap_powerBeam_dvd_d_of_coprime_int`; no second difference-of-powers
factorization was added.

## 5. Exact shared gauge 2

`primitiveSquareSolution_gap_beam_gcd_eq_two` proves:

```text
Nat.gcd (z-y) (z+y) = 2
```

The upper bound reuses the existing PowerGapBeam gcd theorem with degree `2`,
after deriving `Coprime y z` arithmetically from the primitive equation and
`Coprime x y`. The lower bound proves both factors are even from `y` and `z`
being odd. Thus the existing “common divisor divides degree” boundary is
sharpened to the exact shared gauge required by GAGE-005.

## 6. Gauge stripping and square-factor split

The oriented proof names:

```text
A := (z-y)/2
B := (z+y)/2
X := x/2
```

and proves the exact multiplication equalities, rather than relying on
truncating division:

```text
z-y = 2*A
z+y = 2*B
x   = 2*X
```

Using the exact gcd result and
`Nat.gcd_mul_left`, it proves `Nat.Coprime A B`. The square body is then
normalized by cancelling the common factor `4`:

```text
X^2 = A*B
```

Finally, the proof applies
`DkMath.Lib.NumberTheory.power_factor_split` with `d := 2` to obtain:

```text
A = r^2
B = s^2
```

and exposes the endpoint equations:

```text
z-y = 2*r^2
z+y = 2*s^2
```

This is the principal `primitiveSquareSolution_gauge_split` packet.

## 7. Reconstruction boundary

The minimum required landing calibration is complete. The further standard
forms

```text
x = 2*r*s
y = s^2-r^2
z = s^2+r^2
```

were not added: extracting `X = r*s` is straightforward, but a complete
natural-subtraction/order reconstruction would add bookkeeping beyond the
required gauge-split result. No geometric parametrization theorem is claimed.

## 8. GAGE-004 relationship

The two checkpoints are deliberately distinct:

```text
GAGE-004: exponent 2 has zero midpoint correction.
GAGE-005: a primitive square landing has exact shared gauge 2, and
           removing it yields a coprime product of squares.
```

The midpoint-closure theorem alone is not used as a proof of the FLT2 gauge
split.

## 9. Concrete calibrations and classification comparison

`DkMathTest.FLT.Two.GaugeCalibration` checks both requested examples:

```text
(x,y,z) = (4,3,5):
  Gap = 2, Beam = 8, A = 1, B = 4, X = 2.

(x,y,z) = (12,5,13):
  Gap = 8, Beam = 18, A = 4, B = 9, X = 6.
```

It also checks the integer PowerGapBeam square-body bridges and the swapped
orientation using `(3,4,5)`.

Mathlib's Pythagorean-triple classification was not imported or used as a
production proof or test comparator.

## 10. Files changed

```text
DkMath/FLT/Two/GaugeCalibration.lean
DkMathTest/FLT/Two/GaugeCalibration.lean
DkMathTest/FLT/Two/GaugeCalibrationAxiomAudit.lean
docs/dev/Exponent-Unit-Gauge-260923-v0/report-005.md
```

No Mathlib-derived classification code and no GAGE-004 production file were
modified.

## 11. Builds and audits

Final focused builds succeeded:

```text
lake build DkMath.FLT.Two.GaugeCalibration                         -- 8953 jobs
lake build DkMathTest.FLT.Two.GaugeCalibration                     -- 8955 jobs
lake build DkMathTest.FLT.Two.GaugeCalibrationAxiomAudit           -- 8955 jobs
```

The final full build succeeded:

```text
lake build DkMath                                                -- 10275 jobs
```

The axiom audit covers all six substantive public theorems. Each reports only
the existing kernel/library dependencies (`propext`, `Classical.choice`, and
`Quot.sound` where applicable); no `sorryAx` occurs.

The build retains only pre-existing warnings from
`CosmicFormula/HalfUnitZeroConjugate.lean` and unrelated repository sources.

## 12. Forbidden-token and diff checks

The changed production and test Lean files were scanned for `sorry`, `admit`,
`sorryAx`, declared `axiom`, and `unsafe`; none were found. No trigonometric,
Euclidean-geometric, cyclotomic, AdditiveLanding, or general-FLT proof code
was added.

`git diff --check` and `git diff --no-index --check` were run for the changed
tracked and new files; no whitespace errors were reported.

## 13. Next boundary

GAGE-005 is complete. GAGE-006 may proceed unchanged from the separate FLT2
owner and the existing exponent/value gauge APIs. Do not import the FLT2
calibration back into `DkMath.NumberTheory.Gauge`.

Stop after GAGE-005.
