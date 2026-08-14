# IPSM-028 — Q3-F route audit and radial-comparison frontier

Date: 2026-08-14

Repository: `Deskuma/dkmath`

Branch: `wip/RH-CFBRC-prime-side-sign-mechanism-260813-v0`

Status: Q3 finite radial layer Green / Q3-F four-route audit complete / arithmetic-to-radial comparison OPEN / no sign claim / no RH claim

## 0. Executive result

The finite Q3 layer added after IPSM-027 is structurally Green.

Current theorem surface:

```text
ScalarSurface = pi * normalizedArithmetic.re                  GREEN
pi * FixedRadial <= ScalarSurface iff finite defect <= 0      GREEN
safe-radius FixedRadial >= 0                                  GREEN
independent arithmetic-to-radial comparison                   OPEN
```

The dedicated obstruction remains correctly named:

```lean
inductive PascalCenteredXiPrimeSideQuadraticizationRadialComparisonGap : Prop
  | noIndependentArithmeticToRadialProvider :
      PascalCenteredXiPrimeSideQuadraticizationRadialComparisonGap
```

Q3-F audited the four admissible source-derived routes requested by IPSM-027. No existing theorem currently closes the comparison.

This is an obstruction closeout, not an impossibility result.

## 1. Finite Q3 layer review

The current implementation exposes the exact comparison theorem:

```lean
theorem pascalCenteredXiPrimeSideQuadraticization_radial_le_scalarSurface_iff_defect_nonpos
    {ε : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) :
    Real.pi * pascalCenteredXiFixedRadialSecondMomentFunctional W.R ≤
        pascalCenteredXiMellinQuadraticScalarSurface ε W X ↔
      pascalCenteredXiMellinQuadraticArithmeticDefectApproximant ε W X ≤ 0
```

This is the correct sign gate.

The safe-radius radial nonnegativity theorem is also source-derived:

```lean
theorem pascalCenteredXiFixedRadialSecondMomentFunctional_nonneg
    {R : ℝ} (hR : IsPascalCenteredXiBoundarySafeRadius R) :
    0 ≤ pascalCenteredXiFixedRadialSecondMomentFunctional R
```

Its proof rewrites the fixed radial observable to the CF2D radial mass and then uses pointwise

```text
q2(centered zero state) = normSq(centered zero)
```

with nonnegative multiplicities.

This does not use the fixed zero-side defect sign, horizontal-energy sign, anti-mirror energy, RH equivalence, or a limit argument.

Verdict: Q3 finite radial layer is Green.

## 2. Q3-F Route 1 — same-feature / projection bridge

### Files audited

```text
DkMath/CosmicFormula/Rotation/CF2D/ThreeElementBridge.lean
DkMath/RH/CFBRC/PascalCriticalMirrorRadialContourCF2DBridge.lean
DkMath/RH/CFBRC/PascalCenteredXiPrimeSideQuadraticizationAudit.lean
DkMath/RH/CFBRC/PascalCenteredXiPrimeSideWholeSurfaceEnergyAudit.lean
```

### What exists

The generic CF2D bridge proves exact algebraic facts such as:

```text
squareMass(z.core,z.beam) = q2(z)
q2(star r z) = q2(r) * q2(z)
unit-kernel action preserves q2
CF2D conjugation preserves Core and Gap
CF2D conjugation flips the interaction Beam
```

It also builds `cf2dThreeElementFlow` from arbitrary CF2D states.

The RH radial bridge separately proves:

```text
q2(pascalCenteredZeroCF2DState s) = normSq(s - criticalLineCenter)
```

and hence identifies the finite zero-window CF2D radial mass with the radial second moment.

### What does not exist

There is no current theorem supplying a map from the fixed radial CF2D states into the present Mellin whole-feature space, nor a common feature object with a projection, isometry, contraction, norm comparison, or Pythagorean identity.

In particular, the generic `ThreeElementBridge` deliberately contains no RH, zeta, Mellin, complex-phase, or explicit-formula source data.

Therefore the identities

```text
CF2D q2 >= 0
WholeE+ >= 0
WholeE- >= 0
```

remain positivity facts about disconnected objects.

### Route 1 verdict

```text
same-feature / projection bridge     NOT FOUND
status                               OPEN FRONTIER
```

Do not manufacture a map `J` whose definition already encodes the desired inequality.

## 3. Q3-F Route 2 — fixed outer-count layer-cake bridge

### Files audited

```text
DkMath/RH/CFBRC/PascalCenteredXiRadialLayerCakeOuterCountBridge.lean
DkMath/RH/CFBRC/PascalCenteredXiFixedSecondMomentDefectBridge.lean
DkMath/RH/CFBRC/PascalCenteredXiArithmeticDefectRepresentation.lean
```

### What exists

The radial layer is exact and strong.

For a boundary-safe radius, the repository proves the chain

```text
FixedRadialSecondMomentFunctional
= zero-window radial second moment
= CF2D q2 radial mass
= R^2 * OuterCount(R) - integral_0^R 2r * OuterCount(r) dr.
```

The layer-cake module proves the finite layer count, its nonnegativity and monotonicity, the almost-everywhere replacement by the fixed Xi outer count, and the final fixed outer-count representation.

### What does not exist

The audited source contains no finite-`X` theorem connecting

```text
R^2 * OuterCount(R) - integral_0^R 2r * OuterCount(r) dr
```

to a lower bound for

```text
normalizedArithmeticApproximant(ε,W,X).re
```

or equivalently to `ScalarSurface(ε,W,X)`.

The outer count is obtained from fixed Xi outer contour data. The finite arithmetic side is the finite von Mangoldt/archimedean/elementary/top-horizontal surface. Their common relation is currently available only through the already-established ordered analytic limit machinery, not as a finite radial domination theorem.

A rewrite of `OuterCount` back to zero data followed by zero geometry would not be an independent prime-side comparison.

### Route 2 verdict

```text
fixed radial outer-count representation       GREEN
finite-X arithmetic-to-outer-count bound      NOT FOUND
status                                         OPEN FRONTIER
```

## 4. Q3-F Route 3 — exact source-derived completion square

### Files audited

```text
DkMath/RH/CFBRC/PascalCenteredXiPrimeSideWholeSurfaceEnergyAudit.lean
DkMath/RH/CFBRC/PascalCenteredXiPrimeSideQuadraticizationAudit.lean
```

### What exists

The whole source is reconstructed exactly. The current surface layer provides:

```text
ComplexWholeSurface.re = ScalarSurface
ScalarExcess = ComplexWholeSurface.re - pi * FixedRadial
```

The Q2 layer further provides source-derived real whole features and shifted energies:

```text
WholeE+ >= 0
WholeE- >= 0
4 * ScalarSurface = WholeE+ - WholeE-
WholeE- <= WholeE+ iff 0 <= ScalarSurface.
```

### What does not exist

The whole-surface audit explicitly ends at the obstruction boundary: source reconstruction plus radial subtraction does not itself yield a square, Gram form, or nonnegativity theorem for the finite scalar excess.

No source theorem currently has one of the required forms

```text
ScalarSurface - pi * FixedRadial = normSq(source-derived feature)
```

or

```text
ScalarSurface = pi * FixedRadial + nonnegative source-derived remainder.
```

The Q2 shifted-energy polarization is not such a theorem. It represents `ScalarSurface` as a difference of two nonnegative energies and does not insert or control the radial term.

### Route 3 verdict

```text
source-derived completion square     NOT FOUND
status                               OPEN FRONTIER
```

Do not define a synthetic radial shifted energy or remainder whose nonnegativity is merely the target inequality in disguise.

## 5. Q3-F Route 4 — independent finite arithmetic inequality

### File audited

```text
DkMath/RH/CFBRC/PascalCenteredXiPrimeSideSignAudit.lean
```

### What exists

The sign audit supplies only forward order-closedness adapters.

At fixed positive `ε`:

```text
eventually_X finiteDefect(ε,W,X) <= 0
    -> endpointDefect(ε,W) <= 0.
```

Then:

```text
eventually_{ε -> 0+} endpointDefect(ε,W) <= 0
    -> FixedSecondMomentDefect(W.R) <= 0.
```

These theorems preserve a sign supplied by an external provider. They do not prove the hypothesis.

### What does not exist

No audited theorem independently proves either

```text
finiteDefect(ε,W,X) <= 0
```

for all required finite parameters, or

```text
eventually_X finiteDefect(ε,W,X) <= 0
```

for fixed positive `ε`.

### Route 4 verdict

```text
ordered sign transport                 GREEN
independent finite/eventual inequality NOT FOUND
status                                 OPEN FRONTIER
```

No reasoning may run backward from the sign of the ordered limit to finite approximants.

## 6. Four-route audit table

```text
Route 1  same-feature / projection bridge         NOT FOUND
Route 2  finite-X outer-count arithmetic bridge   NOT FOUND
Route 3  source-derived completion square         NOT FOUND
Route 4  independent finite/eventual inequality   NOT FOUND
```

Therefore the existing named gap is still exact:

```text
PascalCenteredXiPrimeSideQuadraticizationRadialComparisonGap
```

No additional provider structure should be introduced merely to restate this gap as a hypothesis.

## 7. Why this is now the genuine mathematical frontier

The repository has separately closed the following layers:

```text
finite arithmetic source decomposition          GREEN
Mellin box integral exchange                     GREEN
source-derived adjoint / mirror conjugation      GREEN
aggregate reality                                GREEN
autocorrelation Gram positivity                  GREEN
whole real feature reconstruction                GREEN
whole shifted PSD energies                       GREEN
whole polarization identity                      GREEN
safe-radius radial source representation         GREEN
CF2D q2 radial representation                    GREEN
fixed Xi outer-count radial layer cake           GREEN
ordered limit transport                          GREEN
```

The missing statement is not another positivity lemma. It is an order relation between two already nonnegative/structured but currently disconnected observables.

The exact finite target is:

```text
pi * FixedRadialSecondMomentFunctional(W.R)
  <= ScalarSurface(ε,W,X).
```

Equivalently:

```text
ArithmeticDefectApproximant(ε,W,X) <= 0.
```

That equivalence prevents the gap from being hidden by notation.

## 8. Zero-side and ordered-limit firewall remains mandatory

The independent zero-side theorem gives, on a safe radius:

```text
FixedSecondMomentDefectFunctional(R)
= 2 * zero-window horizontal energy
>= 0.
```

Vanishing on all safe radii is already equivalent to `RiemannHypothesis`.

Therefore none of the following may be used to prove the finite Q3 target:

```text
fixed-defect nonnegativity
fixed-defect = 2 * horizontal energy
anti-mirror-energy nonnegativity
RH or the all-safe-radius defect-vanishing equivalence
sign of the ordered limit
```

The permitted logical direction remains:

```text
independent finite/eventual prime-side defect <= 0
-> ordered-limit fixed defect <= 0

independent zero-side geometry
-> fixed defect >= 0

therefore fixed defect = 0.
```

The second line may be combined with the first only after the first has been independently established.

## 9. Q3 closeout classification

By the IPSM-027 criterion, Q3 closes under **Green-B: obstruction closeout**.

This means:

```text
Q3 finite equivalence / radial representation     GREEN
Q3-F source-route audit                           GREEN
arithmetic-to-radial comparison theorem           OPEN
finite defect nonpositivity                       OPEN
fixed defect vanishing                            NOT PROVED BY PRIME SIDE
RH                                                NOT CLAIMED
```

`Green-B` is an audit status, not a proof of the missing inequality.

The `RadialComparisonGap` must remain in code.

## 10. Admissible breakthrough theorem shapes

Future work should begin only when there is mathematical content capable of producing one of the following source-derived statements.

### A. Common-feature contraction / projection

```text
radial source -> same feature space as whole arithmetic source
```

with a proved norm relation implying the comparison.

### B. Finite arithmetic outer-count domination

A direct finite explicit-formula/counting estimate controlling the fixed Xi radial layer cake from the finite arithmetic surface.

### C. Exact source-derived positive remainder

```text
ScalarSurface
= pi * FixedRadial + PositiveRemainder
```

where `PositiveRemainder` is proved nonnegative from an independently defined existing source object.

### D. Direct finite/eventual defect theorem

```text
ArithmeticDefectApproximant(ε,W,X) <= 0
```

or the exact eventual form needed by the existing sign transport, proved without any zero-side frontier theorem.

Anything weaker than these is only repackaging the current gap.

## 11. Recommended next checkpoint

Do not immediately add a hypothesis/provider wrapper.

The next research checkpoint should isolate **which source variable could simultaneously encode the radial `q2` observable and the whole Mellin feature**.

A useful investigation should compare the actual source objects, not their final scalar values:

```text
CF2D centered-zero state:
  (Re(s)-1/2, Im(s))

whole Mellin source feature:
  finite right-edge coefficient/amplitude + top-horizontal contribution

fixed Xi outer-count source:
  normalized fixed outer contour count
```

The first acceptable next theorem is a genuine bridge between such source objects. If no such bridge can be constructed, the current `RadialComparisonGap` is the correct stopping point.

## 12. Acceptance checklist

```text
[x] Q3 finite scalar/radial equivalence reviewed
[x] safe-radius radial nonnegativity reviewed
[x] Route 1 generic CF2D bridge audited
[x] Route 2 fixed outer-count layer-cake audited
[x] Route 3 whole-source completion-square route audited
[x] Route 4 finite arithmetic inequality route audited
[x] no zero-side sign used backward
[x] no limit sign used backward
[x] no synthetic completion square
[x] no radial term inserted into WholeE+ / WholeE-
[x] no generic ThreeElement theorem misread as an RH source bridge
[x] no limit exchange
[x] RadialComparisonGap retained
[x] no RH claim
```