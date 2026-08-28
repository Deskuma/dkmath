# IPSM-027 — Q2-K closeout and Q3 radial-comparison audit

Date: 2026-08-14

Repository: `Deskuma/dkmath`

Branch: `wip/RH-CFBRC-prime-side-sign-mechanism-260813-v0`

Status: Q2-K Green / Q3 radial comparison audit / no sign claim / no RH claim

## 0. Q2-K closeout

The current `PascalCenteredXiPrimeSideQuadraticizationAudit.lean` implementation is Green through the whole finite shifted-energy layer.

Current finite whole-feature classification:

```text
WholeBoxFeature pointwise real                         GREEN
WholeBoxFeature finite-box continuous / integrable    GREEN
ComplexWholeSurface = normalized whole-feature avg    GREEN
ComplexWholeSurface = ScalarSurface : ℂ               GREEN
WholeE+ >= 0                                           GREEN
WholeE- >= 0                                           GREEN
4 * ScalarSurface = WholeE+ - WholeE-                 GREEN
WholeE- <= WholeE+ iff 0 <= ScalarSurface             GREEN
independent whole ordering provider                    OPEN
```

The dedicated whole-ordering gap is correct. PSD of the two beams does not order them.

Q2 is therefore closed as an exact source-derived quadraticization/reality result, not as a sign result.

## 1. Q3 is a different comparison problem

The scalar excess is not the scalar surface:

```lean
pascalCenteredXiMellinQuadraticScalarExcess ε W X =
  pascalCenteredXiMellinQuadraticScalarSurface ε W X -
    Real.pi * pascalCenteredXiFixedRadialSecondMomentFunctional W.R
```

The existing exact identity is:

```lean
pascalCenteredXiMellinQuadraticScalarExcess ε W X =
  -Real.pi *
    pascalCenteredXiMellinQuadraticArithmeticDefectApproximant ε W X
```

Thus Q3 is the comparison

```text
π * FixedRadialSecondMomentFunctional(W.R) <= ScalarSurface(ε,W,X)
```

which is equivalent to

```text
ArithmeticDefectApproximant(ε,W,X) <= 0.
```

Do not replace this by `0 <= ScalarSurface`; Q2-K already showed that is only the whole shifted-energy ordering problem.

## 2. Q3-A — expose the exact comparison equivalence

Add a theorem that makes the new gate explicit:

```lean
theorem pascalCenteredXiPrimeSideQuadraticization_radial_le_scalarSurface_iff_defect_nonpos
    {ε : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) :
    Real.pi * pascalCenteredXiFixedRadialSecondMomentFunctional W.R <=
        pascalCenteredXiMellinQuadraticScalarSurface ε W X ↔
      pascalCenteredXiMellinQuadraticArithmeticDefectApproximant ε W X <= 0 := by
  ...
```

Preferred proof: use `pascalCenteredXiMellinQuadraticScalarExcess_eq_neg_pi_mul_defect` and `Real.pi_pos`; do not unfold the entire explicit formula.

Also useful, if not already public in convenient direction:

```lean
theorem pascalCenteredXiPrimeSideQuadraticization_scalarSurface_eq_pi_mul_normalizedArithmetic_re
    {ε : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) :
    pascalCenteredXiMellinQuadraticScalarSurface ε W X =
      Real.pi *
        (pascalCenteredXiMellinQuadraticNormalizedArithmeticApproximant ε W X).re := by
  ...
```

This is only an adapter around the existing normalized-arithmetic/scalar-surface identity.

## 3. Q3-B — radial provenance audit

The fixed radial observable is source-derived independently of the arithmetic feature.

On a boundary-safe radius:

```text
FixedRadialSecondMomentFunctional
= zero-window radial second moment
= CF2D q2 radial mass.
```

The CF2D bridge is pointwise:

```text
q2(centered zero state) = normSq(s - 1/2).
```

The mirror-frozen local-contour representation is also exact, but it is a sum of independent zero-local contours; it is not the same fixed outer arithmetic contour and it is not a whole-box feature identity.

Add, if absent, the safe-radius nonnegativity theorem:

```lean
theorem pascalCenteredXiFixedRadialSecondMomentFunctional_nonneg
    {R : ℝ} (hR : IsPascalCenteredXiBoundarySafeRadius R) :
    0 <= pascalCenteredXiFixedRadialSecondMomentFunctional R := by
  ...
```

Prove it from the zero-window radial-moment / CF2D-q2 representation and termwise nonnegativity.

Immediately document that this theorem is insufficient for Q3:

```text
0 <= radial
and
0 <= ScalarSurface

does NOT imply

π * radial <= ScalarSurface.
```

## 4. Q3-C — zero-side firewall

The fixed defect has the independent zero-side representation

```text
FixedSecondMomentDefectFunctional(R)
= 2 * zero-window horizontal energy
>= 0.
```

Moreover, vanishing on all boundary-safe radii is already proved equivalent to `RiemannHypothesis`.

Therefore the following are forbidden as sources of the finite Q3 inequality:

```text
FixedSecondMomentDefectFunctional_nonneg
FixedSecondMomentDefectFunctional_eq_two_mul_horizontalEnergy
anti-mirror-energy nonnegativity
fixed-defect vanishing / RH equivalence
zero-window horizontal-energy vanishing
```

Using any of these to derive

```text
ArithmeticDefectApproximant(ε,W,X) <= 0
```

would feed the zero-side RH frontier backward into the prime-side finite sign mechanism.

The permitted use of the zero-side sign is only after an independent prime-side finite/eventual nonpositivity provider has been established and transported through the ordered limits.

## 5. Q3-D — ordered-limit direction firewall

The established representation is strictly ordered:

```text
fixed ε > 0:
  X -> infinity

then:
  ε -> 0+
```

The endpoint limit is the fixed Xi defect.

Do not reason backward from the sign of the limit to the sign of finite approximants.

In particular:

```text
FixedDefect >= 0
```

does not supply

```text
finite ArithmeticDefectApproximant <= 0.
```

If the finite nonpositivity is independently obtained, then the existing order-closedness adapters transport it forward and force the fixed defect to be nonpositive. Combined only then with the zero-side fixed-defect nonnegativity, equality follows.

## 6. Q3-E — current cross-geometry audit result

Current repository source provides both sides separately:

```text
Arithmetic side:
  whole finite real box feature
  normalized arithmetic surface
  whole shifted PSD beams

Radial side:
  fixed Xi outer-count layer cake
  zero-window radial second moment
  CF2D q2 radial mass
  mirror-frozen local contour mass
```

What is not currently present is a theorem coupling the two sides by an order-preserving map, norm identity, projection, or completed-square identity.

A search for a Mellin/whole-feature to CF2D-radial coupling found no existing theorem.

Record the precise obstruction:

```lean
inductive PascalCenteredXiPrimeSideQuadraticizationRadialComparisonGap : Prop
  | noIndependentArithmeticToRadialProvider :
      PascalCenteredXiPrimeSideQuadraticizationRadialComparisonGap
```

This gap is not a proof of impossibility. It records that the existing PSD and radial nonnegativity structures are presently disconnected.

## 7. Q3-F — admissible research routes

Before introducing any provider, audit these source-derived possibilities in order.

### Route 1 — same-feature / projection bridge

Search for an exact map placing the CF2D radial `q2` mass and the whole Mellin box feature in one common normed object.

Required theorem shape would be something structurally like:

```text
radial reference object --J--> whole feature space
```

with an independently proved norm/projection relation strong enough to imply the desired comparison.

Do not define `J` merely so that the inequality becomes true.

The generic `DkMath.CosmicFormula.ThreeElement` / CF2D library may be relevant only if an actual source bridge to the present Xi/Mellin objects can be proved. RH-specific facts must not be imported into the generic core.

### Route 2 — outer-count layer-cake bridge

The radial observable already has the exact fixed-Xi representation

```text
R^2 * OuterCount(R) - integral_0^R 2r * OuterCount(r) dr.
```

Audit whether the prime-side finite arithmetic surface has an independent lower-bound or counting representation controlling these outer counts.

A useful bridge would have to be genuinely prime/arithmetic-derived. Rewriting `OuterCount` through its zero finset and then using zero geometry is not an independent prime-side comparison.

### Route 3 — exact completion-square identity

Audit whether source algebra produces an identity of the form

```text
ScalarSurface - π * RadialMass = norm-square term
```

or a sum/integral of such terms.

This is acceptable only if the radial term and the cross term arise from existing source objects and exact theorems.

Do not manufacture a radial shifted energy by definition and then call it a completion square.

### Route 4 — independent finite arithmetic inequality

A direct theorem proving

```text
ArithmeticDefectApproximant(ε,W,X) <= 0
```

for the required finite/eventual regime is also acceptable, provided its proof uses only prime/arithmetic source structure and not the zero-side defect sign/RH frontier.

If this route is found, use the existing ordered-limit adapters rather than re-proving limit transport.

## 8. Q3-G — important sign geometry

The signs intentionally oppose each other across the final bridge:

```text
finite prime-side target:
  ArithmeticDefectApproximant <= 0

ordered limit:
  FixedSecondMomentDefectFunctional <= 0

independent zero-side geometry:
  FixedSecondMomentDefectFunctional >= 0
```

Hence a genuine independent finite prime-side nonpositivity mechanism would force

```text
FixedSecondMomentDefectFunctional = 0.
```

That is why Q3 is the first genuinely RH-critical cross-geometry gate after the successful vertical/horizontal quadraticization.

Do not weaken this tension by changing signs or redefining the defect.

## 9. Acceptance checklist

```text
[ ] Q2-K whole shifted-energy results remain unchanged
[ ] radial <= ScalarSurface iff finite defect <= 0 is explicit
[ ] safe-radius radial nonnegativity is source-derived
[ ] radial nonnegativity is not mistaken for radial comparison
[ ] fixed zero-side defect nonnegativity is not used to prove finite sign
[ ] no reasoning backward from ordered-limit endpoint sign
[ ] no anti-mirror-energy argument on the prime-side finite inequality
[ ] CF2D q2 is treated as a radial representation, not automatically a comparison theorem
[ ] outer-count layer cake is treated as a radial representation, not automatically a prime bound
[ ] no synthetic completion square
[ ] named RadialComparisonGap remains unless a genuine coupling theorem is found
[ ] top-horizontal contribution remains inside ScalarSurface
[ ] no radial term is inserted into WholeE+ / WholeE-
[ ] no limit exchange
[ ] no RH claim
```

## 10. Q3 closeout criterion

Q3 is Green only if one of the following happens.

### Green-A — genuine comparison provider

A source-derived theorem establishes the required radial/arithmetic comparison, or establishes finite/eventual defect nonpositivity, without using the zero-side RH frontier.

Then connect it to the existing ordered-limit sign adapters.

### Green-B — obstruction closeout

No independent coupling theorem is found after the four routes above are audited.

Then keep `PascalCenteredXiPrimeSideQuadraticizationRadialComparisonGap` as the exact named frontier and report:

```text
whole source quadraticization                 GREEN
whole shifted PSD beams                       GREEN
whole ordering iff ScalarSurface >= 0         GREEN
radial source representation                  GREEN
radial nonnegativity                          GREEN
arithmetic-to-radial comparison               OPEN
finite defect nonpositivity                   OPEN
RH                                             NOT CLAIMED
```

This is a valid Q3 audit closeout. It isolates the remaining mathematical content instead of hiding it behind a provider.