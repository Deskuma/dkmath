# IPSM-023 — Q1 closeout and Q2 horizontal box-feature roadmap

Date: 2026-08-14

Repository: `Deskuma/dkmath`

Branch: `wip/RH-CFBRC-prime-side-sign-mechanism-260813-v0`

Status: Q1 closed / Q2 top-horizontal quadraticization audit / no sign claim / no RH claim

## 0. Review result

The IPSM-022 implementation is Green.

The current module now proves, from the finite source itself:

- `AggregatedBoxFeature` is continuous on every finite box interval;
- shifted `+1` and `-1` norm-square functions are unconditionally `IntervalIntegrable`;
- both shifted energies are nonnegative;
- the unconditional polarization identity holds;
- the unconditional ordering equivalence holds.

Current classification:

```text
E+ nonnegative                         GREEN
E- nonnegative                         GREEN
4 * vertical surface = E+ - E-        GREEN
E- <= E+ iff Re(vertical) >= 0         GREEN
independent source ordering            OPEN
```

`PascalCenteredXiPrimeSideQuadraticizationShiftedEnergyOrderingGap` remains a correct audit boundary. The two PSD beams do not order themselves; their ordering is exactly the vertical sign problem.

Q1 is therefore closed as an obstruction/audit result rather than as a sign theorem.

## 1. Q2 principle

Do not quadraticize only the scalar `HorizontalBase.im` by an abstract scalar identity. That would lose the source geometry.

Instead transport the actual fixed-Xi top-horizontal source into the same Mellin box parameter used by the vertical feature.

Use distinct variables:

```text
x : horizontal contour coordinate
v : Mellin box coordinate
```

Intended chain:

```text
top horizontal fixed-Xi source
-> horizontal BoxFeature(x,v)
-> horizontal aggregate in x
-> deoriented horizontal aggregate in v
-> v-reflection Hermitian symmetry
-> real symmetrized horizontal feature
-> combine with the already-real vertical aggregate
-> whole finite feature
```

No radial term is included in Q2.

## 2. Q2-A — top node and fixed-Xi amplitude

```lean
noncomputable def pascalCenteredXiPrimeSideQuadraticizationTopNode
    (W : PascalCenteredXiResidueTransportWindow) (x : ℝ) : ℂ :=
  pascalOrdinaryToCentered
    (pascalSymmetricRectangleTopEdge x W.rectangle.T)
```

```lean
noncomputable def pascalCenteredXiPrimeSideQuadraticizationTopAmplitude
    (W : PascalCenteredXiResidueTransportWindow) (x : ℝ) : ℂ :=
  pascalCenteredXiNegLogDeriv
    (pascalCenteredXiPrimeSideQuadraticizationTopNode W x)
```

This amplitude is not the right-edge decomposed finite-PHZ amplitude. Keep the distinction explicit.

The top horizontal source is a fixed-Xi observable and carries no finite prime cutoff `X`.

## 3. Q2-B — top amplitude interval integrability

Obtain interval integrability of `TopAmplitude W` from the existing fixed-Xi rectangle boundary integrability theorem, preferably by applying

```lean
pascalCenteredXiRectangleBoundaryIntegrable_weightedNegLogDeriv
```

with constant weight `fun _ => 1` and projecting the top-edge component.

Do not decompose the top edge into ordinary zeta / Gamma / elementary terms. The top edge crosses the critical strip, and Q2 should remain on the fixed-Xi source surface.

Acceptance condition:

```text
TopAmplitude W is IntervalIntegrable on the finite horizontal edge
without T -> infinity and without prime-side decomposition.
```

## 4. Q2-C — horizontal box kernel and BoxFeature

```lean
noncomputable def pascalCenteredXiPrimeSideQuadraticizationTopBoxKernel
    (W : PascalCenteredXiResidueTransportWindow) (x v : ℝ) : ℂ :=
  (pascalCenteredXiPrimeSideQuadraticizationTopNode W x) ^ 2 *
    Complex.exp
      ((v : ℂ) * pascalCenteredXiPrimeSideQuadraticizationTopNode W x)
```

```lean
noncomputable def pascalCenteredXiPrimeSideQuadraticizationTopBoxFeature
    (W : PascalCenteredXiResidueTransportWindow) (x v : ℝ) : ℂ :=
  pascalCenteredXiPrimeSideQuadraticizationTopBoxKernel W x v *
    pascalCenteredXiPrimeSideQuadraticizationTopAmplitude W x
```

Prove joint continuity only for `TopBoxKernel`.

Then repeat the P2 finite-rectangle strategy:

```text
TopAmplitude x-integrable
+ compact continuous TopBoxKernel
-> TopBoxFeature IntegrableOn on horizontal-x × Mellin-v rectangle
-> intervalIntegral_intervalIntegral_swap
```

## 5. Q2-D — exact top source / box-average bridge

```lean
noncomputable def pascalCenteredXiPrimeSideQuadraticizationTopAggregatedBoxFeature
    (W : PascalCenteredXiResidueTransportWindow) (v : ℝ) : ℂ :=
  ∫ x in W.rectangle.σ..(1 - W.rectangle.σ),
    pascalCenteredXiPrimeSideQuadraticizationTopBoxFeature W x v
```

For `0 < ε`, prove the exact finite identity:

```text
TopHorizontalContribution(weight ε, W)
= normalized v-average of TopAggregatedBoxFeature W.
```

Use the existing adapter

```lean
pascalCenteredXiMellinQuadraticWeight_eq_generic
```

and the same logarithmic-box identity already used by P2.

No `T -> infinity`, `ε -> 0`, or limit exchange is allowed.

## 6. Q2-E — conjugation audit for the fixed centered Xi source

Target source-level statements:

```lean
pascalCenteredRiemannXiKernel_conj
pascalCenteredXiNegLogDeriv_conj
```

with intended content that the fixed centered Xi kernel and its totalized negative log derivative commute with complex conjugation.

Prove these from the fixed kernel definition and the pinned Mathlib conjugation APIs. Do not infer them from RH or from zero symmetry.

If the pinned API does not directly expose conjugation for `completedRiemannZeta₀`, isolate the exact missing theorem rather than replacing it by a free provider.

This is the first Q2 stop condition.

## 7. Q2-F — reflected top-node geometry

Target:

```text
TopNode W (1 - x) = -conj(TopNode W x).
```

This is source geometry only.

Combining Q2-E with oddness of `pascalCenteredXiNegLogDeriv`, derive:

```text
TopAmplitude W (1 - x) = -conj(TopAmplitude W x).
```

## 8. Q2-G — horizontal BoxFeature Hermitian reflection

For real Mellin box parameter `v`, target:

```text
TopBoxFeature W (1 - x) v
= -conj(TopBoxFeature W x (-v)).
```

The `v -> -v` reflection is essential. Do not claim same-`v` conjugation.

After the affine substitution `x -> 1 - x`, derive:

```text
TopAggregatedBoxFeature W (-v)
= -conj(TopAggregatedBoxFeature W v).
```

Check the exact orientation with `intervalIntegral.integral_comp_sub_left`.

## 9. Q2-H — deoriented horizontal aggregate

The whole complex surface contains the top term as `-I * HorizontalBase`.

Define:

```lean
noncomputable def pascalCenteredXiPrimeSideQuadraticizationHorizontalDeorientedAggregate
    (W : PascalCenteredXiResidueTransportWindow) (v : ℝ) : ℂ :=
  -Complex.I *
    pascalCenteredXiPrimeSideQuadraticizationTopAggregatedBoxFeature W v
```

Target:

```text
HorizontalDeorientedAggregate W (-v)
= conj(HorizontalDeorientedAggregate W v).
```

This is not pointwise reality at fixed `v`.

## 10. Q2-I — real symmetrized horizontal feature

```lean
noncomputable def pascalCenteredXiPrimeSideQuadraticizationHorizontalSymmetricFeature
    (W : PascalCenteredXiResidueTransportWindow) (v : ℝ) : ℂ :=
  (pascalCenteredXiPrimeSideQuadraticizationHorizontalDeorientedAggregate W v +
    pascalCenteredXiPrimeSideQuadraticizationHorizontalDeorientedAggregate W (-v)) / 2
```

Prove:

```text
HorizontalSymmetricFeature W v
= conj(HorizontalSymmetricFeature W v).
```

Then use symmetry of the Mellin interval to prove that its normalized `v` average is unchanged by symmetrization.

Target:

```text
normalized average of HorizontalSymmetricFeature
= -I * pascalCenteredXiMellinQuadraticHorizontalBase ε W.
```

This gives a real feature-space representative of the actual top-horizontal contribution without redefining or absorbing the source term.

## 11. Q2-J — whole finite real feature

```lean
noncomputable def pascalCenteredXiPrimeSideQuadraticizationWholeBoxFeature
    (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) (v : ℝ) : ℂ :=
  pascalCenteredXiPrimeSideQuadraticizationAggregatedBoxFeature W X v +
    pascalCenteredXiPrimeSideQuadraticizationHorizontalSymmetricFeature W v
```

Prove pointwise reality:

```text
WholeBoxFeature W X v = conj(WholeBoxFeature W X v).
```

Then prove:

```text
pascalCenteredXiMellinQuadraticComplexWholeSurface ε W X
= normalized v-average of WholeBoxFeature W X.
```

A useful optional theorem is:

```text
ComplexWholeSurface = (ScalarSurface : ℂ).
```

Only prove this after whole-feature reality is established.

## 12. Q2-K — whole-surface polarization

Once `WholeBoxFeature` is real and its shifted norm-square functions are interval-integrable, define whole `+1` and `-1` shifted energies.

Then prove:

```text
4 * ScalarSurface = WholeE+ - WholeE-
```

and:

```text
WholeE- <= WholeE+ iff 0 <= ScalarSurface.
```

As in Q1, this is exact quadraticization but not a sign theorem.

If no independent source ordering is found, record a named whole-surface ordering gap.

## 13. Expected Q2 closeout

```text
vertical feature-space source              GREEN
horizontal feature-space source            GREEN
whole finite real box feature              GREEN
whole finite polarization                  GREEN
whole shifted energies PSD                 GREEN
independent whole ordering                  OPEN unless new source structure appears
```

This is still before radial subtraction.

## 14. Radial firewall

Do not include

```lean
Real.pi * pascalCenteredXiFixedRadialSecondMomentFunctional W.R
```

in Q2 definitions.

The radial comparison remains Q3.

Do not manufacture a completion of square by inserting the radial term into a shifted energy definition.

Q2 ends at the whole finite arithmetic surface before radial subtraction.

## 15. Acceptance checklist

```text
[ ] Q1 unconditional closeout remains unchanged
[ ] top source stays fixed-Xi, not right-edge decomposed
[ ] top amplitude integrability comes from existing finite boundary API
[ ] horizontal box Fubini is finite in T and ε
[ ] fixed-Xi conjugation is source-derived
[ ] top-node relation uses 1-x and -conj exactly
[ ] horizontal BoxFeature reflection includes v -> -v
[ ] deoriented horizontal aggregate has Hermitian v-reflection
[ ] symmetrized horizontal feature is pointwise real
[ ] its average equals the actual -I * top-horizontal source
[ ] whole feature average equals current ComplexWholeSurface
[ ] top-horizontal is not silently absorbed by definition
[ ] radial comparison remains separate
[ ] no sign theorem
[ ] no limit exchange
[ ] no RH consequence
```

## 16. Stop conditions

If fixed-Xi conjugation cannot be proved with the pinned source/API, stop at Q2-E and record the exact conjugation gap.

If fixed-Xi conjugation is Green but the horizontal aggregate reflection fails, record the exact orientation/reflection obstruction.

If Q2-J closes but no shifted-energy ordering provider is source-derived, close Q2 with:

```text
quadraticization available
PSD beams available
ordering equivalent to the original sign
independent ordering provider absent
```

That is a valid closeout, not a failed implementation.
