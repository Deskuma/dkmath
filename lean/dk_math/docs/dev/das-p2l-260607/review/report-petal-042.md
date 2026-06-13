# Report: issue-petal-028 Closure Survey

Date: 2026-06-14

Source issue:

```text
lean/dk_math/docs/dev/das-p2l-260607/review/issue-petal-028.md
```

## Executive Summary

The core concern in `issue-petal-028` has been resolved enough to return to the
normal Petal -> Zsigmondy route.

The original concern was not that a missing proof merely had to be filled.  The
main target,

```lean
squarefree_implies_padic_val_le_one_research
padicValNat_primitive_prime_factor_le_one_research
```

was too strong as a general statement.  The correct repair was to stop treating
Zsigmondy existence as a valuation bound, and instead split the route into:

```text
Zsigmondy:
  primitive prime existence

Petal / GN / Anchor:
  location on the GN/S0 side, away from the boundary

NoLift / squarefree / ValuationFlow:
  multiplicity control, padicValNat <= 1
```

That split is now implemented across `PrimitiveBeam`, `ValuationFlow`, `ABC`,
`Petal`, and the FLT PrimeProvider surface.

## Original Issue-028 Claims

### Claim 1: the old research theorem is false as a general theorem

Status:

```text
achieved / confirmed
```

Current evidence:

```lean
DkMath.NumberTheory.GcdNext.counterexample_padicValNat_diff_le_one
DkMath.NumberTheory.GcdNext.squarefree_implies_padic_val_le_one_is_false
```

The counterexample is still recorded in:

```text
lean/dk_math/DkMath/NumberTheory/ZsigmondyCyclotomicResearch.lean
```

The essential example remains:

```text
d = 3, a = 5, b = 3, q = 7
5^3 - 3^3 = 98 = 2 * 7^2
```

Therefore the old statement should not be proved.  It is a research placeholder
and compatibility marker.

### Claim 2: Zsigmondy supplies existence, not multiplicity

Status:

```text
achieved / reflected in the design
```

Current Petal-facing structure:

```lean
DkMath.Petal.ZsigmondyD3Bridge
DkMath.Petal.PrimitiveD3ValuationBridge
```

The first bridge supplies the `d = 3` primitive witness / S0-side carrier.
The second bridge is explicitly conditional on local NoLift or squarefree GN.

This is the intended separation:

```text
ZsigmondyD3Bridge:
  existence and location

PrimitiveD3ValuationBridge:
  multiplicity, only after NoLift or squarefree input
```

### Claim 3: the real common API is NoLift / squarefree valuation control

Status:

```text
achieved
```

Main implementation surface:

```lean
DkMath.NumberTheory.PrimitiveBeam.primitive_prime_padic_bound_diff_of_noLift_GN
DkMath.NumberTheory.PrimitiveBeam.primitive_prime_padic_bound_diff_of_squarefree_GN_local
```

Compatibility / older squarefree route:

```lean
DkMath.NumberTheory.PrimitiveBeam.primitive_prime_padic_bound_diff_of_squarefree_GN
```

The design now reads:

```text
NoLift at q:
  main local multiplicity hypothesis

Squarefree GN:
  sufficient condition for local NoLift

old squarefree signatures:
  compatibility wrappers
```

### Claim 4: ABC should use flow/local-load wrappers, not the false target

Status:

```text
achieved
```

Current ABC surface:

```lean
DkMath.ABC.noLift_beam_bounds_local_load
DkMath.ABC.squarefree_beam_bounds_local_load_local
DkMath.ABC.squarefree_beam_bounds_local_load
```

Regression examples:

```lean
DkMath.ABC.ValuationFlowBridgeExamples
```

The examples cover:

```text
q = 31, a = 2, b = 1, d = 5
  squarefree GN sample

q = 7, a = 4, b = 2, d = 3
  non-squarefree GN but local NoLift sample
```

The second example is important because it proves by example that local NoLift
is strictly more flexible than full GN squarefreeness.

### Claim 5: FLT should use a NoLift valuation target

Status:

```text
achieved
```

Current FLT no-sorry valuation surface:

```lean
DkMath.FLT.PrimeProvider.CosmicPetalBridgeGNNoWieferichValuation
```

Main declarations:

```lean
DkMath.FLT.TriominoPrimitivePrimeFactorPadicValNatLeOneTarget
DkMath.FLT.primitivePrimeFactorOfDiffPow_of_FLT_branch
DkMath.FLT.triominoPrimitivePrimeFactorPadicValNatLeOneTarget_of_noLiftGNBridge
DkMath.FLT.triominoPrimitivePrimeFactorPadicValNatLeOneTarget_of_squarefreeGNBridge
```

The user has already confirmed these with:

```lean
#print axioms DkMath.FLT.primitivePrimeFactorOfDiffPow_of_FLT_branch
#print axioms DkMath.FLT.triominoPrimitivePrimeFactorPadicValNatLeOneTarget_of_noLiftGNBridge
#print axioms DkMath.FLT.triominoPrimitivePrimeFactorPadicValNatLeOneTarget_of_squarefreeGNBridge
```

The important structural result is:

```text
FLT Branch-B primitive-prime inputs
  -> PrimitiveBeam.PrimitivePrimeFactorOfDiffPow
  -> PrimitiveBeam no-lift theorem
  -> padicValNat q (z^p - y^p) <= 1
```

### Claim 6: Research imports should not pollute the honest provider route

Status:

```text
mostly achieved
```

Completed:

```text
PrimeProvider.lean:
  imports CosmicPetalBridgeGNNoWieferichValuation
  no longer directly imports CosmicPetalBridgeGNNoWieferichResearch

TriominoSquarefreeGNBridgeProviderImpl.lean:
  imports CosmicPetalBridgeGNNoWieferichValuation
  no longer imports CosmicPetalBridgeGNNoWieferichResearch

CosmicPetalBridgeGN.lean:
  explicitly imports the Valuation surface
```

Remaining direct imports of `CosmicPetalBridgeGNNoWieferichResearch`:

```text
DkMath.FLT.PrimeProvider.CosmicPetalBridgeGNNoWieferichDefault
DkMath.FLT.PrimeProvider.CosmicPetalBridgeGNDescentBQuarantine
```

This is acceptable because both are fixed-injection / quarantine surfaces.

## Current Remaining Research Debt

The following research placeholders still exist:

```text
DkMath.NumberTheory.ZsigmondyCyclotomicResearch.lean
  squarefree_implies_padic_val_le_one_research

DkMath.NumberTheory.GcdNextResearch.lean
  one remaining sorry in the research boundary receiver area
```

Current direct use of `padicValNat_primitive_prime_factor_le_one_research`
remains in research or compatibility paths:

```text
DkMath.NumberTheory.GcdNextResearch
DkMath.NumberTheory.PrimitiveBeam
DkMath.FLT.PrimeProvider.CosmicPetalBridgeGNNoWieferichResearch
```

This is no longer blocking the normal Petal -> Zsigmondy line, because the
honest route is now available through:

```text
PrimitiveBeam
ValuationFlow
ABC.ValuationFlowBridge
Petal.PrimitiveD3ValuationBridge
FLT.PrimeProvider.CosmicPetalBridgeGNNoWieferichValuation
```

## Achievement Score

The issue is not "fully deleted", but it is operationally closed for the next
mainline phase.

```text
False theorem identified:
  complete

Counterexample recorded:
  complete

Honest replacement theorem surface:
  complete

ABC migration:
  complete for the current public wrappers and examples

FLT valuation migration:
  complete for the no-sorry valuation surface

Research import isolation:
  mostly complete

Research placeholder deletion:
  not complete, intentionally deferred
```

Practical status:

```text
issue-petal-028:
  closed as a blocker
  not deleted as historical/research debt
```

## Decision

It is reasonable to return to the normal route:

```text
Petal -> Zsigmondy full connection
```

The next phase should not attempt to prove the old research placeholder.
Instead it should use the already-established layer split:

```text
1. Zsigmondy:
   produce primitive witnesses

2. Petal / GN / Anchor:
   locate witnesses on S0/GN and away from boundary

3. NoLift / squarefree:
   supply multiplicity control

4. ValuationFlow / ABC / FLT:
   consume padicValNat <= 1 or diffMass <= 1
```

## Suggested Next Mainline Target

Return to:

```text
DkMath.Petal.ZsigmondyD3Bridge
DkMath.Petal.PrimitiveD3ValuationBridge
```

Then extend toward the full Petal/Zsigmondy connection by keeping existence and
multiplicity separate:

```text
existence:
  Zsigmondy primitive divisor

location:
  S0 / GN / Anchor carrier

multiplicity:
  NoLift or squarefree hypothesis
```

This is now aligned with both ABC and FLT.
