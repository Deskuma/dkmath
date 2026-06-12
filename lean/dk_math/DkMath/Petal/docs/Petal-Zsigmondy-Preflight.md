# Petal Zsigmondy Preflight

Status: **investigated**

This note records the state before moving from the closed cubic Petal surface
to Zsigmondy-facing work.

## Context

The Petal cubic surface has been closed as:

```text
S0_nat c b
  = GN 3 (c - b) b
  = shifted Eisenstein norm
```

and the reduced branch has the route:

```text
BoundaryD3Reduced
  -> boundary and S0 are separated
  -> primitive S0 witnesses can be read as anchored carriers
```

The next question is not yet "prove Zsigmondy".  The immediate question is:

```text
Can the reduced cubic Petal hypotheses be fed into the existing
Zsigmondy d = 3 existence theorem, and can that same Zsigmondy witness be
shared with the Petal anchored S0 carrier surface?
```

## Existing Zsigmondy Contract

`DkMath.Zsigmondy` already has a concrete primitive-divisor contract:

```lean
def PrimitivePrimeDivisor (a b n q : ℕ) : Prop :=
  Nat.Prime q ∧
  q ∣ a ^ n - b ^ n ∧
  ∀ m : ℕ, 0 < m → m < n → ¬ q ∣ a ^ m - b ^ m
```

Important existing names:

```lean
DkMath.Zsigmondy.PrimitivePrimeDivisor.prime
DkMath.Zsigmondy.PrimitivePrimeDivisor.dvd
DkMath.Zsigmondy.PrimitivePrimeDivisor.not_dvd_lower
DkMath.Zsigmondy.exists_primitivePrimeDivisor_prime_exp
DkMath.Zsigmondy.exists_primitivePrimeDivisor_body_nat
DkMath.Zsigmondy.exists_primitivePrimeDivisor_kernel_nat
DkMath.Zsigmondy.primitivePrimeDivisor_body_three_imp_dvd_GN
```

This means the existence layer is already present.  The missing Petal-facing
piece is a thin translation layer for the `d = 3` reduced cubic surface.

## Recommended New Bridge

Recommended file:

```text
DkMath.Petal.ZsigmondyD3Bridge
```

Recommended first target:

```lean
theorem exists_primitivePrimeDivisor_d3_of_boundaryD3Reduced
    {c b : ℕ} (hbc : b < c) (hb : 0 < b)
    (hcop : Nat.Coprime c b)
    (hred : BoundaryD3Reduced c b) :
    ∃ q : ℕ, DkMath.Zsigmondy.PrimitivePrimeDivisor c b 3 q
```

Recommended Petal/Zsigmondy combined witness:

```lean
theorem exists_anchoredS0Carrier_and_primitivePrimeDivisor_d3
    {c b : ℕ} (hbc : b < c) (hb : 0 < b)
    (hcop : Nat.Coprime c b)
    (hred : BoundaryD3Reduced c b) :
    ∃ q : ℕ,
      DkMath.Zsigmondy.PrimitivePrimeDivisor c b 3 q ∧
      AnchoredS0Carrier q c b q ∧
      ¬ q ∣ c - b
```

This is not a full Zsigmondy theorem.  It is the `d = 3` handshake:

```text
BoundaryD3Reduced hypotheses
  -> Zsigmondy primitive divisor q for c^3 - b^3
  -> the same q as an anchored S0 carrier
```

## Handshake Result

Status: **initial API implemented**

`DkMath.Petal.ZsigmondyD3Bridge` implements this handshake.

The reduced cubic hypotheses now produce a single witness `q` such that:

```text
q is a Zsigmondy primitive divisor for c^3 - b^3
q does not divide c - b
q divides S0_nat c b
q is an anchored S0_nat carrier
q is also a PrimitivePrimeFactorOfDiffPow q c b 3 witness
```

The last item is a compatibility bridge to the existing `PrimitiveBeam` API.
It does not add a valuation claim.  It only ensures that the later
squarefree/no-lift layer can consume the same primitive divisor.

## Important Separation: Existence, Location, Multiplicity

The investigation confirms that three concerns must remain separated.

Existence layer:

```text
Zsigmondy / PrimitiveBeam
  -> a primitive q exists
```

Location layer:

```text
Petal / GN / BoundaryD3 / Anchor
  -> q lies on GN/S0 side, not on the boundary
```

Multiplicity layer:

```text
Squarefree GN / NoLift GN / ValuationFlow
  -> padicValNat q (...) <= 1
```

This separation matters because Zsigmondy gives a prime divisor, but does not
say that the divisor appears with multiplicity exactly one.

## The Research Placeholder Is Not a Zsigmondy Target

`DkMath.NumberTheory.ZsigmondyCyclotomicResearch` still contains:

```lean
squarefree_implies_padic_val_le_one_research
padicValNat_primitive_prime_factor_le_one_research
```

These are research/legacy compatibility routes.  The global statement behind
`squarefree_implies_padic_val_le_one_research` is too strong as written.

The explicit counterexample already recorded in the research file is:

```text
d = 3
a = 5
b = 3
q = 7

5^3 - 3^3 = 98 = 2 * 7^2
S0_nat 5 3 = 49 = 7^2
```

Here `q = 7` is on the S0/GN3 side and does not divide the boundary `a - b = 2`,
but its valuation in the difference is `2`, not `<= 1`.

Therefore:

```text
Zsigmondy can supply primitive q.
Zsigmondy cannot by itself supply padicValNat q (...) <= 1.
```

The research placeholder should not be proved.  It should eventually be removed
or replaced at the callers by honest squarefree/no-lift APIs.

## Honest Replacement Targets

The honest squarefree theorem already exists:

```lean
DkMath.NumberTheory.GcdNext.padicValNat_primitive_prime_factor_le_one_of_squarefree_G
```

This theorem requires:

```lean
Squarefree (GN d (a - b) b)
```

The valuation-flow wrapper also exists:

```lean
DkMath.NumberTheory.ValuationFlow.primitivePrimeFlow_diffMass_le_one_of_squarefree_beam
```

This is the ABC-facing mass-control form.

The underlying primitive-beam route also exists:

```lean
DkMath.NumberTheory.PrimitiveBeam.primitive_prime_dvd_GN
DkMath.NumberTheory.PrimitiveBeam.primitive_prime_padic_eq_GN
DkMath.NumberTheory.PrimitiveBeam.primitive_prime_padic_bound_diff_of_squarefree_GN
```

These are the real replacement targets for valuation `<= 1`.

## Current Research Dependencies

The remaining direct research import chain is visible:

```text
DkMath.NumberTheory.GcdNextResearch
  -> DkMath.NumberTheory.ZsigmondyCyclotomicResearch

DkMath.NumberTheory.PrimitiveBeam
  -> DkMath.NumberTheory.ZsigmondyCyclotomicResearch

DkMath.FLT.PrimeProvider.CosmicPetalBridgeGNNoWieferichResearch
  -> DkMath.NumberTheory.ZsigmondyCyclotomicResearch
```

This is not the same problem as the ZsigmondyD3 bridge.  It is a valuation
spine repair problem.

## Practical Conclusion

Before full Phase 5, the next Lean step should be:

```text
Add DkMath.Petal.ZsigmondyD3Bridge
```

It should prove only the `d = 3` primitive-divisor translation and combined
Petal witness statements.

It should not try to solve:

```text
padicValNat q (c^3 - b^3) <= 1
```

unless an explicit squarefree/no-lift hypothesis is supplied.

The rule for the next phase is:

```text
Zsigmondy gives existence.
Petal gives location.
Squarefree/NoLift gives multiplicity.
```
