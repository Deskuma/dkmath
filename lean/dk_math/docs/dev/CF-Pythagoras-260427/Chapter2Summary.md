# CF-Pythagoras Chapter 2 Summary

cid: 69e72cfc-9944-83e8-8786-53c02b36fb89

## Claim

Chapter 2 extends the Pythagorean Gap/Beam viewpoint to the cubic FLT-shaped
difference route and closes the `d = 3` ordinary primitive branch (`q != 3`) as
a no-sorry abstract contradiction engine.

The closed route is:

```text
PrimitiveBeam
  -> GN
  -> PowerBeam
  -> gcd / p-adic valuation
  -> contradiction
```

The standard entry point is:

```lean
DkMath.CosmicFormula.PowerGapBeam.CubicPrimitiveFLTContext
```

Given a context `C`, the standard contradiction endpoints are:

```lean
C.val_le_one_contradiction
C.squarefree_contradiction
```

## What Was Built

Chapter 2 built these layers.

1. PowerGap / PowerBeam algebra

   `PowerGapBeam.lean` defines the endpoint Gap/Beam language and connects
   FLT-shaped equations to PowerBeam divisibility.

2. GN bridge

   `PowerGapBeamGN.lean` identifies the cubic endpoint PowerBeam with the
   corresponding `GN` expression and transports valuation / squarefree facts.

3. gcd and valuation contradiction

   `PowerGapBeamGcd.lean` proves that the relevant prime divisibility and
   valuation conditions contradict the FLT-shaped equation.

4. Primitive-prime bridge

   `PowerGapBeamPrimitive.lean` transports a natural primitive prime witness to
   the integer endpoint PowerBeam and exposes cubic primitive contradiction
   wrappers.

5. Bundled ordinary cubic context

   `CubicPrimitiveFLTContext` packages the ordinary branch assumptions and
   exposes a short API:

   ```lean
   C.prime
   C.q_not_dvd_three
   C.beam_dvd
   C.beam_ne
   C.val_le_one_contradiction
   C.squarefree_contradiction
   ```

## What Was Not Claimed

Chapter 2 does not claim a complete proof of FLT for `d = 3`.

Two pieces remain outside the closed ordinary branch:

1. The exceptional branch `q = 3`
2. Automatic supply of GN-side fuel:

   ```text
   v_q(GN(3, a-b, b)) <= 1
   Squarefree(|GN(3, a-b, b)|)
   ```

This boundary is intentional.  It keeps the ordinary branch engine precise and
prevents the result from overstating what has been formalized.

## Final Formulation

The strongest accurate formulation is:

```text
The Pythagorean Gap/Beam construction has been extended into a cubic
ordinary-branch FLT obstruction engine.  Under a primitive prime witness
q != 3, the GN/PowerBeam/valuation pipeline reaches contradiction once the
GN-side valuation or squarefree fuel is supplied.
```

The corresponding limit statement is:

```text
The exceptional prime q = 3 and the automatic GN fuel pipeline remain S3 tasks.
```
