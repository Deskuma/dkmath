# GN / GN5 structural bridge implementation report

## Scope

This report closes the Phase F acceptance set in
`CODEX-GN-GN5-STRUCTURAL-BRIDGE-DIRECTIVE-260820.md`.  The implementation is
local to `DkMath.NumberTheory.StructuralArithmetic.GNBridge`; no FLT5 proof
refactor and no duplicate generic GN definition were introduced.

The implementation started from checkpoint `757d034e5d80d3bebc9c19715c460df3ca0e1ea0`.

## Implemented bridges

- `freshPrimeDirection_GN_of_primitivePrimeFactor` reuses
  `PrimitiveBeam.primitive_prime_dvd_GN_body`.  It requires
  `q ∉ S` explicitly, then applies the existing finite-scale fresh-direction
  API.  The corresponding
  `not_primeScaleGeneratedBy_GN_of_primitivePrimeFactor` theorem records the
  non-generation consequence.
- `GN5_eq_generic_GN` proves the exact degree-five identity between the
  existing `DkMath.FLT.Five.GN5` polynomial and
  `DkMath.CosmicFormulaBinom.GN 5`.  The latter is already an abbreviation for
  the canonical Cosmic Formula `GN`; no new GN is defined.
- `GN5_one_one_has_freshPrimeDirection` and
  `GN5_one_one_not_primeScaleGeneratedBy_two_three_five` rewrite the existing
  Phase-E `{2, 3, 5}` finite escape to `FLT.Five.GN5 1 1`; the value `31` is
  not recomputed here.

The declarations carry docstrings stating their exact scope and formal
boundary.  Degree `5`, additive congruence modulo `5`, and PowerGauge period
`5` are intentionally kept distinct.

## Files

- `DkMath/NumberTheory/StructuralArithmetic/GNBridge.lean`
- `DkMath/NumberTheory/StructuralArithmetic.lean` (public aggregate import)
- `docs/dev/StructuralArithmetic-RedRibbon-260818-v0/README.md`

## Verification

Focused builds completed successfully:

```text
lake build DkMath.NumberTheory.StructuralArithmetic.GNBridge
lake build DkMath.NumberTheory.StructuralArithmetic
```

The Phase-A--E baseline modules were also rebuilt before this phase.  The
build output contains the pre-existing warning at
`DkMath/NumberTheory/ZsigmondyCyclotomicResearch.lean:147` (`sorry`) through
the `PrimitiveBeam` dependency; no placeholder was added by Phase F.

`#print axioms` on the generic fresh-direction theorem, the exact GN5
identity, and the specialized non-generation theorem reports only the usual
`propext`, `Classical.choice`, and `Quot.sound` dependencies.

The next bounded route is the Phase-G golden-unit bridge.  This report does
not claim a limit exchange, an RH consequence, or an unconditional FLT
closure.
