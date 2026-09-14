# MG-003A implementation and audit report

## Outcome

**Outcome A — RAW NORMALIZATION AND UNIT-REFINEMENT TRANSPORT ESTABLISHED**

The missing common-scale layer between raw unit coordinates and the existing
primitive `GNGaugeStage` is now production-proved.  Synchronized refinement
acts through the independent factor `k`; a newly captured prime after an old
raw escape must divide `k`.

This remains finite arithmetic transport.  It does not construct a primitive
shape transition, a universal prime provider, or a Legendre/Goldbach result.

## Production modules and facade changes

Added:

```text
DkMath/NumberTheory/MultiGauge/RawNormalization.lean
DkMath/NumberTheory/PrimorialUniverse/MultiGaugeUnitRefinementBridge.lean
```

Updated:

```text
DkMath/NumberTheory/MultiGauge.lean
DkMath/NumberTheory/PrimorialUniverse.lean
```

The generic raw module imports only the generic primitive stage.  The PUU
bridge is downstream and imports the existing unit-coordinate refinement API.

## Raw/common-scale API

`GNRawGaugeStage` stores an unrestricted pair `(x,u)`, with:

- `gnValue` and `value` for the raw observer;
- `scale = Nat.gcd x u`;
- `scaleBy k`, which sends `(x,u)` to `(k*x,k*u)`;
- `primitiveRawStage` and the coprime `primitiveStage`, available under the
  explicit hypothesis `0 < scale`.

The following identities are kernel-checked:

```text
(scaleBy k s).value = k^d * s.value
s.x = s.scale * (s.primitiveStage hg).x
s.u = s.scale * (s.primitiveStage hg).u
s.value = s.scale^d * (s.primitiveStage hg).value
```

The homogeneity proof uses the existing `GTail` binomial boundary identity,
then cancels the common `k^d * u^d` term in `Nat`.

## Prime support

For `Nat.Prime q`, `1 ≤ d`, and positive raw scale, the exact support split is:

```text
RawPrimeCaught q s ↔
  q ∣ s.scale ∨ PrimeCaught q (s.primitiveStage hg)
```

The corresponding escape conjunction is also provided.  No disjointness of
the two support channels is asserted.

For synchronized raw refinement:

```text
RawPrimeEscapes q s →
RawPrimeCaught q (scaleBy k s) →
q ∣ k
```

The converse persistence direction for an already-caught raw prime is also
provided.  The localization proof uses the factorization
`(scaleBy k s).value = k^d * s.value`, independently of `GNGaugeTransition`.

## PUU bridge

`coarseRawStage` and `refinedRawStage` package the two coordinate pairs.  The
theorem `unitRefinement_raw_stage_packet` combines two existing
`unitCoordinate_refine` applications with the exact equality:

```text
refinedRawStage d k x u = scaleBy k (coarseRawStage d x u)
```

The theorem `unitRefinement_raw_capture_packet` carries the two unchanged
absolute-point coordinates and the prime localization `q ∣ k` together.
The generic MultiGauge facade does not import PrimorialUniverse.

## Regression evidence

The raw regression uses `d = 2`, `(x,u) = (1,2)`, and `k = 3`:

- the gcd grows from `1` to `3`;
- the raw value scales by `3^2`;
- gcd normalization recovers coordinates `(1,2)`;
- `3` divides the refined raw value but not the coarse raw value, and `3`
  divides the refined common scale.

The PUU regression additionally checks the `5`-to-`1` unit refinement and the
two synchronized raw coordinates.

## Primitive-shape audit

The normalized primitive coordinates are constructed exactly and the concrete
regression recovers the original coprime pair.  A separate generic theorem
that normalization of every `scaleBy k` stage preserves the primitive stage
was not forced: it requires additional gcd-of-scaled-pair and natural
division transport lemmas, while the concrete common-scale equality and the
raw support theorem already establish the requested transport layer.  This is
recorded as a derived arithmetic fact rather than conflated with a genuine
primitive `GNGaugeTransition`.

## Validation

Commands were run from `lean/dk_math`:

```text
lake build DkMath.NumberTheory.MultiGauge.RawNormalization
lake build DkMath.NumberTheory.PrimorialUniverse.MultiGaugeUnitRefinementBridge
lake build DkMath.NumberTheory.MultiGauge
lake build DkMath.NumberTheory.PrimorialUniverse
```

All completed successfully.  The focused builds completed with `8658`,
`8661`, `8661`, and `8707` jobs, respectively.  The shell profile emitted
`/opt/wonderful/bin/wf-env: Permission denied`; this was environmental noise
and did not affect the successful builds.

Changed Lean sources were scanned for `sorry`, `admit`, and new `axiom`
declarations; none were found.  `git diff --check` completed successfully.

## Scope barriers

No MG-002 automaton, primitive-shape provider, Legendre theorem, Norm,
Eisenstein, TraceOne, ABC/FLT migration, analytic estimate, or conjectural
provider was added.  The new refinement transport is a genuine non-tautological
homogeneous raw arithmetic result, but it does not by itself create a
primitive transition or a global coverage theorem.
