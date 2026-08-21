# GWSS-002 off-critical Mellin witness report

Global objective:
zero configuration -> independent source -> off-critical detector -> arithmetic control -> centered-coordinate uniqueness -> `RiemannHypothesis`

Current GWSS stage:
GWSS-002

Load-bearing provider boundary:
The implementation is a finite zero-side witness construction on a fixed
actual centered-Xi window.  It reuses the C2 full-rank canonical Mellin matrix,
the actual squared-orbit mass aggregation, and the existing positive-width
Mellin admissibility theorems.  The inverse matrix is used only for finite
coordinate extraction.  No new source family or positivity criterion is
introduced.

## Squared-orbit geometry

`complex_sq_im_eq_two_mul_re_mul_im` proves
`(z ^ 2).im = 2 * z.re * z.im`.  Every actual centered Xi zero has nonzero
imaginary coordinate by the existing unconditional
`nontrivialRiemannZetaZero_im_ne_zero` route.  Consequently
`pascalCenteredXiZeroDiskFinset_sq_im_ne_zero` proves that a zero with
`z.re ≠ 0` has an off-axis squared coordinate.  This uses no RH or
functional-equation assumption.

## Orbit-mass nonzero

`pascalCenteredXiSquaredOrbitMass_ne_zero` connects an occupied squared orbit
to an actual carrier point, applies
`pascalCenteredXiZeroMultiplicity_pos`, and proves positivity of the finite
natural-number multiplicity sum before casting it to `ℂ`.  The proof does not
assert a sign for a global explicit-formula sum.

## Dual coordinate extraction

`exists_matrix_coordinate_extractor` takes a nonzero-determinant complex
matrix and uses the corresponding row of `Matrix.nonsingInv` to extract one
target coordinate after `mulVec`.  The actual-window theorem
`exists_pascalCenteredXiMellinMoment_coordinate_extractor` applies this to the
C2 identity
`momentVec = H *ᵥ massVec`.

## Admissible witness weight

`pascalCenteredXiMellinWitnessWeight` is the finite linear combination

```text
z ↦ ∑ i, c i * pascalCenteredXiMellinSecondDifferenceWeight ε (τ i) z.
```

The module proves differentiability, centered evenness, and linearity of its
actual zero-side moment.  The eventual C2 determinant theorem supplies one
positive `ε`; the target coordinate is then selected by the public C2
reindexing bridge `exists_pascalCenteredXiSquaredOrbitCoordinate_eq`.

## Primary classification

`OFF-CRITICAL-MELLIN-WITNESS-FOUND`

An off-critical squared orbit in a fixed actual centered-Xi window admits an
admissible target-dependent finite linear combination of the zero-independent
canonical Mellin family whose actual zero-side weighted moment is nonzero.

## Next unresolved Gap

`MELLIN-WITNESS-ARITHMETIC-CONTROL-GAP`

GWSS-002: CLOSED  
GWSS-003: authorized next but not started  
GWSS-004: not authorized

## Explicit non-goals

The finite witness is not substituted into the arithmetic explicit formula in
this stage.  The top-horizontal term remains present, and no `T → ∞` limit,
prime-side sign, Weil positivity, Li criterion, or RH consequence is claimed.

## Verification

- `lake build DkMath.RH.CFBRC.PascalCenteredXiMellinOffCriticalWitnessAudit`
  succeeds under `leanprover/lean4:v4.32.2`.
- The public witness, mass, and coordinate-extraction results have the
  standard branch axiom footprint (`propext`, `Classical.choice`, and
  `Quot.sound`); no new axiom is introduced.
- No `sorry`, `admit`, or `native_decide` is used.
