# ZDI-010 — positive-density source-connected constant obstruction report

Date: 2026-08-19  
Branch: `wip/RH-CFBRC-zeta-dkreal-zero-interval-260819-v0`

## Scope and conclusion

This report implements the contract in
`0019-ZDI-010-positive-density-source-connected-constant-obstruction-instructions.md`.
The instruction file requires closing the provenance gap left by ZDI-009;
the user request is implemented by
`EtaCriticalMirrorPositiveDensitySourceConnectedConstantObstruction.lean`.

The result remains **O-CONSTANT** for the current residual-majorant /
certified-margin route, now with the actual source objects in the final
theorem statements.  For every realizable positive-density schedule and every
nonreal off-critical point on either audited side, the normalized existing
block-margin power lower bound is eventually less than one sixteenth of the
normalized existing residual power majorant.

No exact Eta-tail cancellation or fixed block-start projection transport is
implemented.

## Source connection

The residual object is the existing

    etaCriticalMirrorBlockStartResidualTailPowerBound

from `EtaCriticalMirrorPairedFrameGrowingBlockTailRemainder.lean`, whose
underlying definition is

    etaCriticalMirrorDefectPairTailPowerBound.

The proof unfolds that definition only to retain the relevant nonnegative
dominant summand.  On the right this is the mirror term

    |s.im| * ‖criticalMirror s‖ / (1 - s.re) *
      (K + S.blockLength K)^(-(1 - s.re)),

and on the left it is the original-side term

    |s.im| * ‖s‖ / s.re *
      (K + S.blockLength K)^(-s.re).

The margin object is the existing

    etaCriticalMirrorRightBlockMarginPowerLowerBound
    etaCriticalMirrorLeftBlockMarginPowerLowerBound

from `EtaCriticalMirrorDefectPairMarginPowerLowerBound.lean`.  Its normalized
limits are reused directly through

    EtaPairPositiveDensityBlockSchedule.rightNormalizedBlockMarginPowerLowerBound_tendsto
    EtaPairPositiveDensityBlockSchedule.leftNormalizedBlockMarginPowerLowerBound_tendsto

from `EtaCriticalMirrorPairedFrameNormalizedConstantAudit.lean`.

The positive-density schedule fields are used without importing or assuming
the incompatible growing-block contract:

    S.density_pos
    S.blockLength_tendsto_atTop
    S.relativeLength_tendsto_density.

The phase/span API from
`EtaCriticalMirrorPairedFramePositiveDensityRotationLimit.lean` remains
available through the existing imports, but no projection transport theorem
is needed for this obstruction.

## New source-derived limits

The module first proves

    ((K + S.blockLength K : ℕ) : ℝ) /
      etaPairFrameLeftEndpoint K
      → 1/2 + S.density,

and, using eventual positivity of the scheduled block length,

    etaPairFrameLeftEndpoint K /
      ((K + S.blockLength K : ℕ) : ℝ)
      → 2 / (1 + 2*S.density).

These are derived from the exact endpoint formula and
`S.relativeLength_tendsto_density`; the desired limit is not stored as a
structure field.

The module then proves the actual dominant normalized residual limits:

    etaPairFrameLeftEndpoint K^(1 - s.re) * rightDominant(K)
      → |s.im| * ‖criticalMirror s‖ / (1 - s.re) *
          (2 / (1 + 2*S.density))^(1 - s.re),

and

    etaPairFrameLeftEndpoint K^s.re * leftDominant(K)
      → |s.im| * ‖s‖ / s.re *
          (2 / (1 + 2*S.density))^s.re.

The proofs use `Real.div_rpow`, `Real.rpow_neg`, and the existing positive
endpoint facts.  They are source expressions, not newly defined target
constants.

## Load-bearing obstruction theorems

The final theorems are:

    EtaPairPositiveDensityBlockSchedule.eventually_sixteen_mul_rightNormalizedBlockMarginPowerLowerBound_lt_residualPowerBound

and

    EtaPairPositiveDensityBlockSchedule.eventually_sixteen_mul_leftNormalizedBlockMarginPowerLowerBound_lt_residualPowerBound.

Each conclusion mentions both actual source objects.  The proof uses the
ZDI-009 point-specialized scalar inequalities, the actual normalized margin
limits, the dominant residual limit, and a midpoint separating the strict
limiting constants.  The full residual majorant dominates its selected
nonnegative summand pointwise, so the conclusion follows without proving a
full two-term residual limit.

## Boundary

The result says only that the current explicit upper majorant and current
certified lower margin cannot certify residual domination.  It does not say
that the exact oscillatory residual is large, that exact cancellation is
impossible, or that a sharper Eta estimate cannot succeed.  It also does not
introduce RH, a no-cancellation provider, centered-sigma coercivity, or any
source-recovery assumption.

Since the obstruction already compares the full actual margin lower-bound
object with the current residual majorant, a projection loss factor
`0 < λ ≤ 1` cannot repair this route.

## Validation

Focused validation from the nested Lake project:

    ./lean-build.sh DkMath.RH.CFBRC.EtaCriticalMirrorPositiveDensitySourceConnectedConstantObstruction

The build passed.  A separate `#print axioms` audit was run for the ratio
lemmas, normalized dominant limits, and both final eventual obstruction
theorems; only the standard Lean axioms (`propext`, `Classical.choice`, and
`Quot.sound`) were reported, with no `sorryAx`.

