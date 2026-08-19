# ZDI-009 — positive-density normalized constant obstruction audit report

Date: 2026-08-19  
Branch: `wip/RH-CFBRC-zeta-dkreal-zero-interval-260819-v0`

## Scope and conclusion

This report implements the audit contract in
`0017-ZDI-009-positive-density-fixed-block-projection-constant-gate-instructions.md`.
The instruction file specifies the Gate 2 audit and its non-goals; the user
request is implemented by the Lean module
`EtaCriticalMirrorPositiveDensityNormalizedConstantObstructionAudit.lean`.

The result is **O-CONSTANT** for the current positive-density
residual-majorant / certified-margin route.  On both off-critical sides, the
current normalized residual constant is strictly greater than sixteen times
the full certified normalized margin constant.  This comparison already uses
the full margin, so no projection-loss factor has been introduced.

Consequently, the positive-density fixed block-start projection transport
gate is not implemented for this route.  This is not a claim that the exact
oscillatory Eta tail is large or that a sharper cancellation argument cannot
succeed.

## Exact source trace

The residual source is the explicit definition

    etaCriticalMirrorBlockStartResidualTailPowerBound

and its underlying pair-tail majorant

    etaCriticalMirrorDefectPairTailPowerBound

in `EtaCriticalMirrorPairedFrameGrowingBlockTailRemainder.lean`.  The
corresponding norm comparison is

    norm_etaCriticalMirrorDefectPairTail_le_powerBound.

The positive-density margin source is the endpoint-power lower-bound API in
`EtaCriticalMirrorDefectPairMarginPowerLowerBound.lean`:

    etaCriticalMirrorRightBlockMarginPowerLowerBound_le
    etaCriticalMirrorLeftBlockMarginPowerLowerBound_le

with the pair-level nontrivial-zero lower bounds supplied by

    etaCriticalMirrorRightPairMarginPowerLowerBound_le_of_nontrivialRiemannZetaZero
    etaCriticalMirrorLeftPairMarginPowerLowerBound_le_of_nontrivialRiemannZetaZero.

After positive-density normalization, the exact limit theorems are

    EtaPairPositiveDensityBlockSchedule.rightNormalizedBlockMarginPowerLowerBound_tendsto
    EtaPairPositiveDensityBlockSchedule.leftNormalizedBlockMarginPowerLowerBound_tendsto

from `EtaCriticalMirrorPairedFrameNormalizedConstantAudit.lean`.  The
positive-density phase/span context remains the already audited API from
`EtaCriticalMirrorPositiveDensityScheduleCompatibilityAudit.lean` and
`EtaCriticalMirrorPositiveDensityBoundedSpanProjectionAudit.lean`; ZDI-007
also records the incompatible relative-length behavior of the growing-block
schedule.

## Lean implementation

The new module proves the scalar inequalities for arbitrary real parameters.
For `1/2 < σ < 1`, `0 < t`, `t ≤ n`, and `ρ > 0`, it proves

    16 * ((t^2 / 4) * ρ * (1 + 2ρ)^(σ - 2))
      < t*n/(1 - σ) * (2/(1 + 2ρ))^(1 - σ).

For `0 < σ < 1/2`, under the same positivity hypotheses, it proves

    16 * ((t^2 / 4) * ρ * (1 + 2ρ)^(-σ - 1))
      < t*n/σ * (2/(1 + 2ρ))^σ.

The proof re-derives the quotients in Lean.  With `a = 1 + 2ρ`, the right
quotient is

    4 * (n/t) * (1/(1 - σ)) * 2^(1 - σ) * (a/ρ),

and the left quotient is

    4 * (n/t) * (1/σ) * 2^σ * (a/ρ).

The strict factor bounds are obtained from `t ≤ n`, the audited strip, the
positive density, and `Real.one_lt_rpow`; no constant is assumed by
definition.

The source-facing point specializations use the generic norm bridges

    |s.im| ≤ ‖s‖
    |s.im| ≤ ‖criticalMirror s‖,

the second through `criticalMirror_im`.  Thus the specializations match the
exact normalized constants with `σ = s.re` and `t = |s.im|`, while retaining
the elementary nature of the scalar obstruction.

## Boundary and classification

The conclusion is only

    current residual majorant > full certified margin.

It does not imply exact residual domination, exact-tail impossibility, global
no-cancellation, a coercivity theorem forcing the critical line, or RH.  In
particular, the unresolved source-recovery / zero-forcing direction remains
outside this module.

The next mathematically relevant route would have to sharpen the residual
majorant using an exact oscillatory Eta identity or a separately justified
source-recovery estimate.  A fixed-block transport theorem with a loss factor
`0 < λ ≤ 1` cannot repair the present strict comparison, since
`λ * M ≤ M < R`.

## Validation

Focused validation was run from the nested Lake project:

    ./lean-build.sh DkMath.RH.CFBRC.EtaCriticalMirrorPositiveDensityNormalizedConstantObstructionAudit

The build passed.  The temporary scratch proof used during development was
removed; no fixed-block transport theorem was added.

