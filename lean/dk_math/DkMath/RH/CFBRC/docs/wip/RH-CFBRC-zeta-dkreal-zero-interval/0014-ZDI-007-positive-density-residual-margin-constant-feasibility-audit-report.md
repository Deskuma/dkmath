# ZDI-007 — positive-density residual/margin constant feasibility audit report

Date: 2026-08-19  
Branch: `wip/RH-CFBRC-zeta-dkreal-zero-interval-260819-v0`

## Scope and conclusion

This report implements the audit contract in
`0013-ZDI-007-positive-density-residual-margin-constant-feasibility-audit-instructions.md`.
The instruction file supplies the schedule/constant audit questions; the user
request is implemented by the compatibility and frame-span theorems in
`EtaCriticalMirrorPositiveDensityScheduleCompatibilityAudit.lean`.

The decisive result is **O-SCHEDULE** for the existing fixed-frame route:

- the preferred positive-density schedule is `N(K) = K`, represented by
  `etaPairHalfDensityBlockSchedule` with density `1/2`;
- the existing `EtaPairGrowingBlockSchedule` requires the same relative length
  to tend to zero;
- a positive-density schedule requires that ratio to tend to a strictly
  positive density;
- therefore no single block-length function can satisfy both schedule
  contracts;
- positive-density blocks have a nonzero limiting frame span in general, so
  the existing shrinking-frame transport theorem cannot simply be reused.

The constant comparison is still informative: for `N(K) ≍ K`, residual and
margin powers are rate-balanced on the relevant side, but the current explicit
upper/lower bounds reduce domination to parameter-dependent constant
inequalities. Those inequalities are not proved uniformly on the off-critical
strip. This is secondary to the schedule incompatibility and is not promoted
to a theorem about the exact Eta tail.

No generic coercivity, no-cancellation, RH-closing provider, or contradictory
schedule instance was introduced.

## 1. Exact positive-density candidate

The repository already contains:

    etaPairHalfDensityBlockSchedule

with exact characterization

    etaPairHalfDensityBlockSchedule.blockLength K = K

and density

    etaPairHalfDensityBlockSchedule.density = 1 / 2.

Its fields prove:

    blockLength K → ∞,
    blockLength K / etaPairFrameLeftEndpoint K → 1 / 2.

Since

    etaPairFrameLeftEndpoint K = 2K + 1,

this is the simplest realizable positive-density candidate. It is not an
instance of the existing sublinear growing-block type.

## 2. Schedule compatibility theorem

The new module

    DkMath/RH/CFBRC/EtaCriticalMirrorPositiveDensityScheduleCompatibilityAudit.lean

proves:

    EtaPairPositiveDensityBlockSchedule.not_relativeLength_tendsto_zero

which states that a positive-density schedule cannot also have its relative
length tend to zero. The proof only uses uniqueness of limits and
`density_pos`; it does not use zeta zeros, residual estimates, or an off-
critical assumption.

The specialized theorem

    EtaPairPositiveDensityBlockSchedule
      .not_common_blockLength_with_etaPairGrowingBlockSchedule

proves that a positive-density schedule and an
`EtaPairGrowingBlockSchedule` cannot have equal `blockLength` functions.

This directly settles the required compatibility check. The old growing-block
theorems require:

    blockLength K → ∞,
    blockLength K / etaPairFrameLeftEndpoint K → 0.

The second field is used by:

    EtaPairGrowingBlockSchedule.frameBlockSpan_tendsto_zero

and by the growing-block quantitative certificates that transport pair-local
signs into a common block-start frame. A positive-density block cannot be fed
to those theorems without changing the geometry contract.

## 3. Positive-density frame span

The same module proves:

    EtaPairPositiveDensityBlockSchedule.blockSpan_tendsto

with exact limit

    etaPairFrameBlockSpan s (K + blockLength K)
      → |s.im| * Real.log (1 + 2 * density).

For the canonical density `1/2`, this becomes

    |s.im| * Real.log 2.

Thus, for `s.im ≠ 0`, the positive-density block span does not tend to zero.
The existing positive-density rotation audit independently records the same
phenomenon through the phase and rotation limits:

    scheduledBlockPhase s K
      → s.im * Real.log (1 + 2 * density),

    scheduledBlockRotation s K
      → exp (I * s.im * log (1 + 2 * density)).

The positive-density module has separate bounded-span/small-angle hypotheses,
such as `SmallAngleAdmissible`, but those do not turn the span into a
shrinking span and do not make the schedule an `EtaPairGrowingBlockSchedule`.

## 4. Exact residual majorant

Let

    σ = s.re,
    t = |s.im|,
    m = criticalMirror s.

The exact existing tail majorant is:

    etaCriticalMirrorDefectPairTailPowerBound s L
      = ‖m‖ * ((L : ℝ)^(-m.re) / m.re)
        + ‖s‖ * ((L : ℝ)^(-σ) / σ).

The block-start residual majorant used by the target domination inequality is

    etaCriticalMirrorBlockStartResidualTailPowerBound s K N
      = t * etaCriticalMirrorDefectPairTailPowerBound s (K + N).

For a standard open-strip point, `m.re = 1 - σ`, so this is exactly

    t * ‖m‖/(1 - σ) * (K + N)^(-(1 - σ))
      + t * ‖s‖/σ * (K + N)^(-σ).

This is an upper bound for the residual tail projection. It is not an exact
formula for the oscillatory residual tail.

## 5. Exact right-side margin lower bound

The primitive right pair margin is the interval integral

    etaCriticalMirrorRightPairMargin s k
      = ∫ x in [2k+1, 2k+2],
          (t² / 4) * x^(-σ - 1) * x^(2σ - 1).

The exact integrand identity already proved is

    x^(-σ - 1) * x^(2σ - 1) = x^(σ - 2).

The certified pair lower bound is:

    (t² / 4) * (2k + 2)^(σ - 2)
      ≤ etaCriticalMirrorRightPairMargin s k.

Consequently, for every finite block of length `N` beginning at `K`, the
certified block lower bound is:

    N * (t² / 4) * (2(K + N) + 2)^(σ - 2)
      ≤ etaCriticalMirrorRightBlockMarginSum s K N.

For the canonical positive-density choice `N = K`, the residual majorant and
half of the certified margin, after normalization by `K^(σ - 1)` on the right
side `σ > 1/2`, have the following limiting upper/lower constants:

    residual upper constant:
      t * ‖m‖/(1 - σ) * 2^(-(1 - σ)),

    half-margin lower constant:
      (t² / 8) * 4^(σ - 2).

The second residual component is asymptotically negligible here because
`K^(1 - σ) * K^(-σ) = K^(1 - 2σ) → 0`.

A sufficient constant inequality for the current bounds would therefore be:

    t * ‖m‖/(1 - σ) * 2^(-(1 - σ))
      < (t² / 8) * 4^(σ - 2).

This inequality is not proved uniformly for all explicit off-critical points
in the strip. In particular, the current bounds contain a factor linear in
`t` on the residual side and quadratic in `t` on the margin side.

## 6. Exact left-side margin lower bound

The primitive left pair margin is:

    etaCriticalMirrorLeftPairMargin s k
      = ∫ x in [2k+1, 2k+2],
          (t² / 4) * x^(-σ - 1).

The certified pair lower bound is:

    (t² / 4) * (2k + 2)^(-σ - 1)
      ≤ etaCriticalMirrorLeftPairMargin s k.

For a block of length `N` beginning at `K`:

    N * (t² / 4) * (2(K + N) + 2)^(-σ - 1)
      ≤ etaCriticalMirrorLeftBlockMarginSum s K N.

For `N = K`, normalize by `K^(-σ)` on the left side `σ < 1/2`:

    residual upper constant:
      t * ‖s‖/σ * 2^(-σ),

    half-margin lower constant:
      (t² / 8) * 4^(-σ - 1).

The mirror residual component is negligible here because
`K^σ * K^(-(1 - σ)) = K^(2σ - 1) → 0`.

The corresponding sufficient current-bound inequality would be:

    t * ‖s‖/σ * 2^(-σ)
      < (t² / 8) * 4^(-σ - 1).

Again, this is a pointwise parameter inequality, not a proved uniform fact
for the off-critical strip. It cannot repair the schedule incompatibility with
the existing shrinking-frame theorem.

## 7. Rate balance versus schedule contract

For a hypothetical `N(K) ≍ ρK`, the relevant powers match:

    right residual: K^(-(1 - σ)),
    right margin:   K^(σ - 1),

and

    left residual:  K^(-σ),
    left margin:    K^(-σ).

This is the rate-balance signal identified by ZDI-006. It does not prove a
strict inequality because the constants above remain.

More importantly, the rate-balanced candidate has relative length tending to
`ρ`, not zero. Therefore it cannot be inserted into the existing
`EtaPairGrowingBlockSchedule` common-frame certificates. The correct conclusion
is not that positive-density exact-tail domination is impossible; it is that
the current fixed-frame proof route cannot certify it under its actual schedule
fields.

## 8. Exact tail versus current majorant

The audit compares:

    current residual upper majorant
      < half of current certified margin lower bound.

Failure or unavailability of this comparison would be an **O-BOUND** result,
not a theorem that the exact oscillatory Eta tail cannot be dominated. Here the
stronger and earlier result is **O-SCHEDULE**: the positive-density block is
not admissible for the old shrinking-frame schedule contract at all.

No claim is made that the exact residual tail has the size of its power
majorant, and no exact-tail domination theorem is asserted.

## 9. Candidate classification

| Candidate | Classification | Reason |
|---|---:|---|
| `N(K)=K` plugged into `EtaPairGrowingBlockSchedule` | O-SCHEDULE | Relative length tends to `1/2`, not `0`. |
| General positive-density block plugged into `EtaPairGrowingBlockSchedule` | O-SCHEDULE | Positive density contradicts the required zero limit. |
| Positive-density rate comparison using current residual majorant and margin lower bound | C1-CONSTANT / O-SCHEDULE | Powers balance, but constants are unproved and the old fixed-frame theorem is unavailable. |
| Exact residual-tail domination for a positive-density schedule | unresolved | Not ruled out by the majorant audit; requires different geometry or a sharper exact estimate. |
| Generic `GlobalLowerBound`, `NoCancellation`, or `Coercive` provider | RED / UNTRUSTED boundary | Would package the RH-closing step and is not introduced. |

The overall ZDI-007 result is **O-SCHEDULE** for the existing fixed-frame
transport contract. It is not C2-CONSTANT.

## 10. Axiom audit and validation

The new load-bearing compatibility theorems were checked with `#print axioms`.
Each has exactly:

    [propext, Classical.choice, Quot.sound]

No `sorryAx` occurs.

Focused validation passed:

    ./lean-build.sh DkMath.RH.CFBRC.EtaCriticalMirrorPositiveDensityScheduleCompatibilityAudit

`git diff --check` also passes. No commit, push, CI run, or full-project build
is claimed.

## 11. Global RH frontier and ZDI-008 recommendation

The global RH frontier has not moved. The new result mechanically prevents the
positive-density candidate from being smuggled into the old shrinking-frame
theorem, while preserving the distinction between rate feasibility and actual
constant domination.

The single smallest next obligation for ZDI-008 is:

> Construct and independently verify a fixed-frame or bounded-span transport
> theorem for a block length comparable to `K`, with an explicit scalar
> functional whose sign survives the unrotated zero equality.

If that geometry cannot be supplied without an RH-equivalent no-cancellation
statement, stop the positive-density branch rather than introducing a generic
provider.
