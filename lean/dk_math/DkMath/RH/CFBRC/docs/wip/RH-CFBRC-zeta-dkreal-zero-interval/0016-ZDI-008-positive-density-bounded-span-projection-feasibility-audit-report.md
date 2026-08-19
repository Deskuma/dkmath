# ZDI-008 — positive-density bounded-span projection feasibility audit report

Date: 2026-08-19  
Branch: `wip/RH-CFBRC-zeta-dkreal-zero-interval-260819-v0`

## Scope and conclusion

This report implements the audit contract in
`0015-ZDI-008-positive-density-bounded-span-projection-feasibility-audit-instructions.md`.
The instruction file supplies the bounded-span feasibility questions; the
user request is implemented by the elementary angle-feasibility theorem in
`EtaCriticalMirrorPositiveDensityBoundedSpanProjectionAudit.lean`.

The result is **O-ROUTE**, with an **O-JOINT / C1-CONSTANT** boundary:

- for each fixed nonreal `s` and each fixed positive safe angle `δ`, a small
  positive density satisfies the limiting phase-span inequality;
- the existing `SmallAngleAdmissible` condition gives a certified bounded-span
  estimate, but does not itself prove a positive-density block-start margin
  theorem;
- the existing positive-density margin theorem uses pair-local rotated
  projections, not one fixed projection for the entire finite block;
- after common normalization, the residual and margin powers balance, but the
  current constants leave a nontrivial parameter inequality and no universal
  density region is proved;
- decreasing density helps the angle condition but makes the margin constant
  tend to zero, so angle feasibility alone cannot close domination.

Thus bounded nonzero phase span is a genuine local feasibility signal, but it
does not produce a jointly certified C2 route. The moving-frame branch should
not be extended into a generic no-cancellation provider.

## 1. Exact positive-density source inventory

The existing source API contains the following exact facts.

For a positive-density schedule `S`:

    leftEndpointRatio K
      = etaPairFrameLeftEndpoint (K + S.blockLength K) /
          etaPairFrameLeftEndpoint K

    leftEndpointRatio K → 1 + 2 * S.density

    scheduledBlockPhase s K
      → s.im * Real.log (1 + 2 * S.density)

    scheduledBlockRotation s K
      → exp (I * (s.im * Real.log (1 + 2 * S.density))).

ZDI-007 added and verified:

    etaPairFrameBlockSpan s K (S.blockLength K)
      → |s.im| * Real.log (1 + 2 * S.density).

For the canonical schedule `etaPairHalfDensityBlockSchedule`, the density is
`1/2`, the block length is exactly `K`, and the phase limit is `s.im * log 2`.

## 2. Schedule realizability

The positive-density schedule structure is realizable; the canonical
half-density schedule is an existing witness. However, ZDI-007 proves that no
positive-density schedule can share a block-length function with
`EtaPairGrowingBlockSchedule`, whose relative length must tend to zero.

Therefore this audit does not construct a fake positive-density instance of
the old growing-block type. A parameterized density schedule is not required
to settle the present obstruction: the existing positive-density structure
already exposes the exact density limit, and the angle-only theorem below is
independent of schedule construction.

## 3. Angle feasibility

For a fixed nonreal point with `t = |s.im| > 0` and a fixed safe angle
`δ > 0`, the new theorem

    exists_positive_density_with_bounded_phase_span

proves

    ∃ ρ > 0,
      |t| * log (1 + 2ρ) < δ.

The proof uses the explicit choice

    ρ = (exp (δ / (2|t|)) - 1) / 2.

This is an exact elementary feasibility statement. It is not a schedule
realizability theorem, does not use a zeta zero, and does not compare a margin
with a residual.

The existing positive-density transport condition is stronger and concrete:

    SmallAngleAdmissible S s :
      32 * etaCriticalMirrorDefectPairNormCoefficient s * S.density < 1.

Together with the exact block-span bound, the existing theorem proves the
uniform subblock estimate

    16 * etaCriticalMirrorDefectPairNormCoefficient s * span < |s.im|.

Thus a sufficiently small density can satisfy the available angular estimate
for each fixed `s`. No uniform density independent of `|s.im|` is obtained or
assumed.

## 4. Fixed block-start projection audit

The repository already defines a legitimate block-start functional:

    etaCriticalMirrorBlockStartDefectPairProjection s K j

and proves exact finite linearity:

    etaCriticalMirrorBlockStartDefectBlockProjection s K N
      = ∑ j < N,
          etaCriticalMirrorBlockStartDefectPairProjection s K j.

This is the right shape for a fixed functional: `K` is fixed while all offsets
`j` in one block are evaluated in the same block-start frame.

However, the existing positive-density module proves instead statements such
as

    rightBlockMarginSum
      < etaCriticalMirrorRotatedDefectProjectionTail,

where the projection is pair-local/rotated. It does not prove the corresponding
positive-density block-start inequality for the whole finite block.

The existing growing-block certificates do prove common-frame pair and block
signs, but their schedule type supplies the relative-length-to-zero field.
They cannot be instantiated with positive density. The gauge audit also shows
that exact gauge removal returns the original unrotated defect partial; it does
not create a new fixed positive energy.

Therefore the fixed scalar mechanism is conceptually available at the
definition level, but its positive-density transport theorem is not currently
available as a proved source fact.

## 5. Exact right-side residual and margin constants

Let

    σ = s.re,
    t = |s.im|,
    m = criticalMirror s,

with `1/2 < σ < 1`, so `m.re = 1 - σ`.

For a positive-density block with

    blockLength K / etaPairFrameLeftEndpoint K → ρ,

the block-start residual majorant is exactly

    t * [
      ‖m‖/(1 - σ) * (K + blockLength K)^(-(1 - σ))
      + ‖s‖/σ * (K + blockLength K)^(-σ)
    ].

After multiplying by
`etaPairFrameLeftEndpoint K^(1 - σ)`, its current upper-limit constant is

    R_right(σ,t,ρ)
      = t * ‖m‖/(1 - σ) *
          (2 / (1 + 2ρ))^(1 - σ).

The original-side residual component is negligible because
`K^(1 - 2σ) → 0`.

The certified right block margin lower bound has normalized limit

    M_right(σ,t,ρ)
      = (t² / 4) * ρ * (1 + 2ρ)^(σ - 2).

If a future fixed-frame transport theorem loses exactly the existing half-
margin factor, the sufficient current-bound comparison would be

    R_right(σ,t,ρ)
      < (t² / 8) * ρ * (1 + 2ρ)^(σ - 2).

No such positive-density fixed-frame theorem or universal parameter inequality
is currently proved.

## 6. Exact left-side residual and margin constants

For `0 < σ < 1/2`, the residual majorant after normalization by
`etaPairFrameLeftEndpoint K^σ` has upper-limit constant

    R_left(σ,t,ρ)
      = t * ‖s‖/σ *
          (2 / (1 + 2ρ))^σ.

The mirror-side residual component is negligible because
`K^(2σ - 1) → 0`.

The certified left block margin lower bound has normalized limit

    M_left(σ,t,ρ)
      = (t² / 4) * ρ * (1 + 2ρ)^(-σ - 1).

With the same prospective half-margin transport loss, the sufficient current-
bound comparison would be

    R_left(σ,t,ρ)
      < (t² / 8) * ρ * (1 + 2ρ)^(-σ - 1).

These are exact normalized consequences of the existing residual majorant and
block-margin lower-bound formulas, not informal matching of powers.

## 7. Joint angle-versus-constant region

The bounded-span condition for a chosen angle `δ` is

    0 < ρ < (exp (δ / |t|) - 1) / 2.

The existing stronger transport condition is

    0 < ρ < 1 /
      (32 * etaCriticalMirrorDefectPairNormCoefficient s).

The right and left residual comparisons additionally require the respective
strict inequalities in Sections 5 and 6.

The dependencies pull in opposite directions:

- reducing `ρ` makes the limiting phase span smaller;
- reducing `ρ` makes both certified margin constants asymptotic to zero;
- the residual constants remain positive as `ρ → 0`;
- the current residual constants contain `‖s‖` or `‖criticalMirror s‖`, while
  the margins contain `|s.im|²`.

Consequently, angle admissibility alone does not produce joint feasibility.
For fixed `s`, some parameter values may satisfy a numerical version of the
constant inequalities, but no universal density region for arbitrary
off-critical standard zeros is proved. In particular, no global bound on
`|s.im|` is assumed.

This is not an impossibility theorem for the exact oscillatory Eta tail. It is
an obstruction to certifying the current residual-majorant / margin-lower-bound
route with the existing positive-density projection API.

## 8. Candidate classification

| Candidate route | Classification | Reason |
|---|---:|---|
| Angle-only bounded positive density for fixed `s` and `δ` | C1 | Exact elementary feasibility is proved, but it gives no margin domination. |
| Existing `SmallAngleAdmissible` estimate | C1 | Certified bounded-span estimate; no positive-density block-start margin theorem. |
| Pair-local rotated projection plus positive-density margin | O-ROUTE | It retains pair-by-pair moving projections and does not solve fixed-sum cancellation. |
| Positive-density fixed block-start projection with current constants | O-ROUTE / C1-CONSTANT | A transport lemma is missing and the normalized constant inequalities are unproved. |
| Universal density for all standard nontrivial zeros | O-JOINT | Angle depends on `|s.im|`; no global height bound is available, and margin constants weaken as density shrinks. |
| Exact Eta-tail domination impossibility | not claimed | The current majorant audit does not determine the exact oscillatory tail. |
| Generic `GlobalLowerBound`, `NoCancellation`, or `Coercive` provider | E / F boundary | Would package the RH-closing step and is not introduced. |

No C0 or C2 route survives this audit.

## 9. Smallest missing transport lemma

The smallest concrete next lemma is a positive-density fixed-block transport
statement, separately on each off-critical side. For example, on the right it
would prove, for a realizable positive-density schedule and an explicit angle
condition,

    (1 / 2) * etaCriticalMirrorRightBlockMarginSum
        s K (S.blockLength K)
      < etaCriticalMirrorBlockStartDefectBlockProjection
          s K (S.blockLength K)

eventually, using one block-start functional for every offset in that block.
The left version has the corresponding negated projection.

This lemma must be proved from exact rotation/projection identities and must
not assume `RightResidualTailDominated`, `LeftResidualTailDominated`, or an
equivalent no-cancellation predicate. Even if it is supplied, the explicit
constant inequalities in Sections 5 and 6 remain a separate gate.

## 10. Recommendation for ZDI-009

Do not begin a generic no-cancellation or coercivity theorem chain.

ZDI-009 should either:

1. implement only the narrow fixed-block transport lemma above and immediately
   test the two explicit normalized constant inequalities; or
2. close the bounded-span moving-frame branch if that lemma requires an
   RH-equivalent global sign statement.

The global RH frontier has not moved. The exact source/remainder bridge and
the global no-cancellation content remain open.

## 11. Axiom audit and validation

The new theorem

    exists_positive_density_with_bounded_phase_span

was checked with `#print axioms` and has exactly:

    [propext, Classical.choice, Quot.sound]

No `sorryAx` occurs.

Focused validation passed:

    ./lean-build.sh DkMath.RH.CFBRC.EtaCriticalMirrorPositiveDensityBoundedSpanProjectionAudit

`git diff --check` also passes. No commit, push, CI run, or full-project build
is claimed.
