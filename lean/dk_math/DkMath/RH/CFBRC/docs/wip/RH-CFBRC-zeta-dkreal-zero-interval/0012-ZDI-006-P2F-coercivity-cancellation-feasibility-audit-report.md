# ZDI-006 — P2-F coercivity / cancellation feasibility audit report

Date: 2026-08-19  
Branch: `wip/RH-CFBRC-zeta-dkreal-zero-interval-260819-v0`

## Scope and conclusion

This report implements the audit contract in
`0011-ZDI-006-P2F-coercivity-cancellation-feasibility-audit-instructions.md`.
The instruction file determines the audit questions and stop conditions; the
user request is implemented by the documented Q2-F convergence corollaries in
`EtaCriticalMirrorPrimeFactorCoercivityAudit.lean`.

The conclusion is negative for a new closed coercivity route:

- P2-F is an exact prime-factor re-encoding of the old Eta defect partial;
- Q2-F convergence is now proved, but is only an upper-bound/convergence fact;
- local pair and block margins are genuine and quantitative, but their useful
  signs occur in moving pair/block frames;
- sublinear growing schedules have a rate mismatch between the available
  residual-tail majorant and the block-margin lower bound;
- positive-density schedules are rate-balanced, but require an explicit
  constant-domination / correction-domination inequality that remains an
  assumption or an equivalent frontier;
- no fixed functional with an independently proved no-cancellation bound was
  found.

Accordingly, the candidate coercivity routes are **C1/O/E**, not C0 or C2.
ZDI-007 should record this obstruction or search for a genuinely new fixed
scalar invariant. It should not rename residual domination as `Coercive`,
`PositiveEnergy`, or `NoCancellation`.

## 1. P2-F re-encoding audit

ZDI-005 proves the exact equality

    etaPrimeFactorMirrorDefectPairedPartial K s
      = etaCriticalMirrorDefectPairedPartial K s.

The left side is a finite sum over factorization supports of the natural Eta
bases. The right side is the already existing complex Eta defect partial.
Therefore any functional depending only on the value or norm of the whole
finite P2-F partial is mathematically a functional of the old Eta partial.
Prime factorization changes the coordinates of the summands but does not add
an independent positive energy or remove complex-vector cancellation.

In particular, a proposed inequality of the shape

    c(s, |centeredSigma s.re|, K)
      ≤ ‖etaPrimeFactorMirrorDefectPairedPartial K s‖

would be an old-Eta inequality with a prime-factorized right-hand notation.
It is not a new rigidity theorem unless the functional uses an independently
proved prime-side positivity or orthogonality statement. No such statement
was found in the audited dependency path.

The cancellation firewall is therefore active. None of the following passages
is available:

    ‖∑ zₖ‖ small → ∑ ‖zₖ‖ small,
    ‖∑ zₖ‖ small → ∑ |projection zₖ| small,
    ‖∑ zₖ‖ small → ∑ ‖zₖ‖² small.

The exact finite equality and triangle/norm inequalities do not justify a
positive scalar lower bound in the reverse direction.

## 2. Q2-F convergence status

The new module

    DkMath/RH/CFBRC/EtaCriticalMirrorPrimeFactorCoercivityAudit.lean

adds the following documented theorems:

    etaCriticalMirrorDefectPairTailPowerBound_tendsto_zero

    etaCriticalMirrorDefectPairTail_tendsto_zero_of_nontrivialRiemannZetaZero

    etaPrimeFactorMirrorDefectPairedPartial_tendsto_zero_of_nontrivialRiemannZetaZero

The first follows directly from the explicit bound

    ‖criticalMirror s‖ *
      ((L : ℝ)^(-(criticalMirror s).re) / (criticalMirror s).re)
    + ‖s‖ * ((L : ℝ)^(-s.re) / s.re)

and the strip facts

    0 < s.re,
    0 < (criticalMirror s).re.

The second uses the established norm majorant. The third transports this
convergence through the ZDI-005 zero-derived equality. Thus, for a nonreal
nontrivial zero, the P2-F source tends to zero as a complex vector.

This is not coercivity. Convergence of the whole source to zero cannot imply
`centeredSigma s.re = 0` without an independently proved lower-bound or
no-cancellation mechanism.

## 3. Exact local rigidity already proved

Let `σ = s.re`, `t = s.im`, and write

    Wₛ(x) = x ^ (2 * centeredSigma s.re).

The factorization theorem gives the continuous defect coefficient

    Cₛ(x) = criticalMirror s * Wₛ(x) - s.

For positive `x`, its exact coordinates are

    Re Cₛ(x) = (1 - σ) Wₛ(x) - σ,
    Im Cₛ(x) = t (Wₛ(x) - 1).

The common radial factor is

    Rₛ(x) = x ^ (-σ - 1),

and on the right side the radial/transport product is exactly

    Rₛ(x) Wₛ(x) = x ^ (σ - 2).

The local quantitative margin theorems prove:

- if `1/2 < σ`, sufficiently late pair projections in the local rotated
  frame are positive and have a right margin with integrand
  `(t² / 4) * Rₛ(x) * Wₛ(x)`;
- if `σ < 1/2`, sufficiently late pair projections are negative and have a
  left margin with integrand `(t² / 4) * Rₛ(x)`;
- both pair margins are strictly positive for `t ≠ 0`;
- the norm-margin comparison and quantitative block certificates control the
  local-frame transfer error;
- finite block projections dominate one half of the corresponding block
  margin sum in the common frame, under the sublinear growing-block schedule.

The explicit power lower bounds are:

    right pair: (t² / 4) * (2k + 2)^(σ - 2),
    left pair:  (t² / 4) * (2k + 2)^(-σ - 1),

and for a block of length `N` beginning at `K`:

    right block:
      N * (t² / 4) * (2(K + N) + 2)^(σ - 2),
    left block:
      N * (t² / 4) * (2(K + N) + 2)^(-σ - 1).

These are genuine local scalar margins. They do not by themselves control
the unrotated finite P2-F sum.

## 4. Exact role of residual-domination predicates

For `EtaPairGrowingBlockSchedule`, the formal constraints are:

    blockLength K → ∞,
    blockLength K / etaPairFrameLeftEndpoint K → 0.

The second condition is exactly what makes the complete block frame span tend
to zero and permits all subblocks to be compared in one block-start frame.

The tail module defines the explicit majorant

    etaCriticalMirrorBlockStartResidualTailPowerBound s K N
      = |s.im| * etaCriticalMirrorDefectPairTailPowerBound s (K + N).

The load-bearing propositions are:

    S.RightResidualTailDominated s :
      eventually residualTailPowerBound
        < (1 / 2) * rightBlockMarginSum,

    S.LeftResidualTailDominated s :
      eventually residualTailPowerBound
        < (1 / 2) * leftBlockMarginSum.

The whole-tail sign theorems explicitly take these propositions as
hypotheses. They are not derived from `NontrivialRiemannZetaZero`, Q2-F, or
the finite source equality. Thus a proposed P2-F coercivity proof that assumes
one of them is **C1 — conditional old frontier**. A proof that is merely strong
enough to imply one of them without an independent new argument is the same
frontier under a new name.

## 5. Asymptotic rate comparison

Put `σ = s.re` with `0 < σ < 1`, and let `N = N(K)`. The available tail
majorant beginning at `K + N` has order

    B(K + N) = O((K + N)^(-(1 - σ)) + (K + N)^(-σ)).

The available block lower bounds have orders

    M_right(K, N) ≳ N (K + N)^(σ - 2),
    M_left(K, N)  ≳ N (K + N)^(-σ - 1).

### Sublinear schedule

For `N(K) = o(K)` and `N(K) → ∞`, `K + N(K) ~ K`.

On the right (`1/2 < σ`), the slow tail term is
`K^(-(1 - σ))`, while the right block lower bound is
`N(K) K^(σ - 2)`. Their available majorant/lower-bound comparison contains
the factor

    K^(-(1 - σ)) / (N(K) K^(σ - 2)) = K / N(K) → ∞.

On the left (`σ < 1/2`), the slow tail term is `K^(-σ)`, while the left block
lower bound is `N(K) K^(-σ - 1)`, again giving the factor

    K^(-σ) / (N(K) K^(-σ - 1)) = K / N(K) → ∞.

Therefore the existing residual majorant cannot establish the required
residual-domination inequality for the sublinear schedule. This is a
provable-bound rate obstruction, not a claim that the actual oscillatory tail
must have the majorant's size. The present formulas are insufficient for the
route, and no stronger schedule was silently introduced.

### Positive-density schedule

For `N(K) / (2K + 1) → ρ` with `ρ > 0`, the rates are balanced:

    right block margin: order K^(σ - 1),
    right residual bound: order K^(σ - 1) + K^(-σ),

and, symmetrically,

    left block margin: order K^(-σ),
    left residual bound: order K^(-(1 - σ)) + K^(-σ).

The leading orders match on the relevant side, so the positive-density route
is not rejected by rate alone. However, it becomes a constant comparison. The
existing normalized-domination audit proves eventual domination only from an
explicit strict constant gate such as

    RightNormalizedAbelCorrectionConstantDominates,
    LeftNormalizedAbelCorrectionConstantDominates.

Those gates imply earlier correction-tail domination, but they are not facts
for every nontrivial zero and do not arise from P2-F/Q2-F. Hence this route is
C1, not C2. The canonical positive-density schedule is realizable, but the
needed constant inequality remains the mathematical burden.

## 6. Fixed-functional and no-cancellation audit

The exact zero equality is a statement about the unrotated whole Eta source.
The successful sign theorems instead use:

    etaPairBaseRotation s k,
    etaCriticalMirrorBlockStartDefectPairProjection s K j,
    etaCriticalMirrorBlockStartWholeTailProjection s K.

These are pair-local or block-start moving frames. Their positivity is useful
for finite local blocks, but the frame changes with `K`; it is not a single
global real-linear functional applied to the original P2-F equality.

The continuous coefficient factorization supplies pointwise positivity only
after the relevant side and local frame are selected. Pointwise nonvanishing
does not survive a complex finite sum as a positive scalar quantity. No
orthogonality, fixed-sign unrotated projection, or positive quadratic identity
was found that converts the finite P2-F sum into a nonnegative observable.

Thus the direct fixed-functional candidate is **O / frontier**: the existing
functional either rotates with the block, or loses the required sign through
complex cancellation. Squaring individual summands or replacing a sum norm by
a sum of norms would violate the cancellation firewall.

## 7. Candidate classification

| Candidate route | Classification | Audit result |
|---|---:|---|
| P2-F whole-partial norm lower bound from prime-factor notation alone | E / frontier | Exact re-encoding of the old Eta partial; if it forces `centeredSigma = 0`, it is RH-closing mathematics. |
| Sublinear common-frame block plus current residual majorant | O | Available majorant/lower-bound rates have ratio `K / N(K) → ∞`. |
| Sublinear block with `RightResidualTailDominated` or `LeftResidualTailDominated` assumed | C1 | Works only under the old load-bearing residual-domination frontier. |
| Positive-density block with normalized constant domination | C1 | Rates balance and the schedule is realizable, but strict constant gates remain unproved source facts. |
| Pointwise kernel coefficient / local pair margin | C1 | Genuine local rigidity, but only after moving-frame sign and tail domination. |
| Single fixed real-linear functional on the unrotated P2-F sum | O / frontier | No independent fixed-sign or no-cancellation theorem was found. |
| Q2-F power-bound convergence | — | Closed convergence fact, but not coercivity and not a C0/C2 route. |
| A new `Coercive`, `PositiveEnergy`, or `NoCancellation` predicate packaging the desired inequality | E / F boundary | It would merely name the missing RH-closing statement and is not introduced. |

No candidate satisfies C0 or C2. No `sorryAx`, unsupported rectangle-source
identification, or RH provider was added.

## 8. Smallest exact missing inequality

The smallest missing bridge is a non-circular global no-cancellation estimate
for the existing finite source. In a form sufficient for the desired
shrinking bound, it would provide an explicitly constructed functional or
positive coefficient `c_s(K)` such that, for all sufficiently large `K`,

    c_s(K) * |centeredSigma s.re|
      ≤ ‖etaPrimeFactorMirrorDefectPairedPartial K s‖,

with

    etaCriticalMirrorDefectPairTailPowerBound s K / c_s(K) → 0.

The current equality and Q2-F bound would then yield

    |centeredSigma s.re|
      ≤ etaCriticalMirrorDefectPairTailPowerBound s K / c_s(K).

No such `c_s(K)` is currently proved. If `c_s(K)` is bounded below by a
positive fixed quantity, the theorem immediately closes the off-critical
exclusion and is therefore E/RH-equivalent in strength. If it is obtained
from residual domination or a rotating-frame noncancellation hypothesis, it is
C1. This is the exact boundary rather than a missing definition.

## 9. Recommendation for ZDI-007

Do not implement a long P2-F coercivity chain under the current hypotheses.
ZDI-007 should choose one of the following explicit directions:

1. record the sublinear rate obstruction and the positive-density C1 constant
   gate as the formal stopping point; or
2. audit a genuinely new fixed-frame scalar invariant whose sign/positivity
   is independently proved and is not an alias for residual domination.

Any route that only rewrites the Eta partial through prime factors, assumes a
residual-domination predicate, or rotates the cancellation into a new named
predicate should be rejected as a continuation of the same frontier.

## 10. Verification

The new module was checked with:

    ./lean-build.sh DkMath.RH.CFBRC.EtaCriticalMirrorPrimeFactorCoercivityAudit

The focused build succeeds. The final axiom audit checks the two new Q2-F
convergence theorems and reports only the standard Lean/Mathlib axioms
`propext`, `Classical.choice`, and `Quot.sound`; no `sorryAx` occurs.

`git diff --check` also succeeds. No commit, push, CI run, or full-project build
is claimed.
