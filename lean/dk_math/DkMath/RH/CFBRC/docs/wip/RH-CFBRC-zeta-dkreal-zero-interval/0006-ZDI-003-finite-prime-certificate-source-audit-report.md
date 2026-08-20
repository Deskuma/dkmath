# ZDI-003 — finite prime-certificate source audit report

Date: 2026-08-19  
Branch: `wip/RH-CFBRC-zeta-dkreal-zero-interval-260819-v0`

## Scope and conclusion

This report implements the audit instructions in
`0005-ZDI-003-finite-prime-certificate-source-audit-instructions.md`.
The task is a source audit, not a new RH proof step. No `map_zero` provider,
prime asymptotic, phase coordinate, strip predicate, or zero defect was added.

The strongest trusted route currently present is:

    S0: NontrivialRiemannZetaZero s
        -> open critical-strip, mirror-zero, and nonreal-height facts
    S1: finite prime/prime-power mode and aggregate identities
        -> exact dependence on δ = centeredSigma s.re
    missing bridge:
        the same zero hypothesis must control a finite source-side quantity
        strongly enough to give δ² * positiveCoefficient <= finiteError

No unconditional S2 finite zero-to-prime bridge and no S3 quantitative finite
coordinate bound were found. In particular, the repository does not prove
that a nontrivial zeta zero makes any finite prime-side Gap ledger vanish, nor
does it bound `|s.re - 1 / 2|` by a finite-stage quantity.

The ZDI-002 interface remains available for the eventual final step:

    s.re and 1 / 2 in every common shrinking DkReal interval
        -> DkMath.Analysis.DkReal.eq_of_mem_all_intervals
        -> s.re = 1 / 2

ZDI-003 does not construct those intervals.

## 1. Zero-side trusted starting facts: S0

The declarations in `CriticalMirrorZeroBridge.lean` start directly from
`hs : NontrivialRiemannZetaZero s` and are proved using standard zeta
nonvanishing facts and the completed-zeta functional equation:

| Declaration | Exact conclusion | Status |
|---|---|---:|
| `nontrivialRiemannZetaZero_re_pos hs` | `0 < s.re` | S0 |
| `nontrivialRiemannZetaZero_re_lt_one hs` | `s.re < 1` | S0 |
| `nontrivialRiemannZetaZero_mem_openCriticalStrip hs` | `0 < s.re ∧ s.re < 1` | S0 |
| `riemannZeta_one_sub_eq_zero_of_nontrivialRiemannZetaZero hs` | `riemannZeta (1 - s) = 0` | S0 |
| `riemannZeta_criticalMirror_eq_zero_of_nontrivialRiemannZetaZero hs` | `riemannZeta (criticalMirror s) = 0` | S0 |
| `criticalMirror_nontrivialRiemannZetaZero hs` | reflected nontrivial zero | S0 |
| `nontrivialRiemannZetaZero_im_ne_zero hs` | `s.im ≠ 0` | S0 |

`StandardZetaRealAxisClosure` proves the last fact's closure form by
contradicting independently proved real-axis nonvanishing. These facts give
zero provenance, strip location, reflection, and nonreal height only. None
contains a finite prime sum or prime-power source term.

## 2. Exact finite prime and prime-power source facts: S1

`CosmicFormulaZetaPrimePowerModeProjection.lean` gives an exact one-mode
factorization. For `hq : 0 < q` and arbitrary `s : ℂ`:

    (q : ℂ) ^ (-s) =
      cfzpPrimePowerCommonRadialCarrier q *
        (primeMirrorLeftAmplitude q (centeredSigma s.re) : ℂ) *
          cfzpPrimePowerCycleState q s.im

For an actual Euler mode,
`eulerPrimePowerMode_eq_commonRadial_mul_leftAmplitude_mul_cycle hp k s`
has `hp : Nat.Prime p`, `k : ℕ`, and `s : ℂ`. The packaged
`eulerPrimePowerMode_cfzp_pair_factorization hp k s` has the same hypotheses
and no zeta-zero hypothesis. The horizontal coordinate is explicitly
`δ = centeredSigma s.re = s.re - 1 / 2`; the cycle state has unit norm and
does not remove this dependence.

`PrimeMirrorFiniteEnergy.lean` proves the generic finite detector
`primeMirrorEnergy_eq_zero_iff_delta_eq_zero` under:

    hS      : S.Nonempty
    hmode   : ∀ n ∈ S, 1 < n
    hweight : ∀ n ∈ S, 0 < weight n
    δ       : ℝ

Its complex-point form concludes
`primeMirrorEnergyAt S weight s = 0 ↔ s.re = 1 / 2`. This is a finite
arithmetic detector, not a theorem that a zeta zero has zero energy.

`CosmicFormulaZetaMirrorGapBeamProjection.lean` gives the exact one-mode
identity

    primeMirrorOffsetGap q δ = δ² * cfzpMirrorGapBeam q δ.

`CosmicFormulaZetaFiniteAggregateProjection.lean` specializes this to the
finite support `canonicalPrimePowerSupportUpTo X`:

    cfzpAggregateMirrorGapUpTo_nonneg X δ
      : 0 ≤ cfzpAggregateMirrorGapUpTo X δ

    cfzpAggregateMirrorGapUpTo_eq_zero_iff_delta_eq_zero
      (hX : 2 ≤ X) (δ)
      : cfzpAggregateMirrorGapUpTo X δ = 0 ↔ δ = 0

    cfzpAggregateMirrorGapUpTo_eq_delta_sq_mul_gapBeam X δ
      : cfzpAggregateMirrorGapUpTo X δ =
          δ² * cfzpAggregateMirrorGapBeamUpTo X δ

    cfzpAggregateMirrorGapBeamUpTo_zero_pos
      (hX : 2 ≤ X)
      : 0 < cfzpAggregateMirrorGapBeamUpTo X 0

The support is finite, contains `2` when `2 ≤ X`, and has positive canonical
shadow costs. These are exact source-side coordinate detectors. They do not
provide the missing equality or inequality from a zeta zero.

No existing theorem was found of the form

    δ² * positiveFiniteCoefficient <= finiteZeroDerivedError

or of the stronger form
`cfzpAggregateMirrorGapUpTo X (centeredSigma s.re) = 0` under
`NontrivialRiemannZetaZero s`. Thus the exact `δ²` factorization cannot yet be
converted into a shrinking bound.

## 3. Exact finite linear Euler / PHZ source: S1

`CosmicFormulaZetaFinitePolarizationProjection.lean` proves finite
same-height linear and norm-square identities. It keeps the finite polarized
source separate from the signed PHZ/Mellin channel and introduces no zeta-zero
hypothesis, infinite product, contour identity, or RH statement.

In `CosmicFormulaZetaMellinSourceProjection.lean`, the theorem
`cfzpCanonicalFunctionalReflectionLinearSourceUpTo_eq_canonicalPHZ_difference`
has only `X : ℕ` and `s : ℂ` and states:

    cfzpCanonicalFunctionalReflectionLinearSourceUpTo X s =
      pascalPrimePowerPHZCanonicalUpTo X (1 - s) -
        pascalPrimePowerPHZCanonicalUpTo X s

`cfzpCanonicalFunctionalReflectionLinearSourceUpTo_eq_finiteSymmetricEulerRate`
has the same hypotheses and identifies that source with
`pascalCenteredXiPrimeSideFiniteSymmetricEulerRate X s`. Both are exact finite
prime-power identities. Neither starts from `NontrivialRiemannZetaZero s` nor
provides a bound on `centeredSigma s.re`.

The later theorem
`pascalCenteredXiPrimeSideFiniteTopZetaMismatchScalar_eq_cfzpProjected_half_integral`
is conditional transport, not S2 or S3. In addition to `hε : 0 < ε`, it
requires `hSafe : IsPascalCenteredXiTopLogDerivDecompositionSafe W` and:

    hZeta      : IntervalIntegrable (... pascalXiOrdinaryZetaNegLogDeriv ...) ...
    hPHZ       : IntervalIntegrable (... pascalPrimePowerPHZFiniteUpTo X ...) ...
    hWeighted  : IntervalIntegrable (... residual top Mellin weight/rate ...) ...
    hρ         : IntervalIntegrable (residual scalar density) ...
    hρm        : IntervalIntegrable (reflected residual scalar density) ...
    hPairLeft  : IntervalIntegrable (mirror scalar density) ...
    hPairRight : IntervalIntegrable (mirror scalar density) ...

A standard nontrivial zero does not automatically provide the rectangle
window, top-log-derivative safety, or these integrability hypotheses.

## 4. Candidate classification

| Candidate family / declaration | Primary status | Boundary |
|---|---:|---|
| `nontrivialRiemannZetaZero_re_pos`, `...re_lt_one`, `...mem_openCriticalStrip` | S0 | Zero-side strip only |
| `riemannZeta_one_sub_eq_zero...`, `criticalMirror_nontrivialRiemannZetaZero` | S0 | Reflected zero only |
| `nontrivialRiemannZetaZero_im_ne_zero` | S0 | Nonreal height only |
| `eulerPrimePowerMode_cfzp_pair_factorization` | S1 | Exact one prime-power mode; no zero input |
| `primeMirrorEnergy_eq_zero_iff_delta_eq_zero` | S1 | Exact finite weighted detector |
| `cfzpAggregateMirrorGapUpTo_eq_zero_iff_delta_eq_zero` | S1 | Exact canonical finite detector; no zero input |
| `cfzpAggregateMirrorGapUpTo_eq_delta_sq_mul_gapBeam` | S1 | Exact `δ²` factorization; no finite error bound |
| `cfzpCanonicalFunctionalReflectionLinearSourceUpTo_eq_canonicalPHZ_difference` | S1 | Exact finite signed PHZ source |
| `cfzpCanonicalFunctionalReflectionLinearSourceUpTo_eq_finiteSymmetricEulerRate` | S1 | Exact finite Euler source |
| finite zero-window energy | C | Finite zero-set detector, not zero-to-prime recovery |
| eta finite blocks and Abel partial sums | C | Eventual, `Tendsto`, or `tsum`; not finite certificate |
| Mellin/top-edge source recovery | C | Requires explicit window, safety, and integrability hypotheses |
| universal standard-zeta `map_zero` | E | RH-equivalent frontier |
| fixed-Xi defect, endpoint balance, moving-line assimilation | E | Previously audited RH-equivalent providers |
| `*_research_goal` declarations with `sorryAx` | F | Untrusted / excluded |

There is no S2 row and no S3 row. Therefore there are no exact S2/S3
hypotheses to promote: no audited theorem starts from a standard nontrivial
zero and reaches finite prime arithmetic, and none gives a finite coordinate
bound.

## 5. Finite identities versus transport and asymptotics

The following are genuinely finite:

- one-mode prime-power factorizations in `q` or `p^k`;
- finite canonical support sums over `canonicalPrimePowerSupportUpTo X`;
- finite `Finset` energies and their nonnegative Gap/Beam factorizations;
- finite PHZ differences and finite symmetric Euler rates;
- fixed-length eta blocks as algebraic finite sums.

The following were kept separate from a finite algebraic certificate:

- `∀ᶠ K in atTop` sign or monotonicity statements;
- `Tendsto` statements for growing blocks or Abel tails;
- `∑'` Abel corrections and infinite eta/Euler tails;
- interval integrals over a `PascalCenteredXiResidueTransportWindow`;
- top-edge, contour-safety, completed-zeta, Gamma, and Mellin transport;
- finite zero-window bookkeeping, which is finite but only says what would
  follow if a separately defined aggregate over the zero set vanished.

Replacing a finite source identity by its `Tendsto` or
`IntervalIntegrable` transport does not create the missing finite bound.

## 6. Explicit-formula and zero-ledger audit

`PascalCenteredXiExplicitFormulaSingularityLedger.lean` defines qualitative
location classes such as `pascalExplicitFormulaAtNontrivialZetaZero s` and
marks which explicit-formula term is at risk. The nontrivial-zero class is:

    riemannZeta s = 0 ∧ 0 < s.re ∧ s.re < 1

The ledger theorem only records a term/class pair. It does not prove a finite
prime identity, residue formula, zero-to-source equality, or coordinate
estimate. It is bookkeeping, not S2 or S3.

The finite zero-window modules prove finite-set and mirror-closure facts, and
`pascalCriticalMirrorZeroWindowEnergy_eq_zero_iff` proves an exact detector for
all members of the window. The direction needed for ZDI-003—each standard zero
makes a suitable finite prime-side energy zero or sufficiently small—is absent.

## 7. Axiom audit

A temporary checker from the nested Lake project ran `#print axioms` on the
strongest proposed S0/S1 declarations and on the conditional transport
theorem. Every checked declaration had exactly:

    [propext, Classical.choice, Quot.sound]

The checked declarations were:

    nontrivialRiemannZetaZero_re_lt_one
    nontrivialRiemannZetaZero_mem_openCriticalStrip
    nontrivialRiemannZetaZero_im_ne_zero
    eulerPrimePowerMode_cfzp_pair_factorization
    cfzpAggregateMirrorGapUpTo_eq_zero_iff_delta_eq_zero
    cfzpAggregateMirrorGapUpTo_eq_delta_sq_mul_gapBeam
    cfzpCanonicalFunctionalReflectionLinearSourceUpTo_eq_canonicalPHZ_difference
    cfzpCanonicalFunctionalReflectionLinearSourceUpTo_eq_finiteSymmetricEulerRate
    pascalCenteredXiPrimeSideFiniteTopZetaMismatchScalar_eq_cfzpProjected_half_integral

No `sorryAx` occurs. `propext`, `Classical.choice`, and `Quot.sound` are
standard Lean/Mathlib foundations and are reported separately from unresolved
project assumptions. No S2 or S3 declaration was proposed for reuse, so no
trusted S2/S3 axiom result exists.

## 8. Strongest route and exact missing bridge for ZDI-004

The strongest source-preserving route is:

    NontrivialRiemannZetaZero s
      -> S0 strip/mirror/nonreal-height facts

    finite canonical prime-power source at X
      -> S1 exact identities, including
         Gap(X, δ) = δ² * GapBeam(X, δ)

The first missing bridge is:

    Given hs : NontrivialRiemannZetaZero s and finite stage X,
    prove an unconditional relation between a zero-derived finite observable
    and cfzpAggregateMirrorGapUpTo X (centeredSigma s.re), with either

      cfzpAggregateMirrorGapUpTo X (centeredSigma s.re) = 0

    or

      cfzpAggregateMirrorGapUpTo X (centeredSigma s.re)
        <= finiteZeroDerivedError X s

    where the right side is independently controlled in a later argument.

The existing `δ²` factorization and positivity at `δ = 0` would then permit an
ordered-ring estimate, but no such zero-to-aggregate relation exists. It must
not be supplied by universal `map_zero`, fixed-Xi defect vanishing, endpoint
balance, moving-line assimilation, or another RH-equivalent provider.

This is the recommended ZDI-004 handoff. First prove the source-side observable
and its zero/finite-error connection. Only afterward attempt rational
majorization and the common shrinking `DkReal` interval construction.

## 9. S3 result and verification

**An S3 certificate does not already exist.** The repository currently stops at
S0 plus S1. The exact missing transformation from this pair to S3 is the
finite zero-to-prime source bridge described in Section 8, followed by a
quantitative estimate for `centeredSigma s.re`.

The implementation is documentation-first. Two existing finite aggregate
theorems received Lean docstrings clarifying that their exact source-side
identities do not provide zero provenance or a quantitative zero-derived
bound. No new definition or theorem was added, and no RH-specific provider
was introduced.

The narrow validation commands were:

    cd /home/deskuma/develop/lean/dkmath/lean/dk_math
    ./lean-build.sh DkMath.RH.CFBRC.CosmicFormulaZetaFiniteAggregateProjection
    ./lean-build.sh DkMath.RH.CFBRC.CosmicFormulaZetaMellinSourceProjection

The temporary axiom checker was removed after inspection. No commit, push, CI
run, or full umbrella build is claimed by this report.

