# ZDI-004 — zero-derived finite-tail source recovery report

Date: 2026-08-19
Branch: wip/RH-CFBRC-zeta-dkreal-zero-interval-260819-v0

## Scope and conclusion

This report implements the audit instructions in
0007-ZDI-004-zero-derived-finite-tail-source-recovery-instructions.md.
The task is to identify the earliest exact finite-main-plus-residual identity
whose zero provenance is genuine. It is not a shrinking-interval proof and it
does not make the finite mirror Gap vanish.

The result is:

- a genuine Eta finite-plus-tail identity exists and is classified T1;
- finite PHZ and prime-power identities exist and are A1;
- no genuine prime-derived P2 identity was found;
- an Eta residual-tail power bound exists, but no prime-derived Q2 bound is
  available;
- the first missing equality is an independently continued, non-tautological
  finite prime/prime-power source identity at a nontrivial zero.

No new source definition or RH provider was introduced. The only Lean source
change is a docstring on the existing renormalized residual, explicitly
rejecting its use as P2.

## 1. Eta finite-plus-tail pattern: T1

The trusted Eta pattern is in EtaCriticalMirrorPairedTail.lean.

For a nontrivial zero hs,

    summable_etaCriticalMirrorDefectPairTerm_of_nontrivialRiemannZetaZero hs

proves summability from the independently proved strip facts

    0 < s.re
    0 < (criticalMirror s).re.

For every finite pair prefix K, the exact identity

    etaCriticalMirrorDefectPairedPartial K s +
        etaCriticalMirrorDefectPairTail K s =
      ∑' k : ℕ, etaCriticalMirrorDefectPairTerm s k

is proved by the ordinary finite-prefix-plus-tail decomposition of a summable
series. At a nonreal nontrivial zero,

    etaCriticalMirrorDefectPairedPartial_tendsto_zero_of_nontrivialRiemannZetaZero
      hs him

gives the finite partial-sum limit, and the complete sum is then proved zero.
Consequently,

    etaCriticalMirrorDefectPairedPartial_eq_neg_tail_of_nontrivialRiemannZetaZero
      hs him K

states the desired zero-derived finite-plus-tail shape:

    finite paired defect partial K = - remaining infinite tail K.

The exact hypotheses are:

    hs  : NontrivialRiemannZetaZero s
    him : s.im ≠ 0
    K   : ℕ

This is genuine zero provenance, and the finite summand is an exact finite
Eta defect block. It is not prime-derived, so its status is T1 rather than
P2. It also remains a tsum identity; it is not a finite prime certificate.

### Eta tail bounds

A quantitative Eta residual bound is already available:

    norm_etaCriticalMirrorDefectPairTail_le_powerBound
      (hs : 0 < s.re) (hm : 0 < (criticalMirror s).re)
      (hL : 1 ≤ L)

gives

    ‖etaCriticalMirrorDefectPairTail L s‖
      ≤ etaCriticalMirrorDefectPairTailPowerBound s L.

The projected block-start form

    abs_etaCriticalMirrorBlockStartResidualTailProjection_le_powerBound
      hs hm hKN

requires hKN : 1 ≤ K + N. Standard nontrivial zeros supply hs and hm through
the S0 strip facts. There are also eventual schedule statements for growing
blocks.

These are Q2-like bounds attached to the T1 Eta source, but they are not
prime-derived, do not produce a bound on centeredSigma s.re, and the stronger
sign conclusions additionally require an explicit off-critical hypothesis
(1/2 < s.re or s.re < 1/2) and a residual-domination assumption. They do not
close the RH route.

## 2. Normalized Abel cancellation obstruction

The normalized Abel route must not be reclassified as a zero/nonzero
collision. The exact balance theorem has hypotheses

    hs  : NontrivialRiemannZetaZero s
    him : s.im ≠ 0

and proves that the normalized moving and correction constants cancel:

    movingConstant + correctionConstant = 0

while each component is nonzero. The corresponding closure decision explicitly
packages this as a nonzero cancellation certificate. In particular,

    etaCriticalMirrorRightNormalizedAbelClosureDecision hs him

proves a zero residual together with nonzero component witnesses.

This is a valid zero-derived analytic cancellation, but it is not a finite-
plus-tail prime source identity. It also does not yield a coordinate bound.
The exact-gauge obstruction records the same failure mode: removing the known
frame rotation returns the original defect partial, whose fixed projection
still tends to zero. The old moving-line / half-plane closure route remains
excluded.

## 3. Finite PHZ and prime source: A1

The finite prime-power source is exact for every complex argument. The main
identities are:

    cfzpCanonicalFunctionalReflectionLinearSourceUpTo X s
      = pascalPrimePowerPHZCanonicalUpTo X (1 - s)
          - pascalPrimePowerPHZCanonicalUpTo X s

    cfzpCanonicalFunctionalReflectionLinearSourceUpTo X s
      = pascalCenteredXiPrimeSideFiniteSymmetricEulerRate X s

They have only X : ℕ and s : ℂ as arguments. The finite source is genuinely
prime/prime-power derived through canonicalPrimePowerSupportUpTo and the
canonical shadow cost. These are A1: no zero provenance is present.

The von Mangoldt bridge gives exact finite identities:

    pascalPrimePowerPHZFiniteUpTo X s
      = ∑ q ∈ Finset.range (X + 1),
          Λ(q) * q^(-s)

and the corresponding finite L-series partial sum. No real-part hypothesis is
needed for these finite equalities.

The first analytic convergence theorem is domain restricted:

    tendsto_pascalPrimePowerPHZFiniteUpTo_LSeries
      (hs : 1 < s.re)

    tendsto_pascalPrimePowerPHZFiniteUpTo_neg_deriv_riemannZeta_div
      (hs : 1 < s.re)

The limit is the von Mangoldt L-series, equivalently
-deriv riemannZeta s / riemannZeta s. The hypothesis 1 < s.re is not
available for a nontrivial zero, which is only known to satisfy
0 < s.re ∧ s.re < 1. No audited continuation theorem converts this finite
partial-sum limit into a finite-plus-residual equality at a nontrivial zero.

## 4. Audit of finite Euler residual: not P2

The declaration

    pascalCenteredXiPrimeSideFiniteEulerRenormalizedZetaResidual X s

is definitionally

    riemannZeta s *
      pascalCenteredXiPrimeSideFiniteEulerCompensator X s

where the compensator is an exponential of a finite Euler potential and is
proved nonzero. Therefore

    riemannZeta s = 0
      -> pascalCenteredXiPrimeSideFiniteEulerRenormalizedZetaResidual X s = 0

is tautological multiplication by a nonzero factor. The finite prime potential
does not explain the zero and no finite prime cancellation is recovered.
This is the rejected pseudo-S2 pattern from the instructions, so the
declaration is A1 transport machinery / C, not P2.

The log-derivative theorem is also punctured-domain only:

    pascalCenteredXiPrimeSideFiniteEulerRenormalizedZetaResidual_negLogDeriv
      (hs1 : s ≠ 1) (hzeta : riemannZeta s ≠ 0)

It identifies the finite residual log derivative with the ordinary zeta
negative log derivative minus the finite PHZ source. It cannot be evaluated
at hs : NontrivialRiemannZetaZero s, because hzeta contradicts hs.1. The
safe-top theorem obtains this nonzero hypothesis from rectangle safety, not
from a zero.

The finite top-mismatch identities are likewise transport statements. They
require an explicit PascalCenteredXiResidueTransportWindow, a
IsPascalCenteredXiTopLogDerivDecompositionSafe hypothesis, and interval
integrability for the zeta and finite PHZ integrands. Such a window and its
safety hypotheses are not generated by a standard nontrivial zero.

## 5. Prime finite-plus-residual candidates and domains

| Candidate | Exact domain / hypotheses | Status | Reason |
|---|---|---:|---|
| cfzpCanonicalFunctionalReflectionLinearSourceUpTo_eq_canonicalPHZ_difference | X : ℕ, s : ℂ | A1 | Exact finite signed PHZ identity; no zero input |
| cfzpCanonicalFunctionalReflectionLinearSourceUpTo_eq_finiteSymmetricEulerRate | X : ℕ, s : ℂ | A1 | Exact finite Euler identity; no zero input |
| pascalPrimePowerPHZFiniteUpTo_eq_LSeries_partialSum | X : ℕ, s : ℂ | A1 | Exact finite von Mangoldt partial sum; no zero input |
| tendsto_pascalPrimePowerPHZFiniteUpTo_LSeries | 1 < s.re | C | Convergence only in the Euler/Dirichlet half-plane |
| tendsto_pascalPrimePowerPHZFiniteUpTo_neg_deriv_riemannZeta_div | 1 < s.re | C | Same domain; limit has a punctured log derivative |
| pascalCenteredXiPrimeSideFiniteEulerRenormalizedZetaResidual_negLogDeriv | s ≠ 1, riemannZeta s ≠ 0 | C | Punctured-domain identity; forbidden at a zero |
| pascalCenteredXiMellinQuadraticArithmeticApproximant_sub_endpoint_eq_two_mul_primeResidual | hε : 0 < ε, finite residue window W, X : ℕ | C | Exact finite cancellation against an Xi endpoint; no zero provenance |
| tendsto_pascalCenteredXiPrimeSideFiniteCutoffResidual | hε : 0 < ε, W; X → ∞ | C | Fixed-ε cutoff limit, not a zero-point finite identity |
| finite PHZ block / finite tail projection identities | finite X,Y, plus explicit window and integrability where integrated | A1/C | Finite source algebra, but no zero-derived equality |
| top-edge / Mellin source recovery | hSafe, IntervalIntegrable zeta/PHZ and residual terms | C | Conditional contour/transport; no realizable zero provider |

All explicit right-edge and rectangle candidates use
W.rectangle.hσ : 1 < W.rectangle.σ for their safe ordinary-zeta factors.
This is a geometry or contour parameter condition, not the critical-strip fact
0 < s.re ∧ s.re < 1. It cannot be instantiated at the zero itself.

## 6. Explicit-formula and contour audit

The finite arithmetic explicit-formula modules prove fixed-height decompositions
of right-edge integrals into ordinary-zeta and non-prime terms. Their exact
inputs include a differentiable weight and a finite residue transport window.
The rectangle geometry uses 1 < σ; the contour and integrability fields are
explicit inputs.

The outer-contour modules subtract finite principal parts at a finite centered
Xi zero set and prove finite residue identities. These are zero-window or
contour ledgers, not prime finite-main-plus-residual identities. Their
regularized log derivatives are handled away from poles and repaired by local
limits; no theorem was found that evaluates the finite prime PHZ source at a
nontrivial zero and returns an independent residual equality.

The singularity ledger records locations and term risks only. It does not
establish a residue-to-prime source identity.

## 7. Classification summary

| Family | Status | Trusted content |
|---|---:|---|
| Standard zero, mirror, strip, and nonreal-height facts | Z0 | Exact consequences of NontrivialRiemannZetaZero |
| Finite mode, finite PHZ, finite von Mangoldt, finite mirror source | A1 | Exact finite arithmetic identities without zero provenance |
| Eta finite partial plus convergent tail | T1 | Exact zero-derived finite-plus-tail identity, not prime-derived |
| Eta explicit tail/power majorants | Q2 | Quantitative T1 residual bounds; no prime or coordinate conclusion |
| Finite cutoff / Xi endpoint residual identities | C | Exact or limiting transport with window/ε hypotheses |
| Euler log-derivative identities | C | 1 < s.re or riemannZeta s ≠ 0 only |
| Universal map_zero, endpoint balance, fixed-Xi defect closure | E | RH-equivalent frontiers |
| *_research_goal or unsupported source identification | F | Excluded from trusted path |

There is no P2 theorem and hence no P2 axiom result to promote. There is
also no prime-derived Q2 theorem. The Eta Q2 bounds were audited only as
non-prime reference bounds attached to T1.

## 8. Axiom audit

The strongest reusable T1, Q2, A1, and conditional transport declarations
were checked with #print axioms from a temporary checker. Every checked
declaration had exactly:

    [propext, Classical.choice, Quot.sound]

The checked declarations included:

    etaCriticalMirrorDefectPairedPartial_tendsto_zero_of_nontrivialRiemannZetaZero
    etaCriticalMirrorDefectPairedPartial_eq_neg_tail_of_nontrivialRiemannZetaZero
    norm_etaCriticalMirrorDefectPairTail_le_powerBound
    abs_etaCriticalMirrorBlockStartResidualTailProjection_le_powerBound
    etaCriticalMirrorRightNormalizedAbelClosureDecision
    pascalCenteredXiMellinQuadraticArithmeticApproximant_sub_endpoint_eq_two_mul_primeResidual
    tendsto_pascalCenteredXiPrimeSideFiniteCutoffResidual
    pascalCenteredXiPrimeSideFiniteEulerRenormalizedZetaResidual_ne_zero
    pascalCenteredXiPrimeSideFiniteEulerRenormalizedZetaResidual_negLogDeriv
    pascalPrimePowerPHZFiniteUpTo_eq_LSeries_partialSum
    tendsto_pascalPrimePowerPHZFiniteUpTo_neg_deriv_riemannZeta_div

No sorryAx occurs. The standard foundational axioms propext,
Classical.choice, and Quot.sound are reported separately and are not
project-local providers.

## 9. First precise missing equality

The first missing equality needed to create a prime-derived P2 bridge is:

    For hs : NontrivialRiemannZetaZero s and every finite cutoff X,

      finitePrimeMain X s + finitePrimeResidual X s =
        zeroDerivedCompleteSource s,

where finitePrimeMain X s is an exact finite prime/prime-power expression,
finitePrimeResidual X s is independently sourced and does not contain
riemannZeta s as a multiplicative factor, and the equality is valid at the
zero's domain 0 < s.re ∧ s.re < 1 (or has a separately proved continuation
to that domain).

A zero theorem would then yield the actual finite-tail relation only if the
complete source is independently shown to vanish:

    finitePrimeMain X s = -finitePrimeResidual X s.

The repository currently has neither this continuation/source equality nor a
zero-derived vanishing theorem for the complete prime source. The existing
1 < s.re L-series limit and the punctured log-derivative identity do not
supply it.

## 10. Recommendation for ZDI-005

P2 is absent, so the next task should have one obligation only:

    Prove one non-tautological finite prime/prime-power main-plus-residual
    equality on the domain of a standard nontrivial zeta zero, with the
    residual independent of a multiplicative riemannZeta s factor.

Do not add a shrinking rational bound, a DkReal representation, a Gap lower
bound, or an RH provider until that equality exists.

## 11. Verification

The changed Lean source was checked with the narrow module build:

    cd /home/deskuma/develop/lean/dkmath/lean/dk_math
    ./lean-build.sh DkMath.RH.CFBRC.PascalCenteredXiPrimeSideFiniteEulerRenormalizedZetaResidualAudit

The finite source and Eta dependencies were checked through the temporary
axiom audit described above. git diff --check is required after the report
is added. No commit, push, CI run, or full RH umbrella build is claimed.
