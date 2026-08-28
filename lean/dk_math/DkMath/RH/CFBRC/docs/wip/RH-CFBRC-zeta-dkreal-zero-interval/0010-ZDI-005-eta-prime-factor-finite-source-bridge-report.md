# ZDI-005 — Eta prime-factor finite source bridge report

Date: 2026-08-19  
Branch: `wip/RH-CFBRC-zeta-dkreal-zero-interval-260819-v0`

## Scope and result

This report implements the supplied
`0009-ZDI-005-eta-prime-factor-finite-source-bridge-instructions.md`.
The instruction document is the audit contract; the user request is the
source-level implementation and documentation of that contract.

The result is a genuine finite prime-factor bridge:

- every positive natural Eta base is rewritten through its finite
  factorization support and prime logarithms;
- the two bases in each Eta pair, `2 * k + 1` and `2 * k + 2`, are rewritten
  exactly;
- the critical-mirror defect pair and its finite partial sum are therefore
  identified with a finite prime-factor source observable;
- at a nonreal nontrivial zeta zero, that finite observable equals the
  negative of the existing zero-derived Eta tail;
- the existing explicit tail majorant transports to the new finite source.

This is classified **P2-F** (finite prime-factor source, zero-derived tail)
with **Q2-F** (inherited finite-source norm bound).  It is not a von Mangoldt
P2 theorem, does not produce a prime-only infinite tail, and does not prove a
coercive estimate for `centeredSigma`.

## Implemented module

The implementation is in
`DkMath/RH/CFBRC/EtaCriticalMirrorPrimeFactorFiniteSourceBridge.lean`.
The public declarations have Lean docstrings describing their exact finite or
transport role and their formal limitations.

### One-mode factorization identity

The primary exact identity is:

    natCpowNeg_eq_exp_factorization_logSum
      (hn : 0 < n) (s : ℂ)

which proves

    (n : ℂ) ^ (-s)
      = Complex.exp
          (-s *
            (((n.factorization.support.sum fun p =>
                (n.factorization p : ℝ) * Real.log (p : ℝ)) : ℝ) : ℂ)).

The proof uses only the finite identity

    sum_factorization_mul_log_eq_log_nat

and the nonzero condition supplied by `0 < n`.  No Euler-product limit or
Dirichlet-series convergence hypothesis is used.

The Eta-specific corollary

    etaUnsignedVector_eq_primeFactorLogExp

applies the identity to the positive base `m + 1`.

## Exact pair and partial-sum rewrite

The theorem

    etaPairTerm_eq_primeFactorLogExp_sub

rewrites `etaPairTerm s k` as the difference of the two finite
factorization-log exponentials for `2 * k + 1` and `2 * k + 2`.

The theorem

    etaCriticalMirrorDefectPairTerm_eq_primeFactorLogExp_sub

then rewrites

    etaCriticalMirrorDefectPairTerm s k

as the difference between the corresponding factorized pair at
`criticalMirror s` and the factorized pair at `s`.

For readability of the finite source, the module defines
`etaPrimeFactorMirrorDefectPairTerm` and
`etaPrimeFactorMirrorDefectPairedPartial`.  Each new observable is
immediately characterized by an exact theorem:

    etaPrimeFactorMirrorDefectPairTerm_eq_etaCriticalMirrorDefectPairTerm

    etaPrimeFactorMirrorDefectPairedPartial_eq_etaCriticalMirrorDefectPairedPartial

Thus the definitions do not hide a new analytic object or silently change the
existing Eta source.  The finite partial is literally a `Finset.range K` sum
of finite prime-factor expressions.

## Zero-derived P2-F bridge

For

    hs  : NontrivialRiemannZetaZero s
    him : s.im ≠ 0
    K   : ℕ

the principal theorem is:

    etaPrimeFactorMirrorDefectPairedPartial_eq_neg_tail_of_nontrivialRiemannZetaZero
      hs him K

with conclusion

    etaPrimeFactorMirrorDefectPairedPartial K s
      = -etaCriticalMirrorDefectPairTail K s.

The proof is a direct equality chain through

    etaCriticalMirrorDefectPairedPartial_eq_neg_tail_of_nontrivialRiemannZetaZero

and therefore inherits the genuine zero provenance already established for
the Eta finite-plus-tail identity.  The left-hand side is finite and
prime-factorized; the right-hand side is the existing Eta residual tail.  No
semantic identification with a different rectangle remainder is made.

The classification is P2-F rather than the stronger von Mangoldt P2 because
the finite source is a factorization-log representation of Eta natural modes.
The implementation does not claim that this source is a prime-only
Dirichlet-series partial sum.

## Q2-F transport

The theorem

    norm_etaPrimeFactorMirrorDefectPairedPartial_le_powerBound

transports the existing bound

    norm_etaCriticalMirrorDefectPairTail_le_powerBound

to the finite prime-factor source.  Its hypotheses are the same zero and
nonreal assumptions together with `1 ≤ K`; the strip inequalities are derived
from the existing zero lemmas.  The conclusion is the explicit
`etaCriticalMirrorDefectPairTailPowerBound`.

This is Q2-F only in the finite-source sense.  It is not a new estimate on the
factorization-log sum, not a bound on `centeredSigma s.re`, and not a sign or
coercivity theorem.  No estimate for `centeredSigma` was invented to close the
route.

## Formal boundaries and rejected stronger claims

The implementation deliberately does not provide:

- Euler-product convergence at a nontrivial zero;
- a zero-point `-ζ'/ζ` identity;
- a prime-only infinite tail equality;
- a finite source identification with the requested rectangle remainder;
- a coercive lower bound in the DkReal horizontal coordinate;
- an RH-equivalent provider or any `*_research_goal` theorem.

The previously audited Euler-renormalized residual remains a zeta factor
times a nonvanishing finite compensator.  It is not used as the present
prime-factor bridge.

## Axiom audit

A temporary nested-project checker ran `#print axioms` on the one-mode theorem,
the exact pair rewrite, the final zero-derived finite-tail theorem, and the
Q2-F transport theorem.  Every checked declaration has exactly:

    [propext, Classical.choice, Quot.sound]

No checked declaration depends on `sorryAx`.

## Validation

The focused project wrapper command passed:

    ./lean-build.sh DkMath.RH.CFBRC.EtaCriticalMirrorPrimeFactorFiniteSourceBridge

This validates the new module and its imported dependency path; it is not a
claim about a full project build, commit, push, or CI run.

## Single next obligation

The next mathematical obligation is to prove one nontrivial coercive or
coordinate estimate connecting the finite factorized Eta source to the target
`DkReal`/`centeredSigma` quantity, under explicit hypotheses and without an
RH-equivalent provider.  Until that bridge exists, P2-F plus Q2-F does not
close the DkReal shrinking-interval argument.
