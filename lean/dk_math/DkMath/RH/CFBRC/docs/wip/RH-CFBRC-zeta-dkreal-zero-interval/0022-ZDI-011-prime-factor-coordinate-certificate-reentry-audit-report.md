# ZDI-011 — prime-factor coordinate certificate re-entry audit report

Date: 2026-08-19  
Branch: `wip/RH-CFBRC-zeta-dkreal-zero-interval-260819-v0`

## Scope and classification

This report implements the audit contract in
`0021-ZDI-011-prime-factor-coordinate-certificate-reentry-audit-instructions.md`.
The instruction file resets the strategy after the ZDI-010 obstruction; the
user request is implemented by the narrow Lean audit module
`EtaCriticalMirrorPrimeFactorCoordinateCertificateReentryAudit.lean`.

The final classification is **O-INFORMATION**.

The existing prime-factor source is genuine and zero-derived, but its finite
whole-sum value is exactly the already audited Eta defect partial.  The
available historical prime-mirror Gap/energy is a valid unconditional
coordinate-lower candidate, but no exact zero-derived upper bridge from the
P2-F source to that positive scalar is present.  Therefore no A/B/C finite
certificate is introduced, and the positive-density/current-majorant route is
not reopened.

## P2-F / Q2-F source recap

ZDI-005 supplies the exact finite prime-factor source

    etaPrimeFactorMirrorDefectPairedPartial K s

and proves

    etaPrimeFactorMirrorDefectPairedPartial K s
      = etaCriticalMirrorDefectPairedPartial K s

for every finite cutoff.  At a standard nonreal zero, the existing source
bridge further gives

    etaPrimeFactorMirrorDefectPairedPartial K s
      = -etaCriticalMirrorDefectPairTail K s,

and ZDI-006 transports the established Eta tail majorant to convergence to
zero.  These are retained as trusted source-spine facts; no new coercivity is
claimed.

The new theorem

    etaPrimeFactorMirrorDefectPairedPartial_eq_separate_endpoint_difference

rewrites the same finite source as

    ∑ k < K, etaPairTerm (criticalMirror s) k
      - ∑ k < K, etaPairTerm s k.

This preserves the two endpoint contributions syntactically, but it does not
provide separate zero-derived identities for those two sums.  The available
zero-derived equation remains their difference, equivalently the old defect
partial.

The prime-factor provenance itself is unchanged: each endpoint mode is
represented by the existing finite factorization-log exponential theorem
`etaPairTerm_eq_primeFactorLogExp_sub` in the ZDI-005 source bridge.

## Closure of the ZDI-007..010 side route

The following route is explicitly closed as `O-CONSTANT / FACT-FIXED`:

    P2-F whole defect
      → moving or positive-density frame
      → certified margin
      → current absolute residual majorant
      → residual domination.

ZDI-007 records schedule incompatibility, ZDI-008 records angle-only
feasibility without fixed-frame transport, ZDI-009 proves the scalar constant
obstruction, and ZDI-010 connects it to the actual residual-majorant and
margin-lower-bound objects.  This audit introduces no renamed residual
domination predicate, schedule, block transport theorem, or RH provider.

## Candidate certificate audit

### 1. Whole-sum norm or projection

Prime-coordinate provenance is present, and the zero-derived upper control is
present through the inherited Eta tail bound.  The coordinate lower control
fails: a norm or projection depending only on the whole sum is a functional of
the old Eta defect partial and does not remove cancellation.

The theorem

    congrArg_of_etaPrimeFactorMirrorDefectPairedPartial_eq_etaDefect

formalizes this factorization for every post-processing function `F`.  Its
zero-derived version transports any such `F` directly to the negative Eta
tail, but still supplies no positive centered-coordinate lower bound.

### 2. Separate endpoint pair

The finite mirror and original endpoint sums are exposed separately in the
new decomposition theorem.  However, no independent zero-derived upper
control for either endpoint scalar is available from the audited source.  A
positive energy formed from the two endpoint coordinates would therefore lack
the required B property.

### 3. Historical finite prime-mirror energy / Gap

The existing APIs provide a strong candidate for C:

    primeMirrorEnergy_nonneg
    primeMirrorEnergyAt_eq_zero_iff_re_eq_half
    cfzpAggregateMirrorGapUpTo_eq_delta_sq_mul_gapBeam

The aggregate Gap is finite, nonnegative, and factors through
`centeredSigma^2` and a nonnegative Gap-Beam.  The new audit module only
reuses its nonnegativity as a candidate fact; it does not identify this
observable with the P2-F source.  No theorem was found that proves the needed

    zero-derived P2-F source → historical Gap/energy upper bound → 0

bridge.  The reverse rigidity statement is not used as a provider.

### 4. Several cutoffs

Consecutive finite cutoffs can recover individual source terms by subtraction
in principle, but the available termwise Eta decay holds throughout the open
strip and is not a new zero-specific centered-coordinate estimate.  No
multi-cutoff positive scalar satisfying A/B/C is available.  The old moving
frame and block-margin construction is not restarted under new names.

## Information-loss firewall

The module proves the concrete generic countermodel

    ∃ z₁ z₂ : ℂ,
      ‖z₁ + z₂‖ = 0 ∧
      0 < ‖z₁‖^2 + ‖z₂‖^2,

using the opposite unit modes `1` and `-1`.  This is not a claim about the
Eta terms; it records why the following passages cannot be inferred from a
small whole sum without an additional source theorem:

    ‖∑ zₖ‖ small → ∑ ‖zₖ‖ small,
    ‖∑ zₖ‖ small → ∑ ‖zₖ‖² small,
    ‖∑ zₖ‖ small → ∑ |projection zₖ| small.

Thus a diagonal positive energy cannot be made zero-derived solely by
rewriting the P2-F whole sum in prime-factor coordinates.

## Boundary and next obligation

No finite radius theorem for `centeredSigma`, no rational shrinking interval,
and no RH consequence is added.  The result is a successful information
audit, not a proof that no future source identity can exist.

The smallest next mathematical obligation is one additional independent
zero-derived identity that upper-bounds a positive prime-coordinate scalar
(for example the historical Gap/energy or an exactly source-matched analogue)
and tends to zero.  Until that bridge exists, pursuing another whole-sum
estimate or the closed positive-density geometry would repeat the audited
information loss.

## Validation

Focused validation from the nested Lake project:

    ./lean-build.sh DkMath.RH.CFBRC.EtaCriticalMirrorPrimeFactorCoordinateCertificateReentryAudit

The build passed.  The load-bearing endpoint decomposition, whole-sum
functional transport, cancellation firewall, and candidate-energy theorem
were checked with `#print axioms`; no `sorryAx` was present.

