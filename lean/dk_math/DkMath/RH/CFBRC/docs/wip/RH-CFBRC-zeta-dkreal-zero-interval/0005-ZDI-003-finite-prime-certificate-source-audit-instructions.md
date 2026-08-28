# ZDI-003 — finite prime-certificate source audit instructions

Branch: `wip/RH-CFBRC-zeta-dkreal-zero-interval-260819-v0`

Parent roadmap: `0000-RH-CFBRC-zeta-dkreal-zero-interval-roadmap.md`

Depends on:

- `0002-ZDI-001-RiemannHypothesis-definition-dependency-audit-report.md`
- `0004-ZDI-002-DkReal-common-shrinking-interval-uniqueness-report.md`

## Goal

Find the **smallest existing unconditional source facts** that connect a standard nontrivial Riemann-zeta zero to finite prime / prime-power arithmetic strongly enough to support a future shrinking rational interval certificate for `s.re`.

This task is a **source audit**. It is not yet a new RH proof step and must not manufacture the missing `map_zero` provider.

The desired future handoff shape is:

```text
NontrivialRiemannZetaZero s
  + finite prime / prime-power source at stage n
  -> exact finite identity or rigorous finite bound involving centeredSigma s.re
  -> |s.re - 1/2| <= q n
  -> common shrinking rational intervals
  -> DkReal.eq_of_mem_all_intervals
  -> s.re = 1/2
```

ZDI-003 only determines how far the repository already reaches toward the first finite bound.

## Fixed facts from ZDI-001 and ZDI-002

Do not re-prove the following.

1. The final target is Mathlib's exact `RiemannHypothesis`.
2. Positive-degree CFBRC already proves

```lean
offCriticalCFBRC d σ Θ = 0 ↔ σ = (1 : ℝ) / 2
```

for `0 < d`.
3. Universal standard-zeta `map_zero` is RH-equivalent and is not an independent provider.
4. `DkMath.Analysis.DkReal.eq_of_mem_all_intervals` now proves that two real values lying in every interval of one shrinking `DkReal` representation are equal.
5. Moving-line `*_research_goal` declarations depending on `sorryAx` are excluded from the trusted spine.

## Core audit principle

Do **not** classify a theorem as useful merely because it contains primes, zeta, `centeredSigma`, or a finite sum.

For every candidate theorem record separately:

- **zero provenance**: does the theorem actually start from `NontrivialRiemannZetaZero s` or another independently proved consequence of it?
- **prime provenance**: is the arithmetic expression exactly derived from prime / prime-power source data, or introduced by a new definition?
- **finiteness**: is the relevant object a finite `Finset` sum / finite block / finite cutoff, or does an infinite `tsum`, limit, contour integral, or asymptotic provider enter?
- **coordinate content**: does the conclusion constrain `centeredSigma s.re`, its square, a mirror amplitude difference, or another quantity from which a bound on `s.re - 1/2` can be proved?
- **antecedent realizability**: are all hypotheses already independently proved for standard nontrivial zeros?
- **frontier status**: is any hypothesis or conclusion already equivalent to `RiemannHypothesis`?
- **axiom status**: does the candidate trusted path contain `sorryAx`?

A theorem that is exact and finite but has no zero provenance is a **finite source fact**, not a zero certificate.

A theorem that starts from a zeta zero but uses an RH-equivalent provider is a **frontier**, not a certificate.

## Mandatory starting candidates

Audit the following source families in dependency order. Do not assume their old CFZP numbering represents proof progress.

### A. Standard zero and mirror facts

Inspect:

- `CriticalMirrorZeroBridge.lean`
- `StandardZetaRealAxisClosure.lean`

At minimum classify:

- `nontrivialRiemannZetaZero_re_lt_one`
- `nontrivialRiemannZetaZero_re_pos`
- `nontrivialRiemannZetaZero_mem_openCriticalStrip`
- `riemannZeta_criticalMirror_eq_zero_of_nontrivialRiemannZetaZero`
- `criticalMirror_nontrivialRiemannZetaZero`
- `nontrivialRiemannZetaZero_im_ne_zero`

These are useful only as independently proved zero-side input. They are not prime certificates by themselves.

### B. Exact one-mode prime-power source

Inspect:

- `CosmicFormulaZetaPrimePowerModeProjection.lean`
- its direct dependencies such as `PascalPrimePowerCanonicalFold`, `PrimeMirrorOffsetCore`, and `CriticalMirrorGeometry`

Pay special attention to:

```lean
natCpowNeg_eq_commonRadial_mul_leftAmplitude_mul_cycle

eulerPrimePowerMode_eq_commonRadial_mul_leftAmplitude_mul_cycle

eulerPrimePowerMode_cfzp_pair_factorization
```

Determine exactly which coordinate dependence on

```text
δ = centeredSigma s.re = s.re - 1/2
```

is exposed without any zero assumption.

### C. Exact finite aggregate detector

Inspect:

- `CosmicFormulaZetaMirrorGapBeamProjection.lean`
- `CosmicFormulaZetaFiniteAggregateProjection.lean`
- `PrimeMirrorFiniteEnergy.lean`

Pay special attention to:

```lean
cfzpAggregateMirrorGapUpTo_nonneg
cfzpAggregateMirrorGapUpTo_eq_zero_iff_delta_eq_zero
cfzpAggregateMirrorGapUpTo_eq_delta_sq_mul_gapBeam
```

Record clearly that a finite detector of `δ = 0` is not yet evidence that a zeta zero makes the detector vanish.

Ask whether the exact factorization can instead yield a **quantitative inequality** of the form

```text
δ^2 * positiveFiniteCoefficient <= finiteZeroDerivedError
```

without assuming the error is zero.

Do not invent such an error term in ZDI-003; only identify an already existing source if present.

### D. Exact finite linear Euler / PHZ source

Inspect:

- `CosmicFormulaZetaFinitePolarizationProjection.lean`
- `CosmicFormulaZetaMellinSourceProjection.lean`
- `PascalCenteredXiPrimeSideFiniteResidualMirrorWeightedSourceRecoveryAudit.lean`

Separate the unconditional finite identities from later conditional Mellin / contour transport.

At minimum audit:

```lean
cfzpCanonicalFunctionalReflectionLinearSourceUpTo_eq_canonicalPHZ_difference
cfzpCanonicalFunctionalReflectionLinearSourceUpTo_eq_finiteSymmetricEulerRate
```

For any theorem involving `PascalCenteredXiResidueTransportWindow`, `IntervalIntegrable`, contour safety, top-edge transport, or a rectangle, record those hypotheses explicitly and do not treat them as automatic consequences of a zeta zero.

### E. Existing zeta-zero-driven eta / finite-block facts

Search the complete `DkMath.RH.CFBRC` tree for declarations whose hypotheses include

```lean
NontrivialRiemannZetaZero s
```

and whose conclusions mention finite sums, finite blocks, paired defects, Abel partial sums, prime-power / Euler expressions, or explicit source terms.

Important families to inspect include, but are not limited to:

- `EtaCriticalMirrorPairedFrameFiniteBlockCertificate.lean`
- `EtaCriticalMirrorPairedAbelProjection.lean`
- `EtaCriticalMirrorPairedFrameAbelTailIdentity.lean`
- `EtaCriticalMirrorPairedFrameCompletedZetaTailNearbyEulerDecomposition.lean`
- `EtaCriticalMirrorPairedFrameCompletedZetaFiniteEtaOrbitExpansion.lean`

Do not inherit their old roadmap status. Trace each useful theorem to primitive hypotheses.

A theorem using `tsum`, an eventual statement, a tail limit, or asymptotic cancellation may still be mathematically valid, but classify it separately from a **finite algebraic certificate**.

### F. Explicit-formula singularity / zero ledgers

Inspect declarations such as:

- `PascalCenteredXiExplicitFormulaSingularityLedger.lean`
- zero-window / finite-zero-set modules if relevant

A `def` such as a singularity class or a predicate saying `riemannZeta s = 0 ∧ 0 < s.re ∧ s.re < 1` is only bookkeeping unless a theorem proves the needed relation from `NontrivialRiemannZetaZero`.

Do not use a ledger definition itself as source recovery.

## Required classification

For every candidate worth mentioning, assign one of these primary statuses:

- **S0 — zero-side unconditional**: independently proved consequence of `NontrivialRiemannZetaZero`, but no prime arithmetic yet;
- **S1 — finite prime source unconditional**: exact finite prime / prime-power identity, but no zeta-zero input;
- **S2 — finite zero-to-prime bridge unconditional**: starts from a standard nontrivial zero and reaches finite prime arithmetic with no unresolved provider;
- **S3 — quantitative finite coordinate bound**: an S2 fact that actually bounds `centeredSigma s.re` or its square and could feed a rational interval;
- **C — conditional transport**: valid theorem with additional hypotheses not yet automatically supplied by a standard zeta zero;
- **E — RH-equivalent frontier**: equivalent to RH or to the audited `map_zero` obligation;
- **F — unresolved / untrusted**: `sorryAx`, inconsistent antecedent, unsupported semantic identification, or another unresolved provider.

The most important question is whether any **S3** theorem already exists.

If no S3 theorem exists, determine the strongest available S2 theorem and the exact missing transformation from S2 to S3.

If no S2 theorem exists, determine the closest pair of S0 and S1 facts and the exact missing bridge between them.

## Rational-interval compatibility audit

For the strongest trustworthy candidate, determine whether its conclusion can in principle be converted by elementary ordered-ring reasoning into a bound of one of these forms:

```text
|s.re - 1/2| <= q
```

or

```text
(s.re - 1/2)^2 <= q^2
```

with `q : ℚ`, or first with an explicit nonnegative real quantity that can later be rationally majorized.

Do not require the rationalization step to be implemented in ZDI-003 unless it is completely generic and independent of zeta / primes.

The source quantity must be proved to shrink later; do not define `q n` merely because a shrinking sequence is desired.

## Definition firewall

Do not add a load-bearing definition merely to make a candidate theorem fit the desired interval form.

If a new abbreviation is unavoidable for documentation, it must have an immediate characterization theorem and must not contain the desired conclusion.

In particular, do not introduce:

- a new evaluation `σ`;
- a new strip predicate;
- a growth exponent chosen for sign;
- a PNT / asymptotic provider;
- a new phase coordinate whose defining equation already forces `s.re = 1/2`;
- a zero defect defined to vanish on zeta zeros.

## RH-equivalence firewall

Before promoting any provider, search for an existing theorem proving it equivalent to `RiemannHypothesis` or to universal `map_zero`.

If such an equivalence exists, mark it **E** and stop that route.

Do not use the following as independent source facts:

- universal standard-zeta `map_zero`;
- endpoint-increment balance on all nontrivial zeros;
- fixed-Xi defect vanishing on all safe radii;
- moving-line / interaction assimilation providers already known RH-equivalent;
- any `*_research_goal` declaration depending on `sorryAx`.

## Axiom audit

Run `#print axioms` on the strongest S0, S1, S2, and S3 candidates actually proposed for reuse.

Any `sorryAx` on a proposed trusted path is a hard stop.

Standard `propext`, `Classical.choice`, and `Quot.sound` should be reported separately, as in ZDI-001 and ZDI-002.

## Implementation restraint

ZDI-003 should preferably be documentation-only.

Add a Lean theorem only when a very small missing **meaning-guarantee or source-connection lemma** is already an immediate consequence of trusted declarations and materially improves the audit.

Do not implement a speculative new prime-to-zero theory in this task.

## Required report

Create:

`0006-ZDI-003-finite-prime-certificate-source-audit-report.md`

The report must include:

1. the zero-side trusted starting facts;
2. the finite prime / prime-power trusted source facts;
3. a table of all serious candidates classified S0/S1/S2/S3/C/E/F;
4. exact hypotheses of every S2/S3 candidate;
5. explicit separation of finite identities from infinite / asymptotic / contour transports;
6. axiom results for proposed reusable declarations;
7. the strongest currently available route toward a shrinking interval bound;
8. one precise missing lemma or missing bridge for ZDI-004;
9. an explicit statement whether an S3 certificate already exists.

## Success condition

ZDI-003 succeeds even if the result is negative.

A successful result may be:

```text
No unconditional finite coordinate bound exists yet.
Strongest facts are S0 + S1, and the exact missing bridge is X.
```

That is preferable to introducing a new assumption.

The task is complete when the repository contains a mechanically grounded map from a standard nontrivial zeta zero to the strongest existing finite prime-side fact, with the first genuinely missing bridge identified and no RH-equivalent proposition smuggled in as a provider.
