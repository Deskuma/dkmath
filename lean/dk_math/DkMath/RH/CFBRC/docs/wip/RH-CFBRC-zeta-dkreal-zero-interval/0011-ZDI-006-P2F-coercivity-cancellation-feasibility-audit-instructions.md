# ZDI-006 — P2-F coercivity / cancellation feasibility audit instructions

Branch: `wip/RH-CFBRC-zeta-dkreal-zero-interval-260819-v0`

Parent roadmap: `0000-RH-CFBRC-zeta-dkreal-zero-interval-roadmap.md`

Depends on:

- `0002-ZDI-001-RiemannHypothesis-definition-dependency-audit-report.md`
- `0004-ZDI-002-DkReal-common-shrinking-interval-uniqueness-report.md`
- `0006-ZDI-003-finite-prime-certificate-source-audit-report.md`
- `0008-ZDI-004-zero-derived-finite-tail-source-recovery-report.md`
- `0010-ZDI-005-eta-prime-factor-finite-source-bridge-report.md`

## Goal

Determine whether the newly obtained P2-F / Q2-F bridge contains enough independently proved rigidity to force a quantitative bound on

```lean
|centeredSigma s.re|
```

for a standard nontrivial zeta zero, or whether any such coercivity statement is merely a renamed form of the previously unresolved Eta residual-domination / cancellation frontier.

This task is a **feasibility and obstruction audit**. Do not begin a long coercivity proof chain. Do not introduce a new provider whose content is already the missing RH step.

The desired future shape remains

```text
NontrivialRiemannZetaZero s
  -> |centeredSigma s.re| <= q K
  -> q K -> 0
  -> common shrinking rational intervals
  -> DkReal.eq_of_mem_all_intervals
  -> s.re = 1 / 2.
```

ZDI-006 asks only whether the first quantitative arrow can be sourced non-circularly from the current P2-F/Q2-F data.

## Fixed facts from ZDI-005

The new finite source is exactly characterized by the old Eta defect partial:

```lean
etaPrimeFactorMirrorDefectPairedPartial K s =
  etaCriticalMirrorDefectPairedPartial K s.
```

At a nonreal nontrivial zeta zero:

```lean
etaPrimeFactorMirrorDefectPairedPartial K s =
  -etaCriticalMirrorDefectPairTail K s.
```

and, for `1 <= K`,

```lean
‖etaPrimeFactorMirrorDefectPairedPartial K s‖ <=
  etaCriticalMirrorDefectPairTailPowerBound s K.
```

The prime-factor source is a genuine finite expression over the factorization supports of the natural Eta bases, but it is an exact nonlinear re-expression of the existing Eta finite partial. It is not a new independent positive energy and not a linear von-Mangoldt sum.

Therefore do not assume that prime-factorization by itself removes complex-vector cancellation.

## Mandatory re-encoding audit

First make the following logical boundary explicit in the report.

Because

```lean
etaPrimeFactorMirrorDefectPairedPartial K s =
  etaCriticalMirrorDefectPairedPartial K s,
```

any lower bound whose left side depends only on the norm or value of the whole P2-F partial is mathematically also a lower bound for the old Eta defect partial.

A theorem of the schematic form

```text
c(s, |centeredSigma s.re|, K)
  <= ‖etaPrimeFactorMirrorDefectPairedPartial K s‖
```

is not automatically easier merely because the right side is written through prime factors.

Record whether any proposed coercive functional uses genuinely new prime-factor structure that was unavailable in the old Eta representation. If not, classify it as a re-encoding rather than new rigidity.

## Cancellation firewall

Do not use any invalid implication of the following forms:

```text
‖sum z_k‖ small -> sum ‖z_k‖ small
‖sum z_k‖ small -> sum |projection z_k| small
‖sum z_k‖ small -> sum ‖z_k‖^2 small
```

or conversely turn a small complex vector sum into a positive energy estimate by squaring individual terms after the summation.

Any passage from the complex finite equality to a nonnegative scalar observable must be justified by an exact identity, a fixed-sign projection theorem, orthogonality, positivity, or another independently proved no-cancellation mechanism.

If the required no-cancellation statement is itself equivalent to the desired off-critical exclusion, mark it as a frontier rather than a provider.

## Existing local rigidity that must be audited

Inspect the complete dependency path around:

- `EtaCriticalMirrorDefectKernelFactorization.lean`;
- `EtaCriticalMirrorDefectKernelQuantitativeMargin.lean`;
- `EtaCriticalMirrorDefectPairQuantitativeMargin.lean`;
- `EtaCriticalMirrorDefectPairNormMarginComparison.lean`;
- `EtaCriticalMirrorPairedFrameBlockMarginDomination.lean`;
- `EtaCriticalMirrorPairedFrameFiniteBlockCertificate.lean`;
- `EtaCriticalMirrorPairedFrameGrowingBlockCertificate.lean`;
- `EtaCriticalMirrorPairedFrameGrowingBlockQuantitativeCertificate.lean`;
- `EtaCriticalMirrorPairedFrameGrowingBlockTailRemainder.lean`.

The existing continuous transport weight is

```lean
etaCriticalMirrorContinuousWeightR s x :=
  x ^ (2 * centeredSigma s.re).
```

The defect kernel is exactly factored through the corresponding off-critical coefficient. Audit whether this factorization already supplies a scalar quantity with a quantitative lower bound in `|centeredSigma s.re|`, and whether that quantity survives the finite summation without cancellation.

Do not infer such a lower bound merely from pointwise nonvanishing.

## Existing off-critical margin route

The repository already proves strong local and block statements under an explicit off-critical side assumption.

For example, right of the critical line the growing-block quantitative certificate proves eventually

```text
(1 / 2) * rightBlockMarginSum
  < blockStartDefectBlockProjection,
```

and the left-side analogue gives the corresponding negative projection.

However, the whole-tail collision step currently requires the explicit predicates

```lean
EtaPairGrowingBlockSchedule.RightResidualTailDominated S s
EtaPairGrowingBlockSchedule.LeftResidualTailDominated S s,
```

whose content is eventually

```text
residualTailPowerBound
  < (1 / 2) * blockMarginSum.
```

These predicates are load-bearing antecedents, not previously proved source facts.

### Required comparison

Determine whether a proposed P2-F coercivity theorem would:

1. independently prove one of these residual-domination inequalities;
2. require one of them as an assumption;
3. be logically strong enough to imply one of them;
4. avoid them by using a genuinely different scalar observable.

If cases 2 or 3 apply without a new independent proof, classify the proposal as the **same unresolved frontier under a new name** and stop that route.

## Asymptotic rate audit

Do not treat `RightResidualTailDominated` or `LeftResidualTailDominated` as plausible merely because both sides tend to zero.

Extract the exact formulas of:

```lean
etaCriticalMirrorDefectPairTailPowerBound
etaCriticalMirrorRightPairMargin
etaCriticalMirrorLeftPairMargin
etaCriticalMirrorRightBlockMarginSum
etaCriticalMirrorLeftBlockMarginSum
```

and the exact constraints on `EtaPairGrowingBlockSchedule.blockLength`.

For a fixed off-critical `s` with `0 < s.re < 1`, compare the provable asymptotic orders of:

- the full residual-tail power bound beginning at `K + blockLength K`;
- the right or left block margin sum over `[K, K + blockLength K)`.

Do this separately for

```text
1 / 2 < s.re
```

and

```text
s.re < 1 / 2.
```

The report must state whether the existing formulas make residual domination:

- provable from current schedule assumptions;
- asymptotically impossible for those assumptions;
- rate-balanced / inconclusive;
- dependent on a stronger schedule condition not currently available.

Do not introduce the stronger schedule merely because it makes the inequality true. If a stronger schedule is considered, audit realizability and whether it is compatible with every earlier frame-span requirement.

If a clean asymptotic obstruction can be formalized with a small theorem, adding that theorem is encouraged. If no theorem is needed, documentation-only completion is acceptable.

## Q2-F convergence audit

Check whether the existing explicit power bound is already proved to tend to zero for every standard nontrivial zeta zero.

If the theorem is missing but follows directly from

```text
0 < s.re
0 < (criticalMirror s).re
```

and standard real-power limits, a small generic theorem or zero-specific corollary may be added.

This result by itself is **not coercivity**. It only fixes the fact that the whole P2-F vector tends to zero.

Do not count

```text
‖P2F K s‖ -> 0
```

as progress toward `centeredSigma s.re = 0` unless an independently proved lower-bound mechanism is also present.

## Direct fixed-functional audit

Search for a way to avoid moving-frame cancellation entirely.

The preferred candidate would be a **single fixed real-linear functional** or nonnegative scalar functional, derived from the exact zero equality, such that for every sufficiently late finite source:

```text
functional (finitePrimeFactorMain K s)
```

has a fixed sign or an explicit lower bound whenever `centeredSigma s.re != 0`.

The functional may use already existing geometry, but it must not depend on `K` in a way that rotates away the very cancellation being tested unless the frame motion is independently controlled globally.

Inspect in particular the exact coefficient formulas involving

```text
etaCriticalMirrorContinuousWeightR s x = x ^ (2 * centeredSigma s.re)
```

and the signed vertical projection already used locally.

If every successful sign theorem requires a pair-local or block-start rotating frame, state that explicitly; it means the passage from local rigidity to the single global zero equality remains the hard step.

## Candidate classification

Classify every proposed coercivity route into exactly one of:

- **C0 — closed coercivity**: a trusted theorem already gives a coordinate lower bound from current facts;
- **C1 — conditional old frontier**: works only after `RightResidualTailDominated`, `LeftResidualTailDominated`, or an equivalent unproved no-cancellation condition;
- **C2 — genuine new candidate**: all hypotheses are independently realizable and it provides new scalar rigidity not present in the old Eta representation;
- **O — obstruction**: cancellation, asymptotic rate, or incompatible schedule conditions rule out the proposed route;
- **E — RH-equivalent frontier**: candidate proposition is already equivalent to `RiemannHypothesis` or directly yields it with only audited facts;
- **F — untrusted**: depends on `sorryAx`, unsupported semantic identification, or another excluded provider.

Do not promote C1 to C2 for progress credit.

## RH-equivalence sanity check

Any theorem that, together with the already proved Q2-F convergence, implies

```lean
centeredSigma s.re = 0
```

for every `NontrivialRiemannZetaZero s` is logically an RH-closing theorem.

That does not make such a theorem invalid, but it means its proof must contain the genuine unresolved mathematics. Do not hide that burden inside a newly defined `Coercive`, `Dominated`, `Noncollapse`, `PositiveEnergy`, or `NoCancellation` predicate.

If a proposed predicate is merely a packaging of the missing RH-closing inequality, label it E/frontier or C1 as appropriate.

## Required report

Create:

`0012-ZDI-006-P2F-coercivity-cancellation-feasibility-audit-report.md`

The report must contain:

1. P2-F re-encoding audit;
2. Q2-F convergence status;
3. exact local margin facts already proved;
4. exact role of old residual-domination predicates;
5. asymptotic rate comparison between block margin and residual tail;
6. fixed-functional / no-cancellation audit;
7. candidate classification table C0/C1/C2/O/E/F;
8. the smallest exact inequality still missing for a bound on `|centeredSigma s.re|`;
9. a recommendation for ZDI-007.

## Stop conditions

Stop and report rather than building a new theorem chain if:

- P2-F coercivity reduces exactly to old residual domination;
- a proposed scalarization loses the equality through triangle inequality in the wrong direction;
- the block margin and residual tail have incompatible asymptotic rates;
- the required schedule cannot satisfy both growth and shrinking-frame-span conditions;
- the only remaining candidate is RH-equivalent by construction;
- a new definition merely names the desired conclusion.

A negative result here is valuable: it prevents the new prime-factor notation from reviving the same moving-frame dead end.

## Verification

For every changed Lean module, run the narrowest relevant `./lean-build.sh` target and `#print axioms` on any theorem promoted to C0/C2 or obstruction status.

Run `git diff --check`.

Do not add `sorry`.

## Completion condition

ZDI-006 is complete when the repository has a mechanically grounded answer to this single question:

> Does P2-F/Q2-F add enough independently proved no-cancellation rigidity to force `centeredSigma`, or is the missing coercivity exactly the previously unresolved residual-domination frontier?

Only if a genuine C2 route survives this audit should ZDI-007 implement it. Otherwise ZDI-007 must record or redirect around the obstruction rather than renaming it.
