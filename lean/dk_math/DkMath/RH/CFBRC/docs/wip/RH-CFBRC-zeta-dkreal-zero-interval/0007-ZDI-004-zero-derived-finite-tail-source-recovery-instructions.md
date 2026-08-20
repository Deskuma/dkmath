# ZDI-004 — zero-derived finite-tail source recovery instructions

Branch: `wip/RH-CFBRC-zeta-dkreal-zero-interval-260819-v0`

Parent roadmap: `0000-RH-CFBRC-zeta-dkreal-zero-interval-roadmap.md`

Depends on:

- `0002-ZDI-001-RiemannHypothesis-definition-dependency-audit-report.md`
- `0004-ZDI-002-DkReal-common-shrinking-interval-uniqueness-report.md`
- `0006-ZDI-003-finite-prime-certificate-source-audit-report.md`

## Goal

Identify or expose the **first genuine zero-derived source-recovery identity** of the form

```text
standard nontrivial zeta zero
  -> finite arithmetic observable + mathematically sourced residual = 0
```

with the finite observable preferably derived from primes / prime powers.

This task does **not** yet prove a shrinking interval bound and does **not** try to make the finite mirror Gap vanish.

The purpose is to repair the missing S0 + S1 -> S2 handoff found by ZDI-003.

## Fixed facts

Treat the following as already audited.

1. `DkMath.Analysis.DkReal.eq_of_mem_all_intervals` is the generic final uniqueness interface.
2. Positive-degree CFBRC zero detection is already closed and must not be re-proved.
3. Universal standard-zeta `map_zero` is RH-equivalent and cannot be used as a provider.
4. The finite canonical mirror Gap is an exact source-side detector:

```lean
cfzpAggregateMirrorGapUpTo X δ = 0 ↔ δ = 0
```

when `2 ≤ X`.
5. The finite aggregate has the exact factorization

```lean
cfzpAggregateMirrorGapUpTo X δ =
  δ ^ 2 * cfzpAggregateMirrorGapBeamUpTo X δ
```

but this contains no zero provenance.
6. The current theorem only proves

```lean
0 < cfzpAggregateMirrorGapBeamUpTo X 0
```

at the center. Do not silently treat this as a uniform positive lower bound at an unknown `δ`.
7. ZDI-003 found no prime-side S2 or S3 theorem.

## Important correction to the old proof instinct

Do **not** seek a theorem saying that every finite prime truncation vanishes at a zeta zero.

A global analytic zero generally need not be a zero of a finite truncation. The intended source shape is instead:

```text
finite main term + residual/tail = complete source
```

and, at a zeta zero,

```text
finite main term = - residual/tail.
```

The future quantitative route may then bound the residual and obtain a shrinking finite error.

## Rejected pseudo-S2 pattern

Audit and explicitly reject the following as a source-recovery bridge:

```lean
pascalCenteredXiPrimeSideFiniteEulerRenormalizedZetaResidual X s :=
  riemannZeta s * pascalCenteredXiPrimeSideFiniteEulerCompensator X s
```

The compensator is an exponential and is nonzero. Hence `riemannZeta s = 0` trivially implies the renormalized residual is zero, but the zero remains carried entirely by the `riemannZeta s` factor.

This is useful transport machinery but it is **not** a finite prime observable whose cancellation explains the zero.

A theorem of the schematic form

```text
zetaZero -> zetaValue * nonzeroFinitePrimeFactor = 0
```

must not be classified as S2.

## Log-derivative safety rule

Do not evaluate a declaration involving

```text
- deriv riemannZeta s / riemannZeta s
```

at `hs : riemannZeta s = 0`.

Any log-derivative bridge requiring `riemannZeta s ≠ 0` is a punctured-domain / contour transport theorem and cannot itself be the zero-point S2 bridge.

If such a theorem is useful, record precisely how it is used away from the zero and what independent limiting or residue theorem would be required to return to the zero.

## Mandatory source families to audit

### A. Eta finite-plus-tail pattern — reference pattern, not automatically the target

Inspect:

- `EtaCriticalMirrorPairedTail.lean`
- `EtaCriticalMirrorPairedFrameAbelTailIdentity.lean`
- the smallest dependencies that prove the corresponding eta convergence at a nontrivial zeta zero.

At minimum record the exact role of:

```lean
etaCriticalMirrorDefectPairedPartial_eq_neg_tail_of_nontrivialRiemannZetaZero
```

and

```lean
etaCriticalMirrorDefectPairedPartial_tendsto_zero_of_nontrivialRiemannZetaZero
```

This is an important **pattern witness**:

```text
zero provenance
  -> finite partial + convergent tail = 0
```

but it is not yet a prime-side S2 result.

Do not revive the old eta moving-line / half-plane proof chain. In particular inspect the recorded normalized Abel cancellation decision and keep its failure mode visible: a zero residual formed by cancellation of two nonzero constants is not a zero/nonzero collision.

### B. Finite Euler / PHZ source

Inspect:

- `PascalCenteredXiPrimeSideFiniteEulerRenormalizedZetaResidualAudit.lean`
- `PascalPrimePowerCanonicalFold.lean`
- `CosmicFormulaZetaPrimePowerModeProjection.lean`
- `CosmicFormulaZetaFinitePolarizationProjection.lean`
- `CosmicFormulaZetaMellinSourceProjection.lean`

Determine whether the repository already has an exact decomposition of a standard zeta or completed-zeta quantity into:

```text
finite prime/prime-power expression + explicit remainder
```

on a domain that actually includes nontrivial zeros or admits an independently proved continuation to them.

Do not count a definition whose remainder still contains the complete zeta factor multiplicatively as the desired decomposition.

### C. Domain audit for standard Dirichlet / Euler representations

For every candidate finite-prime decomposition, record the exact real-part hypothesis.

In particular distinguish:

```text
1 < s.re
```

Dirichlet-series / Euler-product identities from facts valid in the open critical strip

```text
0 < s.re < 1.
```

A theorem valid only for `1 < s.re` cannot be instantiated at a nontrivial zeta zero. Do not bridge this domain gap by historical convention or informal analytic continuation.

If the repository / Mathlib already contains an exact continuation theorem suitable for a finite-plus-remainder decomposition in `0 < s.re`, identify the exact declaration and audit its axioms and hypotheses.

### D. Explicit-formula and contour source

Inspect only to answer whether an existing theorem already converts zero information to a prime-side finite main term plus an explicit remainder.

Do not introduce a new rectangle parameter, strip parameter, or asymptotic provider.

If the only available bridge requires contour safety, integrability, or a window not generated from the zero itself, classify it as conditional transport and record the missing realizability theorem.

### E. Existing zero-derived finite arithmetic outside the prime tree

Search the CFBRC tree for theorems with an explicit hypothesis

```lean
hs : NontrivialRiemannZetaZero s
```

and a conclusion containing a finite `Finset` sum / finite endpoint / finite block.

Classify each relevant result by whether it is:

- a genuine finite-plus-tail identity;
- merely a finite detector under an independent zero assumption;
- eventual / asymptotic only;
- dependent on an off-critical side assumption such as `s.re < 1/2` or `1/2 < s.re`;
- RH-equivalent;
- or blocked by a known cancellation obstruction.

The purpose is to reuse a successful **source-recovery mechanism**, not to restart an old closure route.

## Desired S2 theorem shape

The preferred prime-side result, if supported by existing source material, is schematically:

```lean
theorem finitePrimeMain_eq_neg_residual_of_nontrivialZero
    {s : ℂ} (hs : NontrivialRiemannZetaZero s) (X : ℕ) :
    finitePrimeMain X s = - finitePrimeResidual X s
```

where:

- `finitePrimeMain X s` is genuinely finite and prime / prime-power derived;
- `finitePrimeResidual X s` is not defined by rearranging the desired conclusion;
- the equality comes from an independently proved complete-source identity;
- all hypotheses are realizable for every standard nontrivial zero;
- neither side hides an RH-equivalent provider;
- the trusted dependency chain has no `sorryAx`.

The exact names and algebraic form may differ.

A useful weaker form is also acceptable:

```text
norm (finitePrimeMain X s - zeroDerivedTarget s) <= residualBound X s
```

provided the target and residual are independently sourced and the bound is not assumed.

## What ZDI-004 does not need to prove

Do not require in this task:

- a rational `q X`;
- `q X -> 0`;
- a `DkReal` representation specialized to zeta;
- a lower bound for `cfzpAggregateMirrorGapBeamUpTo X δ`;
- `cfzpAggregateMirrorGapUpTo X δ = 0`;
- `centeredSigma s.re = 0`;
- `offCriticalCFBRC ... = 0`;
- `RiemannHypothesis`.

Those are downstream questions.

## Quantitative coefficient warning

If an inequality route later uses

```text
Gap(X, δ) = δ² * B(X, δ),
```

then a bound on `Gap(X, δ)` only yields a bound on `δ` after proving a suitable positive lower bound for `B(X, δ)` on a region known to contain the actual `δ`.

The existing theorem `B(X, 0) > 0` alone is insufficient for an unknown off-center `δ`.

Do not add such a lower bound in ZDI-004 unless it is already present and directly relevant to classifying an existing source bridge.

## Classification for this audit

Use the following labels.

- **Z0** — exact standard-zeta zero fact.
- **A1** — exact finite arithmetic source without zero provenance.
- **T1** — exact finite-plus-tail identity with genuine zero provenance, but not prime-derived.
- **P2** — exact prime/prime-power finite-plus-residual identity with genuine zero provenance.
- **Q2** — quantitative residual bound attached to a P2/T1 source.
- **C** — conditional contour / transport / domain-restricted statement.
- **E** — RH-equivalent frontier.
- **F** — `sorryAx`, inconsistent hypothesis, unsupported semantic identification, or another untrusted provider.

Do not invent a P2 row if none exists.

## Required implementation behavior

Prefer documentation-first completion.

Add a Lean theorem only when it exposes an exact source identity already implicit in trusted definitions and materially sharpens the handoff. Do not create a speculative source definition to make the classification table look complete.

If a useful existing theorem lacks a docstring explaining a critical domain or trust boundary, a small docstring-only change is acceptable.

Do not modify historical failed modules to make them appear successful.

## Required report

Create:

`0008-ZDI-004-zero-derived-finite-tail-source-recovery-report.md`

The report must include:

1. the exact eta finite-plus-tail pattern and why it is T1 rather than prime P2;
2. the audit of the finite Euler renormalized zeta residual and why multiplication by a nonzero finite factor is not S2/P2;
3. a table of all serious candidate prime finite-plus-residual identities and their domains;
4. the exact `s.re` domain of every Dirichlet/Euler/log-derivative theorem considered;
5. any genuine P2 theorem found, including complete dependency and axiom audit;
6. if no P2 exists, the **first precise missing equality** needed to create one;
7. whether an existing Q2 tail/error bound is already available;
8. the known eta cancellation obstruction that prevents simply reviving the old closure route;
9. a recommendation for ZDI-005 that names one mathematical obligation only.

## Stop conditions

Stop and record an obstruction if:

- the candidate prime identity is valid only in `1 < s.re` with no audited continuation to the zero;
- the supposed residual contains `riemannZeta s` multiplicatively so zero provenance is tautological;
- a log derivative is evaluated at a zero despite a nonzero denominator hypothesis;
- a theorem uses an RH-equivalent provider;
- a finite main term is defined by subtracting an arbitrary residual from the desired zero quantity;
- a required window / contour hypothesis is not generated from the zero-side trusted facts;
- or the route again reduces to cancellation of independently nonzero terms without a coordinate estimate.

A domain obstruction or absence of P2 is a valid completion result.

## Verification

Run the narrowest relevant Lean builds for every touched Lean source file.

Run `#print axioms` on every theorem proposed as P2 or Q2 and report the exact axiom set.

Run `git diff --check`.

Do not claim a full RH umbrella build unless it was actually run.

## Completion condition

ZDI-004 is complete when the repository has a mechanically grounded answer to this question:

> From `NontrivialRiemannZetaZero s`, what is the earliest exact finite-main-plus-residual arithmetic identity currently available, and is any such identity genuinely prime-derived on the zero's domain?

The answer may be that no prime-derived P2 bridge exists yet. In that case the report must isolate the first missing equality without manufacturing it.