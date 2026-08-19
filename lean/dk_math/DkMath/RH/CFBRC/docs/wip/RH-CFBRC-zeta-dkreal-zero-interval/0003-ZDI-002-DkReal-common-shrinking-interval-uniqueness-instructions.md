# ZDI-002 — DkReal common shrinking interval uniqueness instructions

Branch: `wip/RH-CFBRC-zeta-dkreal-zero-interval-260819-v0`

Parent roadmap: `0000-RH-CFBRC-zeta-dkreal-zero-interval-roadmap.md`

Depends on: `0002-ZDI-001-RiemannHypothesis-definition-dependency-audit-report.md`

## Goal

Expose the smallest reusable Lean theorem saying that two real values contained in every interval of one `DkReal` shrinking nested rational interval representation are equal.

This task is an **analysis-library interface task**. It is not a zeta theorem, not a prime theorem, and not an RH proof attempt.

Do not introduce a new analytic provider or any new hypothesis about zeta zeros.

## Fixed facts from ZDI-001

Treat the following as already audited and do not re-prove them in this task:

- the exact Mathlib target is `RiemannHypothesis`;
- positive-degree CFBRC zero detection already proves `σ = 1 / 2`;
- the remaining RH-equivalent frontier is the standard-zeta `map_zero` source-recovery obligation;
- no theorem equivalent to RH may be used as an independent provider;
- the moving-line `*_research_goal` declarations depending on `sorryAx` are excluded from the trusted spine.

ZDI-002 must remain completely independent of all of those RH-specific declarations.

## Existing DkReal structure to audit first

Inspect at minimum:

- `DkMath.Analysis.DkReal`;
- `DkMath.Analysis.DkReal.lowerReal`;
- `DkMath.Analysis.DkReal.upperReal`;
- `DkMath.Analysis.DkReal.widthReal`;
- `DkMath.Analysis.DkReal.semanticValue`;
- `DkMath.Analysis.DkReal.semanticValue_mem_interval`;
- `DkMath.Analysis.DkReal.tendsto_widthReal_zero`;
- `DkMath.Analysis.DkReal.eq_semanticValue_of_mem_all_intervals`;
- `DkMath.Analysis.DkReal.semanticValue_eq_of_equiv`.

Search the whole `DkMath.Analysis.DkReal` tree before adding anything. If an equivalent two-point uniqueness theorem already exists, reuse it and document that no new theorem is necessary.

## Preferred theorem

If no equivalent theorem already exists, add the smallest theorem in the existing semantic module, preferably with a statement equivalent to:

```lean
theorem eq_of_mem_all_intervals
    (x : DkMath.Analysis.DkReal) {r s : ℝ}
    (hr : ∀ n, r ∈ Set.Icc (lowerReal x n) (upperReal x n))
    (hs : ∀ n, s ∈ Set.Icc (lowerReal x n) (upperReal x n)) :
    r = s := by
  calc
    r = semanticValue x := eq_semanticValue_of_mem_all_intervals x r hr
    _ = s := (eq_semanticValue_of_mem_all_intervals x s hs).symm
```

The exact theorem name may be adjusted to match local naming conventions, but keep the statement minimal and generic.

Prefer composition of the existing semantic uniqueness theorem over rebuilding the squeeze/convergence argument.

## Meaning guarantee

The theorem must make the following mathematical fact explicit:

```text
one DkReal representation x
  + r belongs to every cast interval of x
  + s belongs to every cast interval of x
  + widths shrink to zero by the DkReal invariant
  -> r = s
```

No additional completeness assumption should be introduced. Completeness is already encapsulated in `semanticValue` and its existing uniqueness theorem.

## Important restraint

Do not specialize the theorem to `1 / 2` in the core analysis module.

Do not mention:

- `riemannZeta`;
- `NontrivialRiemannZetaZero`;
- `RiemannHypothesis`;
- `offCriticalCFBRC`;
- prime counting;
- critical strips;
- zeta zero ordinates;
- any historical CFZP provider.

The analysis theorem should remain useful outside RH.

## Optional corollary

Only if it is genuinely useful and remains generic, a second theorem may expose the same uniqueness principle for a rationally centered interval representation, but do not create a new structure merely for ZDI.

For example, if existing APIs make it natural, a corollary may state that if a real `r` and the cast of a rational `q` belong to every interval of `x`, then `r = q`.

This is optional. The one essential theorem is the two-real common-interval uniqueness theorem.

## Definition audit rule

Avoid new `def` declarations in ZDI-002.

If a new definition appears necessary, stop and justify all of the following before adding it:

1. why existing `DkReal` data cannot express the theorem;
2. exact source provenance of every field;
3. characterization theorem;
4. realizability under the parent invariants;
5. why the definition does not encode a desired later RH conclusion.

A helper theorem is preferred over a helper definition.

## Axiom audit

Run `#print axioms` or an equivalent Lean checker for:

- `eq_semanticValue_of_mem_all_intervals`;
- the new common-interval uniqueness theorem, if added.

Report the exact axiom sets and distinguish standard Lean/Mathlib foundations from `sorryAx`.

Any `sorryAx` dependency is a hard failure for this task.

## Build verification

Run the narrowest relevant build, expected to include:

```text
./lean-build.sh DkMath.Analysis.DkReal.Semantic
```

If the public import surface is changed, also build the corresponding umbrella module that imports it.

Do not touch `DkMath.RH` merely to expose this analysis theorem unless the existing architecture already requires it.

## Required report

Create:

`0004-ZDI-002-DkReal-common-shrinking-interval-uniqueness-report.md`

The report must contain:

1. whether an equivalent theorem already existed;
2. exact theorem added or reused;
3. its dependency path to existing DkReal invariants;
4. confirmation that no RH-specific declaration appears in its proof or imports;
5. axiom-audit result;
6. build commands and results;
7. recommendation for ZDI-003.

## ZDI-003 handoff boundary

Do not begin the finite prime-certificate search inside ZDI-002.

The only handoff ZDI-002 should provide is a theorem of the logical shape:

```text
same shrinking rational interval family
  contains candidate real r at every stage
  contains target real c at every stage
  -> r = c
```

ZDI-003 will separately investigate whether existing unconditional finite prime/zeta facts can construct such a common interval family for `s.re` and `1 / 2`.

## Prohibited actions

Do not:

- add a zeta-specific interval definition;
- assume `s.re = 1 / 2`;
- assume a critical strip;
- import an RH-equivalent frontier;
- use moving-line research goals;
- add `sorry`;
- re-prove real completeness from scratch;
- continue historical CFZP numbering;
- create a long theorem chain around a result that is already a one-line corollary of semantic uniqueness.

## Completion condition

ZDI-002 is complete when the repository exposes, or explicitly identifies as already existing, a small axiom-audited generic theorem that collapses two real points lying in every interval of the same `DkReal` shrinking nested rational representation, with no RH-specific dependency.