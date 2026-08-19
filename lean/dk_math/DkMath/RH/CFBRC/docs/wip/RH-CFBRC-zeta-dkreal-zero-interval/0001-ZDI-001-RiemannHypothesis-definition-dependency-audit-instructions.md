# ZDI-001 — `RiemannHypothesis` definition dependency audit instructions

Branch: `wip/RH-CFBRC-zeta-dkreal-zero-interval-260819-v0`

Parent roadmap: `0000-RH-CFBRC-zeta-dkreal-zero-interval-roadmap.md`

## Goal

Audit the exact Lean dependency path from Mathlib's `RiemannHypothesis` to the existing DkMath CFBRC bridge before introducing any new proof mechanism.

This task is an **audit and trust-boundary task**, not an RH proof attempt.

The output must identify exactly which declarations are already closed facts, which are merely definitions, which propositions are RH-equivalent frontiers, which hypotheses are conditional, and which declarations depend on unresolved `sorry` or other untrusted providers.

## Required starting point

Use Mathlib's exact declaration:

```lean
def RiemannHypothesis : Prop :=
  ∀ (s : ℂ) (_ : riemannZeta s = 0) (_ : ¬∃ n : ℕ, s = -2 * (n + 1)) (_ : s ≠ 1),
    s.re = 1 / 2
```

Do not replace it by an informal or historically equivalent formulation.

## Declarations that must be traced

At minimum inspect the complete definitions, theorem statements, proofs, imports, and axiom dependencies of:

- `riemannZeta`;
- `RiemannHypothesis`;
- `NontrivialRiemannZetaZero`;
- `riemannHypothesis_iff_nontrivialZero_re_eq_half`;
- `centeredSigma`;
- `centeredSigma_eq_zero_iff`;
- `offCriticalCFBRC`;
- `cfbrcR_eq_zero_iff_x_eq_zero`;
- `offCriticalCFBRC_eq_zero_iff_re_eq_half`;
- `ZeroToCFBRCBridge`;
- `re_eq_half_of_zeroToCFBRCBridge`;
- `StandardZetaToCFBRCBridge`;
- `riemannHypothesis_of_standardZetaToCFBRCBridge`;
- `riemannHypothesis_of_standardZeta_map_zero`;
- `standardZeta_map_zero_iff_riemannHypothesis`.

Also search the full `DkMath.RH.CFBRC` tree for declarations mentioning `RiemannHypothesis`, `NontrivialRiemannZetaZero`, `map_zero`, `iff_riemannHypothesis`, and `research_goal`.

## Definition audit rule

For each load-bearing `def`, do not write merely "definition is accepted because Lean compiled it".

Record all of the following:

1. what primitive data the definition actually expands to;
2. whether its intended semantic interpretation is definitional or needs a separate theorem;
3. whether downstream hypotheses involving it are realizable under the parent type invariants;
4. whether a characterization theorem already exists;
5. whether a missing meaning-guarantee theorem should be added before the definition is trusted downstream.

If a definition was historically introduced only because a later theorem needed a certain sign, strip, exponent, balance, or zero condition, flag it for provenance review even when the definition itself is well-typed.

## Required classification

Classify every load-bearing declaration into exactly one primary category:

- **A — primitive / Mathlib-backed**: imported primitive or Mathlib theorem whose dependency is accepted for this project;
- **B — definitional packaging**: introduces notation or packages an already fixed proposition without adding mathematical content;
- **C — independently Lean-proved DkMath fact**: theorem proved without RH or an RH-equivalent frontier;
- **D — conditional interface**: theorem or structure valid only after an explicit provider is supplied;
- **E — RH-equivalent frontier**: proposition or provider Lean-proved equivalent to `RiemannHypothesis`;
- **F — unresolved / untrusted**: depends on `sorry`, inconsistent antecedent, unsupported semantic identification, or another unresolved provider.

A declaration may have secondary notes, but it must receive one primary category.

## Axiom audit

Run `#print axioms` or equivalent Lean inspection for the final dependency spine.

At minimum report the axiom sets for:

- `cfbrcR_eq_zero_iff_x_eq_zero`;
- `offCriticalCFBRC_eq_zero_iff_re_eq_half`;
- `riemannHypothesis_iff_nontrivialZero_re_eq_half`;
- `riemannHypothesis_of_standardZeta_map_zero`;
- `standardZeta_map_zero_iff_riemannHypothesis`.

If `Classical.choice`, quotient soundness, or standard Mathlib axioms appear, distinguish them from `sorryAx` or project-local unresolved assumptions.

Any appearance of `sorryAx` on the intended trusted spine is a hard stop and must be reported.

## RH-equivalence firewall

Search for propositions already proved equivalent to `RiemannHypothesis`.

Examples known to require special attention include endpoint-balance, fixed-defect-vanishing, moving-line collision / interaction providers, and any declaration whose name ends in `_iff_riemannHypothesis`.

For every such proposition:

- record the exact theorem proving the equivalence;
- mark the proposition **E — RH-equivalent frontier**;
- state explicitly that it may not be used as an independent provider in a non-circular proof of RH.

Do not attempt to prove any of these frontier propositions during ZDI-001.

## Historical CFZP audit boundary

Do not continue the former CFZP forward chain.

The previous branch exposed at least one important pattern: a well-typed predicate could be impossible under its parent structure. Treat this as a general audit rule.

When a historical conditional theorem is encountered, check antecedent realizability before counting it as reusable progress.

Do not introduce a replacement `σ`, strip parameter, growth exponent, PNT provider, asymptotic hypothesis, or phase coordinate in this task.

## New Lean module

Create an audit module only if it adds machine-checkable trust facts that are not already available.

Preferred name if needed:

`DkMath.RH.CFBRC.RiemannHypothesisDefinitionDependencyAudit`

Acceptable contents include small characterization / consistency theorems, explicit frontier aliases, or compile-time axiom inspection helpers.

Do **not** duplicate existing proofs merely to make the audit module look substantial.

If no new theorem is mathematically necessary, documentation-only completion is acceptable and preferable.

## Required report document

Create:

`0002-ZDI-001-RiemannHypothesis-definition-dependency-audit-report.md`

The report must contain:

1. the exact trusted dependency graph;
2. the declaration classification table;
3. the axiom-audit results;
4. all RH-equivalent frontier declarations found;
5. all unresolved or semantically unaudited definitions encountered;
6. the smallest remaining non-circular obligation after removing repackagings;
7. a recommendation for ZDI-002 that does not assume any new analytic fact.

## Expected mathematical conclusion

The audit is expected to test, not assume, the following candidate spine:

```text
NontrivialRiemannZetaZero s
  ↓
[remaining genuine zero-preserving obligation]
  ↓
offCriticalCFBRC d s.re (phase s) = 0
  ↓  existing positive-degree CFBRC theorem
s.re = 1 / 2
  ↓
RiemannHypothesis
```

If the repository proves a sharper or smaller equivalent spine, report that instead.

## Prohibited actions

During ZDI-001 do not:

- add a new speculative mathematical definition to make a proof pass;
- assume the critical strip or critical line;
- use a proposition already known equivalent to RH as a helper provider;
- prove a new asymptotic theorem merely because an old route used one;
- revive CFZP numbering;
- modify historical modules to hide a failed route;
- add `sorry`;
- count a conditional implication as progress without auditing its antecedent.

## Verification

Run the narrowest relevant Lean build for every touched Lean module and then the project RH umbrella import if practical.

Report commands and results exactly.

## Completion condition

ZDI-001 is complete when the repository contains a reviewable report giving a mechanically grounded trust map from Mathlib `RiemannHypothesis` to the smallest genuine unresolved DkMath obligation, with no new speculative provider introduced.
