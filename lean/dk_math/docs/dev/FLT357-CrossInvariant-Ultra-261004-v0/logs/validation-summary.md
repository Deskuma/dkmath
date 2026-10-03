# Focused validation — FLT357 pre-audit

Date: 2026-10-04. Working directory for Lean commands:
`/home/deskuma/develop/lean/dkmath/lean/dk_math`.
Toolchain and Mathlib: v4.34.1. Initial source state: `69d44fa3e`.
The existing compiled imports were used; this pre-audit changed only docs and
the three test-only Lean files listed below.

## Commands and results

```bash
lake env lean docs/dev/FLT357-CrossInvariant-Ultra-261004-v0/checks/UnitPowerClassAudit.lean
lake env lean docs/dev/FLT357-CrossInvariant-Ultra-261004-v0/checks/EndpointAudit.lean
lake env lean docs/dev/FLT357-CrossInvariant-Ultra-261004-v0/checks/SourceDependencyAudit.lean
```

All three final commands returned exit0.

| Probe | Scope | Output |
| --- | --- | --- |
| UnitPowerClassAudit | Root-choice unit-class independence in an integrally closed domain; same fixed ramifier; actual normal-domain instances and exponent3/5/7 specializations | [unit-power-class.log](unit-power-class.log) |
| EndpointAudit | Current p3/p5 endpoints, extraction, sectors and descent; current p7 corrected receiver and real-cubic unit criterion; conditional quadratic sectors; exact p3/p5 normalization identities | [endpoint-audit.log](endpoint-audit.log) |
| SourceDependencyAudit | Four named declaration closures, recursively visiting kernel types, bodies including opaque bodies, and inductive constructors; fail on forbidden dependencies/missing declarations/unreadable expected bodies | [source-dependency.log](source-dependency.log) |

The two neutral lemma axiom sets are propext, Classical.choice, Quot.sound.
The named production theorem axiom sets contain only these standard axioms.
Normalization identities have smaller subsets. The output states the exact
hypotheses of the conditional generic sector endpoints.

## Final compiled dependency counts

| Root | Reachable constants | Readable bodies |
| --- | ---: | ---: |
| `Three.fermatThree_no_positive_solution` | 15,283 | 14,092 |
| `Five.flt5Target` | 17,552 | 16,272 |
| `SevenRealCubic.CurrentCarrierPower.currentCarrier_ramified_element_receiver` | 74,075 | 71,420 |
| `SevenRealCubic.CurrentCarrierPower.currentCarrier_ramifiedIdeal_mul_seventh_power` | 74,075 | 71,420 |

Every root has empty forbidden/missing/unreadable lists. All axiom leaves are
propext, Quot.sound, Classical.choice. The explicitly enumerated forbidden
filters cover sorryAx, the pinned completed Mathlib FLT3/FLT4 families and
private proof-family names, and the local FLT3_core/FLT4_core bridges. Pinned
Mathlib has no completed FLT5 file; generic FLT.Basic definitions and conditional
reductions are deliberately not classified as completed external proofs.
The exact filters are saved in the diagnostic code and log.

In particular, importing historical Kummer modules does not make the current
p7 receiver use their sorryAx. This compiled check concerns these four
declaration closures; it does not exclude modules from an import graph.

## Diagnostic corrections and scope

- The first unit-class proof check passed.
- EndpointAudit's first attempt used a wrong namespace and inappropriate ring
  tactics in its two normalization examples. The examples were repaired by
  explicit coordinate identities and kernel decide; the final check passed.
- SourceDependencyAudit's first attempt needed an explicit Nat annotation in
  a diagnostic counter. Its type/value check then passed; constructor traversal
  was added after review and the final strengthened check also passed. Final
  counts above refer to that strengthened check.
- No full Lake build was run. The test-only probes compile against the existing
  production artifacts; they do not claim a fresh rebuild of the entire repo.

The initial inventory is [source-inventory.log](source-inventory.log).
Whitespace, artifact-link/table checks and scoped diff review are recorded in
the final findings checkpoint.
