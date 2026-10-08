# Instruction 008 validation

All commands ran from `/home/deskuma/develop/lean/dkmath/lean/dk_math`, Lean4.34.1.

## Acceptance build

```bash
lake build DkMath.NumberTheory.Legendre.ParitySafeIncidenceUpper \
  DkMath.NumberTheory.Legendre.ParitySafeExcessCertificate \
  DkMathTest.NumberTheory.LegendreHybridProvider \
  DkMathTest.NumberTheory.LegendreHybridClassification \
  DkMath.NumberTheory.Legendre DkMath
```

Exit0; **10378 Lake jobs**, including replayed dependencies, not10378 newly compiled modules. [Authoritative final build log](evidence/MANIFEST.md#log-532339d998a07169).

The expanded upper module, new certificate module, mandatory regression, bounded classification/data, facade and root pass. The final008 sources have no warnings/errors. Five existing root research warnings are replayed in `ZsigmondyCyclotomicResearch`, `TriominoCosmicBranchA`, `GcdNextResearch`, `CyclotomicPrincipalization`, `TriominoFLT`; the full new dependency audit below contains no `sorryAx`.

Earlier focused logs record development checkpoints. The initial classification log includes an unscoped-budget linter warning; the final source scopes that option to individual finite reductions and the acceptance log is clean for008 source.

## Kernel regressions and certificate provenance

[Mandatory regression](../../../DkMathTest/NumberTheory/LegendreHybridProvider.lean) checks: cap425→418 in the main block, cap7→6 at shell21, all six previously loose waves corrected, the two separate failed-formula diagnostics, exact shell29 point identities, actual candidate/support witness conditions, local/card/excess lower bounds, U29≥1 and a prime in(841,900).

No global I29 or E29 evaluation occurs in the hybrid proof. The certified prime subsets and two distinct seats supply E29≥4 through the production local aggregation theorem. All support membership conditions are checked via the actual production iff: prime, bounded by anchor, odd, not dividing anchor, and dividing the actual point.

[Bounded classification](../../../DkMathTest/NumberTheory/LegendreHybridClassification.lean) checks all99 cap/candidate pairs, the disjoint59/10/30 partition, exact finite certificate sets, all successful uncovered/prime consequences, and all30 budget-obstruction inequalities. It also checks counterexamples77 and91 to two proposed anchor-factor class criteria, and numerical strict gains77,85,95 over the old cap with the same excess budget4.

[Exploration script](checks/classify-008.py) generates finite data in [ClassificationData](../../../DkMathTest/NumberTheory/LegendreHybridClassificationData.lean); generated values are proved separately in Lean using `decide +kernel`. The script is not a trusted oracle. It does not compute whole-shell incidence/excess sums. [JSON data](evidence/MANIFEST.md#log-06b786cc4416c28e) · [Summary](evidence/MANIFEST.md#log-049be64e2b4c4056).

## Inventory and complete dependency audit

```bash
lake env lean DkMathTest/NumberTheory/LegendreHybridProviderInventory.lean
lake env lean DkMathTest/NumberTheory/LegendreHybridProviderAxiomAudit.lean
python3 docs/dev/GapFocusing-ExponentGauge-Ultra-261004-v0/checks/check-008.py
```

Inventory and axiom commands exit0. The source-derived audit covers **20/20 new public production declarations** (3 definitions,17 theorems). It additionally covers the21 existing public declarations in the changed upper module, so the production audit is41 declarations in total. All36 new named regression/data declarations are also covered: **77/77** declarations have `#check` and `#print axioms` and dependency sets contained in `{propext, Classical.choice, Quot.sound}`.

[Source manifest](evidence/MANIFEST.md#log-c635a9ef11f97835) · [Raw dependency audit](evidence/MANIFEST.md#log-4fd5a822b5f64237) · [Coverage](evidence/MANIFEST.md#log-ca1d8f021bc84441) · [Audit Lean](../../../DkMathTest/NumberTheory/LegendreHybridProviderAxiomAudit.lean) · [Exact source types](evidence/MANIFEST.md#log-3070195d1190e582).

The private odd-divisor counting helper is reached through the audited public pair theorem; the audit inspects complete theorem dependency sets. The required but absent `ParitySafePrimeSupport` filename is reconciled to actual production modules in [source inventory](source-inventory-008.md).

## Token, whitespace and document checks

The complete changed production files and all008 Lean probes have zero whole-word matches for `sorry`, `sorryAx`, `admit`, `axiom`, `native_decide`, `unsafe`. [Complete scan scope](evidence/MANIFEST.md#log-d737fef31c238043). Inspection commands `#print axioms` introduce no additional assumptions.

`git diff --check` and new-file whitespace checks pass. All local links in checkpoint documents resolve. [Whitespace log](evidence/MANIFEST.md#log-39da13d1a3d1aea5). The reproducible [checker](checks/check-008.py) verifies source-derived declaration coverage, trust sets, scan scope and these document checks; `--generate` refreshes only the audit source/manifest.

## Semantic scope

Generic cap refinement, unconditional finite support certificates, hybrid consumers and the infinite no-pair-improvement theorem are production and facade exported. Shell29 and bounded numerical/classification results live in `DkMathTest`. No independent global incidence/excess/gap ledger is added. The finite budget obstruction and successful69-shell classification are not uniform Legendre results. No unconditional infinite class of prime-existence providers is claimed.
