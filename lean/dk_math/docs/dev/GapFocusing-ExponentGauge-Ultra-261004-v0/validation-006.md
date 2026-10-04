# Instruction 006 validation

All commands ran from `/home/deskuma/develop/lean/dkmath/lean/dk_math`.

## Final build

```bash
lake build DkMath.NumberTheory.Legendre.ParitySafeBlockLocalization \
  DkMathTest.NumberTheory.LegendreBlockLocalization \
  DkMath.NumberTheory.Legendre DkMath
```

Exit0; **10372 Lake jobs**, including replayed dependency jobs. This is not a count of newly compiled modules. [Authoritative final build log](logs/build-final-006.txt).

The changed/new production module, facade, root and regression build successfully. New006 source has no warnings or errors. The root build replays five pre-existing research `sorry` warnings in `ZsigmondyCyclotomicResearch`, `TriominoCosmicBranchA`, `GcdNextResearch`, `TriominoFLT` and `CyclotomicPrincipalization`; the complete new theorem dependency audit below does not contain `sorryAx`.

Earlier logs record local elaboration checkpoints; `calibration-006.txt` is an exploratory log, not the acceptance build. The final build above checks the completed source, including the corrected bounded Fourth and terminal-key normalizations.

## Kernel numerical checks and semantic regressions

[Regression source](../../../DkMathTest/NumberTheory/LegendreBlockLocalization.lean) includes39 named normalization, calibration and theorem declarations. Actual candidate/support and bounded exact-witness Finsets are reduced using ordinary `decide`, with scoped and documented kernel reduction budgets. No evaluation result is used as an unproved numerical assumption.

Kernel values: A=490, I=418, E=106, Q=O=137, residual31, C=F=S=D=0, Near0, prime-square depth209, Fourth14, LowCost223, terminal17, LowCost-after-unused14, uncovered178. The test imports005's checked245/169/97/110 calibrations and conditional148/38 bounds.

Checked outputs include the localization of005's38; three separately justified finite full-cover failures; a square-cell prime with n in21..40; exact readable deficit44, support-only slack490, strongest cancellation slack72; positive fresh cost without collision; and the failure of replacing an upper-side quantity by its lower bound.

## Source inventory

```bash
lake env lean DkMathTest/NumberTheory/LegendreBlockLocalizationInventory.lean
```

Exit0. [Exact checked types](logs/source-inventory-006.txt). Document spellings which differ from live production names are reconciled in [source inventory](source-inventory-006.md).

## Complete axiom audit

```bash
lake env lean DkMathTest/NumberTheory/LegendreBlockLocalizationAxiomAudit.lean
```

Exit0. Source extraction identifies **15/15 new public production theorems +39/39 named regression declarations =54/54**. Each has both `#check` and `#print axioms`. A machine check matches every printed name against the [source manifest](logs/declaration-coverage-006.json), including the empty-axiom output form, and verifies all axiom sets are subsets of `{propext, Classical.choice, Quot.sound}`.

[Raw audit](logs/axiom-audit-006.txt) · [coverage result](logs/axiom-coverage-006.txt) · [audit Lean](../../../DkMathTest/NumberTheory/LegendreBlockLocalizationAxiomAudit.lean).

No new production proof depends on `sorryAx` or an additional axiom. This covers the whole dependency set of each new theorem, not just textual occurrence checks.

## Forbidden constructs and whitespace

The complete changed production files (`ParitySafeBlockLocalization.lean` and facade `Legendre.lean`) and new main regression source were scanned for whole-word `sorry`, `sorryAx`, `admit`, `axiom`, `native_decide`, `unsafe`: zero matches. The audit's `#print axioms` commands are inspection commands, not axiom declarations. [Scan](logs/forbidden-token-scan-006.txt).

`git diff --check` and whitespace checks of each new file against `/dev/null` pass. Relative links in all new006 Markdown files resolve. [Whitespace log](logs/diff-check-006.txt).

## Scope

The finite main block is refuted, but this uses already-existing balance/frontier machinery and exact actual incidence; it does not establish a new38-dependent cancellation obstacle. Generic block mathematics is in production and facade-exported. The particular20-block numerical regression and prime consequence are in `DkMathTest`. No global Legendre provider, asymptotic estimate, new covering framework or new mathematical ledger was added.
