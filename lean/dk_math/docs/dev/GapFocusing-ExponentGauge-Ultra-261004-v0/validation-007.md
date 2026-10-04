# Instruction 007 validation

Commands ran from `/home/deskuma/develop/lean/dkmath/lean/dk_math`, Lean4.34.1.

## Acceptance build

```bash
lake build DkMath.NumberTheory.Legendre.ParitySafeMobiusOddCorrection \
  DkMath.NumberTheory.Legendre.ParitySafeIncidenceUpper \
  DkMathTest.NumberTheory.LegendreIncidenceUpper \
  DkMath.NumberTheory.Legendre DkMath
```

Exit0; **10374 Lake jobs**, including replayed dependencies. This is not a count of newly compiled modules. [Authoritative final log](logs/build-final-007.txt).

The changed counting module, new upper module, regression, facade and root all pass. New007 source has no warnings or errors. The root build replays five existing research warnings in `ZsigmondyCyclotomicResearch`, `TriominoFLT`, `TriominoCosmicBranchA`, `GcdNextResearch`, `CyclotomicPrincipalization`; the dependency audit of every new declaration below contains no `sorryAx`.

## Numerical and semantic checks

[Regression](../../../DkMathTest/NumberTheory/LegendreIncidenceUpper.lean) has26 named definitions/theorems. The seven prescribed widths reduce prime/floor caps and existing candidate sets in the Lean kernel. `decide +kernel` handles the irreducible well-founded prime-factor-list definition; no native evaluation is used. Ordinary elaborator `decide` failed at that unfolding boundary during exploration, not at a false inequality.

Checked caps: spacing602, odd endpoints510, best single-divisor425. Main temporal criterion has slack103; unconditional uncovered lower bound65. Widths20,10,5,4,3,2,1 have upper/candidate pairs425/490,162/200,73/90,55/70,45/54,24/32,7/12. Each yields a cover failure, positive uncovered sum and square-cell prime. Shell21 has at least5 uncovered candidates and a prime strictly between441 and484.

Diagnostic checks: shell29 upper31/candidates28 fails the zero-excess criterion; n18,q5 actual seats{1,11,31} refute exact2q adjacency; six residual-wave calibrations account for the7 cap excess above the old actual-incidence diagnostic418; q<=7 cap sum261; shell21 point-factor seat upper17 versus wave7 and mature odd endpoint10. Actual incidence is used only in diagnostic declarations. Structural main/width proofs consume upper caps and candidate demand.

## Source and complete dependency audit

```bash
lake env lean DkMathTest/NumberTheory/LegendreIncidenceUpperInventory.lean
lake env lean DkMathTest/NumberTheory/LegendreIncidenceUpperAxiomAudit.lean
python3 docs/dev/GapFocusing-ExponentGauge-Ultra-261004-v0/checks/check-007.py
```

Inventory and axiom commands exit0. The source-derived manifest covers **22/22 public production declarations** (5 definitions,16 new theorems and1 publicly exposed existing counting theorem), plus **26/26 regression declarations**. Every declaration has `#check` and `#print axioms`; all48 dependency sets are subsets of `{propext, Classical.choice, Quot.sound}`.

[Manifest](logs/declaration-coverage-007.json) · [Raw audit](logs/axiom-audit-007.txt) · [Coverage](logs/axiom-coverage-007.txt) · [Audit source](../../../DkMathTest/NumberTheory/LegendreIncidenceUpperAxiomAudit.lean) · [Inventory output](logs/source-inventory-007.txt).

The counting theorem's proof was not replaced: only its visibility/name and one internal reference changed. The existing incidence ledger is unchanged; the new module is exported by the Legendre facade and root.

## Token, whitespace and document checks

Complete changed production files and all new007 Lean probes have zero whole-word matches for `sorry`, `sorryAx`, `admit`, `axiom`, `native_decide`, `unsafe`. [Scan scope/result](logs/forbidden-token-scan-007.txt). Inspection commands `#print axioms` are not declarations of additional axioms.

`git diff --check` and new-file whitespace checks pass. All local links in the checkpoint documents resolve. [Whitespace result](logs/diff-check-007.txt). The reproducible Python check verifies these checks and exact declaration coverage.

## Scope

This validates an independent structural incidence upper API, Nat-safe deficit consumers and explicit finite width shrinking. It does not validate a uniform-in-N fixed-width theorem or Legendre's conjecture. Two-divisor exclusion and shell29's independent excess certificate are proposals in the report, not implemented results.
