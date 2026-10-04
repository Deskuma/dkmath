# Instruction 009 validation

All commands run from `lean/dk_math`, with the repository's Lean4.34.1 toolchain. Baseline `cfd1d5f12` was clean. Acceptance evidence covers the changed Legendre facade, the new production CRT module, mandatory/CRT/classification regressions and complete new-declaration dependencies.

## Builds and kernel inspection

The final combined command succeeded with10383 jobs:

```sh
lake build DkMath.NumberTheory.Legendre.ParitySafeCRTSeat \
  DkMathTest.NumberTheory.LegendreAdaptiveCertificate \
  DkMathTest.NumberTheory.LegendreCRTSeat \
  DkMathTest.NumberTheory.LegendreAdaptiveClassification \
  DkMath.NumberTheory.Legendre DkMath
```

[Final build log](logs/build-final-009.txt). The new modules have no warnings. Root replay includes five existing unrelated research declarations using `sorry`; the complete dependency inspection below establishes that none is used by the new declarations. A successful root build alone is not treated as proof of global absence of admissions.

[Mandatory focused build](logs/build-mandatory-009.txt) checked41/91 without full incidence/excess evaluation. [Classification focused build](logs/build-classification-009.txt) checked all30 previous Class2 shells, actual witnesses, charges, partition, five successful prime conclusions and25 charge-budget obstructions. [CRT development log](logs/build-crt-009.txt) and [earlier CRT regression checkpoint](logs/build-crt-regression-009.txt) retain intermediate failures/warnings for investigation; the final combined log supersedes them for acceptance.

Both inventory and axiom probes were executed through `lake env lean` and exited0:

```sh
lake env lean DkMathTest/NumberTheory/LegendreAdaptiveCertificateInventory.lean
lake env lean DkMathTest/NumberTheory/LegendreAdaptiveCertificateAxiomAudit.lean
```

[Initial source types](logs/source-inventory-009.txt), [final source types](logs/source-inventory-final-009.txt), [complete axiom output](logs/axiom-audit-009.txt). All numerical proofs use ordinary kernel checking (`decide`, including scoped `decide +kernel`); no native evaluator trust is introduced.

## Complete declaration coverage

[Manifest](logs/declaration-coverage-009.json) enumerates66 new declarations:

| Source | New public declarations |
| --- | --- |
|Production `ParitySafeCRTSeat`|19 theorems|
|Mandatory41/91 regression|4 definitions,16 theorems|
|CRT regression|10 theorems|
|Classification data|5 definitions|
|Classification proofs|2 definitions,10 theorems|
|Total|66|

The generated [audit probe](../../../DkMathTest/NumberTheory/LegendreAdaptiveCertificateAxiomAudit.lean) performs `#check` and `#print axioms` for every manifest entry. [Coverage result](logs/axiom-coverage-009.txt) verifies all66 complete axiom sets, including all19 production declarations, contain only `propext`, `Classical.choice`, and `Quot.sound` or are empty. No `sorryAx` or additional custom axiom is present.

## Source, headers and document checks

`python3 docs/dev/GapFocusing-ExponentGauge-Ultra-261004-v0/checks/check-009.py` checks the manifest against source declarations, dependency sets against the full probe output, forbidden tokens, every written Lean header, tracked/new-file whitespace, and local document links.

- [Forbidden-token scan](logs/forbidden-token-scan-009.txt): zero matches for `sorry`, `sorryAx`, `admit`, `axiom`, `native_decide`, `unsafe` in the changed facade and all seven new Lean files.
- [Header check](logs/header-style-009.txt): all eight changed/new Lean files use the common copyright header, import block, and immediately following `#print "file: Full.Module.Name"`.
- [Whitespace check](logs/diff-check-009.txt): `git diff --check` plus checks of untracked new files passed.
- All links in the009 inventory, findings, report, validation and checkpoint README resolve.

The discovery script [classify-009.py](checks/classify-009.py) restricts input to the previous30 Class2 anchors in2..100, offsets1..2n, at most three distinct actual seats and at most three active witnesses per seat. Its generated data are subsequently proved in Lean; discovery output is not accepted as a proof. The classification reuses the already checked008 cap/candidate values and never evaluates whole-shell incidence/excess.

These checks establish the stated finite certificates and conditional/general CRT interfaces. They do not establish uniform charge sufficiency or Legendre's conjecture.
