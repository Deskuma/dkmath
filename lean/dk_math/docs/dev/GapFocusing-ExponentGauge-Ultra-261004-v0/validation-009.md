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

[Final build log](evidence/MANIFEST.md#log-7d27c32ea64a9030). The new modules have no warnings. Root replay includes five existing unrelated research declarations using `sorry`; the complete dependency inspection below establishes that none is used by the new declarations. A successful root build alone is not treated as proof of global absence of admissions.

[Mandatory focused build](evidence/MANIFEST.md#log-138ced6e1b2e55a1) checked41/91 without full incidence/excess evaluation. [Classification focused build](evidence/MANIFEST.md#log-4d50dc4372ffc5bc) checked all30 previous Class2 shells, actual witnesses, charges, partition, five successful prime conclusions and25 charge-budget obstructions. [CRT development log](evidence/MANIFEST.md#log-29f3fcf8ed35bc0d) and [earlier CRT regression checkpoint](evidence/MANIFEST.md#log-9a9894dfd1f2ab04) retain intermediate failures/warnings for investigation; the final combined log supersedes them for acceptance.

Both inventory and axiom probes were executed through `lake env lean` and exited0:

```sh
lake env lean DkMathTest/NumberTheory/LegendreAdaptiveCertificateInventory.lean
lake env lean DkMathTest/NumberTheory/LegendreAdaptiveCertificateAxiomAudit.lean
```

[Initial source types](evidence/MANIFEST.md#log-8825fb8c9e727d2a), [final source types](evidence/MANIFEST.md#log-bb201df0bed76a5a), [complete axiom output](evidence/MANIFEST.md#log-f89401867e84cb4b). All numerical proofs use ordinary kernel checking (`decide`, including scoped `decide +kernel`); no native evaluator trust is introduced.

## Complete declaration coverage

[Manifest](evidence/MANIFEST.md#log-94bb72aed424b8d6) enumerates66 new declarations:

| Source | New public declarations |
| --- | --- |
|Production `ParitySafeCRTSeat`|19 theorems|
|Mandatory41/91 regression|4 definitions,16 theorems|
|CRT regression|10 theorems|
|Classification data|5 definitions|
|Classification proofs|2 definitions,10 theorems|
|Total|66|

The generated [audit probe](../../../DkMathTest/NumberTheory/LegendreAdaptiveCertificateAxiomAudit.lean) performs `#check` and `#print axioms` for every manifest entry. [Coverage result](evidence/MANIFEST.md#log-8231672fdf4774bc) verifies all66 complete axiom sets, including all19 production declarations, contain only `propext`, `Classical.choice`, and `Quot.sound` or are empty. No `sorryAx` or additional custom axiom is present.

## Source, headers and document checks

`python3 docs/dev/GapFocusing-ExponentGauge-Ultra-261004-v0/checks/check-009.py` checks the manifest against source declarations, dependency sets against the full probe output, forbidden tokens, every written Lean header, tracked/new-file whitespace, and local document links.

- [Forbidden-token scan](evidence/MANIFEST.md#log-67728e4aff5ec685): zero matches for `sorry`, `sorryAx`, `admit`, `axiom`, `native_decide`, `unsafe` in the changed facade and all seven new Lean files.
- [Header check](evidence/MANIFEST.md#log-1d7a164b6d4702bb): all eight changed/new Lean files use the common copyright header, import block, and immediately following `#print "file: Full.Module.Name"`.
- [Whitespace check](evidence/MANIFEST.md#log-eed193ad9d1c5df1): `git diff --check` plus checks of untracked new files passed.
- All links in the009 inventory, findings, report, validation and checkpoint README resolve.

The discovery script [classify-009.py](checks/classify-009.py) restricts input to the previous30 Class2 anchors in2..100, offsets1..2n, at most three distinct actual seats and at most three active witnesses per seat. Its generated data are subsequently proved in Lean; discovery output is not accepted as a proof. The classification reuses the already checked008 cap/candidate values and never evaluates whole-shell incidence/excess.

These checks establish the stated finite certificates and conditional/general CRT interfaces. They do not establish uniform charge sufficiency or Legendre's conjecture.
