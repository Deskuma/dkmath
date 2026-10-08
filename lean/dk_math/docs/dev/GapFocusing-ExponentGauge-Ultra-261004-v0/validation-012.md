# Instruction012 validation

Lean4.34.1; Lake cwd `/home/deskuma/develop/lean/dkmath/lean/dk_math`.

|Check|Result|Evidence|
|---|---|---|
|All four new production targets, including sqrt-cutoff bounds|Passed|[build-production-012.txt](evidence/MANIFEST.md#log-c49f63b1f611f21f)|
|Seven anchors: exact four root charges, A/B2, demand, minimal tested cutoffs and direct rough floor proofs|Passed|[build-calibration-012.txt](evidence/MANIFEST.md#log-cbf90d29755dcde8)|
|Erased-root/default-root/cap-tail/sequential-subtraction/multiplicity regressions, exact old union credit, sqrt-bound sharpness|Passed|[build-regression-012.txt](evidence/MANIFEST.md#log-db1df8d2ba310ebc)|
|Actual E and four-cutoff tail/rough-seat cards, derived using the smaller coverage diagnostic|Passed|[build-diagnostics-012.txt](evidence/MANIFEST.md#log-4abe8c31f611031a)|
|`lake build DkMath.NumberTheory.Legendre`|Passed after final production additions|[build-facade-012.txt](evidence/MANIFEST.md#log-5a50c6c1e0055935)|
|`lake build DkMath`|Passed after final production additions; five old research warnings|[build-root-012.txt](evidence/MANIFEST.md#log-89427617a0ec8379)|
|All66 new public production dependency sets|Passed, only standard axioms|[production-axioms-012.txt](evidence/MANIFEST.md#log-cf94fb45fe3ac69f), [production-axiom-coverage-012.txt](evidence/MANIFEST.md#log-d9c0f5fea157800c)|
|Complete114 public declaration dependency sets|114/114 passed:66 production,48 calibration/diagnostic/regression/data|[declaration-coverage-012.json](evidence/MANIFEST.md#log-e60c09e19e383175), [axiom-audit-012.txt](evidence/MANIFEST.md#log-3fde4290036ee244), [axiom-coverage-012.txt](evidence/MANIFEST.md#log-3c8add0360910b4a)|
|Source inventory compiler probe|Passed|[source-inventory-012.txt](evidence/MANIFEST.md#log-e274f086078db255)|
|Forbidden constructs in all12 written Lean files|Zero matches|[forbidden-token-scan-012.txt](evidence/MANIFEST.md#log-de95fedc2184e941)|
|Uniform copyright/import-adjacent module prints|12/12 passed|[header-style-012.txt](evidence/MANIFEST.md#log-b4166f940afc6c83)|
|Tracked and new-file whitespace|Passed|[diff-check-012.txt](evidence/MANIFEST.md#log-a716fe03b57e2450)|
|Seven structural rows,28 diagnostics, report arithmetic and local links|Passed|[artifact-check-012.txt](evidence/MANIFEST.md#log-57bc2882e37f7149)|

The [combined final audit](evidence/MANIFEST.md#log-a1f675351dfdfc4b) passes all coverage, source and artifact checks.

Numerical checks use `decide +kernel`; Python discovery is not imported as a
Lean proof. The diagnostic module imports structural calibration, with no
reverse dependency. Generic current currency keeps B2-I slack, and odd-prime
anchor exactness is a separate proved theorem.

The whole build replays pre-existing placeholder warnings at:

- `DkMath/NumberTheory/ZsigmondyCyclotomicResearch.lean:147`
- `DkMath/FLT/PrimeProvider/TriominoCosmicBranchA.lean:4187`
- `DkMath/NumberTheory/GcdNextResearch.lean:850`
- `DkMath/CosmicFormula/TriominoFLT.lean:1919`
- `DkMath/FLT/Kummer/CyclotomicPrincipalization.lean:5389`

These are outside the checked new production dependency sets. This validation
does not assert absence of placeholders elsewhere in the project.

Complete new dependency sets are subsets of
`{propext, Classical.choice, Quot.sound}`. All114 public declarations, including
all66 production declarations and the1009/1013 prime endpoints, are free of
`sorryAx`. The source scan checks `sorry`, `sorryAx`, `admit`, `axiom`,
`native_decide`, `unsafe`; it includes facade, inventory and generated audit
alongside all production/calibration/diagnostic modules.

The final diagnostic strategy kernel-checks cutoff11 rough-covered seats,
then uses the checked structural rough-wave sum and exact balance identities
to recover actual E and all four tail cards. It avoids numerical whole-E
reduction. Heavy numerical facts reside in a separate counts module; the
production-object bridge module consumes them. The first slow diagnostic
attempt was interrupted, stale owned child builds were removed, and the final
local membership-normalization repairs were rechecked by focused builds.

Reproducible commands:

```sh
python3 docs/dev/GapFocusing-ExponentGauge-Ultra-261004-v0/checks/discover-012.py
lake build DkMath.NumberTheory.Legendre.ParitySafeCanonicalRootTail DkMath.NumberTheory.Legendre.ParitySafeCanonicalRootEleven DkMath.NumberTheory.Legendre.ParitySafeCanonicalRoughCount DkMath.NumberTheory.Legendre.ParitySafePrimeAnchorCap
lake build DkMathTest.NumberTheory.LegendreCanonicalTailCalibration
lake build DkMathTest.NumberTheory.LegendreCanonicalTailRegression DkMathTest.NumberTheory.LegendreCanonicalPrimeCapCalibration
lake build DkMathTest.NumberTheory.LegendreCanonicalTailDiagnostics
lake build DkMath.NumberTheory.Legendre
lake build DkMath
python3 docs/dev/GapFocusing-ExponentGauge-Ultra-261004-v0/checks/check-012.py --generate
lake env lean DkMathTest/NumberTheory/LegendreCanonicalTailInventory.lean > docs/dev/GapFocusing-ExponentGauge-Ultra-261004-v0/logs/source-inventory-012.txt
lake env lean DkMathTest/NumberTheory/LegendreCanonicalTailAxiomAudit.lean > docs/dev/GapFocusing-ExponentGauge-Ultra-261004-v0/logs/axiom-audit-012.txt
python3 docs/dev/GapFocusing-ExponentGauge-Ultra-261004-v0/checks/check-012.py
```
