# Instruction 011 validation

Lean4.34.1; Lake cwd `/home/deskuma/develop/lean/dkmath/lean/dk_math`.

|Check|Result|Evidence|
|---|---|---|
|Three new production targets, focused|Passed|[build-production-011.txt](logs/build-production-011.txt)|
|Kernel finite calibration: root charges, caps, demand, cutoff,211/503 endpoints|Passed|[build-calibration-011.txt](logs/build-calibration-011.txt), final rebuilt calibration in [build-regression-011.txt](logs/build-regression-011.txt)|
|Candidate endpoint / shared-exclusion / triangle regressions|Passed|[build-regression-011.txt](logs/build-regression-011.txt)|
|`lake build DkMath.NumberTheory.Legendre`|Passed|[build-facade-011.txt](logs/build-facade-011.txt)|
|`lake build DkMath`|Passed, five existing warnings outside new declarations|[build-root-011.txt](logs/build-root-011.txt)|
|Source inventory probe|Passed|[source-inventory-011.txt](logs/source-inventory-011.txt)|
|Every new public declaration: `#check`, `#print axioms`|57/57 checked, including41 production declarations and16 calibration/regression/data declarations|[declaration-coverage-011.json](logs/declaration-coverage-011.json), [axiom-audit-011.txt](logs/axiom-audit-011.txt), [axiom-coverage-011.txt](logs/axiom-coverage-011.txt)|
|Forbidden constructs in all eight written Lean files|Zero matches|[forbidden-token-scan-011.txt](logs/forbidden-token-scan-011.txt)|
|Uniform copyright/import/post-import file-print headers|Eight/eight checked|[header-style-011.txt](logs/header-style-011.txt)|
|Tracked/new-file whitespace|Passed|[diff-check-011.txt](logs/diff-check-011.txt)|
|Independent diagnostics / Lean data / report arithmetic and local links|Passed|[artifact-check-011.txt](logs/artifact-check-011.txt), [checkpoint-audit-011.txt](logs/checkpoint-audit-011.txt)|

All complete axiom sets of new public declarations are subsets of
`{propext, Classical.choice, Quot.sound}`. In particular, the two hard-checkpoint
prime endpoints and all new production declarations have no `sorryAx`
dependency. The source scan covers `sorry`, `sorryAx`, `admit`, `axiom`,
`native_decide`, `unsafe`. Numerical checks use `decide +kernel`, not native
numerical proof generation.

The root build replays pre-existing `sorry` warnings in:

- `DkMath/NumberTheory/ZsigmondyCyclotomicResearch.lean:147`
- `DkMath/FLT/PrimeProvider/TriominoCosmicBranchA.lean:4187`
- `DkMath/NumberTheory/GcdNextResearch.lean:850`
- `DkMath/FLT/Kummer/CyclotomicPrincipalization.lean:5389`
- `DkMath/CosmicFormula/TriominoFLT.lean:1919`

Those declarations are outside the checked new dependency sets. This validation
does not assert absence of research placeholders elsewhere in the repository.

Reproducible commands:

```sh
python3 docs/dev/GapFocusing-ExponentGauge-Ultra-261004-v0/checks/discover-011.py
lake build DkMath.NumberTheory.Legendre.ParitySafeCanonicalRootFiber DkMath.NumberTheory.Legendre.ParitySafeCanonicalRootSieve DkMath.NumberTheory.Legendre.ParitySafeCanonicalRootCharge
lake build DkMathTest.NumberTheory.LegendreCanonicalRootCharge
lake build DkMathTest.NumberTheory.LegendreCanonicalRootRegression
lake build DkMath.NumberTheory.Legendre
lake build DkMath
python3 docs/dev/GapFocusing-ExponentGauge-Ultra-261004-v0/checks/check-011.py --generate
lake env lean DkMathTest/NumberTheory/LegendreCanonicalRootInventory.lean > docs/dev/GapFocusing-ExponentGauge-Ultra-261004-v0/logs/source-inventory-011.txt
lake env lean DkMathTest/NumberTheory/LegendreCanonicalRootAxiomAudit.lean > docs/dev/GapFocusing-ExponentGauge-Ultra-261004-v0/logs/axiom-audit-011.txt
python3 docs/dev/GapFocusing-ExponentGauge-Ultra-261004-v0/checks/check-011.py
```

The diagnostic Python script independently factors candidate shell points and
compares their minimum-root contributions with floor-wave charges. Its output
is never imported as a Lean proof. The actual root-fiber equalities are separate
Lean diagnostic endpoints; the211/503 demand proofs depend on structural wave
counts and disjoint-root lower bounds, not on those diagnostics or direct E/I
evaluation.
