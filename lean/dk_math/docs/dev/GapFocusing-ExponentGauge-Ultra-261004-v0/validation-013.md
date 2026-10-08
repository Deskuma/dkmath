# Validation 013

Lean toolchain: `leanprover/lean4:v4.34.1`. Lake cwd: `lean/dk_math`.

## Executed builds

|Command / scope|Result|Log|
|---|---|---|
|`lake build DkMath.NumberTheory.Legendre.ParitySafeSqrtRoughFactorization` (all4 new production modules)|PASS,9048 jobs; no new warnings|[production](evidence/MANIFEST.md#log-c87ad9840e08ca31)|
|`lake build DkMathTest.NumberTheory.LegendreSqrtRoughMomentCalibration DkMathTest.NumberTheory.LegendreSqrtRoughMomentRegression` (all3 calibration/test modules)|PASS,9053 jobs; no new warnings|[calibration](evidence/MANIFEST.md#log-8a120e29804ed4db)|
|`lake build DkMath.NumberTheory.Legendre`|PASS,9083 jobs|[facade](evidence/MANIFEST.md#log-39e9d13056b4a644)|
|`lake build DkMath`|PASS,10386 jobs; five existing out-of-scope placeholder warnings|[root](evidence/MANIFEST.md#log-2d388bc18400e575)|
|`lake env lean DkMathTest/NumberTheory/LegendreSqrtRoughMomentAxiomAudit.lean`|PASS,96 checks and96 complete axiom sets|[axiom audit](evidence/MANIFEST.md#log-9afa238ee76b8621)|
|`python3 checks/check-013.py`|PASS,coverage/trust/source/header/whitespace/artifact checks|[artifact audit](evidence/MANIFEST.md#log-283d617f6383da28)|

## Trust and source scope

[Declaration manifest](evidence/MANIFEST.md#log-8e3f03a1721c80b9):66 production declarations plus30 numerical calibration, bridge, and regression declarations. All are inspected with both #check and #print axioms, including definitions/abbreviations. All dependency sets are subsets of `{propext, Classical.choice, Quot.sound}`; none contains sorryAx. The checker parses entire multiline dependency sets and requires exact manifest equality.

The forbidden-source scan checks all seven implementation/calibration files for the six prohibited constructs. Header/marker checks cover nine written Lean files:4 production,3 calibration/regression,1 generated audit and the modified facade. `git diff --check` covers tracked diffs; `git diff --no-index --check /dev/null FILE` covers each new Lean source. Python/report local links and all430 discovery rows are checked independently.

The root build replays five pre-existing `sorry` warnings, outside the96 audited declaration dependencies:

- `NumberTheory/ZsigmondyCyclotomicResearch.lean:147`
- `FLT/PrimeProvider/TriominoCosmicBranchA.lean:4187`
- `NumberTheory/GcdNextResearch.lean:850`
- `CosmicFormula/TriominoFLT.lean:1919`
- `FLT/Kummer/CyclotomicPrincipalization.lean:5389`

This is scoped trust evidence; it is not a placeholder-free audit of the entire DkMath repository.

## Kernel calibrations and diagnostic boundary

Five anchors211,503,1009,1013,1019 have kernel-checked actual prime inventories, small-prime filters, rough carrier count, roughI and pair/triple moments. U is recovered through the proved conservation law. Product-wave regrouping instances and structural prime square-cell proofs consume the production moment/product-wave API. No whole E/I evaluation is used for those endpoints.

Regressions cover local identity failure at k=4; empty n=0; sharp three-support seat19; both repeated-prime branches13/29; actual candidate floor count1 with exact rough triple count0 at503.

The bounded prime scan<=3000 was executed by [discovery script](checks/discover-013.py); runtime9.16 seconds,430 prime anchors, last2999, no direct-failure/moment-success case. [JSON](evidence/MANIFEST.md#log-2e97fe715bb50d71) contains all rows. This scan is an external diagnostic, not a430-anchor Lean theorem. No uniform demand, Legendre conjecture or analytic sieve claim is made.
