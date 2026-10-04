# Instruction 010 validation

Commands run in `lean/dk_math` with the repository Lean4.34.1 toolchain. Baseline `cd04ef580` was clean. Scope: two new production modules, the changed Legendre facade, explicit bounded family data, diagnostic proofs, regressions and complete new-declaration dependency inspection.

## Kernel builds

The focused merge and mixed/scaling targets succeed: [merge log](logs/build-merge-010.txt), [mixed log](logs/build-mixed-010.txt). The [diagnostic build](logs/build-diagnostic-010.txt) covers all34 basis/anchor checkpoints, restricted-basis saturation, exact charges, cap/candidate values, all25 previous-survivor prime conclusions, named58/68/97/107/127 conclusions, zero mixed period ranges, primehood labels and counterexample/lift regressions.

The final combined acceptance command is:

```sh
lake build DkMath.NumberTheory.Legendre.ParitySafeMergedCRT \
  DkMath.NumberTheory.Legendre.ParitySafeMixedCRT \
  DkMathTest.NumberTheory.LegendreMergedCRT \
  DkMathTest.NumberTheory.LegendreMergedCRTRegression \
  DkMath.NumberTheory.Legendre DkMath
```

[Final build log](logs/build-final-010.txt). Root replay's existing unrelated research admission warnings are distinct from the new dependency audit. No new production proof uses a research endpoint containing an admission.

The final combined build succeeds with10388 jobs and no warnings in the new modules. The earlier focused diagnostic log retains style warnings from before workload comments were added; the final source/build supersedes that checkpoint.

The numerical proofs use ordinary Lean kernel checking, including scoped `decide +kernel`. No `native_decide` is used. Scoped recursion/heartbeat settings accommodate the finite data. The cap/candidate audit reuses008 checked values for previous shells and independently checks the extra107/127/211/503 caps. It does not evaluate whole-shell incidence/excess.

The anchor8 noninjective counterexample derives E=1 from the structural cap5, four explicit covered seats, the exact ledger and the merged lower certificate. The mixed320 counted-family theorem and three concrete lifts are independently checked.

## Complete dependency audit

The [manifest](logs/declaration-coverage-010.json) contains59 public declarations:

| Source | Public declarations |
| --- | --- |
|Production merged module|2 definitions,10 theorems|
|Production mixed/scaling module|9 theorems|
|Bounded data|7 definitions|
|Diagnostic proofs|2 definitions,23 theorems|
|Regressions|6 theorems|
|Total|59; production21, regression/data38|

[Inventory source](../../../DkMathTest/NumberTheory/LegendreMergedCRTInventory.lean) and [generated audit source](../../../DkMathTest/NumberTheory/LegendreMergedCRTAxiomAudit.lean) are executed with `lake env lean`. [Exact inventory](logs/source-inventory-010.txt), [full axiom output](logs/axiom-audit-010.txt), [coverage summary](logs/axiom-coverage-010.txt). Every new public production definition/theorem is included, as are every new diagnostic/data/regression declaration. Each complete axiom set is empty or contained in{propext,Classical.choice,Quot.sound}; no `sorryAx` or custom axiom is present.

## Source and artifact checks

`python3 docs/dev/GapFocusing-ExponentGauge-Ultra-261004-v0/checks/check-010.py` verifies source-to-manifest equality and full axiom sets, then:

- [Forbidden-token scan](logs/forbidden-token-scan-010.txt): zero occurrences of `sorry`, `sorryAx`, `admit`, `axiom`, `native_decide`, `unsafe` in all changed/new Lean sources.
- [Header audit](logs/header-style-010.txt): all8 changed/new Lean files have the same copyright/import layout and exact module-specific `#print "file: …"` immediately after imports.
- [Whitespace audit](logs/diff-check-010.txt): tracked `git diff --check` and untracked new-file checks.
- All local009/010 checkpoint links in the checked documents resolve.
- [Artifact check](logs/artifact-check-010.txt): all34 discovery tables equal the actual Lean data, all25 survivor and15 prime window/floor report rows match the checked values.

[Bounded discovery](checks/classify-010.py) uses only explicit bases7/10, pair/triple subsets,34 specified basis/anchor checkpoints no larger than503, and each shell's offsets1..2n. [Discovery output](logs/discovery-run-010.txt), [certificate data](logs/classification-010.json), [summary](logs/classification-summary-010.txt). Python produces candidate evidence; Lean checks realization, charges and restricted-basis saturation. The basis is not the full active-prime universe.

The finite negative findings are checked charge shortages at211/503 for both pools, empty conservative mixed pair/triple ranges at the13 specified small mixed anchors, and the naive noninjective-sum counterexample. They are not a universal impossibility result for CRT, an absence-of-primes claim, or an asymptotic estimate.

The20 prime basis/anchor combinations also have separate floor-prefix checks: raw costs equal the sum of the exact per-family floor costs, while merged charges are computed from actual prefix seats. This distinguishes the theorem-guaranteed prefixes from additional finite window hits. The diagnostic scopes include comments explaining their finite kernel workload; default limits are retained outside those scopes.

`checkpoint_floor_charge_le_excess` formally transports every recorded merged floor-prefix charge into the existing excess sum through the realized-family subset proof.
