# Validation 025

All builds used LEAN_NUM_THREADS=2. The build runner retains the exact commands, exit status and elapsed time. Timings are individual local runs with dependency reuse, not performance comparisons.

| Check | Target scope | Exit | Elapsed seconds |
| --- | --- | --- | --- |
| focused | Five affected production source modules and two calibration modules | 0 | 12.34 |
| facade | DkMath.NumberTheory.Legendre | 0 | 12.215 |
| root | DkMath | 0 | 1399.916 |
| axiom-audit | DkMathTest.NumberTheory.PascalPrebirthAxiomAudit | 0 | 12.107 |

- [focused-025.txt](evidence/MANIFEST.md#log-5b37b19dc99dc600) records all five affected production module targets and both calibration targets.
- [facade-025.txt](evidence/MANIFEST.md#log-9c5366cff53c84e7) records the complete requested Legendre facade build.
- [root-025.txt](evidence/MANIFEST.md#log-9fe7f61f302d96d9) records the complete requested DkMath root build.
- [axiom-audit-025.txt](evidence/MANIFEST.md#log-4e747f7600706844) contains installed API signature checks and print-axioms evidence for all named public declarations in the covered sources.

## Complete declaration coverage

Coverage includes 95 production declarations and 33 calibration declarations, 128 total. All 49 new production declarations and all 33 new calibration declarations are included. Existing named public declarations in changed production files are also included. The generated manifest is [declaration-coverage-025.json](evidence/MANIFEST.md#log-2092ea8ffd4895a6).

Allowed axiom dependencies are only propext, Classical.choice and Quot.sound. Every covered declaration is checked against that set. No new sorryAx dependency is accepted. This audit is scoped to the enumerated declarations; it is not a claim that every historical root theorem is free of placeholders.

## Root warnings

The root build reports the existing warnings below. They are outside the newly added declarations.

- DkMath/NumberTheory/Legendre/PacketCross.lean:285:5: Variable name `hrs` is not explicitly referenced.
- DkMath/CosmicFormula/TriominoFLT.lean:1919:6: declaration uses `sorry`
- DkMath/NumberTheory/ZsigmondyCyclotomicResearch.lean:147:6: declaration uses `sorry`
- DkMath/NumberTheory/GcdNextResearch.lean:850:6: declaration uses `sorry`
- DkMath/FLT/PrimeProvider/TriominoCosmicBranchA.lean:4187:8: declaration uses `sorry`
- DkMath/FLT/Kummer/CyclotomicPrincipalization.lean:5389:8: declaration uses `sorry`

## Additional checks

The forbidden-construct scan covers ten affected Lean files, including the two facades and the axiom probe. It rejects proof placeholders, custom axiom declarations and unchecked computation constructs. Standard headers and the traditional file-print markers are retained. Neutral Pascal modules do not depend on Legendre, Zsigmondy or exponent-period PowerGauge.

The tracked diff check and untracked Lean whitespace checks pass. The four new reports and all 025 text/JSON logs use ASCII without backslash notation. Compiler logs were normalized only after every build writer completed.

Required finite-row diagnostics and exact fractional counterexamples are retained in [pascal-diagnostics-025.json](evidence/MANIFEST.md#log-ddd5c41ceba520f1). Six anchor factorization ledgers were computed by factorial valuations and their full prime-power products compared with exact binomial values. Log readouts remain approximate diagnostics; Lean proofs use exact identities and prime log positivity instead.

The report contains all sixteen required answers and exactly one final Outcome B judgment. Next implementation proposals are explicitly separated from proved results.

The reproducible artifact audit is checks/check-025.py; its final output is [checks-025.txt](evidence/MANIFEST.md#log-5b9fcc5e79ad025a).
