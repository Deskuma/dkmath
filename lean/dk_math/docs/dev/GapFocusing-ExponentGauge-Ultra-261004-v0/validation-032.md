# Validation 032 - Final checked scope

Commands run from lean/dk_math with LEAN_NUM_THREADS=2:

- lake build DkMath.NumberTheory.Legendre.GnomonCofactorLeastFactor DkMathTest.NumberTheory.GnomonCofactorLeastFactorCalibration
- lake build DkMath.NumberTheory.Legendre
- lake build DkMath
- lake build DkMathTest.NumberTheory.GnomonCofactorLeastFactorAxiomAudit

| Build | Exit | Seconds | Peak RSS kbytes | Major faults | Minor faults | Swaps |
| --- | --- | --- | --- | --- | --- | --- |
| focused | 0 | 7.552 | 980964 | 0 | 33491 | 0 |
| facade | 0 | 12.624 | 6746160 | 0 | 200335 | 0 |
| root | 0 | 13.162 | 7109488 | 0 | 203249 | 0 |
| axiom-audit | 0 | 12.665 | 6688208 | 0 | 195672 | 0 |

All exits are zero. GNU time records Lake and waited descendants, with no
build memory failure. Changes comprise the new production module, calibration,
axiom audit and one facade import. Earlier production modules have no diff.
All 20 production and 15 named calibration declarations are covered;
only propext, Classical.choice and Quot.sound occur, with no sorryAx.
Private calibration helpers are covered transitively. Focused and axiom logs
have no warnings. Inherited warnings are recorded below; root success is not
a repository-wide no-sorry certificate.

facade: 1 inherited warnings.
- warning: DkMath/NumberTheory/Legendre/PacketCross.lean:285:5: Variable name `hrs` is not explicitly referenced.

root: 6 inherited warnings.
- warning: DkMath/NumberTheory/Legendre/PacketCross.lean:285:5: Variable name `hrs` is not explicitly referenced.
- warning: DkMath/NumberTheory/ZsigmondyCyclotomicResearch.lean:147:6: declaration uses `sorry`
- warning: DkMath/FLT/PrimeProvider/TriominoCosmicBranchA.lean:4187:8: declaration uses `sorry`
- warning: DkMath/NumberTheory/GcdNextResearch.lean:850:6: declaration uses `sorry`
- warning: DkMath/CosmicFormula/TriominoFLT.lean:1919:6: declaration uses `sorry`
- warning: DkMath/FLT/Kummer/CyclotomicPrincipalization.lean:5389:8: declaration uses `sorry`

Kernel checks include canonical routing of 49 and 77, all canonical triples
at 29, a noninitial-basis cutoff counterexample, duplicate cover at 32, the
exact cover/error lower witness at 9, corrected exactness at 9, preservation
of the 7 consumer, equality at 3, exact integer products and symbolic-log
consumer recovery at 29 and failure at 31. Minimality of the numeric failure
at 31 is not kernel claimed. Scoped recursion/heartbeat budgets for large
products are documented. Binomial evaluation uses the proved fast_choose
identity, without native_decide or added axioms.

Independent diagnostics cover every n=3..300 plus 1031 and 5000, totaling
300 rows, with 13 retained anchor reconstructions. The 031 source digest,
canonical quotient restrictions, exact factor pairs and squares, duplicates,
weighted identities and floating-only consumer comparisons are audited.
The artifact check additionally covers public axiom names, forbidden
constructs, import direction, headers, immediate file markers, whitespace,
Markdown links and ASCII logs. Results are scoped to these checks.

Evidence: [focused](evidence/MANIFEST.md#log-9d4fbadd8daf3b43), [facade](evidence/MANIFEST.md#log-55d6b42b4aab3d25),
[root](evidence/MANIFEST.md#log-a60b32de25f3ecbb), [axioms](evidence/MANIFEST.md#log-effba3224231ac5d),
[coverage](evidence/MANIFEST.md#log-773477a7c71c2eff), [diagnostics](evidence/MANIFEST.md#log-fe03023e0ec1782a),
[artifact audit](evidence/MANIFEST.md#log-e0a1b2ad6c5e4916).

Outcome B - finite factor bound and local square correction; no global closure.
