# Validation 034 - Final checked scope

Commands executed from lean/dk_math with LEAN_NUM_THREADS=2:

- lake build DkMath.NumberTheory.Legendre.GnomonCofactorThreePrime DkMathTest.NumberTheory.GnomonCofactorThreePrimeCalibration
- lake build DkMath.NumberTheory.Legendre
- lake build DkMath
- lake build DkMathTest.NumberTheory.GnomonCofactorThreePrimeAxiomAudit

| Build | Exit | Seconds | Peak RSS kbytes | Major faults | Minor faults | Swaps |
| --- | --- | --- | --- | --- | --- | --- |
| focused | 0 | 7.704 | 963240 | 3 | 32429 | 0 |
| facade | 0 | 12.916 | 6747264 | 0 | 197544 | 0 |
| root | 0 | 14.029 | 7110348 | 0 | 204571 | 0 |
| axiom-audit | 0 | 13.114 | 6692328 | 0 | 199089 | 0 |

All exits are zero. GNU time includes Lake and waited descendants; no build
memory failure occurred. Changes comprise the new production module,
calibration, axiom audit and one facade import. Earlier modules have no diff.
All 15 production and nine named calibration declarations are covered;
only propext, Classical.choice and Quot.sound occur, with no sorryAx.
The two private production helpers and private calibration helpers are
covered transitively. Focused and axiom logs have no warnings. Root success
is not a whole-repository no-sorry certificate. Inherited warnings follow.

facade: 1 inherited warnings.
- warning: DkMath/NumberTheory/Legendre/PacketCross.lean:285:5: Variable name `hrs` is not explicitly referenced.

root: 6 inherited warnings.
- warning: DkMath/NumberTheory/Legendre/PacketCross.lean:285:5: Variable name `hrs` is not explicitly referenced.
- warning: DkMath/NumberTheory/ZsigmondyCyclotomicResearch.lean:147:6: declaration uses `sorry`
- warning: DkMath/FLT/PrimeProvider/TriominoCosmicBranchA.lean:4187:8: declaration uses `sorry`
- warning: DkMath/NumberTheory/GcdNextResearch.lean:850:6: declaration uses `sorry`
- warning: DkMath/CosmicFormula/TriominoFLT.lean:1919:6: declaration uses `sorry`
- warning: DkMath/FLT/Kummer/CyclotomicPrincipalization.lean:5389:8: declaration uses `sorry`

Kernel checks certify the complete triple carrier at 32, membership of 343
and 539, complete combined coverage and Y=Q at 9,12,31,32, preservation of
the 31 consumer, the four-factor survivor 2401 at 69, exact products and
symbolic-log consumer at 32, and equality at 3. Product uniqueness, pair/triple
disjointness, exact combined mass and old-ledger excess are production proofs.
Scoped finite-product recursion/heartbeat budgets are documented, and binomial
computation uses the proved fast_choose identity without native_decide.

Diagnostics cover 300 rows, n=3..300 plus 1031,5000, with 15 anchor
reconstructions. Recoveries at 210,297,1031 and failure at 5000 are numerical
only. No first-failure claim is made across the untested gap. Audits check
source digests, exact triple reconstruction, weak ordering/repetition,
injection, disjointness, composite inclusion, weighted identities and floating-
only margins. Additional checks cover axiom names, forbidden constructs,
imports, headers, immediate markers, whitespace, ASCII artifacts and Markdown
links. Evidence is scoped to these recorded checks.

Evidence: [focused](logs/focused-034.txt), [facade](logs/facade-034.txt),
[root](logs/root-034.txt), [axioms](logs/axiom-audit-034.txt),
[coverage](logs/declaration-coverage-034.json), [diagnostics](logs/diagnostics-034.json),
[artifact audit](logs/artifact-check-034.txt).

Outcome B - material bounded triple correction; stop automatic factor-depth continuation.
