# Validation 026

All final checks passed with LEAN_NUM_THREADS=2.

| Check | Exit | Seconds |
| --- | --- | --- |
| focused | 0 | 7.524 |
| facade | 0 | 12.16 |
| root | 0 | 13.87 |
| axiom-audit | 0 | 12.237 |

The focused check built all three new production modules and the calibration
module. The Legendre facade exports them; the DkMath root imports that facade.
The root source itself was not edited.

Complete named public axiom coverage includes 60 new
production declarations and 19 calibration declarations,
79 total. Every declaration is printed in the dedicated axiom audit.
Only propext, Classical.choice and Quot.sound are permitted by the checker.
No new sorryAx dependency occurs.

The final focused and axiom logs contain no warnings. The facade replayed
the existing PacketCross unused-variable warning. The root replayed previously
existing unrelated warnings:

- warning: DkMath/NumberTheory/Legendre/PacketCross.lean:285:5: Variable name `hrs` is not explicitly referenced.
- warning: DkMath/CosmicFormula/TriominoFLT.lean:1919:6: declaration uses `sorry`
- warning: DkMath/NumberTheory/ZsigmondyCyclotomicResearch.lean:147:6: declaration uses `sorry`
- warning: DkMath/FLT/PrimeProvider/TriominoCosmicBranchA.lean:4187:8: declaration uses `sorry`
- warning: DkMath/NumberTheory/GcdNextResearch.lean:850:6: declaration uses `sorry`
- warning: DkMath/FLT/Kummer/CyclotomicPrincipalization.lean:5389:8: declaration uses `sorry`

The exact integer diagnostic scan covers all 5000 anchors n=1..5000.
The final checker independently reconstructs the higher-power event inventory,
verifies the stored event properties and bounds, and checks parser-safe artifacts.
Real logarithms and strict numerical comparisons remain floating diagnostics.
Named Lean calibrations certify the six preserved higher-event summaries.

Forbidden-construct and header/file-marker scans cover three new production
modules, calibration, axiom audit, and the edited facade. Tracked diff checks
and separate untracked Lean whitespace checks passed. No RH import was added.

The final status evidence is in focused-026.txt, facade-026.txt, root-026.txt,
and axiom-audit-026.txt, with their performance JSON records. The build-026-*.txt
files retain earlier focused elaboration attempts and are historical logs,
not final validation status.

[Final checker output](logs/checks-026.txt) records the completed audits.
[Complete declaration coverage](logs/declaration-coverage-026.json) lists every
printed declaration. [Report](report-026.md) separates the proved small-budget
criteria from the unresolved universal lower-mass provider and the next proposal.
