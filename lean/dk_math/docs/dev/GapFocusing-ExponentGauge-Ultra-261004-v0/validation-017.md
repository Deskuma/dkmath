# Validation 017

All commands ran in lean/dk_math with the repository-pinned Lean 4.34.1.
Four new production modules, one regression module and one axiom audit module
were written. Two existing facades gained one import each; the existing README
gained the checkpoint entry. Production headers follow the existing copyright
style and import-adjacent file marker convention.

## Focused builds

Each command completed successfully. Job totals are Lake dependency-task
totals, not counts of changed or freshly compiled modules.

| Command | Job total | Evidence |
|---|---|---|
| lake build DkMath.CosmicFormula.QuadraticCenteredBridge | 8937 | [quadratic-017.txt](logs/quadratic-017.txt) |
| lake build DkMath.NumberTheory.Legendre.QuadraticGnomonFold | 3141 | [fold-017.txt](logs/fold-017.txt) |
| lake build DkMath.NumberTheory.Legendre.CenteredOwnerFold | 8992 | [owner-017.txt](logs/owner-017.txt) |
| lake build DkMath.NumberTheory.Legendre.CenteredFoldSupportNorm | 8993 | [norm-017.txt](logs/norm-017.txt) |
| lake build DkMathTest.NumberTheory.LegendreCenteredFoldRegression | 9075 | [regression-017.txt](logs/regression-017.txt) |
| lake build DkMathTest.NumberTheory.LegendreCenteredFoldAxiomAudit | 9111 | [axiom-audit-017.txt](logs/axiom-audit-017.txt) |
| lake build DkMath.NumberTheory.Legendre DkMath.CosmicFormula | 9172 | [facades-017.txt](logs/facades-017.txt) |
| lake build DkMath | 10400 | [root-017.txt](logs/root-017.txt) |

Intermediate calibration errors were repaired before the final builds.
The final new-source builds have no linter warnings. The facade log reports an
existing ZsigmondyCyclotomicResearch warning. The root build reports five
existing declarations using sorry outside the new declaration dependency sets:

- DkMath/NumberTheory/ZsigmondyCyclotomicResearch.lean:147.
- DkMath/FLT/PrimeProvider/TriominoCosmicBranchA.lean:4187.
- DkMath/NumberTheory/GcdNextResearch.lean:850.
- DkMath/FLT/Kummer/CyclotomicPrincipalization.lean:5389.
- DkMath/CosmicFormula/TriominoFLT.lean:1919.

The root build is therefore not evidence that the whole repository is free of
sorry. The scoped public axiom audit below is evidence for the new declarations.

## Complete public axiom audit

The source manifest contains 66 production declarations and 18 regression
theorems, 84 total. It includes every theorem, def, noncomputable def and abbrev
in the five newly written implementation/regression modules. All 84 have both
#check and #print axioms commands in LegendreCenteredFoldAxiomAudit.lean.
Every complete axiom set is a subset of propext, Classical.choice and Quot.sound;
no sorryAx or extra axiom occurs. Generated auxiliaries are covered through
the dependencies of their public declarations.

The manifest also supplies category A/B/C/D for every new declaration:
24 A, 33 B and 9 C production declarations; no D. The 18 calibrations are
listed separately as A applications or explicit finite counterexamples.
See [declaration-coverage-017.json](logs/declaration-coverage-017.json) and
[declaration-classification-017.md](declaration-classification-017.md).

## Kernel calibration scope

LegendreCenteredFoldRegression kernel-checks unit forward and second differences,
rational steps 1, 1/2, 1/4 and 1/8, the Nat/Int zero boundary, involution,
CenteredPair fold partners, gap ladder, concrete pair decomposition, translation
nonpreservation of divisibility, forced prime-gap support separation, common
support without equal least owners, the false reverse owner rule, the exact
norm-activated capacity at 6, the one-seat successor mismatch, and consecutive
norm support exclusion. It also checks a covered compatible trajectory at
13, the inherited near miss at 5, the prime-norm common-support exclusion at
297, exact 1031 common-support counts 206 and 17, and the inherited 1031
non-cover/survivor/prime endpoint. No same-owner example can exist by the
proved universal parity theorem. No native_decide is used.

The all-natural-anchor tables remain finite Python diagnostics. In particular,
the exact 1031 owner coloring and total 223 support incidence are not presented
as new kernel census theorems. The kernel floor theorem proves the two selected
1031 per-prime counts independently.

## Diagnostic and source checks

Commands:

    python3 docs/dev/GapFocusing-ExponentGauge-Ultra-261004-v0/checks/discovery-017.py
    python3 docs/dev/GapFocusing-ExponentGauge-Ultra-261004-v0/checks/check-017.py --generate
    python3 docs/dev/GapFocusing-ExponentGauge-Ultra-261004-v0/checks/check-017.py
    git diff --check

The discovery command records all 300 natural anchors 1..300 plus extra 1031,
including every fold color, all capacities, actual support fibers, ratio records,
forced-prime-gap cases, previous-survivor comparison and first counterexamples.
The prime-gap lists are independently checked for completeness by check-017.py.
The corrected prime list reaches 2100, covering the largest internal gap 2061.

The final check script passes full manifest equality, all 84 axiom sets, all
8 touched Lean file headers/markers, scoped forbidden-token scans, whitespace
checks for both tracked and untracked sources, all natural-anchor diagnostics,
all individual declaration classifications, ASCII documents, document links,
thirteen report answers, the one next theorem contract and the final Outcome B.
The forbidden tokens are sorry, admit, axiom, native_decide, unsafe and
implemented_by in new production/regression code. #print axioms is the audit
command, not an added axiom declaration. The generic half-step adapter is not
imported by the new Legendre sources or its facade.

Raw compiler logs retain Lean's own Unicode output. New prose/checkpoint
artifacts and diagnostic JSON use ASCII text. The final check output is in
[check-017.txt](logs/check-017.txt). Validation is scoped to these declarations
and finite diagnostics; it does not establish a uniform coverage provider.
