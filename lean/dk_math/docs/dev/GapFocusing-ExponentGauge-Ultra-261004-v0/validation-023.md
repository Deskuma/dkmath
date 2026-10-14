# Validation 023

All commands use the nested project at lean/dk_math. Builds use
LEAN_NUM_THREADS=2. No memory fault occurred. Performance measurements are
individual observed runs with the current dependency cache, not benchmarks
or evidence of a general speed improvement.

| Completed check | Result | Jobs | Seconds | Peak RSS KiB |
| --- | --- | --- | --- | --- |
| Seven focused production and calibration targets | PASS | 9020 | 86.67 | 9686852 |
| DkMath.NumberTheory.Legendre | PASS | 9114 | 13.21 | 6716608 |
| DkMath | PASS | 10416 | 14.03 | 7063784 |
| LegendreRetainedAxiomAudit | PASS | 9124 | 13.71 | 6722260 |

The focused command builds FinsetSupportDirections, CoarseTownRetainedDirections,
CoarseTownSymmetricDeletion, CoarseTownPrimeHandoff, LegendreRetained297Calibration,
LegendreRetained1031Calibration and LegendreHandoffRegression. The separately
recorded 1031 calibration build took 72.82 seconds and peak RSS 9792636 KiB.
The final focused build recompiles the calibration after the direct carrier
partition APIs were added. It checks the same entire arithmetic carriers and
represented counts, not a smaller surrogate.

Successful final evidence:

- [focused-023.txt](evidence/MANIFEST.md#log-dfdcd9ef41987875)
- [facade-023.txt](evidence/MANIFEST.md#log-0c725623bacff71c)
- [root-023.txt](evidence/MANIFEST.md#log-157d43dbc391c65a)
- [axiom-audit-023.txt](evidence/MANIFEST.md#log-23c9291f819af594)
- [1031-023.txt](evidence/MANIFEST.md#log-41047c2c9c0b5bec)

The audit has 144 entries: all 116 new public production declarations, 26
new public regression/calibration declarations and both preserved 022 endpoint
theorems. The generated manifest records file and source line for every entry.
The audit generator includes apostrophes in declaration names, including the
max' and min' adapter names. The first audit generation omitted those suffixes;
the generator and axiom-log parser were repaired. The complete audit includes
the final shared, left and right disjoint carrier partition APIs.

The root build reports five pre-existing unrelated sorry warnings:

- ZsigmondyCyclotomicResearch, line 147.
- TriominoCosmicBranchA, line 4187.
- GcdNextResearch, line 850.
- TriominoFLT, line 1919.
- CyclotomicPrincipalization, line 5389.

It also replays the existing PacketCross unused hrs warning. Root build success
is not an axiom audit of the whole project. The new public declaration audit
checks the dependencies of the requested finite results separately.

The early neutral, retained, symmetric and handoff logs are development trial
logs and may contain failed attempts. The final focused log supersedes those
trials. The 297-handoff and chain-check logs record earlier successful checks;
the final focused build checks the current source including uniform branching
and both full-cycle exclusions.

Discovery is reproducible with checks/discover-023.py. The independent checker
checks/check-023.py reconstructs all 602 worlds using collision edges and an
existential continuation definition rather than copying discovery endpoint
comparisons. It checks both complete represented unions, loss and master
residuals, handoff sources, ranks, depth and the exact better-loss frontier.
The declaration manifest and generated audit are reproduced with its
--generate option. checks/plain-logs-023.py normalizes completed compiler logs
to ASCII while preserving declaration names, logical axiom sets and build
success evidence.

The final independent checker passes all five groups: full public dependency
coverage, standard headers and file markers with forbidden-construct and
whitespace checks, all 602 independently reconstructed diagnostics, twenty
report answers with the exact outcome and four successful build logs, and
ASCII text artifacts. Every audited dependency set is a subset of
{propext, Classical.choice, Quot.sound}; no sorryAx appears. Tracked changes
and all eight new Lean files pass the whitespace check. The neutral module
imports no application NumberTheory module.

Final results: [checks-023.txt](evidence/MANIFEST.md#log-379c12867dc57fc1). The existing source modules
from 022 are unchanged; the tracked production change is the three facade
imports, with new proof and calibration modules added separately.
