# Validation 024

Commands run from lean/dk_math with LEAN_NUM_THREADS=2. No memory fault
occurred. Timings describe individual observed runs with existing dependencies,
not performance improvements or cold-build estimates.

| Completed build | Result | Jobs | Seconds | Peak RSS KiB |
| --- | --- | --- | --- | --- |
| Three focused targets | PASS | 9023 | 18.92 | 6873584 |
| DkMath.NumberTheory.Legendre | PASS | 9116 | 13.09 | 6715372 |
| DkMath | PASS | 10418 | 13.75 | 7064696 |
| LegendreTerminalProductAxiomAudit | PASS | 9127 | 13.61 | 6729224 |

The focused targets are CoarseTownTerminalProduct, CoarseTownSourceMultiplicity
and LegendreTerminalProductCalibration. The separately recorded successful
calibration build took 18.91 seconds with peak RSS 6876696 KiB. The final
focused build checks the current complete calibration source.

Final build evidence:

- [focused-024.txt](evidence/MANIFEST.md#log-89e5736c66a5a917)
- [facade-024.txt](evidence/MANIFEST.md#log-aaa22daa40625a30)
- [root-024.txt](evidence/MANIFEST.md#log-5b1a9c191b267bb6)
- [axiom-audit-024.txt](evidence/MANIFEST.md#log-4f1198bf4af3663b)

The generated audit covers 100 declarations: all 64 public production entries,
33 new public calibration entries and three preserved 023 branching and 022
endpoint names. Private computation adapters are covered through the public
theorem dependencies. The manifest records declaration file and line, and
checks/check-024.py regenerates the complete audit with --generate.

Calibration verifies actual carriers and products at the first recorded
shared-source example n=11 seat19, n=297 shared seat350 and branching seat44,
and n=1031 seat90. It also verifies the exact source sums 9/8 and 48/53 using
the existing checked missing counts, and kernel-checks the n=2 weak-budget
example and base1 boundary. Certified town and old-prime inventories are
reused without modifying or rebuilding their source files.

Root reports five pre-existing unrelated sorry warnings:

- ZsigmondyCyclotomicResearch, line147.
- TriominoCosmicBranchA, line4187.
- GcdNextResearch, line850.
- TriominoFLT, line1919.
- CyclotomicPrincipalization, line5389.

The pre-existing PacketCross unused hrs warning is also replayed. Root build
success does not certify the unrelated root research placeholders. The scoped
public dependency audit is the evidence for the new finite results.

Early terminal-product and source-multiplicity logs record development checks;
the first may preserve an unsuccessful proof attempt. The final focused log
checks the current modules and supersedes those attempts. No failed attempt
is used as proof evidence. Completed compiler logs are normalized to ASCII
by checks/plain-logs-024.py while preserving declaration names, logical axiom
sets and successful build evidence.

The 602 diagnostic worlds retain their existing geometry. The normalized
initial cutoff is max(S), while noninitial supports use the prime lower bound
2. Empty S is explicitly recognized as an initial-cutoff presentation too.
The 68813 oriented deleted-seat records are stored in CSV to avoid repeating
a large pretty-printed JSON document. Aggregates and preserved examples are
in discovery-024.json.

checks/check-024.py independently reconstructs full-town seats by complete
offset range and gcd, factors each complete point by trial division, and
defines terminal membership by absence of any later or earlier supporting
seat. This differs from discovery's prime-fiber extremum calculation.
It independently checks all carrier lists and products, exact source sums,
local and uniform power budgets, global retained-excess contributions and
all capacity comparison flags.

Final result: [checks-024.txt](evidence/MANIFEST.md#log-fa2124658765013d) passes all five groups:
complete public dependency coverage, headers/file markers and forbidden/import
and whitespace checks, independent 602-world and 68813-record reconstruction,
exact source residuals and capacity comparisons, and report/outcome/ASCII
checks with all four successful builds. Every audited dependency set is a
subset of {propext, Classical.choice, Quot.sound}; none contains sorryAx.
The new four Lean files and tracked facade changes pass whitespace checks.

The proposed next cofactor bridge has a separate numerical exploration script
and JSON artifact. The checker recomputes its four difference products directly
and verifies the same gcd/cofactor values, rather than copying the modular
product algorithm. This additional arithmetic check is not a Lean proof of
the proposed next theorem and is not classified as new capacity power.
