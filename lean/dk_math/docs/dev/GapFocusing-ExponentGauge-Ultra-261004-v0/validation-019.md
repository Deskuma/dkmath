# Validation 019

Toolchain: the live nested Lake checkout, Lean 4.34.1.
Working directory: lean/dk_math.

## Source and mathematical scope

The production changes are two Legendre modules and one neutral Primitive
helper, plus extraction of the existing PacketCross proof and two facade
imports. The public PacketCross proposition and its named hrs premise are
retained. The extraction no longer needs that premise; Lean reports an unused
variable warning on that existing declaration. The new module proofs are
complete finite arithmetic, with no added axioms or proof holes.

The first broader import was removed after it exposed two redundant tactic
tails in an existing downstream proof. That existing source was not edited.
The helper now imports only Mathlib.Data.Nat.Prime.Basic. Primitive still
imports no Legendre module.

## Reproducible commands

```text
lake build DkMath.NumberTheory.Primitive.CrossPeriod DkMath.NumberTheory.Legendre.PacketCross DkMath.NumberTheory.Legendre.PrimeWorldPacketBridge DkMath.NumberTheory.Legendre.CoarsePrimorialTown DkMathTest.NumberTheory.LegendreCoarseTownRegression
lake build DkMath.NumberTheory.Legendre
lake build DkMath
lake build DkMathTest.NumberTheory.LegendreCoarseTownAxiomAudit
python3 docs/dev/GapFocusing-ExponentGauge-Ultra-261004-v0/checks/discover-019.py
python3 docs/dev/GapFocusing-ExponentGauge-Ultra-261004-v0/checks/check-019.py
```

## Build evidence

All final sequential checks passed:

| Check | Result | Evidence |
| --- | --- | --- |
| Five focused targets, including 11 regressions | Success, 9000 jobs | logs/focused-019.txt |
| Legendre facade | Success, 9102 jobs | logs/facade-019.txt |
| Root DkMath | Success, 10404 jobs | logs/root-019.txt |
| Complete public declaration audit | Success, 9104 jobs | logs/axiom-audit-019.txt |

The public dependency audit contains 65 complete axiom sets; all are empty
or subsets of propext, Classical.choice and Quot.sound. There is no sorryAx.
The root replays five existing proof-hole warnings, in
ZsigmondyCyclotomicResearch, TriominoCosmicBranchA, GcdNextResearch,
CyclotomicPrincipalization and TriominoFLT. The retained PacketCross order
premise adds the documented unused-variable warning. No new module has a
proof-hole warning. Root success is not evidence that every repository
theorem is free of proof holes.

## Public API and trust audit

The generated declaration-coverage-019.json manifest covers every new public
definition, abbreviation and theorem: 53 production declarations and 11
regressions, plus the retained collision theorem, for 65 total checks.
LegendreCoarseTownAxiomAudit prints each type and its complete axiom set.
The audit script accepts only propext, Classical.choice and Quot.sound.
Private helper dependencies are consequently covered transitively.

## Regression and diagnostic scope

The kernel regressions preserve modulus one, distinguish phased offsets
from offset units, check an anchor not divisible by its modulus, refute
whole-town support separation despite local coprimality, distinguish
incidences from packets, preserve near-pair repeated occupancy, certify the
n=6 four-seat family through the existing capacity consumer, and reject
embedding the full n=3 odd-gap radical below that anchor.

The diagnostic generator uses exact integer arithmetic for anchors 1..300
and 1031, with two fitting finite worlds, for 602 rows. Its results are not
kernel proofs. The independent audit reconstructs actual supports and
ordered incidence occupancies, checks near/far decomposition, verifies the
greedy family's pairwise support disjointness, and compares all recorded
counts. Original 018 fold statistics are retained in each row.

## Artifact and whitespace checks

The final script checks complete declaration coverage, scoped forbidden
constructs, all touched Lean headers and import-adjacent file markers,
Primitive dependency direction, tracked and untracked whitespace, ASCII
and absence of backslash notation in new prose artifacts, report links,
sixteen answers, and the exact final judgment. Raw compiler logs may contain
Unicode. Root build success is not a repository-wide no-sorry claim;
transitive public axiom audits cover the specified 65 declarations.

Final check-019.py result: all public axiom, source, 602-row diagnostic,
ASCII report, sixteen-answer, and build-evidence checks passed. The complete
output is logs/check-019.txt.
