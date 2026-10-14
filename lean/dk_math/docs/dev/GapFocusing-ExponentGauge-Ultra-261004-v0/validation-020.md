# Validation 020

All commands ran from lean/dk_math with Lean 4.34.1.

## New scope

Four production modules, totaling 68 public declarations:

- DkMath.Combinatorics.FinsetSupportPacking: 3
- DkMath.NumberTheory.Legendre.CoarsePrimeWorldFullTown: 25
- DkMath.NumberTheory.Legendre.CoarsePrimeWorldVerticalCapacity: 28
- DkMath.NumberTheory.Legendre.CoarseTownSupportPacking: 12

The existing Legendre facade gained three specialized imports. The new
regression module has 17 public declarations. Private computed support
helpers are not public API entries. The generated audit checks all 85
public entries, including definitions and their dependencies.

## Performed Lean checks

- Focused build of the four modules and LegendreFullTownRegression:
  passed, 9005 jobs. [Log](evidence/MANIFEST.md#log-bf977e3ccb17eb48)
- lake build DkMath.NumberTheory.Legendre:
  passed, 9106 jobs. [Log](evidence/MANIFEST.md#log-ca35877c28879e10)
- lake build DkMath:
  passed, 10408 jobs. [Log](evidence/MANIFEST.md#log-a4ca4d223187fea1)
- lake build DkMathTest.NumberTheory.LegendreFullTownAxiomAudit:
  passed, 9109 jobs. [Log](evidence/MANIFEST.md#log-f5ac6cb90674922c)

The final regression additions only changed test modules. The facade and
root logs cover the final production sources; the focused and audit logs
cover the final test sources as well.

Each manifest entry has both a check command and a print-axioms command.
All 85 resulting dependency sets are subsets of propext, Classical.choice,
and Quot.sound. No new declaration depends on a proof-hole axiom.
[Complete manifest](evidence/MANIFEST.md#log-f345e5063ca99a33)

The root log retains five existing proof-hole warnings in:

- ZsigmondyCyclotomicResearch.lean:147
- FLT/PrimeProvider/TriominoCosmicBranchA.lean:4187
- GcdNextResearch.lean:850
- FLT/Kummer/CyclotomicPrincipalization.lean:5389
- CosmicFormula/TriominoFLT.lean:1919

The retained PacketCross binder warning for hrs is also replayed.
These files were not changed in this checkpoint. Root build success is
not asserted to certify the entire pre-existing project without holes.
The complete new-API dependency audit supplies the narrower guarantee.

## Regression scope

Kernel checks cover zero modulus, the modulus-one endpoint, K=2 equality,
the inherited n=3 reuse example, uniformly sparse columns failing global
separation, n=5 same-column reuse, the old-pass/new-fail n=5 frontier,
all fifteen distinct discovered vertical-deficit pairs and their prime
consumer, n=11 empty edges and its packing consumer, the 31-versus-32
multi-prime edge overcount, canonical phase/block-shift arithmetic, and
the 1031 grid cardinality and column family theorem.

No compiled-code decision shortcut was used. Greedy diagnostic families
and the full 41-row edge-obstruction census are not promoted to kernel
certificates.

## Discovery and artifact checks

[discover-020.py](checks/discover-020.py) writes 602 exact finite rows for
n=1..300 and n=1031 in the same operational worlds as 019.
[check-020.py](checks/check-020.py) reconstructs each grid and its supports,
builds edges independently by prime-fiber unions, checks all recorded
counts and families, and audits the complete declaration manifest.
The checker also verifies headers, immediate import markers, forbidden
constructs, neutral dependency direction, ASCII prose without backslashes,
report sections and judgment, successful logs, and whitespace.

The tracked diff and every newly written Lean file pass whitespace checks.
The complete artifact checker passed; its output is preserved in
[check-020.txt](evidence/MANIFEST.md#log-b78fe00d396cd27d).
