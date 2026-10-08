# Validation 030 - Exact scope and final evidence

Commands run from lean/dk_math with LEAN_NUM_THREADS=2:

- lake build DkMath.NumberTheory.Legendre.GnomonCofactorWindow DkMathTest.NumberTheory.GnomonCofactorWindowCalibration
- lake build DkMath.NumberTheory.Legendre
- lake build DkMath
- lake build DkMathTest.NumberTheory.GnomonCofactorWindowAxiomAudit

| Build | Exit | Seconds | Peak RSS kbytes | Major faults | Minor faults | Swaps |
| --- | --- | --- | --- | --- | --- | --- |
| focused | 0 | 32.58 | 6787268 | 0 | 382210 | 0 |
| facade | 0 | 17.866 | 6745432 | 0 | 202257 | 0 |
| root | 0 | 18.475 | 7108304 | 0 | 208158 | 0 |
| axiom-audit | 0 | 16.891 | 6686300 | 0 | 199490 | 0 |

All exits are zero. GNU time includes Lake and waited descendants. There is no
memory failure and all swap counts are zero. Focused build: 8957 jobs;
Legendre facade: 9133 jobs; root: 10429 jobs; axiom audit: 8958 jobs.
The affected implementation is the new GnomonCofactorWindow module, its new
calibration and axiom audit, and one import in the existing facade. Earlier
production modules were inspected/reused but have no source diff.

Axiom coverage is complete for 18 new production declarations and 13 named
calibrations. The three private production helpers occur only under audited
public proofs. The allowed dependency set is propext, Classical.choice,
Quot.sound. No sorryAx or custom axiom occurs in that checked scope.

Focused and axiom builds emit no warnings. Facade/root replay the existing
PacketCross.lean:285 unused-variable warning. Root also replays existing sorry
warnings in ZsigmondyCyclotomicResearch.lean:147, TriominoFLT.lean:1919,
TriominoCosmicBranchA.lean:4187, GcdNextResearch.lean:850 and
CyclotomicPrincipalization.lean:5389. No repository-wide absence claim is made.

The kernel checks certify the first strict slack n=4, exactness n=3,
all n=3..6 consumer margins, the passing anchor 8, and the first failure n=7 by integer products
and log monotonicity. Independent sieve diagnostics cover n=3..5000 and match
the hashed earlier inventory. Large log values and margins are floating only.

The final artifact check verifies all printed names, standard axiom sets,
forbidden constructs, unified headers, immediate file markers, imports,
git diff --check and untracked Lean whitespace, both source digests,
bounded diagnostic identities, Markdown links and ASCII artifacts. The
root build and diagnostics are evidence only for their recorded scopes.

Evidence: [focused](evidence/MANIFEST.md#log-083b4d451d1366ff), [facade](evidence/MANIFEST.md#log-6f6a768985c61bce),
[root](evidence/MANIFEST.md#log-7ebbedc5a426b0d3), [axioms](evidence/MANIFEST.md#log-d0d6959d29e62d15),
[coverage](evidence/MANIFEST.md#log-abc792d831351a16), [diagnostics](evidence/MANIFEST.md#log-3f2ce7bfefe50584),
[artifact audit](evidence/MANIFEST.md#log-508b5b84465b3b8e).

Outcome B - independent finite bound; no universal strict budget gain.
