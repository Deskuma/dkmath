# Validation 018

Commands ran in lean/dk_math using the repository-pinned Lean4.34.1.
CenteredFoldSupportNorm was extended, CenteredFoldGcdAggregate was added, and
the Legendre facade exports the aggregate module. One regression and one axiom
module were added. Existing017 declarations and their mathematical meanings
were retained. All5 touched Lean files use the uniform copyright header and
import-adjacent full-module file marker.

## Build evidence

Every final command completed successfully. Job totals are Lake dependency
tasks, not counts of changed or freshly compiled modules.

| Command | Jobs | Log |
|---|---|---|
| lake build DkMath.NumberTheory.Legendre.CenteredFoldSupportNorm | 8993 | [local-gcd-018.txt](evidence/MANIFEST.md#log-a7d1b4783c796a56) |
| lake build DkMath.NumberTheory.Legendre.CenteredFoldGcdAggregate | 8994 | [aggregate-018.txt](evidence/MANIFEST.md#log-59f285493d126103) |
| lake build DkMathTest.NumberTheory.LegendreFoldGcdRegression | 9077 | [regression-018.txt](evidence/MANIFEST.md#log-692b847e41b16058) |
| lake build DkMathTest.NumberTheory.LegendreFoldGcdAxiomAudit | 9113 | [axiom-audit-018.txt](evidence/MANIFEST.md#log-5d14760813c48903) |
| lake build DkMath.NumberTheory.Legendre | 9097 | [facade-018.txt](evidence/MANIFEST.md#log-609daf97d81a813d) |
| lake build DkMath | 10401 | [root-018.txt](evidence/MANIFEST.md#log-9c1966c529711dfb) |

Intermediate gcd-rewrite, polynomial-name/cast and finite valuation calibration
errors were repaired before final validation. The final new-source builds have
no linter warnings. The full build reports the same five existing declarations
using sorry outside the new public declaration dependency sets:

- DkMath/NumberTheory/ZsigmondyCyclotomicResearch.lean:147.
- DkMath/FLT/PrimeProvider/TriominoCosmicBranchA.lean:4187.
- DkMath/NumberTheory/GcdNextResearch.lean:850.
- DkMath/FLT/Kummer/CyclotomicPrincipalization.lean:5389.
- DkMath/CosmicFormula/TriominoFLT.lean:1919.

A successful root build is not a whole-repository no-sorry certificate. The
scoped public axiom audit below supplies that evidence for the checked results.

## Complete public declaration trust scope

There are52 new production declarations:13 added to CenteredFoldSupportNorm
and39 in CenteredFoldGcdAggregate. They include49 theorems,2 definitions and
1 abbreviation. There are20 new regression theorems, hence72 new declarations.
The audit additionally checks the14 existing declarations in the extended norm
module, for86 complete public declaration axiom sets.

The manifest [declaration-coverage-018.json](evidence/MANIFEST.md#log-441fdd5dfd7cd7bd)
records source names, kinds, positions and whether each declaration is new
relative to the initial HEAD baseline. Attribute-prefixed declarations are
included. Every public declaration has both #check and #print axioms in
LegendreFoldGcdAxiomAudit.lean.

Every complete axiom set is a subset of propext, Classical.choice and Quot.sound.
No sorryAx or additional axiom appears. This includes both explicit cyclotomic
evaluation orientations, the existing order-four-address consumer, the uniform
positive-anchor norm primality detector and all valuation formulas. Proof
auxiliaries are included through the checked public dependency closures.

## Kernel regressions

The20 regression declarations check gap one; zero boundary; prime norms5/13;
fresh gcd5 at3; old gcd5 at6; repeated local gcd25 at21; a gcd above its anchor
still containing old support; distinct aggregate values and valuations at8;
small odd prime support; an exact fresh-support packet; covered coprime
subfamilies at4 and5; prime norm177013 at297 with both products equal1;
1031 prime visibility/exclusion without huge products; a fourth-order
cyclotomic address; consecutive aggregate separation; the empty full-cover
counterexample; prime recurrence at nonconsecutive anchors3/6; and prime norm
with failure of full coverage at5.

The297 prime certificate is kernel-checked anew. Its aggregate and local
product value1 follow symbolically rather than by expanding the huge odd
product. The1031 regression checks divisibility by5 and61 and invisibility of
6977, not the whole census. The exact1031 aggregate value305, nontrivial-pair
count220 and multiplicity map5^206*61^17 remain Python diagnostics. The earlier
017 per-prime common-support counts206/17 were already kernel-checked.
No native_decide is used.

## Diagnostics and source checks

Executed commands:

    python3 docs/dev/GapFocusing-ExponentGauge-Ultra-261004-v0/checks/discovery-018.py
    python3 docs/dev/GapFocusing-ExponentGauge-Ultra-261004-v0/checks/check-018.py --generate
    python3 docs/dev/GapFocusing-ExponentGauge-Ultra-261004-v0/checks/check-018.py
    git diff --check

The finite discovery checks every natural anchor0..300 plus1031 with integer
gcds and exact factorizations. Products are stored as support/valuation maps,
not huge decimal integers. The source/check script verifies:

- Complete source manifest equality and all86 public axiom sets.
- All5 touched Lean file headers and exact file markers.
- Scoped absence of sorry, admit, axiom, native_decide, unsafe and implemented_by.
- Tracked and untracked source whitespace, plus git diff --check.
- Complete finite odd-prime support, factorization minima, old/fresh split,
  bounded first counterexamples and selected1031 statistics.
- ASCII prose, no backslash notation, valid links, all14 report answers, the
  single next theorem contract and the final Outcome B.
- All final focused, facade and root logs end with successful build evidence.

Raw compiler logs retain Lean's Unicode output. New instruction/findings/report
artifacts are ASCII text without LaTeX control sequences. Existing reports and
instructions were not rewritten. The final machine-readable check output is
[check-018.txt](evidence/MANIFEST.md#log-c01f5969a221b95a).

## Mathematical boundary

No positive full-cover shell occurred in the finite scan. The scan therefore
cannot refute positive-anchor implications from full cover. Covered subfamilies
and the empty shell are explicitly distinguished from fully covered positive
shells. No logical-independence claim, uniform coverage obstruction, Legendre
result, asymptotic claim or primitive first-appearance law is inferred.
The next prime-power floor contract is proposed, not implemented in this checkpoint.
