# Validation 031 - Final checked scope

Commands executed from lean/dk_math with LEAN_NUM_THREADS=2:

- lake build DkMath.NumberTheory.Legendre.GnomonCofactorSieve DkMathTest.NumberTheory.GnomonCofactorSieveCalibration
- lake build DkMath.NumberTheory.Legendre
- lake build DkMath
- lake build DkMathTest.NumberTheory.GnomonCofactorSieveAxiomAudit

| Build | Exit | Seconds | Peak RSS kbytes | Major faults | Minor faults | Swaps |
| --- | --- | --- | --- | --- | --- | --- |
| focused | 0 | 8.365 | 969160 | 0 | 33992 | 0 |
| facade | 0 | 13.868 | 6745696 | 0 | 197696 | 0 |
| root | 0 | 14.676 | 7110708 | 0 | 208666 | 0 |
| axiom-audit | 0 | 13.946 | 6687756 | 0 | 198883 | 0 |

All exits are zero. GNU time includes Lake and waited descendants. No build
memory failure occurred. The affected Lean files are the new production
module, calibration, audit and one facade import. Earlier modules have no diff.
The complete audit covers 13 production and 13 named calibration declarations;
only propext, Classical.choice and Quot.sound occur, with no sorryAx. Private
calibration helpers are covered transitively. Focused and axiom logs have no
warnings. Inherited facade/root warning scope is recorded below; root success
is not a repository-wide absence-of-sorry certificate.

facade: 1 inherited warnings.
- warning: DkMath/NumberTheory/Legendre/PacketCross.lean:285:5: Variable name `hrs` is not explicitly referenced.

root: 6 inherited warnings.
- warning: DkMath/NumberTheory/Legendre/PacketCross.lean:285:5: Variable name `hrs` is not explicitly referenced.
- warning: DkMath/NumberTheory/ZsigmondyCyclotomicResearch.lean:147:6: declaration uses `sorry`
- warning: DkMath/CosmicFormula/TriominoFLT.lean:1919:6: declaration uses `sorry`
- warning: DkMath/FLT/PrimeProvider/TriominoCosmicBranchA.lean:4187:8: declaration uses `sorry`
- warning: DkMath/NumberTheory/GcdNextResearch.lean:850:6: declaration uses `sorry`
- warning: DkMath/FLT/Kummer/CyclotomicPrincipalization.lean:5389:8: declaration uses `sorry`

Kernel checks certify basis/product, n=3 equality, n=7 carriers/products/strict
saving/consumer, absence of composites at 3..8, exact log(49) error at 9,
non-prime-power survivor 77 at 12, integer and symbolic-log consumer failure
at 29, and period-density/unsafe-basis endpoint counterexamples. n=29 first
failure minimality is diagnostic only. Scoped recursion/heartbeat allowances
for its large finite products are documented in calibration source; binomial
computation uses the proved fast_choose identity, not native_decide.

Independent diagnostics cover n=3..5000, with 14 directly factored anchors and
four admissible fixed wheel alternatives. All weighted numeric margins are
floating-only diagnostics. The artifact audit checks source digest, all rows,
exact anchor carriers, integer obstructions, public axiom coverage, forbidden
constructs, headers, file markers, whitespace, Markdown links and ASCII logs.

Evidence: [focused](evidence/MANIFEST.md#log-45e3a6ccd33b5708), [facade](evidence/MANIFEST.md#log-9c53c17dcac01b68),
[root](evidence/MANIFEST.md#log-29cdadffa806ff5b), [axioms](evidence/MANIFEST.md#log-413216b50e5f68fe),
[coverage](evidence/MANIFEST.md#log-eed5d0b250c34e4e), [diagnostics](evidence/MANIFEST.md#log-52fe69656210b928),
[artifact audit](evidence/MANIFEST.md#log-f315ce579d0caa41).

Outcome B - independent finite wheel bound; accumulated error remains uncontrolled.
