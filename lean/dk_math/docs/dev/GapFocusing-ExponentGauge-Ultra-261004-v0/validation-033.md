# Validation 033 - Final checked scope

Commands executed from lean/dk_math with LEAN_NUM_THREADS=2:

- lake build DkMath.NumberTheory.Legendre.GnomonCofactorSemiprime DkMathTest.NumberTheory.GnomonCofactorSemiprimeCalibration
- lake build DkMath.NumberTheory.Legendre
- lake build DkMath
- lake build DkMathTest.NumberTheory.GnomonCofactorSemiprimeAxiomAudit

| Build | Exit | Seconds | Peak RSS kbytes | Major faults | Minor faults | Swaps |
| --- | --- | --- | --- | --- | --- | --- |
| focused | 0 | 7.747 | 969916 | 0 | 33179 | 0 |
| facade | 0 | 13.225 | 6748736 | 0 | 200541 | 0 |
| root | 0 | 13.764 | 7109584 | 0 | 206987 | 0 |
| axiom-audit | 0 | 12.856 | 6691424 | 0 | 198028 | 0 |

All exits are zero. GNU time includes Lake and waited descendants, with no
build memory failure. Changes comprise the new production module, calibration,
axiom audit and one facade import. Earlier production modules have no diff.
All 15 production and ten named calibration declarations are covered;
only propext, Classical.choice and Quot.sound occur, with no sorryAx.
The private production pair-facts helper and private calibration helpers are
covered transitively. Focused and axiom builds have no warnings. Inherited
warnings are recorded below; root success is not a whole-repository no-sorry
certificate.

facade: 1 inherited warnings.
- warning: DkMath/NumberTheory/Legendre/PacketCross.lean:285:5: Variable name `hrs` is not explicitly referenced.

root: 6 inherited warnings.
- warning: DkMath/NumberTheory/Legendre/PacketCross.lean:285:5: Variable name `hrs` is not explicitly referenced.
- warning: DkMath/CosmicFormula/TriominoFLT.lean:1919:6: declaration uses `sorry`
- warning: DkMath/NumberTheory/ZsigmondyCyclotomicResearch.lean:147:6: declaration uses `sorry`
- warning: DkMath/FLT/PrimeProvider/TriominoCosmicBranchA.lean:4187:8: declaration uses `sorry`
- warning: DkMath/NumberTheory/GcdNextResearch.lean:850:6: declaration uses `sorry`
- warning: DkMath/FLT/Kummer/CyclotomicPrincipalization.lean:5389:8: declaration uses `sorry`

Kernel checks include 49/77 pair and product membership, complete witness
coverage and Z=Q at 9,12,29,31, exclusion of the two 539 representations,
all residual windows at 32, preserved consumer at 29, exact integer products
and strict consumer recovery at 31, strict improvement over 032 at 31, and
equality at 3. Scoped recursion/heartbeat allowances for the 31 products are
documented; binomial computation uses the proved fast_choose identity.
No native_decide or custom evaluation axiom is used.

Independent diagnostics retain 300 rows: n=3..300 plus 1031 and 5000, with
14 direct anchor reconstructions. The first numeric failure 210
and its minimality are diagnostic only, not kernel claims. Audit checks
source digests, exact endpoint prime-pair carriers, product injection,
composite and square inclusion, finite weighted identities and floating-only
margins. Target factorization in diagnostics is not used to construct D.
Additional checks cover public axiom names, forbidden constructs, import
scope, headers, immediate file markers, whitespace, Markdown links and ASCII
logs. Results are evidence only for these recorded scopes.

Evidence: [focused](evidence/MANIFEST.md#log-b482f17c2ceab9f1), [facade](evidence/MANIFEST.md#log-18bb7b707606133e),
[root](evidence/MANIFEST.md#log-12bda66ec2ee5ae1), [axioms](evidence/MANIFEST.md#log-ed92341eb0d9ed49),
[coverage](evidence/MANIFEST.md#log-558f80e854573f6e), [diagnostics](evidence/MANIFEST.md#log-b00f73678067f7c1),
[artifact audit](evidence/MANIFEST.md#log-677d0385b2a07d0b).

Outcome B - distinct semiprime correction; no global closure.
