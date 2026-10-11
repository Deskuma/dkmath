# Review 042 — source-backed correction of Row-Z frontier and STOP042

Date: 2026-10-11
Branch: `feature/GTail-SelectiveGap-FLT7-261009-v0`
Decision: **APPROVED — Step 042 COMPLETE / Outcome B (research/source audit) / STOP042**
Step043: **NOT SELECTED.** This review is a correction to `review-041.md` and `instruction-042.md`, not a new proof or implementation instruction.

## Evidence and verification level

Read from the pushed GitHub branch:
- `report-042.md`, `source-inventory-042.md`, `research-decision-042.md` and the appended Step042 ROADMAP checkpoint;
- **actual proof code** `SevenBaseTerminalRowZSignedResidualCore.lean` (especially `exists_residualCore_eq_seventh_power`, `nonempty_signedRamifiedArithmeticObligation`, `signedRamifiedArithmeticObligation`, `signedRamified`, `ramifiedChartResolution`);
- `SevenBaseTerminalRamifiedSummit.lean` (actual `nonempty_ramifiedSummit` and canonical summit);
- `SevenBaseTerminalFermatChartResolution.lean` (the older TERM-009 obligation and subtype);
- `SevenBaseTerminalDescentProvider.lean`, `SevenBaseTerminalDescentSeedExclusion.lean` (seed↔closure, lifted necessary depth and negative terminal result);
- `SevenRamifiedFusionDirectChartObstruction.lean`, `SevenRamifiedFusionStrictDescentFailureBoundary.lean`, `SevenBaseTerminalLiftedReconstruction.lean`, `SevenBaseTerminalCellCarryDependency.lean` (previously read for review-041);
- `DkMath.FLT.Seven.Basic.CounterexamplePack` and Step039–041 actual conclusions.

**This was a source-documentation audit only.** Codex explicitly reports no new Lean source/test declaration, no #check/#print audit, no Lean or Lake build. Reviewer checked the pushed GitHub code and documents, NOT an independent Lean build. The ROADMAP records only the new Step042 appendix and preserves earlier entries. No full Git tree identity/diff was independently recomputed locally.

## Critical correction: terminal Row-Z is ALREADY CLOSED at TERM-010

The prior `review-041.md` and `instruction-042.md` characterized
`AwaySevenBaseTerminalRowZSignedRamifiedArithmeticObligation` (root in `TraceOneInt (-2)` satisfying `cyclotomicSevenToTraceOne (x:ℤ) (-(y:ℤ))=sevenAxis*root^7`) as an unresolved extraction. **That statement is false for the current complete repository.** It reflects the intermediate TERM-009 declaration but ignores its **later constructor/consumer**:

1. `AwaySevenBaseTerminalRowZSignedResidualCore.exists_residualCore_eq_seventh_power` proves the real discriminant−7 residual core is a seventh power using checked coprimality with its conjugate and the genuine earlier `exists_eq_seventh_power_of_coprime_mul_eq_pow` extraction; the proof consumes actual signed norm=b^7.
2. `AwaySevenBaseTerminalRowZProfile.nonempty_signedRamifiedArithmeticObligation` is an **inhabited** theorem under the actual Row-Z terminal profile; it builds the subtype witness by rewriting the real source coordinate equation.
3. `AwaySevenBaseTerminalRowZProfile.signedRamifiedArithmeticObligation` chooses an inhabitant, and `AwaySevenBaseTerminalRowZProfile.signedRamified` supplies the complete `SignedRamifiedCoordinateNormalForm (z:ℤ) (-(y:ℤ)) (x:ℤ)`.
4. `AwaySevenBaseTerminalUnitSectorPacket.ramifiedChartResolution` resolves surviving terminal Row-Y to a natural and Row-Z to a signed ramified chart; Row-Sum is already excluded.
5. `SevenBaseTerminalRamifiedSummit.AwaySevenBaseTerminalUnitSectorPacket.nonempty_ramifiedSummit` **further constructs one common primitive ramified summit** for the terminal packet. Thus even “Row-Z is now ramified but no common summit exists” would be outdated.

**Explicitly withdraw the Row-Z-extraction OPEN claim** from the mathematical status in `review-041.md` / `instruction-042.md`; retain those historical files unchanged as requested. This correction supersedes their old fact claim; it does **not** retroactively invalidate correct Step041 numerical/Lean results.

**Important non-implication:** An inhabited signed ramified form or common summit is *not* the nonexistence of original primitive Fermat7 counterexamples, not a primitive next counterexample and not a global ramified closure theorem. The remaining obstruction lies strictly downstream of TERM-010.

## Correct branch decisions and proof directions

### Terminal pivot exponent ONE
`SevenBaseTerminalDescentSeedExclusion.no_descentReconstructionSeed_of_exponent_eq_one` proves **¬Nonempty** of the reconstruction seed, and `no_descentClosureProvider_of_exponent_eq_one` proves **¬Nonempty** of the original provider. This follows from `seed.two_le_pivotExponent`: such a seed implies ≥2, inconsistent with exponent=1. A universal terminal seed proposal is **mathematically refuted**, not merely unproved. However, **this is not a proof that the source `CounterexamplePack` itself cannot exist**. Terminal Row-Y/Z instead reach the already constructed ramified summit.

### Lifted pivot exponent ≥ TWO
The `2≤exponent` test is only **necessary** for `AwayDescentReconstructionSeed`; it is not a sufficient existence theorem. `SevenBaseTerminalDescentProvider` already proves an inhabited seed ↔ original closure provider, and actual seed → next primitive counterexample with strict carrier depth reduction, but the proof still requires a **concrete nextX/Y/Z map**, an inhabited `AwayCoordinateNormalForm`, and an `AwayExceptionalCarrierSource` matching the old root second-coordinate absolute carrier. The audit identifies no independently justified new triple formula, and so does **not** select a fictitious Step043 seed implementation.

### Ramified FUSION and direct chart shortcut
`SevenRamifiedFusionDirectChartObstruction.no_direct_signedFermatSevenChart` rules out the *visible extracted roots* as an immediate signed Fermat chart by exact 7-adic depth5; it **does not** contradict the original hypothetical chart. The internal carrier depth drop5→4 is real, but `InternalDepthFourCounterexampleReconstructionObligation` remains **not inhabited by the checked boundary**. Lack of an inhabitant is not a proof of its negation. Also existing downstream finite/nested/centered receiver obstructions or conditional exclusions are not blanket impossibility of **every** reconstructed primitive chart.

### Original CRT integer residual
`SevenBaseTerminalLiftedReconstruction.modulus_dvd_originalReconstructionDefect` proves the four **actual original-integer coordinate residuals** are multiples of the combined modulus. The centered `integerWeightedDefect` is a different object. Centering each representative does not bound `model * scale^3` or `model * scale^7`; no independent four-coordinate `abs(originalResidual)<M` source theorem is supplied. Even if such bounds forced exact original-coordinate reconstruction, an additional **original↔centered bridge or row-specific contradiction** would be required. The nine fixed first-residual identities are already linear combinations of universal/endpoint/root residuals and add no new independent equation.

### Step040 proof direction
Full prime-square support + strict defect magnitude bound implies Δ=0 and **Fermat7Equation**, not FLT7 impossibility. This observation and the two genuine Step041 independence witnesses were verified. Simply using the exact Fermat equation to derive the support/size hypotheses and then restoring the same equation would be circular as a FLT7 argument.

## Scientific decision and acceptance

**APPROVED — Outcome B documentation correction and proof-branch audit.** It adds no new checked mathematical proposition but materially corrects the research frontier. `research-decision-042.md` correctly declines to choose Step043: (I) the signed Row-Z extraction is already proved; (II) lifted-away has no explicit new natural primitive triple map; (III) CRT has no independent original-coordinate magnitude inequality or downstream contradiction. This is the instruction's explicit **STOP** branch, not an incomplete implementation.

**Re-entry criteria:** Before any new implementation instruction, specify at least ONE source-compatible noncircular arithmetic lemma with concrete algebraic expressions and an actual path to either contradiction or a well-founded primitive counterexample descent, and verify it is neither already proved in later owners nor excluded by the current boundary theorems. Good next targets to *research, not assume*, include an explicit lifted new-triple construction (with primitive additive identity and source-match) or a proved original CRT discrepancy bound coupled to a genuine row contradiction; the successful Row-Z extractor alone is not a target.

No `instruction-043.md` is created. No Lean owner or test edits, fake build/public axiom verification, PR, merge, rebase, facade change, arbitrary local modulus/depth ladder, or FLT7 theorem are authorized or claimed.

**Method correction for future reviews:** trace each obligation from **definition → later inhabited constructor → actual consumer → latest facade/import and roadmap** before declaring a frontier “open”. The previous reviewer failed that post-owner check at TERM-010; the user's correction is sustained by the actual code.
