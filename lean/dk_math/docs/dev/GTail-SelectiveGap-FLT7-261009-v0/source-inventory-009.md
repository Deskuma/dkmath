# Source inventory 009 — seven-unit focused branch

Date: 2026-10-09 (JST). Branch `feature/GTail-SelectiveGap-FLT7-261009-v0`; initial clean worktree; HEAD `0c83f1bf50fd067bc8eaf888bd0ab3e794bf256b`. Step 009 only, no facade promotion, branch operation or full-suite build.

## Direct existing inputs

- `DkMath/FLT/Seven/GTailValuationAudit.lean`, `padicValNat_focused_gap_balance`: natural a,b,c,g; positive a,b, Fermat7Equation a b c, a+b=c+g, ¬7∣c yield `v7(g)=v7(a)+v7(b)+v7(a+b)+2*v7(Q)` with Q=a²+ab+b². This is the exact input for the focused unit simplification.
- `GTailConstraintAudit.seven_dvd_focused_gap`: only exact Fermat equation and sum relation give 7∣g. `fermat7_focused_bounds`: positive a,b and the equation give max a b<c<a+b, hence g≠0 under the sum relation. No full primitivity premise is added here.
- `DkMath/Lib/Cosmic/GTailSevenValuation.lean`: `padicValNat_gtail_seven_eq_one` needs 7∣g and ¬7∣c; the residual is nonzero by the excluded second divisibility layer. `padicValNat_gap_mul_gtail_seven` additionally needs g≠0. Both are upstream via Step 008; neither is rewritten.
- `DkMath/Lib/NumberTheory/PadicValNat.lean`: `Vp_ge_one_iff hp hn` converts 1≤v_p(n) to p∣n for prime p, n≠0. `padicValNat_le_iff_dvd hp hn k` converts k≤v_p(n) to p^k∣n. Existing generic carrier shape theorem concerns a prime-power product and has a different residual equation; it is not reused as if the squared-Q product were a seventh power.
- Mathlib `padicValNat.eq_zero_of_not_dvd` needs only ¬p∣n. `padicValNat.mul` needs a prime Fact instance and both factors nonzero. `padicValNat.pow` needs the prime Fact instance and no nonzero premise. The new neutral proof explicitly tracks every nonzero product factor.

## Existing FLT7 local interfaces: inspected, not imported

| Source and endpoint | Actual hypotheses/conclusion | Relation to Step 009 |
| --- | --- | --- |
| `ModSevenSectors.fermat7Equation_modSeven_linear` | exact equation gives x+y=z in ModSeven | Existing linear residue necessity. New sum-unit transfer uses the proved 7∣g plus natural sum divisibility, avoiding this heavier owner. |
| `SevenBaseFirstOrderModSeven.AwaySevenBaseCarrierQuotient.first_order_eq_mod_seven` | typed AwaySevenBaseCarrierQuotient q over pivot/routing packets gives its row-sensitive first-order core equation in ZMod 7 | Different routed quotient data; not inferred from the focused sum gap alone. |
| `PrimitiveCyclotomicDepth.fortyNine_dvd_cyclotomicSeven_sub_seven_mul_pow` | integer 7∣z-y gives 49∣cyclotomicSeven z y - 7*y⁶ | Existing residual head congruence; difference carrier, not g=a+b-c. |
| `PrimitiveCyclotomicDepth.not_fortyNine_dvd_cyclotomicSeven` | same integer gap premise and ¬7∣y exclude 49∣kernel | Residual has one layer while the focused carrier may have ≥2; no contradiction between these allocations. |
| `SevenBaseTerminalRamifiedUnitClassAudit.RamifiedGapUnitBridgePacket.isSeventhPowerMod49_iff_residue` | typed packet's explicitUnit 2 is a seventh power mod49 iff its residue is one of 1,18,19,30,31,48 | Finite unit-image classification, not the scalar focused carrier divisibility or a global unit-class receiver. |
| `SevenRamifiedFusionAllocationResidueSieve.fortyNinth_power_mod_seven_cube_of_one` | Nat.ModEq 7 s 1 gives Nat.ModEq (7³) (s^49) 1 | Explicit mod343 lifting theorem on a different power. |
| Same source, `nested_full_gap_residue_sieve` | ¬7∣w and ModEq (7^27*r^49) (s^49) (w⁶) give s≡1 mod7 and w⁶≡1 mod343 | Requires an exact large-modulus allocation congruence; not available from an ordinary mod49 Fermat compatibility check. |
| Same source, `nestedGNResidual_residue_sieve` | Coprime u (7*M) and GN 7 (7^27*r^49) u=7*s^49 give the corresponding mod7/mod343 pair | Different normalized receiver/equation; no transfer to a focused gap is assumed. |
| `RoutingLocalSolubility.nonempty_localSolution_leftCubic_of_root` | prime q≠7 and a normalized cubic root in ZMod q give a local solution in each routing row | Local satisfiability, not a global equation/descent provider. |

This is an explicit bounded overlap comparison, not an exhaustive classification of every FLT7 theorem. No novelty, equivalence to the packet constraints, or new obstruction is claimed. The new endpoints package necessary scalar valuation consequences; Outcome B.

## New ownership and audit

Neutral `DkMath.Lib.NumberTheory.SevenUnitAllocation` imports only Lib.NumberTheory.PadicValNat. It has two endpoints: squared-factor allocation in an exact abstract product, and conversion of positive doubled valuation into 49-divisibility. Conditional `DkMath.FLT.Seven.GTailSevenUnitAudit` imports only GTailValuationAudit and the neutral allocation module. It has four endpoints: sum-unit transfer, doubled valuation, Q seven-divisibility and focused g forty-nine-divisibility. Tests separately import their direct owners. No reverse Lib→FLT import or production→test import.

Comment-stripped header closure audit: neutral owner 1074 source names / 2 local modules; conditional owner 8797 / 17; neutral test 1075 / 3; conditional test 8798 / 18. DFS union: 19 local modules, no cycle. Neutral closure has zero FLT modules; owner closure has no Seven facade, routing/descent/closure owner. External terminal names are included, implicit compiler/native dependencies are not. Counts are source reachability, not jobs/kernel proof evidence. Local full lists are in `.lake/build/gtail-step009/imports.json`.

Lib/Seven facades, root test driver, ledger, Step 008 sources and LegendreMergedCRT stay unchanged. Test submodule glob discovers the two new tests; only focused builds are scheduled. Optional aggregate-unit adapter is not needed and not implemented.
