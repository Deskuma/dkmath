# Review 032 — exact GTail balance equivalence and bounded local-sufficiency countermodel

Date: 2026-10-11
Branch: `feature/GTail-SelectiveGap-FLT7-261009-v0`
Decision: **APPROVED — Step 032 COMPLETE / Outcome B**

## Evidence and verification limits

Statically inspected pushed GitHub files:
- `DkMath/FLT/Seven/GTailGlobalBalanceFirewall.lean` (39 lines);
- `DkMathTest/FLT/Seven/GTailGlobalBalanceFirewall.lean` (184 lines, 38 reported examples);
- `report-032.md`, `source-inventory-032.md`, `frontier-032.md`;
- prior `GTailBridge`, conditional Step010/031 arithmetic, Step017 Eisenstein ideal address and Steps025/029/030 cyclotomic depth; original `DescentClosureAudit` and `SevenRamifiedSignedRootDepth` read only as future-owner comparators.

Reviewer **did not independently run Lean**. Codex reports final focused production and test builds passing (source 01; final test 04), Step031, Step030 and `GTailBridge` regressions passing, 38 examples and the two new public declarations' `#print axioms` restricted to `propext`, `Classical.choice` and `Quot.sound`. Build 02 correctly rejected a false historical-focus assertion; test revision and final build 03/04 passed. Local source/import/whitespace/forbidden-token scans were reported clean; no full clean repository build has been claimed.

## Actual Lean proof audit

1. `fermat7Equation_iff_focused_scalar_balance`, for any naturals a,b,c,g and **only** `a+b=c+g`, proves `Fermat7Equation a b c ↔ g*GTail 7 1 g c=7*a*b*(a+b)*(a²+a*b+b²)²`. The forward is the previously checked `gtail_seven_eq_of_fermat7Equation`; the reverse uses the **actual Nat shell** `gtail_seven_shell`, rewriting by the proposed balance and applying `omega` to cancel an identical natural summand. It neither divides by g nor assumes positivity/copimality/prime, and does **not** independently solve FLT7.
2. `fermat7Equation_iff_focused_norm_balance` reuses the prior conditional integer norm readout and the actual `norm_gtailSevenNormCoord_sq` identity. The reverse converts the integer scalar equality to the natural one by `exact_mod_cast`, then invokes the first iff. This **does not** construct an E→R RingHom, identify an Eisenstein α² with an R-factor F_i, or transport their prime ideals.
3. The q43 numeric witness `(a,b,c,g)=(1166,1857,1858,1165)` has actual additive focus 3023, positive primitive geometry, `Nat.Coprime`, all five q-unit guards, `Q=6,973,267`, `T=1,914,732,507,483,487,090,603`, `v43(g)=0,v43(Q)=1,v43(T)=2`, exact doubled valuation budget, `q|Q`, `q²|T`, `q³∤T`, and **fails both the Fermat equation and the exact natural/integer balances**. All claims are either direct checkable examples or proved from the new iff.
4. The same exact witness separately verifies Eisenstein root37, `α²∈P37²` with conjugate/scalar ideal exclusions; cyclotomic root11, **all six** `F_i∈K_(sixInverseSlot i)²\setminus K_(sixInverseSlot i)³`, wrong-slot first-power exclusions and the six-slot permutation. These are **two different integral carrier evaluations** sharing q43, not a proof of element/ideal correspondence between carriers.
5. The existential example packages the bounded positive primitive geometry, five q43 units, scalar q43 valuations and **failure of** `Fermat7Equation` into a satisfiable native tuple, disproving **sufficiency of that specific finite set of local properties only**. The numeric tuple does NOT fulfill the exact global balance, does NOT produce a positive FLT7 solution, and notably has **7∤1165**. It is not a countermodel to *all* known necessary FLT7 conditions.
6. Crucial source correction: **the reviewer's instruction-032 mistakenly asserted the old tuple (5,8,9,4) failed additive focus. This is false**: `5+8=9+4=13`, and the old tuple also satisfies strict geometric inequalities. The Step032 test caught and corrected this claim. The new tuple is genuinely stronger because the old tuple has Tail q43 depth one, **fails the doubled scalar budget and K² support**, whereas the new tuple satisfies those constraints. The old instruction remains a historical artifact and should be treated as **superseded on this fact**; no claim that its false premise survives is acceptable.
7. The tests carefully distinguish the q43 focused non-Fermat witness from the prior q43,c9,g32598 example: the latter has actual selected `K³\setminus K⁴` but does **not** satisfy `a5+b8=c9+g32598`. q3 repeated Eisenstein root, q7 no nontrivial seventh root, q13 Gap-only and zero-coordinate Fermat equation cases remain outside their respective required premises.
8. `frontier-032.md` source-audits `AwayDescentClosureProvider` requiring nextX/Y/Z, new `CounterexamplePack`, new `AwayValuationTransferPacket` and exact `carrier_match`, plus `RamifiedSignedRootDepthPacket` requiring real-cubic balanced source, signed roots, 7-adic units, gap/quotient identities and the normalized equation. None follows from the new q43 local receiver or from a finite-field common codomain. The file correctly distinguishes **a missing implemented construction** from a theorem proving such a construction impossible.

## Scope and next research recommendation

**APPROVED — Outcome B.** The exact global balance and the Fermat equation are equivalent under focus; local scalar norms/valuations/ideal depth are insufficient without additional global information. This is an important **circularity and source-type firewall**, but not an FLT7 descent or impossibility theorem.

Suggested **Step033: prove an explicit no-direct-integral-ring-hom theorem**, not speculate that a shared finite field produces E→R or R→E. Source arithmetic yields cheap, satisfiable finite-field obstructions:

- Actual E=`TraceOneInt (-1)` has generator τ with τ²−τ+1=0. R=`SevenCyclotomicDegreeSixInt.Ring` has a checked RingHom evaluation into `ZMod 29` at the explicitly available nonidentity seventh root **r=7** (`7^7=1 (mod29)`). But `ZMod29` has **no** element satisfying x²−x+1=0 (29≡2 mod3); this is finite and `decide`-checkable. Therefore a unital `RingHom E R` would yield a contradiction upon composing with that evaluation. This is a **proposed theorem, not yet Lean checked**.
- Conversely E evaluates into `ZMod13` at the root **t=4**, since 4²−4+1=0 modulo13. R's ζ satisfies **Φ7(ζ)=0** via checked `zeta_geom_sum`. There is **no** root of Φ7 in `ZMod13` (13≡6 mod7; finite `decide` candidate). Thus `RingHom R E` is likewise impossible. Verify the actual Φ7 identity in R and genuine E-residue RingHom before asserting this reverse obstruction.
- These disallow **direct unital integral RingHoms** in the named directions only. They do **not** disallow common extension rings, embeddings of R/E into a cyclotomic compositum, `ℤ`-bilinear tensors, shared integer scalar norms or all possible typed correspondence constructions. State this qualification prominently.
- Source-check `QuadraticBridge.cyclotomicSevenToTraceOne : TraceOneInt (-2)`: the **discriminant −7** companion is distinct from E's **discriminant −3** generator; do not let the name “quadratic bridge” license a type substitution.
- Next Step033 should use only existing evaluation homs (Step019/R, Step013/E), actual τ and ζ relations, finite prime q29/q13 `decide` regressions, and an honest partial/Outcome C if any source hom/API obstacle blocks the claim. It should not invent a bogus map, infer FLT7 impossibility, or silently use the old signed provider.

No PR, merge/rebase, facade, K⁵, generic ideal valuation, new signed packet, unit/class-power extraction or Fermat closure authorized.
