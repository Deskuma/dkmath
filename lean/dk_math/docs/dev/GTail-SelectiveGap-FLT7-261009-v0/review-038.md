# Review 038 — complete focused prime routing, Gap root guard, Tail receiver

Date: 2026-10-11
Branch: `feature/GTail-SelectiveGap-FLT7-261009-v0`
Decision: **APPROVED — Step 038 COMPLETE / Outcome B**

## Reviewed actual files and evidence boundary

Inspected on the pushed GitHub branch:
- `DkMath/FLT/Seven/GTailFocusedPrimeRoute.lean` (120 lines);
- `DkMathTest/FLT/Seven/GTailFocusedPrimeRoute.lean` (265 lines);
- `report-038.md`, `source-inventory-038.md`, `frontier-038.md`;
- existing Step010 `GTailPrimeAllocationAudit`, Step031 `GTailFocusedNormCyclotomicDepthBridge`, Step032 exact global balance, and Step037 `GTailFocusedGenericPrimeReceiver`.

**Reviewer performed a static GitHub Lean proof-route audit, not an independent Lean build.** Codex reports final source05 / test06 and Step037/036 regression07/08 exit0, warning0; 60 checked examples and seven public `#print axioms` within `[propext, Classical.choice, Quot.sound]`. The intermediate source04 failure from a missing nat-cast rewrite and corrected source05 are documented. Source/test build targets, not a full clean repository suite, were checked.

## Mathematical proof audit

1. `gap_ratio_eq_one` correctly proves for any prime q, q∤c and q|g:
   `gtailSevenTailRatio q c g=1`. The denominator `(c:ZMod q)≠0` is established from actual divisibility; q|g gives `(g:ZMod q)=0`; `div_eq_iff` supplies the legal cancellation. The theorem does not require hEq, focus or q|T. It also applies at q=7 and q=3 given those raw premises.
2. `gap_nonidentity_guard_unavailable` makes the **canonical** nontrivial seventh-root guard false in the same Gap data. It does NOT claim no other nontrivial seventh root exists in ZMod q. The test q43,c1,g43 with an **independent** supplied r11 is a correct counterguard.
3. `focused_coordinate_units` derives q∤a,b,a+b from the actual primitive quadratic coprimality theorem and q∤c from the existing **Fermat-equation-dependent** endpoint lemma. It does not silently assume the endpoint unit when branching.
4. `focused_prime_route` has **no initial q|T** assumption. It reuses `prime_square_focused_allocation` for actual positive primitive hEq, focus, q≠7 and q|Q. Gap route: q²|g, q∤T and ratio=1 using the proved endpoint unit. Tail route: q²|T, q∤g and q|T by actual divisibility transitivity. Both alternatives remain live; no contradiction or independent valuation proof is inferred.
5. `tail_receiver` demands the **Tail branch q²|T** and retains all hEq/primitive/positive/focus/q≠7/q|Q assumptions. It invokes Step031's checked unit guards and Step037's `focused_receiver`, and adds Step037's actual supplied-root `pairedKernel_eq_sup` for the **same** chosen canonical roots. It delivers a typed E/R ideal join, maximal C kernel, two contractions, native α/F0 memberships, `v_q(T)=2v_q(Q)`, parity and one-way mixed M²/M³/M⁴ support. It creates no Gap-side receiver and no new global obstruction.
6. `norm_image_ne_cyclotomic` is genuinely stronger than the previous numeric example: for any suitable R seventh-root evaluation, q∤b and **every** u:R, `fromEisenstein(gtailSevenNormCoord a b) ≠ fromCyclotomic u`. Apply the actual C imaginary-coordinate map to equality; the E norm-coordinate has imaginary part the integer b whereas a coefficient-ring image has imaginary part zero. Applying the genuine R→ZMod q evaluation to `(b:R)=0` contradicts q∤b. No new domain/injective integer-cast axiom or Fermat equation is assumed.
7. `tail_source_images_ne` correctly specializes that already source-typed inequality to the hypothetical Tail branch with guards derived from Step031. This is **not** a Fermat7 impossibility theorem: Fermat7Equation does not assert those two distinct C elements are equal. Equal zero residues in C/J also never imply equality in C.
8. Symbolic tests repeat exact route signatures, including entry hT absence; q13 raw Gap tuple (14,29,30,13) has ratio=1, q|g but **q²∤g**, and is **not** a Fermat solution. q43 (1166,1857,1858,1165) remains a focused non-Fermat Tail-support witness with q² support and mixed products; q43 small (5,8,9,4) **does satisfy focus** but has only q-first-power Tail and fails the valuation budget. q127 t20/r2 remains supplied-root only. q7/q3 finite raw controls do not exceed their hypothesis scopes.
9. Source imports Step037 directly and reuses its conditional/readout owners transitively. The report records seven public standard-only axiom audits, no forbidden proof shortcuts, neutral Lib→FLT edges, old-owner modifications, new facades or added direct signed-packet imports. One exploratory `ZMod.isUnit_iff` API check failed; it was replaced by real checked APIs, and the final source uses direct nonzero denominator proof.
10. The old `AwayDescentClosureProvider` still requires a *new primitive CounterexamplePack*, `AwayValuationTransferPacket`, nextX/Y/Z and exact `carrier_match : nextRoute.carrier=Int.natAbs p.normal.root.snd`. The separate old `RamifiedSignedRootDepthPacket` needs actual balanced signed roots and normalized equation. Source image inequality and a native C ideal do not inhabit these fields or produce the Step032 exact global balance.

## Outcome and next research direction

**APPROVED / Outcome B.** Step038 is an honest *total conditional branch interface*. The mathematical work is important for accurate routing but largely invokes **existing** Step010/031/037 consequences. It does not make either branch contradictory, invent a signed packet or advance a primitive descent.

Do not continue by adding C ideal powers, a second generic grid, or a Gap receiver with an arbitrary substituted seventh root. A substantive next **noncircularity** question is: **how much of the same focused square routing survives when the exact Fermat equation is relaxed to a nonzero defect divisible by q²?**

The existing `GTailBridge.gtail_seven_defect` already proves over ℤ, under focus,

```text
Δ := (a:ℤ)^7+(b:ℤ)^7−(c:ℤ)^7
g*T = 7*a*b*(a+b)*Q² + Δ.
```

Since q|Q forces q² to divide the quadratic contribution, an assumption **q²|Δ** forces **q²|g*T**, even when **Δ≠0** and hEq fails. Under primitive coordinate/endpoint-unit guards and q≠7, the same elementary q² Gap/Tail branch split should then follow, **without hEq**. This would precisely show that the Step038 square route cannot alone distinguish an exact Fermat equation from a congruence solution through depth two. An endpoint-unit lemma derived from q|Q, primitive pair, focus and q|Δ (without hEq) would be especially useful if provable; do not hide q∤c as a magical transfer.

Independently calculated **two plausible positive primitive, additive-focused non-Fermat controls**:
- Tail: q43, (a,b,c,g)=(1166,1857,1858,1165), q²|Q² and Δ, q²|T, q∤g, **v43(Δ)=2**.
- Gap: q13, (a,b,c,g)=(196,211,238,169), a+b=c+g=407, gcd(a,b)=1, 0<g<a,b<c<a+b, q13|Q, q13²|g, q13∤T, **v13(Δ)=2** and hEq false.

These figures were independently evaluated using integer arithmetic, **not separately kernel checked**; any Step039 instruction must reverify them in Lean and refrain from claiming an impossible positive FLT solution. This is a local-defect stability/countermodel result, not a new global obstruction, and does not fill signed-packet or recursive descent fields.

The next downstream proof after such a defect audit would have to use genuinely **global** information beyond finite local q-power congruence, or actually construct the old provider's signed primitive recursive counterexample fields.

No PR, rebase/merge, facade, class/unit theory, new all-k valuation, signed packet or unconditional FLT7 claim authorized.
