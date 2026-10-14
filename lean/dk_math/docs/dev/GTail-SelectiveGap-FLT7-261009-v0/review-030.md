# Review 030 — selected cyclotomic K-fourth cutoff and exact depth three

Date: 2026-10-10
Branch: `feature/GTail-SelectiveGap-FLT7-261009-v0`
Decision: **APPROVED — Step 030 COMPLETE / Outcome B**

## Evidence and verification limit

Inspected the actual GitHub branch source:
- `DkMath/FLT/Seven/GTailCyclotomicTailDepthFour.lean` (113 lines);
- `DkMathTest/FLT/Seven/GTailCyclotomicTailDepthFour.lean` (202 lines);
- `report-030.md`, `source-inventory-030.md`;
- Step029 actual complement, K³ scalar contraction, Step025 selected cofactor, Step024 integer-coordinate scalar cancellation, and Step022 conditional six-kernel splitting;
- Step010 `GTailPrimeAllocationAudit`, Step012 `GTailSevenNormReadout`, Step017 `GTailSevenIdealSquareAddress` for a distinct source-typed FLT7 frontier, not as additional premises for Step030.

This is **a static GitHub Lean source/proof-route review, not an independently executed build**. Codex's report records passing final focused source/test targets and Step029/028 regressions, 38 examples, four new public `#print axioms` outputs each `[propext, Classical.choice, Quot.sound]`, no new axioms/unsafe/placeholders and no source import cycles. Final files are recorded warning-free.

## Audit findings

1. The source uses the actual `SevenCyclotomicDegreeSixInt.Ring` and actual maximal ideals `sixRootKernel r ... j` for **a supplied nonzero, nonidentity seventh root in ZMod q**, with prime q. There is no implicit existence claim for arbitrary q.
2. The new private `pow_inf_mul_of_comaximal` genuinely rechecks the generic lattice lemma `I^n ⊓ (I*J)=I^n*J` under `I⊔J=⊤` and n≠0. It does not try to access Step029's private compiled identifier; `Ideal.mul_eq_inf_of_isCoprime`, `Ideal.pow_sup_eq_top`, product monotonicity and the needed containment are applied to the right ideals.
3. `sixRootKernel_fourth_inf_scalar` specializes Step029's actual `K*J=(q)` and `K+J=⊤` to prove **`K⁴∩(q)=(q)*K³`**, not the generally false whole-ideal identity `K⁴=(q⁴)` or `(q)K³=(q⁴)`.
4. The new private scalar-support lemma maps **an embedded natural scalar n** through the actual root-indexed RingHom, deriving q|n, and constructs membership in the scalar ideal (q). It is not a claim about general signed or non-scalar ring elements.
5. `natCast_mem_sixRootKernel_fourth_iff` combines `K⁴≤K`, the checked fourth intersection, `Ideal.mem_span_singleton_mul`, and Step024's **actual six-integral-coordinate** injection for scalar multiplication by nonzero q. After n=q*m, the source element y∈K³ is identified with the actual scalar m; Step029's **already proved** scalar cube iff gives q³|m, hence q⁴|n. The reverse follows from embedded q∈K, `Ideal.pow_mem_pow` and ideal closure. No IsDomain, DVR, PID, Dedekind or valuation-function instance is assumed.
6. `gtailCyclotomicFactor_mem_fourth_iff` uses the actual five-factor cofactor `U_i`, its Step025 **nonmembership** in the selected maximal kernel, and `U_i*F_i=(GTail:R)`. `Ideal.IsMaximal.mul_mem_pow` at exponent 4 is correctly used for saturation. Thus, under q-prime, q∤c,g and q|T, `F_i∈K_(sixInverseSlot i)^4 ↔ q⁴|GTail 7 1 g c` holds for all six genuine integral factors.
7. `gtailCyclotomicFactor_depth_three` does not introduce a global ideal-adic valuation. It simply pairs the checked Step029 K³ iff and Step030 K⁴ iff to prove `F_i∈K³∧F_i∉K⁴` when q³|T and q⁴∤T.
8. The q43,c9,g32598 examples derive all six actual `K³\setminus K⁴` certificates from the general theorem and previously checked scalar 43³ support and 43⁴ nondivisibility. The earlier g4/g1165 boundary cases retain their lower depths; six wrong-slot exclusions, same canonical ratio11, derivative and selected cofactor residue28, Hensel first/second digits, and zero/gap/root exceptions are consistently checked.
9. The new owner adds four public theorems and no global `K⁵`/all-k factor valuation, signed packet, cyclotomic unit/principal ideal statement, or Fermat descent. Codex reports all 38 examples and all four public axiom audits succeeded with the standard Lean foundations. This reviewer did not perform a full repository build or independently reproduce those compiler logs.
10. The direct new production import remains Step029 only; the preexisting six-coordinate carrier and all previous owners are unmodified. No reverse neutral Lib→FLT edge, facade promotion, PR or branch merge occurred. The feature branch is still diverged one new commit behind develop as of review.

## Honest mathematical interpretation

**APPROVED — Outcome B.** This is the first **exact bounded depth-three** instance for each of the six actual selected bare-root cyclotomic factors: at q43,c9,g32598, `F_i∈K³\setminus K⁴`. It is stronger than the scalar 43⁴ nondivisibility alone, yet it does not establish a general prime-ideal valuation function or FLT7 descent.

**Do not automatically extend to K⁵**. The next legitimate frontier is source-typed synchronization, NOT a guessed integral ring hom between Eisenstein `TraceOneInt (-1)` and seventh-cyclotomic `SevenCyclotomicDegreeSixInt.Ring`.

Inspected exact source APIs:
- `DkMath.Lib.NumberTheory.GTailSevenNormReadout.gtailSevenNormCoord a b : TraceOneInt (-1)`, `norm_gtailSevenNormCoord = (Q:ℤ)`, and `norm_gtailSevenNormCoord_sq=(Q²:ℤ)`;
- `DkMath.Lib.NumberTheory.GTailSevenIdealSquareAddress.gtailSevenNormCoord_split_square_address` gives the oriented Eisenstein `α²∈P_t²`, conjugate/scalar exclusion at a split prime q≠3 under q|Q and q∤b;
- `DkMath.FLT.Seven.GTailBridge.gtail_seven_eq_of_fermat7Equation` gives the exact natural scalar relation `g*T=7*a*b*(a+b)*Q²` under the **hypothetical** Fermat equation and a+b=c+g;
- `DkMath.FLT.Seven.GTailPrimeAllocationAudit.prime_focused_support_exclusive` and `padicValNat_focused_quadratic_budget` give the q-local exclusive gap/Tail support and `v_q(g)+v_q(T)=2 v_q(Q)`, with exact positive/primitive/equation hypotheses;
- `DkMath.Lib.NumberTheory.GTailSevenPairedResidue` already pairs the two residue roots in a shared `ZMod q` **without any integral carrier map**;
- Steps025,029,030 provide `F_i∈K²/K³/K⁴ ↔ q²/q³/q⁴|T` under canonical Tail q-unit/support hypotheses.

Proposed Step031, strictly source-typed: from an **explicit scalar balance** and proved q-unit assumptions derive the **evenness of Tail valuation on the q-unit gap branch**, and connect that integer/norm readout to the two actual ring ideal statements. In the hypothetical positive primitive Fermat-facing specialization with q|Q and q|T, obtain `v_q(T)=2v_q(Q)`, Eisenstein `α²∈P_t²` and cyclotomic `F_i∈K²`, plus **no exact K³\setminus K⁴ support** because the scalar Tail q-depth is even. This is a **necessary condition already implicit in Step010’s valuation budget**, not a new independent FLT7 obstruction. Keep the purely arithmetic balance lemma separate from the Fermat adapter, and exhibit non-Fermat q43 split/norm examples without fabricating an exact positive Fermat solution.

Need to verify whether existing Step010's budget already states the specialized parity conclusion; source comparison is mandatory. No ideal `P_t=K_j`, Eisenstein→cyclotomic ring hom, signed packet identification, class/unit power, smaller counterexample or global FLT7 result is permitted without an additional typed theorem.
