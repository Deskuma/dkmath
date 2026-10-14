# Review 029 — actual third-power membership of native GTail cyclotomic factors

Date: 2026-10-10
Branch: `feature/GTail-SelectiveGap-FLT7-261009-v0`
Decision: **APPROVED — Step 029 COMPLETE / Outcome B**

## Evidence, audit boundaries

Static GitHub source inspection of:
- `DkMath/FLT/Seven/GTailCyclotomicTailDepthThree.lean` (147 lines);
- `DkMathTest/FLT/Seven/GTailCyclotomicTailDepthThree.lean` (141 lines);
- `report-029.md` and `source-inventory-029.md`;
- Steps 020–028 actual root-indexed maximal ideals, six-kernel scalar splitting, integer six-coordinate cancellation, five-factor selected cofactor, prior bounded square-depth theorem, and actual second Hensel digit.

**This reviewer did not independently run Lean.** Codex reports successful final focused source/test builds and direct Step028/027 regressions, 25 examples, nine public declaration axiom checks all within ordinary `propext`, `Classical.choice`, `Quot.sound`; no new axioms, placeholders or import cycles. Early build had only an unused simplifier-argument warning, repaired to final warning-free source/test.

## Reviewed mathematical structure

1. `sixRootKernelComplement` is the actual finite product of the five ideals at **other root slots** of the existing degree-six cyclotomic ring. `sixRootKernel_mul_complement` uses the previously verified Step022 six-kernel product and a correct erase/reinsert identity to prove `K_j*J_j=(q)`.
2. `sixRootKernel_sup_complement` does not infer coprimality from ideal inequality. It uses Step021's verified pairwise maximal/comaximal kernel result and the actual `IsCoprime.prod_right` for the five erased ideals. `sixRootKernel_pow_sup_complement` uses `Ideal.pow_sup_eq_top`, a genuine whole-ideal statement valid at arbitrary natural exponent.
3. The private `pow_inf_mul_of_comaximal` is proved as a **generic CommRing ideal identity** under `I⊔J=⊤` and `n≠0`:
   `I^n ⊓ (I*J) = I^n*J`.
   Its forward containment exploits `I*J≤J`; its reverse uses `I^n≤I` and checked ideal-product monotonicity. It uses the current `Ideal.mul_eq_inf_of_isCoprime` API with correct orientation rather than presuming an unverified ideal-theoretic equality.
4. `sixRootKernel_square_inf_scalar` and `sixRootKernel_cube_inf_scalar` specialize this real comaximal identity and `K*J=(q)` to prove, respectively, `K²∩(q)=(q)K` and `K³∩(q)=(q)K²` **in the actual R**. Neither is replaced by the generally false `K^n=(q^n)`.
5. `scalar_support_of_kernel_mem` maps an embedded natural through the actual packet-free RingHom and derives `q|n`; it separately constructs actual source membership in `(q)` using a natural quotient witness. It is correctly limited to **natural scalar elements**.
6. `natCast_mem_sixRootKernel_square_iff` obtains scalar q² contraction from `K²⊆K`, the checked square intersection and Step024's **scalar-only** `(q)K` contraction; its converse specializes the already verified scalar-square membership theorem.
7. `natCast_mem_sixRootKernel_cube_iff` uses `K³⊆K` to write `n=q*m`, obtains `(n:R)∈(q)K²` from the checked cube intersection, extracts a genuine `y∈K²` with `(n:R)=q*y` from `Ideal.mem_span_singleton_mul`, then applies Step024's six-coordinate `cyclotomic_natCast_mul_injective` to identify `y=(m:R)`. The previous scalar-square iff forces `q²|m`, hence `q³|n`. Its converse follows from actual embedded q∈K and ideal power membership/closure. No hidden IsDomain, DVR, UFD, principal K or valuation function is assumed.
8. `gtailCyclotomicFactor_mem_cube_iff` considers **the real element** `F_i` and **the real five-factor cofactor** `U_i`. The Step025 product says `U_i*F_i=(GTail:R)`, and `U_i∉K_assigned` is already proved. The actual `Ideal.IsMaximal.mul_mem_pow` at exponent 3 provides precisely the required reverse saturation. Coupled with the genuine scalar cube iff this proves:
   `F_i∈K_(sixInverseSlot i)^3 ↔ q³|GTail 7 1 g c`,
   under prime q, q∤c,g and q|T, uniformly across all six indices.
9. q43,c9 examples check all six selected factors: g4 outside K² and K³; g1165 inside K² but outside K³; g32598 inside K³ via Step028's **generic scalar cube lift**. All wrong-root slots remain excluded at first power. q43 scalar 43³∈K³ and 43²∉K³ are also checked via the new generic scalar contraction. The residue root11, inverse index permutation [0,3,4,1,2,5], selected cofactor28 and exact negative Fermat7 example remain consistent.
10. The arithmetic test `43⁴∤GTail 7 1 32598 9` is **not** converted into `F_i∉K⁴`; such a conclusion needs a separately proved fourth-power scalar contraction. The report consistently avoids false unguarded exact depth/valuation, old signed-depth packet identification or FLT7 descent.
11. Nine new public declarations consist of one definition and eight theorems, reported kernel-checked with standard axioms. The source imports only Step028, does not alter neutral Hensel/old valuation owners or public facades, and the audited local import graph remains cycle-free with no neutral→FLT import.

## Scientific scope and Step 030 recommendation

**APPROVED — Outcome B.** The result is a genuine *bounded third-depth typed cyclotomic receiver* for the native natural GTail factors, not a new general valuation theorem, ideal principality statement or Fermat7 obstruction.

The **precise next missing gate** is fourth-power contraction to turn g32598 from “at least third” into “exactly third” in every selected cyclotomic kernel. The prior source already proves a **private general ideal-complement lemma** `pow_inf_mul_of_comaximal`; preserve the existing owner but reuse its *method* at n=4 (or source-check how to avoid duplicating private proof using a targeted public wrapper):

```text
K_j^4 ⊓ (q) = (q)*K_j^3,
(n:R) ∈ K_j^4 ↔ q^4|n,
F_i(c,g)∈K_(sixInverseSlot i)^4 ↔ q^4|GTail.
```

The scalar proof should follow the **exact same tested six-coordinate cancellation route**, using Step029's already proved scalar cube iff, rather than asserting `(q)*K³=(q⁴)` as ideals. The selected factor proof should reuse the Step025 cofactor and Mathlib's maximal-power saturation at n=4, not reprove source factorization or cofactor nonmembership.

These formulas are **suggested Step 030 targets**, not Step029 theorems. If checked, the numerically established `43³|T(32598)` and `43⁴∤T(32598)` would yield `F_i∈K³\setminus K⁴` for all six actual factors at that input. This completes the first three-level calibration without inviting an endless digit/depth ladder. After Step030, re-evaluate progress toward independent FLT7 restrictions and the still missing Eisenstein↔cyclotomic carrier bridge rather than automatically building all-k infrastructure.

Branch is currently diverged from develop by one develop commit. Do not silently merge/rebase. No PR, façade promotion, signed packet construction, class/unit powers or unconditional FLT7 claim is authorized.
