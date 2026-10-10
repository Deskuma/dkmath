# Review 023 — exact native GTail seven-tail as six integral cyclotomic factors

Date: 2026-10-10
Branch: `feature/GTail-SelectiveGap-FLT7-261009-v0`
Decision: **APPROVED — Step 023 COMPLETE / Outcome B**

## Evidence and verification scope

Static GitHub review of pushed sources:
- `DkMath/FLT/Seven/GTailCyclotomicTailFactorProduct.lean` (128 lines);
- `DkMathTest/FLT/Seven/GTailCyclotomicTailFactorProduct.lean` (155 lines);
- `report-023.md` and `source-inventory-023.md`;
- existing `DkMath.Lib.Cosmic.GTailCyclotomic` shell identity, Steps 019–022 packet-free evaluation/kernels/splitting, the actual degree-six carrier and an older **signed-packet-indexed** oriented carrier valuation report.

**Reviewer did not independently run Lean.** Codex reports passing final focused new production/test targets and Steps 022/021 test regressions, 31 kernel-checked examples, and twelve new public declaration axiom audits with standard foundations only. Report records a failed intermediate cancellation rewrite and successful correction without changing the theorem's premise/conclusion.

## Theorems inspected

1. `gtailCyclotomicFactor c g i := (c+g:R) - zeta^(i.val+1)*(c:R)` lives in the genuine `SevenCyclotomicDegreeSixInt.Ring`, with correctly oriented powers 1..6. `gtailCyclotomicFactor_zero` agrees **as an actual element** with Step 019's existing `gtailCyclotomicLinearFactor`.
2. `zeta_geom_sum` proves the seven-term geometric sum directly from the ring's checked quadratic relation `zeta²-t*zeta+1=0` and real-trace cubic `t³+t²−2t−1=0`. The private `geom_of_relations` supplies an algebraic linear-combination certificate. No cancellation by possibly nonregular `zeta-1`, new domain instance, root packet or numerical ZMod field surrogate is used.
3. The private `product_of_geom` is checked for *any commutative ring* carrying an element satisfying that seven-term relation. It explicitly expands the homogeneous `Fin 6` factor product and `Fin 7` shell with a Lean-checked polynomial `linear_combination` certificate. Hence `prod_six_zeta_factors_eq_shell` holds **for all integral source elements X,Y**, stronger than just natural arguments c,g.
4. `GTail_seven_one_eq_homogeneous_sum` reuses `GTail_one_eq_GTailCyclotomicShell` from the actual neutral GTail implementation and reverses the seven terms by a finite identity. No gap cancellation is performed; g=0, c=0 and signed source coordinates in the separate general carrier theorem are legitimate.
5. `prod_six_gtailCyclotomicFactor_eq_GTail` combines the source-shell factorization with the actual natural GTail identity. Its signature has **no** prime q, supplied residue root, Fermat7 equation, positivity or nonzero-gap hypothesis.
6. `evalCyclotomic_gtailFactor` applies the actual packet-free RingHom and sends every factor to `(c+g)-s^(i+1)*c` in the finite field. Root proofs, source carrier and natural-cast conventions are visibly correct.
7. `gtailCyclotomicFactor_mem_sixRootKernel_iff` carefully requires q prime, q∤c, q∤g and q|GTail, establishes the canonical ratio, cancels the nonzero c residue and uses a finite-order mod-7 power-injectivity theorem. It obtains `F_i∈K_j ↔ (i+1)(j+1)≡1 (mod 7)`. The actual source uses `mul_left_inj' hc0` with the orientation matching its field equality; this fixes the earlier failed test-time rewrite, not the mathematical premises.
8. `sixInverseSlot=[0,3,4,1,2,5]` and its involution/index iff are verified by finite arithmetic, independent of q43. `gtailCyclotomicFactor_unique_slot` proves every factor belongs to **exactly one of the six supplied root-indexed kernels**. It does NOT identify its principal ideal with that kernel or claim exact local ideal power.
9. The q43 example independently verifies scalar `GTail 7 1 4 9=14491387=43·337009`, `F_0=13−9*zeta`, the factor→kernel permutation, all 36 **actual RingHom** residual evaluations, and scalar GTail's presence in all K_j while `F_0∉(43)`. All comparisons keep element products separate from ideal products. q43,a5,b8 remains a neutral, **non-Fermat** calibration.
10. Generic zero-gap `GTail 7 1 0 c=7*c^6`, c=0/g=1, c=1/g=0 and c=g=0 are checked. The unconditional element product remains valid in the characteristic-seven boundary *in source R* even where a nontrivial root in ZMod7 cannot be provided. The Gap-only q13 example has no q|Tail and cannot supply root-address premises.
11. Twelve public declarations are reported with only `propext`, `Classical.choice`, and `Quot.sound` as applicable. The source additions have no new sorry/axiom/unsafe, changed existing signed-packet endpoints, reverse neutral→FLT imports or import cycles. No full build was executed by Codex in Step023.

## Overlap / novelty boundary and next gate

The product identity is an **exact typed bridge from native GTail to six genuine integral cyclotomic linear factors**. Together with Step022, it gives a tested correspondence between a scalar product and six q-local prime slots. But neither `Ideal.span {F_i}=K_j` nor a generic assertion of K-adic valuation exactly one follows: F_i may carry additional q-adic depth and unrelated prime factors.

Important older owner: `SevenRamifiedFusionOrientedCarrierValuationOwnership` already has exact local-power cutoffs for **signed-depth packet-indexed quotient roots** and a separate ramified q7 prime. Those results should **not** be claimed novel or copied to this bare natural-Tail ratio without constructing the missing typed address equality. The new step should focus on what **can** be derived directly from Steps 021–023 under a *scalar first-order* premise, not assume exact K-depth unconditionally.

A candidate, separately guarded Step 024:

```text
q prime, q∤c,g, q|GTail, q²∤GTail
  → F_i∈K_(sixInverseSlot i)
    ∧ F_i∉K_(sixInverseSlot i)^2.
```

The proof cannot be inferred from the first-order residue evaluation alone. A possible route is to multiply **actual** six F_i: if one F_i lies in K_assigned² and all other factors in their respective K's, then GTail lies in `(∏K_j)*K_assigned=(q)*K_assigned`. For an embedded natural scalar n, q-torsionfree six signed coordinates and integer contraction `K_assigned∩ℤ=(q)` should give

```text
(n:R)∈(q)*K_assigned → q²∣n.
```

This is a proof target, NOT a Step023 theorem. It needs exact ideal-multiplication membership and a valid **scalar cancellation/coordinate** argument. If any missing premise occurs, report it; do not postulate `(q)*K=(q²)` (false as ideals) or conflate scalar-square depth with generic ideal-adic valuation. q43 provides a nonvacuous instance because `43|14491387` but `43²∤14491387`.

A quotient CRT ring equivalence `R/(q)≃+*(Fin6→ZMod q)` is another valid later API candidate, but the first-order local factor depth has closer direct bearing on new native GTail arithmetic.

**Decision: APPROVED — Outcome B.** Authorize a focused Step024 *conditional first-order depth firewall* if its generic scalar-contraction lemma can be kernel checked. No unguarded exact valuation, signed-packet manufacture, ideal class/unit extraction, primitive Fermat descent or unconditional FLT7 claim. No PR, merge or facade promotion authorized.
