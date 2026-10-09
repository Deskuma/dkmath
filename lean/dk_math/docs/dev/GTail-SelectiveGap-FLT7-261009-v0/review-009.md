# Review 009 — exact seven-unit focused branch

Date: 2026-10-09
Branch: `feature/GTail-SelectiveGap-FLT7-261009-v0`
Decision: **APPROVED — Step 009 COMPLETE / Outcome B**

## Reviewed evidence and method

Static GitHub review of:
- `DkMath/Lib/NumberTheory/SevenUnitAllocation.lean`, `DkMath/FLT/Seven/GTailSevenUnitAudit.lean`;
- `DkMathTest/NumberTheory/SevenUnitAllocation.lean`, `DkMathTest/FLT/Seven/GTailSevenUnitAudit.lean`;
- `source-inventory-009.md`, `report-009.md`, `ROADMAP.md`;
- upstream Step 008 valuation and Step 006 prime-gap interfaces.

The reviewer **did not independently rerun Lean**. Codex reports successful final focused builds, Step 008 regressions and six `#print axioms` results limited to `[propext, Classical.choice, Quot.sound]`.

## Mathematical review

1. `not_seven_dvd_sum_of_focused_equation` uses the checked `seven_dvd_focused_gap` and additive divisibility cancellation. No invalid rule that sums of two units must be units was invoked.
2. `padicValNat_focused_gap_unit_balance` reuses the Step 008 conditional equality and derives zero valuations for a, b, and a+b from explicit 7-unit premises; no `Nat.Coprime a b` is needed.
3. `seven_dvd_quadratic_of_focused_units` proves g≠0 from positive height, gets `v7(g)≥1`, uses doubled valuation to force `v7(Q)≥1`, proves Q≠0 and converts the valuation to `7∣Q`.
4. `fortyNine_dvd_focused_gap_of_units` reuses the neutral lemma deriving `49∣g` from g≠0, `7∣g`, and an even valuation equality.
5. `padicValNat_seven_unit_product` is a genuinely satisfiable neutral arithmetic theorem. The abstract tuple (g,T,A,B,C,Q)=(49,7,1,1,1,7) checks the equation and conclusion without a Fermat premise. These abstract factors are *not* asserted to be instantiated from a positive Fermat solution.
6. The exact-vs-modular calibration (a,b,c,g)=(8,9,10,7) satisfies primitive input, height, unit and mod-49 conditions, but not the exact Fermat equation; it has `v7(g)=v7(Q)=1`, so the doubled valuation and 49-divisibility fail. This refutes only the **weakened congruence-only inference**, not the proved conditional theorem.
7. The code and report separate already-known mod-7 / mod-49 / mod-343 necessary conditions from a newly packaged sum-focus formulation; they do not claim FLT7 closure, descent, or a norm/unit-class theorem. Direct neutral-to-owner imports have no cycle or extra axioms.

## Recorded validation

Codex's report records final successful focused builds of two new production modules, two new test modules, and the two Step 008 regression targets (after a concrete-test elaboration repair that unfolded `Fermat7Equation`). All six public theorem axiom lists show standard foundations only. No unproved new assumptions, placeholder proofs, forbidden circular FLT7 theorem calls, or changed historical Legendre/Step 007 sources were found in the submitted diff. Broad all-suite verification was not attempted in this checkpoint.

## Remaining frontier / next research target

The next question should not be limited to another v7 unit corollary. For a prime `q≠7` dividing `Q=a²+ab+b²` at a primitive positive Fermat7 hypothetical packet, the Step 005 equality and Step 006 coprimality suggest the **q-adic square budget**:

`v_q(g)+v_q(T)=2*v_q(Q)`, with `T=GTail 7 1 g c`.

This exact allocation requires checking positivity/nonzeroness, `q∤7ab(a+b)`, and the full equality, not merely mod-q congruence.

A possible stronger *exclusivity* is worth testing, not assuming: if q∣Q, q≠7, and q∤c, then q∣g should imply q∤T by the canonical GTail head-collapse `T ≡ 7*c^6 (mod q)`. If q∣Q and the exact equation additionally imply q∤c, the square budget together with exclusivity would force the entire even q-power into exactly one of g,T rather than allow mixed one-plus-one allocation. This implication and all needed premises are **research targets**, not results of Step 009.

Do not deduce `Coprime g c` or `Coprime g Q` from primitive a,b. Do not claim an order-21 result or next Fermat packet without typed proofs.

## Decision

**APPROVED / Outcome B.** Authorize a narrowly scoped Step 010 q-local valuation and exclusivity study. Keep prior unproved norm/unit gauge, order-21 and descent questions separate. No merge or PR is authorized.
