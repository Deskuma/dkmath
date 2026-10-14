# Review 025 — exact square-depth characterization

Date: 2026-10-10
Branch: feature/GTail-SelectiveGap-FLT7-261009-v0
Decision: **APPROVED — Step 025 COMPLETE / Outcome B**

## Source audit

Reviewed the pushed Lean production module `DkMath/FLT/Seven/GTailCyclotomicTailDepthTwo.lean`, its direct test `DkMathTest/FLT/Seven/GTailCyclotomicTailDepthTwo.lean`, `report-025.md`, `source-inventory-025.md` and preceding Steps 023–024.

This is a **static review**. Codex reports focused source/test builds, Step 024/023 regressions, 27 examples and all seven new public declaration axiom prints successful. The reviewer did not independently rerun Lean.

## Verified conclusions

1. `mem_maximal_square_of_mul_mem` applies the actual Mathlib `Ideal.IsMaximal.mul_mem_pow` and uses cofactor nonmembership to deduce x in J² from U*x in J². It relies on maximality rather than an invalid prime-only cancellation.
2. `gtailCyclotomicCofactor` multiplies the five other actual degree-six cyclotomic factors. The proof `gtailCyclotomicCofactor_mul_factor` recovers the original scalar GTail using Step 023's unconditional integral factorization.
3. `gtailCyclotomicCofactor_not_mem_selected` establishes all five factors outside the selected prime kernel using unique inverse-exponent slots, then the prime-ideal finite-product membership theorem. It is not a numeric-only argument.
4. `natCast_mem_sixRootKernel_square_of_sq_dvd` derives q²-multiple scalar membership in K² from q in K by actual ideal-power membership. It makes no equality claim between the whole ideals K² and (q²).
5. `gtailCyclotomicFactor_mem_square_of_sq_dvd_GTail` uses the scalar multiple, actual five-factor cofactor, and maximal-power saturation to prove the missing reverse implication.
6. `gtailCyclotomicFactor_mem_square_iff` correctly combines the new reverse direction with Step 024's scalar contraction to establish, under prime q, q∤c,g and q|GTail, the **generic equivalence**:

```text
F_i(c,g) ∈ K_(sixInverseSlot i)^2 ↔ q^2 ∣ GTail 7 1 g c.
```

The q=43,c=9,g=4 sample has q²∤T and excludes all six selected factors from their kernel squares. The q=43,c=9,g=1165 sample has q²|T and **positively places all six factors in their selected squared ideals**. Both applications invoke generic Lean theorems. All five wrong slots remain excluded at first power in either example.

There are 7 new public declarations (one definition and six theorems). Codex records standard Lean logical axioms only; no extra axioms, placeholders or import cycles in these modules. No full repository rebuild was reported.

## Scope boundary and Step 026

**Outcome B is appropriate.** This is a bounded selected depth-two result, not an all-k ideal valuation theorem, a signed-root packet identification, individual factor principality, unit-class extraction or a Fermat7 descent.

The tests incidentally verify the same **nonzero cofactor residue 28** at each of the six selected q43 roots for both g=4 and g=1165. This is an observation, not yet a source theorem.

Recommend Step 026 as a narrow **cyclotomic shell derivative / cofactor evaluation** bridge. If G_c(X)=Σ_(j=0)^6 X^(6-j)c^j and (X−c)G_c(X)=X^7−c^7, then at the selected nontrivial Tail root X=c+g mod q:

```text
g*G_c'(c+g)=7*(c+g)^6
ev_selected(cofactor_i)=G_c'(c+g)=7*(c+g)^6/g.
```

These are **proposed** theorem targets, not results of Step 025. The formal derivative and source-ring factor product must be connected through checked polynomial APIs. This would explain the common q43 value 28, show the selected cofactor is a unit modulo its kernel and clarify the source's root simplicity before any all-power ideal cutoff is attempted.

No PR, branch merge, facade promotion, generalized exact ideal valuations, signed packet construction or FLT7 closure is authorized.
