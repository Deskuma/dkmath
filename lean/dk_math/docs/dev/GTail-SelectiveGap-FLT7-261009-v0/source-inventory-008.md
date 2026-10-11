# Source inventory 008 — exact focused seven-adic calibration

Date: 2026-10-09. Initial branch `feature/GTail-SelectiveGap-FLT7-261009-v0`, clean worktree; HEAD `eac957324c3fe8aadfff7ce7d8d588f002654d8a`. Read review-007, report-007, report-006 and constraint-ledger-006. The five neutral and two conditional Step 007 imports are present in Lib/Seven. No branch or facade edit is needed for this bounded experiment.

## Existing contracts and overlap

- `GTailSevenArithmetic.gtail_seven_exact_seven_layer`: for natural g,c, `7 ∣ g` and `¬7 ∣ c` imply `7 ∣ GTail 7 1 g c ∧ ¬7^2 ∣ GTail 7 1 g c`. Neither g-nonzero nor Coprime g c is required. This is the direct source of the new residual valuation endpoint.
- `GTailCongruence.GN_modEq_head_mod_sq_of_odd_prime_dvd_x`: natural x,u, prime p, `3 ≤ p`, `p ∣ x` yield the residual head congruence modulo p². `prime_dvd_GN_iff_dvd_gap` identifies the prime gap channel. Step 006 already uses both; no congruence is reproved here.
- `GTailPadic.padicValNat_GN_prime_eq_one_of_dvd_gap`: prime p, `3 ≤ p`, Coprime g u and `p ∣ g` yield residual valuation 1. The new degree-seven theorem uses endpoint-unit hypotheses instead of full coprimality; (14,2) has gcd 2. Existing head-unit valuation-zero and exact-boundary APIs have `¬p ∣ choose d r * u^(d-r)`, which is false for the seven-row r=1 head, so they cannot replace the exact-one argument.
- `Lib.NumberTheory.PadicValNat.Vp_ge_one_iff`: prime p and n≠0 give `1 ≤ v_p(n) ↔ p ∣ n`. `padicValNat_le_iff_dvd hp hn k` gives `k ≤ v_p(n) ↔ p^k ∣ n`. Used directly rather than rebuilding general valuation definitions.
- Mathlib `padicValNat.mul`, in `NumberTheory/Padics/PadicVal/Basic.lean`: `[Fact p.Prime]`, a≠0, b≠0 give `v_p(a*b)=v_p(a)+v_p(b)`.
- Mathlib `padicValNat.pow` in the same prime instance gives `v_p(a^n)=n*v_p(a)` **without a nonzero premise**. The DkMath wrapper `padicValNat_pow hp d ha` asks for a≠0 even though its proof delegates to that stronger Mathlib API. Product factors must still be nonzero.
- `GTailBridge.gtail_seven_eq_of_fermat7Equation`: equation and a+b=c+g give the exact focused product `g*T=7*a*b*(a+b)*Q²`.
- `GTailConstraintAudit.fermat7_focused_bounds`: positive a,b and the equation give c<a+b; combined with the supplied sum relation, this gives g>0. `seven_dvd_focused_gap` gives 7∣g with no primitivity premise.

## Other FLT7 coordinates and classification

Inspected without importing `CounterexampleRouting.padicValNat_GN_seven_eq_one_of_counterexample` and `padicValNat_gap_shape_of_counterexample`: these use a primitive CounterexamplePack and the difference gap z-y, yielding a residual one-layer and gap shape 6+7*m from a seventh-power product. `PrimitiveCyclotomicDepth.padicValNat_GN_seven_sub_eq_one_iff` uses b≤a and Coprime a b, for the difference a-b. These are different carriers/coordinates from the sum focus a+b-c and do not prove its coprimality. No transfer is assumed. This checkpoint classifies the new balance as Outcome B, not an independent obstruction.

Optional unit branch is not implemented. Existing `ModSevenSectors.fermat7Equation_modSeven_linear` would be relevant to proving a+b a seven-unit under the equation and endpoint-unit hypothesis. Unit coordinates alone cannot supply that fact (e.g. 1+6). No general mod-49 obstruction, q² allocation, order-21 or unit-class theorem is asserted.

## Planned/new direct owners

Neutral `GTailSevenValuation` imports only GTailSevenArithmetic and Lib.NumberTheory.PadicValNat. Conditional `GTailValuationAudit` imports only GTailConstraintAudit and the new neutral module. Separate tests import the respective direct module. No Lib/Seven facade, descent/closure owner, production root or root test aggregator is changed. Lake's test submodule glob discovers both new tests; focused invocation is recorded in report-008.

Seven-layer nondivisibility implies T≠0, because every natural divides zero. The residual result can therefore omit g≠0; the product result retains it. Conditional positivity excludes all zero factors before multiplying valuations. No subtraction is used to cancel the common layer.

The pre-existing LegendreMergedCRT source is byte-identical to HEAD; no heartbeat changes, profiling, memory/configuration changes or broad build. The owner full-test evidence is separated in validation-addendum-007.md; no Step 008 result is inferred from that older run.

## Final import audit

Header-only source closures: neutral owner 1082 names (6 local), conditional owner 8795 (15 local), neutral test 1083 (7 local), conditional test 8796 (16 local). DFS passes over the union of 17 local modules. Neutral closure contains no FLT module. No production/test cycles or heavy local closure owner occurs. The corrected Step 007 parser was reused without running its write-to-Step-007 audit section; names are retained in `.lake/build/gtail-step008/imports.json`.
