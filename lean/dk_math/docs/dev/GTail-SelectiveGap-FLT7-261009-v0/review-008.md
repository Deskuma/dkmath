# Review 008 — seven-adic focused-gap calibration

Date: 2026-10-09
Branch: `feature/GTail-SelectiveGap-FLT7-261009-v0`
Decision: **APPROVED — Step 008 COMPLETE / Outcome B**

## Evidence

Static review of pushed:
- `DkMath/Lib/Cosmic/GTailSevenValuation.lean`
- `DkMath/FLT/Seven/GTailValuationAudit.lean`
- corresponding focused tests
- `report-008.md`, `source-inventory-008.md`, `validation-addendum-007.md`.

This review does not independently rerun Lean. Codex reports passing focused builds, earlier regressions, standard foundational axioms for all three new public endpoints, and no new sorry/unsafe or FLT impossibility dependency.

## Mathematical findings

1. `padicValNat_gtail_seven_eq_one`: from 7 dividing the residual and 49 not dividing it, establish nonzero residual and exact valuation one, with no need to assume a nonzero gap. The zero-gap, endpoint-unit regression is legitimate.
2. `padicValNat_gap_mul_gtail_seven`: requires nonzero g as well as a nonzero residual. This is essential because `padicValNat 7 0 = 0` in the used natural-valued API.
3. `padicValNat_focused_gap_balance`: uses the Step 005 exact product, Step 006 focused height and 7-divisibility, proper nonzero factors, Mathlib's product and power valuation laws, and cancellation of a single common valuation layer. No unproved coprimality of g and c is introduced.
4. Exact hypotheses remain `0<a`, `0<b`, `Fermat7Equation a b c`, `a+b=c+g`, and `¬7∣c`.
5. The tests at (7,2), (14,2), the zero gap, and (7,7) distinguish genuine assumptions from misleading generalizations. The last one refutes exact-one valuation when the c-unit premise is removed, not a Fermat-conditioned theorem.
6. The new theorem is a correctly checked necessary valuation identity, not a contradiction, root/unit class resolution or constructive descent. The existing general GTailPadic one-layer theorem assumes stronger full gap-endpoint coprimality; this new local API assumes only that c is a 7-unit.

## Step 007 addendum

The owner-supplied successful `./lb -T` run and its actual Lake test route are recorded separately in `validation-addendum-007.md`. The historical interrupted Codex attempt remains in `report-007.md`; the additional test log lacks a captured runtime git hash or standalone numeric exit code. Do not equate the earlier test run with verification of subsequently added Step 008 files.

## Next narrow experiment

Under `7∣g`, `a+b=c+g`, and `¬7∣c`, infer `¬7∣a+b`. When a,b are 7-units, the established balance reduces to `v7(g)=2*v7(Q)` for `Q=a²+a*b+b²`. Positive g and 7-divisibility would then force `7∣Q` and `49∣g`. This remains a prospective Step 009 theorem, not an already checked endpoint.

Require a satisfiable **abstract product valuation** calibration to protect against vacuity of full positive Fermat hypotheses. Compare the result with existing mod-49/mod-343 constraints. A concrete residue-consistent non-Fermat example `(a,b,c,g)=(8,9,10,7)` should demonstrate that mod-49 Fermat congruence alone does not force `49∣g`.

**Decision: APPROVED / Outcome B.** No branch merge or new FLT7 closure claim.
