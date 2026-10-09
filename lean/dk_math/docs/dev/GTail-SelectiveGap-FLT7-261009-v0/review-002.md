# Review 002 — selective factor/content kernel

Date: 2026-10-09  
Branch: `feature/GTail-SelectiveGap-FLT7-261009-v0`  
Decision: **APPROVED — Outcome B (reusable factor kernel)**

## Scope of review

Reviewed the pushed repository sources:

- `DkMath/Lib/Cosmic/GTailFactor.lean` (204 lines)
- `DkMathTest/CosmicFormula/GTailFactor.lean` (182 lines)
- `report-002.md` / `source-inventory-002.md` / `ROADMAP.md`
- Step 001's `GTailSelection` API and canonical GTail definitions.

This is a **static code, theorem-contract and report review**, not an independently run Lean build. Local focused builds and axiom results below are **reported by Codex**.

## Findings

1. `activeSelectedIndices` correctly intersects S with degree range. Every bound in the factor theorem is imposed on this active set; out-of-range input indices do not manufacture factors.
2. `selectedBody_eq_monomial_mul_residual` is a valid commutative-semiring identity for indices `i ≤ k ≤ j ≤ d`. The proof uses natural exponent splitting, finite sums and associativity, not division/cancellation. The empty set is handled.
3. `selectedBody_eq_min_max_mul_residual` obtains genuine extrema of the active set under explicit nonemptiness.
4. `coeffGCD` uses the natural finite gcd of Pascal coefficients, empty gcd 0, and the endpoint theorems correctly force gcd 1.
5. `coeffGCD_mul_monomial_dvd_selectedBody` proves the **joint** divisor: it does not incorrectly combine unrelated divisibility statements by assuming coprimality.
6. `coeffGCD_eq_prime_of_interior` correctly assumes **index 1 is selected** before asserting exact gcd p for a sparse prime interior. `coeffGCD_prime_interior` handles p=2.
7. `prime_mul_coords_dvd_selectedBody_interior` specializes the combined factorization to `p*x*u` with appropriate prime lower bound.
8. Regression tests cover sparse selections, endpoints, d=0, empty, out-of-range, p=2/3/7 and zero coordinates, with a general `CommSemiring` carrier where appropriate.
9. Codex records successful focused builds `DkMath.Lib.Cosmic.GTailFactor` and `DkMathTest.CosmicFormula.GTailFactor`, replay of Step 001, and `#print axioms` for sixteen exported theorems: `[propext, Classical.choice, Quot.sound]`. This review does not independently reproduce those commands.
10. No FLT owner import, no proof of FLT7 closure, and no claims about maximal exponent, exact evaluated gcd or valuation preservation were introduced.

## Nonblocking guidance for Instruction 003

- Formulate movement with **additive equalities over a semiring**, not subtraction requiring cancellation/ring hypotheses.
- Work on **active sets**: an index outside `0..d` must be a no-op.
- Each moved term transfers between Body and Gap but Big remains fixed. For arbitrary S,T, distinguish terms going **into** and **out of** Body.
- The balance identity is invariant; `coeffGCD`, divisibility, gcd and valuations generally **are not**. In particular, selecting a degree-p endpoint changes interior coefficient gcd from p to 1.
- Any congruence or divisibility preservation needs explicit hypotheses on the moved terms.
- Preserve canonical `GTail` indexing: k means exponent of x.

## Decision

**Approved with no blocking changes.** Proceed to Instruction 003 (`GTailTransport`). Defer degree-seven norm-square algebra and the FLT7 hypothesis bridge to Steps 004–005.
