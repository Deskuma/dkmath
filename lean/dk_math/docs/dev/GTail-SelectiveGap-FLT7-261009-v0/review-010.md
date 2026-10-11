# Review 010 — q-local exclusive square allocation

Date: 2026-10-10
Branch: `feature/GTail-SelectiveGap-FLT7-261009-v0`
Decision: **APPROVED — Step 010 COMPLETE / Outcome B**

## Material and review method

Inspected pushed GitHub files:
- `DkMath/Lib/Cosmic/GTailSevenPrimeAllocation.lean` (71 lines);
- `DkMath/FLT/Seven/GTailPrimeAllocationAudit.lean` (108 lines);
- `DkMathTest/CosmicFormula/GTailSevenPrimeAllocation.lean` (61 lines);
- `DkMathTest/FLT/Seven/GTailPrimeAllocationAudit.lean` (57 lines);
- `report-010.md`, `source-inventory-010.md`, and the existing primitive/coprimality, bridge and valuation contracts.

This is a **static code/proof-route/report review**, not an independently executed Lean build. Codex reports final successful incremental focused builds, Step 009 regressions, and standard foundational axioms for all eight new public theorem endpoints.

## Verified theorem-contract observations

1. `not_prime_dvd_gtail_seven_of_gap` correctly specializes the existing head-unit theorem. For prime q≠7, q|g and q∤c, the constant head is 7*c^6, so q∤T. Importantly, this assertion does **not** claim the same for q=7.
2. `not_prime_dvd_coordinate_product_of_quadratic` uses the already proved coprimality of a*b*(a+b) and Q under Coprime a b; no positiveness or Fermat premise is necessary for this neutral conclusion.
3. `not_prime_dvd_endpoint_of_quadratic` derives q∤c rather than assuming it. From the exact Fermat equality and the degree-seven balanced identity, q|Q and q|c imply q|(a+b)^7. Primality then forces q|a+b, contradicting the ordinary-factor coprimality. Its actual hypotheses omit q≠7 and the focused sum relation, appropriately.
4. `prime_focused_support_exclusive` proves q divides at least one of g,T using the exact Step 005 product and q|Q, then eliminates simultaneous support via the derived endpoint-unit premise. This is q-local and does not manufacture global Coprime g c or Coprime g Q.
5. `padicValNat_prime_square_product` is a satisfiable neutral valuation budget with explicit nonzero hypotheses on every factor. The coefficient seven and ordinary factors are q-units; no mistaken assumption vq(T)=1 is made for arbitrary q.
6. `padicValNat_focused_quadratic_budget` obtains nonzero g from positive focused height, nonzero T from positivity of the exact product, and obtains the ordinary q-unit premises from q|Q and primitive a,b. Its conclusion is vq(g)+vq(T)=2*vq(Q).
7. `prime_square_allocation_of_budget` requires an **explicit exclusion** `q|g -> q∤T`. The conditional `prime_square_focused_allocation` discharges it using the GTail head and q∤c. The two possible disjuncts are justified; no fixed selection of which side receives the square is asserted.
8. Satisfiable ordinary-number tests isolate needed conditions: q=13,g=13,c=2 on the g-only side; q=43,g=3,c=1 on the T-only side; abstract q=43 products with exclusive and mixed valuations. The mixed example refutes a **budget-only** square assignment, not the proved theorem.

## Codex validation and mathematics status

Reported final focused builds: neutral and conditional owners, both corresponding tests, and both Step 009 regressions all exited 0. The initial conditional-owner build's binomial endpoint order mismatch was fixed by a targeted commutativity rewrite, not weaker hypotheses. Eight `#print axioms` checks report `[propext, Classical.choice, Quot.sound]` each. Source import closure is acyclic with no FLT owner in the neutral module, and the source audit reports no added placeholders or unsafe rules. No broad suite was attempted in Step 010.

**Outcome B is correct.** The proof checks local necessary prime support and its exact allocation under hypothetical primitive positive Fermat7 data, without providing a contradictory local class, a number-field norm/unit receiver or constructive descent.

## Research decision for Step 011

A natural, *branch-sensitive* next target is multiplicative order:

- From q|Q and q∤ab, modulo q one gets a nontrivial cube root **except q=3**, hence 3|(q-1) for q≠3.
- From q|T and q∤g c, the ratio (c+g)/c modulo q has seventh power one but is not one, hence order exactly 7 and 7|(q-1).
- On the **T branch** of Step 010, q≠7 and the order-7 result exclude q=3 automatically. Combining orders 3 and 7 gives 21|(q-1).
- On the **g branch**, the order-7 argument is unavailable: do **not** assert 21|(q-1) for every q|Q.

For an entirely satisfiable neutral joint-residue calibration, at q=43 use (a,b,c,g)=(5,8,9,4): a+b=c+g, gcd(a,b)=1, Q=129=3*43, q|GTail 7 1 4 9, q∤g c, and the seventh-power Fermat equation holds **only modulo 43**, not over naturals. This is independent evidence that the underlying finite-field mechanism is nonvacuous. As a contrast, at q=13 use (a,b,c,g)=(14,29,30,13) with gcd1, q|Q, q|g, q∤T and q not congruent to 1 modulo 7; it demonstrates why the g-branch must not receive the order-21 conclusion absent additional hypotheses.

Next instruction should prove the neutral finite-field order lemmas first, source-audit existing cyclotomic residue/order theorems, and only then attach the T-side corollary to the Step 010 FLT7 receiver. Existing typed cyclotomic/root packet conclusions must not be imported as if their carriers were already constructed.

**Decision: APPROVED / Outcome B.** No merge, PR, facade promotion or FLT7 closure claim.
