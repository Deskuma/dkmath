# Instruction 023 — exact six-factor cyclotomic reconstruction of GTail 7 1

Date: 2026-10-10
Branch: `feature/GTail-SelectiveGap-FLT7-261009-v0`
Working directory: `lean/dk_math`
Prerequisites: `review-022.md`, `report-022.md`, `source-inventory-022.md`.
**Scope: Step 023 only — an exact element-level GTail cyclotomic factorization in the existing degree-six integral carrier, plus a checked factor-to-prime-slot incidence. No ideal valuation, principalization, signed packet reconstruction or FLT7 descent.**

## Objective and mathematical boundary

Step 022 established for a prime q with an explicit nontrivial seventh root r in ZMod q:
`(⨅ i:Fin 6, K_i) = (∏ i:Fin 6, K_i) = cyclotomicScalarIdeal q`,
where `K_i` are six actual distinct maximal ideals of
`R := SevenCyclotomicDegreeSixInt.Ring`.

Reconnect this result to the **original natural GTail** rather than building further abstract quotient infrastructure.

With `ζ := SevenCyclotomicDegreeSixInt.zeta`, define for naturals c,g and i:Fin6:

`F_i(c,g) := (c+g:R) - ζ^(i.val+1)*(c:R)`.

Target, as an equality **of elements of the actual source ring R**:

`∏ i:Fin6, F_i(c,g) = ((DkMath.CosmicFormula.GTail 7 1 g c : ℕ) : R)`.

This is the classical degree-seven homogeneous cyclotomic identity:
`∏_{k=1}^6 (X - ζ^k Y) = Σ_{j=0}^6 X^(6-j)Y^j`
and `GTail 7 1 g c = Σ_{j=0}^6 (c+g)^(6-j)c^j`.

**These are proof targets, NOT Step022 results.** This element product is not the ideal product of Step022. Neither equality licenses `(F_i)=K_j`, exact K-adic valuations, or an FLT7 contradiction. The element equation should be universal in natural c,g, without q-prime, GTail divisibility, Fermat equation, positivity, q-units or a supplied residue root.

## Phase 0 — existing-source and API inventory

Inspect exact signatures and possible already-proved generic factorization:
- `DkMath.FLT.Seven.SevenRamifiedFusionCyclotomicDegreeSixCarrier`: actual R, ζ, ζ^7=1, ζ≠1, primitive-root proof, quadratic relation, real-cubic alpha cubic relation, six additive coordinates and `ofReal`.
- `SevenRamifiedFusionCyclotomicDegreeSixDomain` if a legitimate IsDomain/nonzerodivisor proof is needed for cancellation.
- `DkMath.Lib.Cosmic.GTailNat` / `GTailSeven`: natural depth-one tail, exact degree-seven shell and any homogenous geometric quotient API.
- `DkMath.FLT.Seven.GTailCyclotomicSixRootInterpolation` (Step022) and `GTailCyclotomicSixRootOrbit` (Step021): existing six packet-free prime slots and scalar ideal product.
- `DkMath.FLT.Seven.GTailCyclotomicLocalEval`, `GTailCyclotomicPrimeAddress`: existing linear factor and actual RingHom image of ζ.
- `DkMath.NumberTheory.CyclotomicQRTraceOneBridge`, `DkMath.FLT.Kummer.CyclotomicPrincipalization` and Mathlib `Polynomial.cyclotomic`/primitive-root/finite product lemmas: identify any reusable exact seventh factorization without duplicating old owners.
- Verify all theorem names using source or `#check` and document the cheapest valid proof path.

Create `source-inventory-023.md` with ring type, exact sign/cast conventions, existing overlap, domain/cancellation requirements, and proof gates. No full FLT facade or signed-packet fabrication.

## Phase 1 — actual homogeneous sixth-degree product

Create a narrow owner, suggested `DkMath/FLT/Seven/GTailCyclotomicTailFactorProduct.lean`.

Define the six factors F_i and show `F_0(c,g) = gtailCyclotomicLinearFactor c g` in the actual degree-six ring, by using `ζ^1=ζ` and natural cast arithmetic.

Prove, for arbitrary X,Y:R if the infrastructure is convenient, or directly for universal c,g:

`∏ i : Fin 6, (X - ζ^(i.val+1)*Y) = ∑ j : Fin 7, X^(6-j.val)*Y^j.val`.

Acceptable routes:
- verified Mathlib cyclotomic-polynomial/primitive-root product identities, specialized to **this** degree-six source;
- explicit integral coordinate expansion using the existing ζ quadratic relation and the real-cubic generator cubic equation;
- a properly justified integral-domain root-factor/cancellation argument, with the genuine source IsDomain instance if needed.

**Crucial caution:** ζ^7=1 and ζ≠1 in an arbitrary commutative ring do not in themselves prove 1+ζ+...+ζ^6=0 by cancelling ζ−1. Either prove the needed non-zero-divisor premise, or use the actual carrier relations. Do not hide this gap behind informal division or a fresh axiom.

Do not replace the exact universal source identity by six numerical finite-field evaluations. Do not claim that each F_i is a prime element or generates a maximal kernel.

## Phase 2 — original natural GTail identity, including g=0

Prove the exact natural equality
`GTail 7 1 g c = ∑_{j=0}^6 (c+g)^(6-j)*c^j`
using existing GTail recursion/binomial structure or by a checked explicit degree-seven expansion.

**Do not cancel g from** `g*GTail=(c+g)^7-c^7` without first handling g=0: the main theorem must cover g=0 and c=0. A direct polynomial expansion is acceptable. Avoid defining an unrelated substitute for GTail.

Cast the natural identity to R and combine with Phase1 to prove the main public endpoint
`prod_six_gtailCyclotomicFactor_eq_GTail` (choose the actual theorem name). Verify the source equality is unconditional in natural c,g and compare against the prior owner expression of F_0.

**Primary success gate:** exact source element product for arbitrary c,g. If unavailable, stop at the strongest actually proved intermediate theorem, report Outcome C/partial and the missing polynomial/cancellation lemma; do not assert a weaker six-root evaluation as a replacement for the claim.

## Phase 3 — indexed factor versus indexed kernel: inverse exponents

For q prime with supplied nontrivial seventh root r and step021 root slots
`s_j = r^(j.val+1)` and `K_j=ker(ev_(s_j))`, evaluate each actual factor F_i:

`ev_(s_j)(F_i(c,g)) = (c+g:ZMod q) - s_j^(i.val+1)*(c:ZMod q)`.

Now specialize to **canonical Tail input** q∤c, q∤g and q|GTail, so r=(c+g)/c is admissible. Prove, without q|Q or Fermat hypotheses:

`F_i(c,g) ∈ K_j ↔ ((i.val+1)*(j.val+1)) % 7 = 1`.

This follows by cancelling the nonzero residue c and the checked `orderOf r=7`. The index relation is the **inverse-exponent permutation, not i=j**.

An explicit verified lookup is fine instead of general modular inverse machinery:
factor index i=0,1,2,3,4,5 must receive kernel index j=0,3,4,1,2,5, respectively. If using `fin_cases` to prove it, keep q and supplied r **generic**; do not hardcode q=43 into the theorem.

Establish that each F_i lies in exactly one among the six K_j, and in none of the five others. Make all memberships actual Ideal statements through Step020/021's RingHoms, not guessed from symbols.

This is an optional second-stage gate **after the exact element product**. It establishes q-local residue support only, NOT equality `Ideal.span {F_i}=K_j` and NOT exact powers of these primes in F_i.

## Phase 4 — calibrate and distinguish the two products

At q=43, c=9,g=4, canonical r=11, roots are [11,35,41,21,16,4]:
- prove generic factor-product theorem yields the scalar natural `GTail 7 1 4 9` as an actual R element;
- F_0 is the existing `13−9ζ` and is in K_0 but not K_1;
- verify the full factor-to-kernel permutation [0,3,4,1,2,5] and at least some actual nonzero cross-evaluations;
- scalar GTail belongs to all six kernels because 43|GTail. F_0 does **not** belong to scalar (43) despite that scalar product being in (43).
- display separately `∏ F_i = GTail:R` and `∏ K_i = (43):Ideal R`. DO NOT assert the finite products are equal to one another, since they are different carriers and mathematical objects.
- the q43 tuple with a=5,b=8 is explicitly **not** an exact Fermat7Equation solution.

Boundary tests: g=0, c=0 with g=1, c=1 with g=0; q=13 Gap branch has ratio1 and lacks q|T; q=7 has no nontrivial scalar seventh root but the **unconditional** element product should still be valid in R. c=0,g=0 evaluates all six factors to zero, and should not be used to claim unique q-local support.

The old signed packet factorization, Eisenstein degree-two ideal and the six residue kernels are separate mathematical structures. No ring hom between integral Eisenstein and cyclotomic carriers is obtained from this product identity.

## Deliverables, validation and STOP

Required:
- `DkMath/FLT/Seven/GTailCyclotomicTailFactorProduct.lean`;
- `DkMathTest/FLT/Seven/GTailCyclotomicTailFactorProduct.lean`;
- `source-inventory-023.md`, `report-023.md`;
- truthful post-022 `ROADMAP.md` entry.

Build sequential focused new source/test and Step022/021 regression with process-local `LEAN_NUM_THREADS=2`. Record command/exit, new public theorem signatures, all `#print axioms`, exact proof method, intermediate repairs, source/graph/forbidden-token checks and edge-case numbers. Do not edit existing ring definitions, heavy signed packet owners, facades or unrelated Legendre files; no full clean build, PR or merge.

**Outcome B expected** for a real degree-six element-level GTail six-factor identity (and optionally complete inverse-index incidence), without FLT7 descent. **Outcome C** if a required source-domain/cyclotomic relation is missing, or a proposed factor-index identity is false: report the smallest corrected contract and preserve checked partial results. **Outcome A** only for an independently compared noncircular FLT7 arithmetic obstruction, not a restatement of cyclotomic factorization.

**STOP after Step023.** No ideal principalization, exact K-adic valuations, class-group/unit-power extraction, reconstructed primitive counterexample, or unconditional FLT7 conclusion.
