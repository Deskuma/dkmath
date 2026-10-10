# Review 019 — packet-free evaluation of the actual degree-six cyclotomic carrier

Date: 2026-10-10
Branch: `feature/GTail-SelectiveGap-FLT7-261009-v0`
Decision: **APPROVED — Step 019 COMPLETE / Outcome B**

## Evidence and verification limit

Static GitHub inspection of:
- `DkMath/Lib/NumberTheory/GTailSevenRealTraceResidue.lean` (33 lines);
- `DkMath/FLT/Seven/GTailCyclotomicLocalEval.lean` (126 lines);
- two corresponding `DkMathTest` modules (43 and 106 lines);
- `report-019.md`, `source-inventory-019.md`, Step 018 neutral root theorems;
- packet-indexed `SevenRamifiedFusionCyclotomicPrimeAddress`, `SevenRamifiedFusionCyclotomicDegreeSixCarrier`, `SevenRamifiedFusionCyclotomicLinearPrimeAddress`, and `SevenRamifiedFusionGlobalOrientedPrimeFactorization`, for carrier/API overlap.

This is **static Lean source/proof-route inspection**. Codex records successful final focused builds of both new production/test pairs, the Step 018/017 regressions, 30 examples and all fourteen public declaration axiom prints within standard Lean foundations. Reviewer did not independently rerun Lean. Failed intermediate elaborations and subsequent repairs are documented in the local report, not hidden.

## Review findings

1. `seventhRootBeta` is a genuine `ZMod q` trace `1+r+r⁻¹`. `seventhRootBeta_cubic` proves `β³−2β²−β+1=0` using nontrivial r^7=1, nonzero r, Step 018 seven-term geometric sum and field denominator cancellation. It does not assume an existing signed-depth packet or transport a real-cubic alpha by fiat.
2. `seventhRootBeta_quadratic` verifies the **correct carrier sign** `r²=−1+(β−1)r` from r≠0 and the inverse identity. This relation uses no seventh-power premise; the cubic relation is a separate gate.
3. `evalRealFromSeventhRoot : SevenRealCubicInt →+* ZMod q` is a **bundled RingHom** on arbitrary signed triple coordinates, with multiplication checked using the existing ring's explicit coordinate laws and the newly proved cubic relation. The generator `alpha` evaluates to β and embedded integers are mapped correctly.
4. `evalCyclotomicFromSeventhRoot : SevenCyclotomicDegreeSixInt.Ring →+* ZMod q` uses the actual `QuadraticAlgebra SevenRealCubicInt (-1) (alpha−1)` re/im coordinate multiplication. Its multiplication proof explicitly consumes both the real-cubic RingHom and the quadratic r/β relation; `zeta↦r`, `ofReal x↦evalReal x`, and `ofReal alpha↦β` are checked. No new or imaginary map from `TraceOneInt(-1)` to this ring appears.
5. `gtailCyclotomicEval` genuinely instantiates the packet-free degree-six RingHom at the Step 018 natural Tail ratio r=(c+g)/c. Its source hypotheses are exactly q∤c, q∤g and q|GTail, under prime q; **no** signed quotient-root packet or Fermat7 equation is smuggled into the signature.
6. `gtailCyclotomicEval_linearFactor` correctly establishes `ev_r((c+g)−ζ c)=0` by the **ratio definition and c-unit denominator**, and `gtailCyclotomicLinearFactor_mem_ker` places that actual degree-six element in the actual RingHom kernel. The proof does not establish principalization, an ideal power, or equivalence with a previously indexed signed-depth linear carrier.
7. Numerical q=43, a=5,b=8,c=9,g=4 verifies r=11, r⁻¹=4, β=16; real α↦16, degree-six ζ↦11, and evaluation of `ofReal 13−ζ*ofReal9` is 13−11*9=0. The tuple satisfies neutral Q/T congruences while `¬Fermat7Equation 5 8 9`. Other tests guard r=1 in characteristic 43, distinct q=7 ramified ζ↦1, q=3 Eisenstein repeated root, q=5 Eisenstein inert, and q=13 gap-side missing T support.
8. Public symbols comprise five definitions and nine theorems. Codex's final logs report 13 declarations with the standard three axioms and `gtailCyclotomicLinearFactor` with `[propext, Quot.sound]`. No new axiom/placeholder/unsafe or neutral→FLT owner import was found; neutral β module imports only neutral owners. The FLT carrier owner imports the existing degree-six owner directly, without full FLT facade. Full test suite was not rerun.

## Critical API overlap

The existing `CyclotomicLinearPrimeAddress` is **packet-indexed** by a `RamifiedSignedRootRoutingPacket` and quotient-prime address. It already proves:
- `evalKernel_isMaximal`;
- `evalKernel_comap_ofReal`;
- `evalKernel_comap_intCast`;
- `evalKernel_cardQuot`;
- orientation of the signed-depth linear factor and its conjugate.

Step 019's new evaluation has **the same coordinate formula** when both maps share the same root r, but the neutral GTail r does not supply the old signed-depth packet. The old API is not an interchangeable source of these conclusions on the new data. Conversely, a generic root-indexed kernel's maximality and contractions can be proved directly from surjectivity of the new RingHom; that is a typed interface adaptation, not a new FLT7 arithmetic obstruction.

## Next research boundary for Step 020

Prioritize an **actual packet-free local prime address with root uniqueness**:
- Let `K_r := RingHom.ker (evalCyclotomicFromSeventhRoot r hr0 hr7 hr1)` in the existing degree-six carrier. Show surjectivity by scalar integer lifts, maximality, real-cubic/integer contractions and (optionally) cardinality of quotient, carefully comparing against the named packet-indexed proof.
- For an independent second nontrivial seventh root s of the same `ZMod q` and c q-unit, show
  `eval_s ((c+g)−ζ c)=0 ↔ s = (c+g)/c`.
  Thus a Tail factor selected by its natural ratio lies **in exactly one of the distinct root-indexed kernels**. The implication does not require an FLT7 equation; constructing `eval_s` does require the separate nontrivial root proofs.
- Prove `K_r ≠ K_s` for distinct roots using an **actual kernel witness**, e.g. `ζ−ofReal (ZMod.val r)`, not merely different values of homomorphisms. At q=43 with r=11, s=35=11², F(9,4) lies in K11 and not K35; both RingHoms exist, and 43 does not divide c=9.
- If low cost, compare the new bare-root evaluation to old `localEval` **only when an old address exists and the two root values are shown equal**. Do not construct a signed-depth packet from the neutral q=43 example.
- Do not infer a six-prime product equality `(q)=∏_{k=1}^6 K_{r^k}`, exact q-ideal valuations, equality with the **different Eisenstein kernel**, or a descent mechanism without further separate theorems.

**Decision: APPROVED / Outcome B.** Step 020 should be a tightly scoped typed kernel-and-unique-root address, not a general cyclotomic factorization or FLT7 closure. No PR, merge or facade promotion authorized.
