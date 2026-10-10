# Review 020 — packet-free maximal kernels and unique Tail root address

Date: 2026-10-10
Branch: `feature/GTail-SelectiveGap-FLT7-261009-v0`
Decision: **APPROVED — Step 020 COMPLETE / Outcome B**

## Reviewed evidence and verification limit

Inspected the pushed GitHub sources:
- `DkMath/FLT/Seven/GTailCyclotomicPrimeAddress.lean` (135 lines);
- `DkMathTest/FLT/Seven/GTailCyclotomicPrimeAddress.lean` (142 lines);
- `report-020.md`, `source-inventory-020.md`, earlier Steps 018–019;
- `SevenRamifiedFusionCyclotomicLinearPrimeAddress.lean` and `SevenRamifiedFusionGlobalOrientedPrimeFactorization.lean` to distinguish prior packet-indexed results from this genuinely new bare-root receiver.

This is a **static source, theorem-contract, example and proof-route review**. Codex's local report records passing final focused production/test builds, Step 019/018 regression builds, 23 checked examples and standard-only axiom audits. **No independent Lean rebuild was performed** in this review.

## Mathematical conclusions

1. `seventhRootKernel r hr0 hr7 hr1` is literally `RingHom.ker (evalCyclotomicFromSeventhRoot r hr0 hr7 hr1)` in the actual `SevenCyclotomicDegreeSixInt.Ring`. The input is a scalar seventh root, **not** a `RamifiedSignedRootDepthPacket`. Kernel membership is equivalent to zero evaluation with the same explicit root proofs.
2. `evalCyclotomicFromSeventhRoot_surjective` lifts every `ZMod q` class via the embedded integer residue representative `ofReal (z.val : SevenRealCubicInt)`. Since the codomain is a field for prime q, the subsequent `seventhRootKernel_isMaximal` and `seventhRootKernel_isPrime` are actual checked structural conclusions, not assertions from nomenclature.
3. `seventhRootKernel_comap_ofReal` uses the already proved `evalCyclotomicFromSeventhRoot_ofReal` for the precise real-cubic base kernel. `seventhRootKernel_comap_intCast` uses the correct integer-cast-zero iff to identify contraction with `Ideal.span {(q:ℤ)}` **in integers**, not as an unproved ideal factorization in the degree-six carrier.
4. `seventhRootKernel_cardQuot` uses the established quotient-kernel equivalence of the surjective map and `Nat.card_zmod` to show residue cardinality q. These new theorems parallel existing packet-indexed API but apply to strictly more general *supplied root* input data.
5. `evalCyclotomic_linearFactor_eq_zero_iff` is correctly guarded by q∤c, and **does not require** q|GTail or q∤g: it directly cancels the nonzero field denominator in `(c+g)-s*c=0` to identify `s=(c+g)/c`. The availability of the canonical root-indexed RingHom itself is a separate fact using q|T, q∤c, q∤g.
6. `seventhRootKernel_separating_element` constructs the **actual integral witness** `zeta-ofReal(r.val)`, which lies in K_r and not in K_s for r≠s. `seventhRootKernel_ne` uses that witness; mere inequality of map values is not substituted for ideal inequality.
7. `gtailCyclotomicLinearFactor_unique_address` combines Step 019's canonical Tail membership with exclusion from any different admissible seventh-root kernel. It makes no unsupported assertion that **every** prime ideal in the degree-six ring is one of these root kernels.
8. q=43 checks r=11, s=35=11², nontrivial seventh powers, K11/K35 maximal/prime with integer and real contractions and quotient cardinality 43, and **the same** actual F(9,4) in K11 but not K35. The finite difference `13-35*9≠0` is tested through an actual RingHom as well as by computation. q13 Gap and q7 ramified boundary checks are not confused with root-indexed q43 support.
9. The test-only optional comparison proves equality of the new bare-root RingHom with the old packet-indexed `a.eval` under an **actually supplied old address** and the same root value. It does not manufacture a packet from q43 neutral data or assert an ideal equality absent an evaluation equality theorem.
10. The explicit false-boundary witness `c=g=0` gives F=0 in both distinct root kernels and demonstrates that q∤c is essential for unique addressing. The q43 tuple still refutes the **exact** Fermat equation, so this successful typed receiver alone is not an FLT7 obstruction.
11. Codex reports one new definition, eleven theorems, all twelve public axiom lists equal to `[propext, Classical.choice, Quot.sound]`, no placeholders/extra axioms/unsafe, and no neutral→FLT owner cycle. Intermediate errors were repaired without changing theorem hypotheses. These claims are sourced from the report rather than an independently executed build.

## Decision and targeted next frontier

**APPROVED / Outcome B** is accurate. We now have a packet-free *single-root* maximal prime address and a uniquely selected Tail factor support slot in the existing degree-six carrier. We do **not** yet have classification of every prime above q, full q splitting/product `(q)=∏K_{r^i}`, exact ideal-adic valuations, a map between the different Eisenstein and seventh-cyclotomic integral rings, a compatible signed-depth packet from the natural Tail tuple, or a Fermat descent.

**Step 021 proposal — finite six-root orbit / pairwise comaximality:**
- An admissible root r has exact multiplicative order seven. Its six powers `r^1,...,r^6` are nontrivial and pairwise distinct. Build a small finite indexed packet over `Fin 6`, **without** constructing any signed-depth packet.
- Specialize Step 020's actual root kernels. Distinctness is already proved by the separating element; combine with their actual maximality to show **pairwise comaximality**. For the selected Tail factor under q∤c, q∤g and q|GTail, show membership in precisely the canonical r-slot and exclusion from the other five indexed root kernels.
- q43 supplies the six concrete roots `11,35,41,21,16,4` (successive powers of 11), so the six-kernel construction is satisfiable and all tests can be explicit.
- Optionally inspect the existing degree-six `rotateEquiv_zeta` (ζ↦ζ²) and quadratic `star_zeta` (ζ↦ζ⁻¹) as possible **source automorphism** transports between root-indexed kernels. An equality of evaluations must be proved on the whole carrier, not guessed from the ζ image alone. Since these owners have heavy packet closures, no additional import is mandatory.
- Crucially, pairwise comaximality of six ideals by itself does **not** show their product equals `(q)`. That future result additionally needs a full **coordinate interpolation/intersection** or equivalent equality proof. Do not infer it in Step 021.

No PR, branch merge, façade promotion, cyclotomic ideal product, unit-power class, or unconditional FLT7 claim is authorized.
