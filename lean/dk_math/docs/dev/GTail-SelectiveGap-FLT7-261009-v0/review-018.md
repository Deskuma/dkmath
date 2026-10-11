# Review 018 — paired roots in one finite residue field

Date: 2026-10-10
Branch: `feature/GTail-SelectiveGap-FLT7-261009-v0`
Decision: **APPROVED — Step 018 COMPLETE / Outcome B**

## Evidence and inspection scope

Static GitHub inspection of:
- `DkMath/Lib/NumberTheory/GTailSevenPairedResidue.lean` (82 lines);
- `DkMathTest/NumberTheory/GTailSevenPairedResidue.lean` (138 lines);
- `report-018.md`, `source-inventory-018.md` and the previous Step 011/014/017 contracts;
- existing `SevenRamifiedFusionCyclotomicPrimeAddress.lean`, `SevenRamifiedFusionCyclotomicDegreeSixCarrier.lean`, and `SevenRealCubicInt.lean` (reviewed as **different owner/carriers**).

This reviewer did **not** independently run Lean. Codex's report records final focused production/test builds, Step 017 and Step 011 regressions and public `#print axioms` lists for one new definition and five theorems, all within standard foundations.

## Mathematical and Lean API review

1. `gtailSevenTailRatio q c g = (c+g)/c : ZMod q` requires a prime-field `Fact` to use field division; the definition itself does not assert that c is a unit.
2. `gtailSevenTailRatio_pow_seven` correctly uses the **natural GTail degree-seven equality cast into ZMod q**, together with q|T and q∤c. It does not divide by g; the hypothesis q∤g is not needed for this seventh-power-one endpoint.
3. `gtailSevenTailRatio_ne_one` uses q∤c and q∤g to exclude a trivial ratio. The nonzero ratio follows from the checked seventh-power equation and not from an unproved numerator-unit assertion.
4. `seven_geom_sum_eq_zero_of_pow_eq_one` multiplies the explicit seven-term sum by (r-1), uses the exact polynomial telescoping identity and cancels **only after** proving r≠1. The test r=1 in ZMod43 demonstrates why the nontriviality guard is essential; r^7=1 by itself is insufficient.
5. `gtailSeven_paired_residue` combines the existing *Eisenstein* root t=−a/b (satisfying t²−t+1=0), the independently constructed seventh root r=(c+g)/c (r^7=1≠r and r≠0), the seven-term vanishing sum, and q≠3 obtained from the existing Step 011 order theorem. Its source hypotheses are **satisfiable without Fermat7**, include q≠7, q|Q, q|T, q∤b,c,g, and do not assert a map between the integral source rings.
6. At q=43, a=5,b=8,c=9,g=4, the tests independently check coordinate balance, q|Q and q|T, t=37, 1−t=7, r=11, the two root relations, and the Step 017 actual Eisenstein α/α² ideal orientation. They explicitly verify `¬Fermat7Equation 5 8 9`. q=13 demonstrates the *gap branch* yields ratio 1 and q∤T. q=3 repeated root, q=5 root absence, q=7 excluded characteristic are kept distinct.
7. There are 20 kernel-checkable examples in the report. The first test build failed because the test attempted to decide an unexpanded Fermat7Equation; unfolding the predicate repaired the test without changing any mathematical statement. Final reported production/test builds and Step 017/011 regressions exited 0. Six public symbol axiom checks returned `[propext, Classical.choice, Quot.sound]` and no new sorry/axiom/unsafe.
8. The **production** module imports only neutral Lib owners, with no FLT7 owner in its dependency closure. The **test** imports `DkMath.FLT.Seven.Basic` solely to refute the exact equation on the concrete neutral tuple, explaining the enlarged test import closure; no owner cycle exists.

## Existing cyclotomic carrier and the true missing receiver

The Step 018 report correctly identifies a **previously implemented** degree-six evaluation:
- `SevenCyclotomicDegreeSixInt.Ring = QuadraticAlgebra SevenRealCubicInt (-1) (alpha-1)` with ζ²−(α−1)ζ+1=0 and ζ^7=1.
- `SevenCyclotomicDegreeSixInt.localEval` already maps this exact carrier into `ZMod q`, but is parameterized by `QuotientPrimeMuSevenAddress` from a `RamifiedSignedRootDepthPacket`; it **cannot** be instantiated from the Step 018 bare neutral Tail ratio without additional proven packet premises.
- `QuotientPrimeMuSevenAddress.beta_cubic_relation` already proves the real-cubic relation for β=1+ratio+ratio⁻¹, and `evalAlphaRoot` already constructs a cubic RingHom from that relation. These are reusable proof *patterns* but retain packet-indexed interfaces.
- The seventh-cyclotomic **ramified q=7** owner is a different carrier and prime from the earlier `TraceOneInt(-1)` **ramified q=3** kernel. Do not identify them or induce an ideal transport by equal codomains.

The next disciplined experiment is a **packet-free** specialization of the same well-understood algebra: take an arbitrary nontrivial seventh root r in ZMod q, prove β=1+r+r⁻¹ satisfies `β³−2β²−β+1=0`, then construct a real-cubic RingHom and, if it kernel-checks with narrow imports, a degree-six `Ring →+* ZMod q` sending ζ to r. For the Step 018 Tail ratio the needed r premises are already proved. This would supply an **actual evaluation map from the existing seventh cyclotomic carrier**, not a map from the separate Eisenstein ring into it and not a comparison of prime ideals.

At q=43, c=9,g=4, r=11, r⁻¹=4 and β=16. The natural linear cyclotomic factor `(c+g) − ζ c` should evaluate to zero (13−11·9≡0 mod43). This is the most informative nonvacuous target of a proposed Step 019. Existing packet-indexed `localEval` must be left untouched; any extensional relation requires a **separately proven ratio equality** on overlapping premises.

## Decision

**APPROVED — Outcome B**. The common ZMod root packet is checked, but no ring/ideal map between Eisenstein and seventh-cyclotomic carriers, novel FLT7 obstruction, unit-power class or descent has been obtained.

Proceed to a narrowly scoped **Step 019 packet-free degree-six evaluation** if focused Lean builds support it, with the cubic relation and base RingHom as independent acceptance gates. No PR, branch merge, facade promotion, cyclotomic ideal equality or FLT7 closure is authorized.
