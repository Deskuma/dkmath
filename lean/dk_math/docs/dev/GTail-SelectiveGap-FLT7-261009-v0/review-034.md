# Review 034 — common quadratic receiver and typed prime contractions

Date: 2026-10-11
Branch: `feature/GTail-SelectiveGap-FLT7-261009-v0`
Decision: **APPROVED — Step 034 COMPLETE / Outcome B**

## Evidence and verification level

Statically reviewed the actual pushed GitHub sources:
- `DkMath/FLT/Seven/GTailEisensteinCyclotomicCommonReceiver.lean` (149 lines);
- `DkMathTest/FLT/Seven/GTailEisensteinCyclotomicCommonReceiver.lean` (159 lines);
- `report-034.md`, `source-inventory-034.md`, `frontier-034.md`;
- existing `TraceOneQuadratic`, `GTailSevenResidueIdeal`, `GTailCyclotomicLocalEval`, `GTailCyclotomicPrimeAddress`, `GTailCyclotomicSixRootOrbit`, and Step033 two no-direct-hom declarations.

**This is a static source/proof-route review, not an independently executed Lean build.** Codex's recorded final new production build (04), test build (07), and Step033/032 focused regressions (08/09) all exit 0 and report warning count 0; 37 examples and 23 public declaration `#print axioms` checks were recorded. The reported nonstandard axiom set is empty; only normal Lean foundations `propext`, `Classical.choice`, `Quot.sound` appear where used. Intermediate failed source gate (01: nested ext normalization) and test (06: wrong sign of second Eisenstein coordinate) were **fixed and disclosed**; the complete final build was not claimed.

## Actual checked mathematics

1. `Carrier := QuadraticAlgebra SevenCyclotomicDegreeSixInt.Ring (-1) 1` is a quadratic algebra over the **actual degree-six integral carrier R**. The additional generator ω has `ω²−ω+1=0`. It matches `TraceOneInt(-1)` (discriminant −3), not the old `TraceOneInt(-2)` (discriminant −7). No field, integral domain, rank-12 basis, minimal compositum or flatness is asserted.
2. `fromCyclotomic : R→+*Carrier` is the canonical unital `algebraMap`; `fromEisenstein : TraceOneInt(-1)→+*Carrier` is the actual two-signed-coordinate formula `x↦⟨(x.fst:R),(x.snd:R)⟩`. Multiplication is checked using source E's `s=-1` multiplication and C's genuine quadratic structure. No source-to-source hom is introduced.
3. `fromEisenstein_tau`, `fromCyclotomic_zeta`, `fromEisenstein_intCast`, `scalar_images_eq`, `omega_relation` give actual generator images, unital integer-scalar compatibility and the E-generator's equation inside C. Only integer scalar images agree universally; arbitrary E/R elements do not.
4. `fromCyclotomic_injective` invokes the actual `QuadraticAlgebra.algebraMap_injective`; `fromEisenstein_injective` compares real/imaginary C coordinates and uses the actual projection `z.re.fst` of R to recover integers. These are proofs of **separate embeddings**, not an assumption from the names of the rings.
5. `eval43 : C→+*ZMod43` has the genuine formula `evR11(x.re)+37*evR11(x.im)`. Its multiplication law is proved from `37²−37+1=0` in the field and actual QuadraticAlgebra re/im multiplication, not from a fictional integral 37-root in R.
6. `eval43_comp_cyclotomic` and `eval43_comp_eisenstein` are **actual RingHom equalities** to the preexisting R-root11 and E-root37 RingHoms. `eval43_zeta`, `eval43_tau` and `eval43_scalar` check generator residue values 11,37 and all integer casts.
7. `M43 := RingHom.ker eval43 : Ideal C`; `M43_comap_eisenstein` and `M43_comap_cyclotomic` prove that the SAME ideal contracts to **P37 : Ideal E** and **K11 : Ideal R**, respectively. `M43_comap_cyclotomic_slot_zero` checks that K11 is the Step021 slot-zero kernel. Contractions are typed ideal equalities *within their respective rings*; they do not identify ideals across source rings.
8. `eval43_surjective` uses the checked surjectivity of the R evaluation and its commuting triangle; `M43_isMaximal` and `M43_isPrime` follow from the actual surjection onto prime field ZMod43. There are no unsupported dimension, domain, discrete-valuation or class-group assumptions.
9. Actual non-Fermat Step032 witness `α=gtailSevenNormCoord 1166 1857∈E` and `F0=gtailCyclotomicFactor 1858 1165 0∈R`: the test proves `α²∈P37²` with E conjugate/scalar exclusions and `F0∈K0²` using earlier generic theorems. Their **separate** images both lie in M43 and evaluate to 0. Yet `fromEisenstein α ≠ fromCyclotomic F0`: compare the independent C imaginary coordinate, which is the nonzero integer 1857 in the first image and 0 in the second, and reduce it through evR43. This is an actual Lean negative equality, not a semantic interpretation alone.
10. Step033's two **nonexistence of direct unital E→R/R→E** theorems still compile: both positive embeddings into C are mathematically consistent with these no-direct-map results. Source does not construct an E↔R ring hom, signed packet or equality of ideal extensions/powers. The witness does NOT satisfy Fermat7Equation, and is not misrepresented as an FLT counterexample.
11. `Carrier` is an abbreviation; the new owner has three bundled RingHom definitions, an Ideal definition, and eighteen public theorems = **23 public declarations**. The report records standard-only axiom audits, correct direct import (Step033), no new neutral→FLT cycle, source placeholders, unsafe shortcuts or old-owner edits. Regret from the first incorrect im-coordinate sign is explicitly reflected in test repair; the final test uses the true `gtailSevenNormCoord_eq : α=⟨a,b⟩` identity.

## Frontier: avoid overreading a shared prime

**APPROVED / Outcome B.** We now possess two actual injective source RingHoms and a common q43 maximal ideal whose separate contractions recover the source prime addresses. This is a constructive, genuinely type-correct bridge, but it does **not** imply equality of the two embedded source elements, global FLT7 balance, equality of extended source ideals, or transport of their arbitrary ideal powers.

Suggested **Step035**: illuminate the **fiber multiplicity** of that common address rather than postulating equality of extensions or building an arbitrary class/valuation tower.

- At q43, the Eisenstein generator has **two** distinct root choices `t∈{37,7}` satisfying `t²−t+1=0`; the R seventh-root generator has **six** distinct nontrivial choices `s=11^(j+1)` for `j:Fin6`, already verified via `sixSlotRoot_injective`.
- Each pair `(t,s)` defines a genuine source-compatible `evalPair_{t,s}:C→+*ZMod43`, simply the checked Step034 quadratic coordinate evaluation formula. Its maximal kernel `M_{t,s}` contracts back to `P_t` on E and `K_s` on R.
- Prove injectivity of the **2×6 kernel address map** `(Fin2×Fin6)→Ideal C`, using contractions and existing separation of E conjugate root ideals and R six-slot roots. This gives **12 distinct maximal ideals**, and explains why one prime in either source does not force a unique prime above it in C.
- Optional but substantive: prove each extension `Ideal.map fromEisenstein P37` and `Ideal.map fromCyclotomic K0` is **properly smaller than M_37,11** via a second root evaluation: `ω−37` witnesses the R-side non-equality using t7 at fixed s11; `ιRζ−11` witnesses the E-side non-equality using t37 at s35. A precise `Ideal.map` containment/nonmembership proof is needed; no ideal equality may be assumed. This is a proposed next gate, not established in Step034.
- Test whether `M_37,11` agrees with the already checked `M43` and retain actual q43 witness cofactor/non-Fermat boundaries. Do not call this 12-ideal grid the **complete** prime spectrum of C or prove arbitrary K-adic power transfer.

This next phase gives a rigorous geometric/local branching picture to inform future signed-carrier or global reconstruction research, while keeping old Step010 local valuation and Step032 global balance frontiers separate.

No PR, merge/rebase, facade, all-k ideal valuation, class/unit extraction or FLT7 descent is authorized.
