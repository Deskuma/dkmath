# Review 017 — norm-square support in ramified and split Eisenstein primes

Date: 2026-10-10
Branch: `feature/GTail-SelectiveGap-FLT7-261009-v0`
Decision: **APPROVED — Step 017 COMPLETE / Outcome B**

## Basis and verification limit

Static inspection of the pushed GitHub files:
- `DkMath/Lib/NumberTheory/GTailSevenIdealSquareAddress.lean` (99 lines);
- `DkMathTest/NumberTheory/GTailSevenIdealSquareAddress.lean` (130 lines);
- `report-017.md`, `source-inventory-017.md`;
- actual Step 012, 014–016 typed norm/ideal/ramified theorems and Step 010–011 FLT7 prime-support owners.

**Reviewer did not independently execute Lean.** Codex's local report records successful final focused production/test builds, Step 015–016 regressions, 22 kernel-checked examples and seven standard-foundation-only axiom audits.

## Mathematical findings

1. `three_dvd_norm_iff_mem_ramifiedIdeal` uses the existing prime norm/kernel disjunction at q=3 and the actual coincident roots t=2=1-t. It rewrites memberships to raw evaluations before identifying the repeated ideal, correctly avoiding proof-term dependent rewriting.
2. `scalar_three_dvd_square_of_dvd_norm` obtains z in the actual ramified kernel, applies `Ideal.mul_mem_mul`, rewrites the Step 016 **proved** `P*P=eisensteinScalarIdeal 3`, and uses `Ideal.mem_span_singleton` to convert to element-level embedded scalar 3 divisibility. It is valid for arbitrary signed `z:TraceOneInt(-1)`; it does **not** imply scalar 3 divides z.
3. `scalar_three_dvd_gtailSevenNormCoord_sq` reuses the Step 012 integer/natural norm-divisibility iff for the exact selected element alpha(a,b), with no invented Fermat equation or norm-square-to-element-square converse.
4. `square_mem_eisensteinResidueIdeal_mul_self` is a general actual ideal-product membership, with no primality required. It makes no assertion of exact ideal-adic exponent.
5. `square_not_mem_conjugate_eisensteinResidueIdeal` obtains the conjugate kernel's **IsPrime** from Step 014's checked maximality for prime q. Nonmembership of z excludes its square by the prime-ideal product property. No hidden separation is required for this standalone exclusion.
6. `split_eisenstein_square_address` additionally uses the Step 015 **separated-root intersection** equality to rule out membership of z² in the scalar principal ideal (q). The canonical `gtailSevenNormCoord_split_square_address` supplies q-prime, q≠3, q|Q and q∤b to derive actual orientation. It does not silently deduce orientation from norm divisibility alone.
7. Numerical calibration is genuine: pi=⟨1,1⟩ has norm3, embedded3∤pi but embedded3|pi². Signed z=⟨-2,1⟩ also has norm3 and is covered by the generic theorem. At alpha=⟨5,8⟩, norm alpha=129, alpha²=⟨-39,144⟩, norm(alpha²)=129², alpha²∈P37², alpha²∉P7, and embedded43∤alpha² despite 43|norm alpha and 43²|norm(alpha²). Embedded3|alpha² still holds. Thus the unguarded split-prime scalar square-lift is **false**, while ramified three is valid.
8. No new FLT7 owner was added, correctly avoiding an unsupported identification between q-support in the scalar GTail gap/Tail product and a selected Eisenstein/cyclotomic prime ideal. The direct neutral import is Step 016 only; no neutral→FLT cycle. Codex's source audit reports no placeholders/new axioms/unsafe, and final builds/axioms pass.

## Classification / original frontier

**Outcome B** is an accurate classification. Degree-two ideal-square **support** is now proved, but neither exact ideal-adic exponents (P² but not P³), an equality of principal ideals (z²)=P², nor a typed degree-seven cyclotomic norm/unit/descent transfer has been established. The result is a nonvacuous neutral arithmetic instrument, not a new FLT7 contradiction.

Before proposing a naive ring homomorphism transporting the Eisenstein degree-two ideal P into the current FLT7 degree-six cyclotomic `SevenCyclotomicDegreeSixInt.Ring`, inspect its **different base and relation**. The former has generator tau with tau²=tau-1, while the latter is `QuadraticAlgebra SevenRealCubicInt (-1) (alpha-1)` with generator zeta satisfying zeta²-(alpha-1)zeta+1=0 and zeta^7=1. These are not definitionally the same quadratic algebra or even over the same base. The existing `SevenRamifiedFusionCyclotomicRamifiedPrime` constructs a **different q=7 ramified uniformizer**, unrelated to the q=3 Eisenstein P just built. No unproved direct ring embedding or ideal map is authorized.

## Step 018 recommendation: common finite-residue field, not false carrier identification

A narrow **shared ZMod q receiver** is the mathematically disciplined next experiment on the *Tail* branch:
- retain t=-(a/b) in ZMod q with t²-t+1=0 as the Eisenstein root;
- retain r=(c+g)/c in ZMod q with r^7=1≠r and r≠1, provided prime q≠7, q|Q, q|T and q∤a,b,c,g;
- show r is a zero of the **seventh cyclotomic polynomial** Phi_7(X)=1+X+...+X^6 over ZMod q using r^7=1 and r≠1;
- expose the selected Eisenstein RingHom at t and the **independent scalar** cyclotomic-root evaluation at r in their shared residue field; no map between the integral rings is implied;
- use the nonvacuous q=43, (a,b,c,g)=(5,8,9,4) calibration. The exact Fermat equation is **false** for this tuple; the modular root intersection is independently satisfiable.

Research must first source-audit any existing typed degree-six cyclotomic residue evaluation and Mathlib polynomial cyclotomic APIs. An actual RingHom from the degree-six FLT7 carrier to ZMod q is **optional and must not be asserted** without a checked map including its real-cubic base. This prevents accidental conflation of the two quadratic conventions.

This is a genuine **receiver-interface / feasibility** study. If a shared-field root pair only repackages Step 011's 21|q-1 result, state so; no new FLT7 obstruction/descent follows.

**Decision: APPROVED / Outcome B.** No develop merge, PR, facade promotion or FLT7 closure claim.
