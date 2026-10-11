# Instruction 025 — exact second-power membership at the selected GTail prime slot

Date: 2026-10-10
Target branch: `feature/GTail-SelectiveGap-FLT7-261009-v0`
Working directory: `lean/dk_math`
Prerequisites: `review-024.md`, `report-024.md`, `source-inventory-024.md`.
**Scope: Step 025 only — the reverse square-depth implication and a genuine second-level iff for natural GTail factors with a canonical Tail root. No arbitrary all-k valuation, principalization, signed packet synthesis or FLT7 descent.**

## Target — a stronger statement than Step 024

Let `R=SevenCyclotomicDegreeSixInt.Ring`. From Steps 019–024, under prime q and natural c,g with

```text
hc : ¬ q ∣ c
hg : ¬ q ∣ g
hT : q ∣ GTail 7 1 g c
r := gtailSevenTailRatio q c g
J_i := sixRootKernel r (proofs from Step018) (sixInverseSlot i)
F_i := gtailCyclotomicFactor c g i
T := GTail 7 1 g c
```

Step 023 proves `∏ F_i = (T:R)` and `F_i∈J_j ↔ j=i` in this reindexed family; Step 022 proves `∏J_i=(q)`. Step 024 already gives

```text
F_i ∈ J_i² → q² ∣ T.
```

**Main new proof target**:

```text
q² ∣ T → F_i ∈ J_i².
```

Then package the checked exact iff for every factor index i:

```text
F_i ∈ J_i² ↔ q² ∣ T.
```

This is conditional on q|T and the two q-unit premises, not an assertion that q²|T universally. Step 024’s theorem under q²∤T remains valid as a corollary and should not be weakened.

### Mathematical route to check, not assume

1. From q²|T and scalar q∈J_i, deduce **embedded scalar T∈J_i²** by actual ideal multiplication / ideal-power membership (since `(q²:R)∈J_i²`). The conclusion does **not** identify J_i² with scalar(q²).
2. Fix i. By Step 023’s **unique-slot** theorem, for each h≠i, the other factor `F_h∉J_i`. Show the cofactor
   `U_i := ∏_{h∈Fin6, h≠i} F_h`
   also lies outside J_i: use primality of the **actual maximal** ideal J_i (Step 020/021) and finite-product prime nonmembership, or map its factors into the field `ZMod q` and show the product of their *nonzero* residues is nonzero.
3. In a commutative ring, if J is maximal and U∉J then the principal ideal (U) is comaximal with J. It is consequently comaximal with J²: **check** a Mathlib comaximal-power theorem, or prove an elementary Bézout identity. This is the genuinely new step; J being merely prime does **not** by itself give a two-power cancellation rule in arbitrary rings.
4. Use `U_i*F_i = (T:R)∈J_i²` and the comaximality of (U_i) and J_i² to deduce `F_i∈J_i²`. This is *saturation by a unit modulo J_i²*, not unrestricted cancellation in R.
5. Reverse the factor product with a checked \`Finset.prod_erase_mul\` identity in the actual source ring and a proof that i belongs to \`Finset.univ\`. Do not substitute a numerical q43 equality for a generic product theorem.

A completely elementary source-level route for Gate3: from maximality and U∉J, find a,b with `a*U+b=1` and b∈J. Squaring yields

```text
1 = U * (a²*U + 2*a*b) + b².
```

Thus 1 belongs to (U)+J². Multiplying the identity by F_i and using U*F_i∈J² proves F_i∈J². **Every witness and membership is to be kernel checked in Lean**; this identity is not permission to postulate an arbitrary Bézout pair.

If any gate fails because a Mathlib name does not exist, source-check before writing a custom lemma. If the statement is disproved under the current premises, exhibit a real counterexample and record Outcome C rather than inserting a new assumption quietly.

## Phase 0 — exact source and overlap inventory

Inspect:
- `DkMath.FLT.Seven.GTailCyclotomicTailDepthOne`: seven public theorem signatures, the scalar q² contraction iff and the finite excess-factor lemma;
- `GTailCyclotomicTailFactorProduct`: actual source factor product, inverse slot permutation and first-level incidence;
- `GTailCyclotomicSixRootInterpolation`: actual split scalar ideal and six-kernel product;
- `GTailCyclotomicSixRootOrbit` / `GTailCyclotomicPrimeAddress`: each packet-free maximal/prime kernel and zero-evaluation iff;
- `SevenRamifiedFusionOrientedCarrierValuationOwnership` and July 2026 U1.2 report **for comparison only**. It contains signed-depth-packet-indexed all-k cutoffs, which do not apply to bare natural F_i absent typed identification.
- Mathlib \`Ideal.IsMaximal\`, \`IsCoprime\`, \`Ideal.span_singleton\`, \`Ideal.IsPrime\`, product outside a prime ideal, \`Ideal.mul_mem_mul\`, ideal power, finite products and comaximality of powers. **Discover exact APIs via source/#check, not by presumed names.**

Write `source-inventory-025.md` with a proof gate checklist, the exact math premise needed for saturation, carrier distinction, old packet overlap, and a minimal import closure. Keep all new results in the actual existing degree-six R, without a new ring, generic ideal-adic valuation implementation, or a heavy facade.

## Phase 1 — generic comaximal square-saturation lemma

Suggested owner `DkMath/FLT/Seven/GTailCyclotomicTailDepthTwo.lean`, directly importing Step024 only (and targeted Mathlib if an API is missing).

Prove a modest generic reusable lemma, for any `CommRing A` and an **actually maximal** ideal `J : Ideal A`:

```text
(hJ : J.IsMaximal) (hU : U ∉ J)
(hProd : U*x ∈ J²) → x ∈ J².
```

A clean proof should:
- show `Ideal.span {U} ⊔ J = ⊤` from maximality and U∉J, with an exact API or actual ideal inclusion logic;
- prove comaximality of `Ideal.span {U}` and `J²`, either via a verified \`IsCoprime.pow_right\`-style API or by the explicit square of a Bézout identity;
- conclude from U*x∈J² that x∈J² by a checked ideal membership argument.

Ensure the theorem remains valid when U is a unit, when J is maximal but not principal, and when A has zero divisors (if an API requires \`IsDomain\`, either prove it for R only or state the true minimal generic hypothesis). Avoid a theorem \`U*x∈J² → x∈J²\` under **merely J.IsPrime**: that inference is unjustified.

Build this gate alone. **Do not proceed to the selected factor theorem before this proof kernel checks.**

## Phase 2 — actual selected cofactor is outside the chosen kernel

With the canonical Tail premises, for each i define or locally bind:

```text
J_i := K_(sixInverseSlot i)
U_i := ∏ h ∈ Finset.univ.erase i, gtailCyclotomicFactor c g h.
```

Prove:
- each h≠i gives F_h∉J_i from Step023’s unique-root incidence plus injectivity of the explicit sixInverseSlot involution;
- `U_i∉J_i` using the actual J_i.IsPrime (or the nonzero **field product** of all five actual RingHom values). It is insufficient to note that *some* other factor is outside J_i; establish nonmembership of **all five** or directly of the cofactor.
- `U_i * F_i = (T:R)` via the actual Step023 product theorem and correct multiplication order in commutative R.

Do not assert equality of principal ideals (F_i)=J_i or that F_i has no other rational prime factors.

## Phase 3 — recover the missing reverse implication and iff

Using q²|T:
- construct `(T:R)∈J_i²` from an actual scalar q² multiple and q∈J_i. A proof from the existing `seventhRootKernel_comap_intCast` or \`map_natCast\` is appropriate; no ideal equality (q)*J=(q²) is claimed.
- rewrite the scalar product as U_i*F_i;
- apply the Phase1 maximal-ideal square-saturation lemma with `U_i∉J_i`;
- prove a public \`gtailCyclotomicFactor_mem_square_of_sq_dvd_GTail\`-style theorem.
- reuse Step024’s `GTail_mem_scalar_mul_kernel_of_factor_mem_square` plus `natCast_mem_scalar_mul_sixRootKernel_iff` (or an existing forward theorem without the negative guard) for reverse direction to establish

```text
F_i(c,g) ∈ J_i² ↔ q²∣T.
```

This is the **mandatory exact second-level gate**; a stand-alone q43 check is not sufficient.

Optionally give a compact bounded-depth classification:
- first-power membership always holds on this canonical Tail branch;
- second-power membership is equivalent to q²|T;
- if ¬q²|T, depth-one is exactly Step024;
- if q²|T, depth at least two is **proved**, while membership in J³ is **unresolved**, not automatically excluded.

Do not jump to `∀k, F_i∈J_i^k ↔ q^k|T` without a separately verified general saturation and scalar-contraction induction.

## Phase 4 — strong nonvacuous regressions

**q43,c9,g4, canonical r11:** T=14491387, q|T but q²∤T, so every F_i is in its unique K, **not** in K² (Step024). The new iff must recover the negative cases without using a finite-field \`decide\` on ideal powers.

**q43,c9,g1165, canonical r11:** report-024 checked

```text
T=2638461449052811747,
43∤9, 43∤1165, 43|T, 43²|T,
gtailSevenTailRatio 43 9 1165 = 11.
```

Use the **generic new reverse theorem** to prove for **all** i:Fin6

```text
gtailCyclotomicFactor 9 1165 i ∈
  (K_(sixInverseSlot i))².
```

Check all five other K slots still exclude each factor at first power; no j≠assigned has membership just because T has a square prime divisor. This is the crucial improvement over Step024’s “guard fails, multiplicity unknown” sample.

Boundaries: g=0 and c=0 remain valid for Step023 unconditional product but fail the canonical q-unit contract. q13 Gap has no q|T and no nontrivial root packet. Characteristic q7 is a separate old ramified ζ↦1 address, not an instance of the six-root split theorem. q43,a5,b8 is **not** an exact Fermat7 solution.

Optional: if meaningful, provide a specific non-vacuous scalar q² element in K_i² independent of the Tail factor, but it is not a substitute for the actual F_i membership test.

## Phase 5 — output, build and audit discipline

Required:
- `DkMath/FLT/Seven/GTailCyclotomicTailDepthTwo.lean`;
- `DkMathTest/FLT/Seven/GTailCyclotomicTailDepthTwo.lean`;
- `source-inventory-025.md`, `report-025.md`;
- truthful **post-024** `ROADMAP.md` addendum without changing historical Step024 records.

Implement/build stages sequentially in the local repo with process-local `LEAN_NUM_THREADS=2`:
1. generic maximal square-saturation source gate;
2. selected cofactor and product identity gate;
3. generic q² reverse and iff gate;
4. q43 two-case regressions and Step024/023 replay;
5. public \`#print axioms\`, import graph/neutral→FLT, forbidden-source-token and whitespace checks.

Log actual final exit codes and failed repairs. No new axiom, \`sorry\`, \`admit\`, \`unsafe\`, \`False.elim\`, heavy full repository test, unrelated Legendre edits, public facade, PR or branch merge.

**Outcome B expected** for the exact bounded second-level iff, with genuinely new positive depth-two calibration, no FLT7 descent. **Outcome C/partial** if maximal-ideal square saturation or the generic reverse implication fails with the available hypotheses; give the smallest verified obstacle or counterexample and preserve stronger compiled partial results. **Outcome A** only for a separately source-compared, noncircular new restriction on hypothetical positive primitive FLT7 solutions, not an equivalence between two presentations of q-local multiplicity.

**STOP after Step025.** Do not infer all-k valuations, exact higher multiplicities, cyclotomic/Eisenstein ideal map, signed-packet identification, ideal class/unit-power extraction, primitive smaller Fermat tuple or unconditional FLT7 closure.
