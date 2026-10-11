# Instruction 029 — third-power cyclotomic ideal address from scalar GTail cubic support

Date: 2026-10-10
Target branch: `feature/GTail-SelectiveGap-FLT7-261009-v0`
Working directory: `lean/dk_math`
Prerequisites: `review-028.md`, `report-028.md` and `source-inventory-028.md`.
**Scope: Step 029 only.** Prove an actual **third-power** membership iff for the six selected natural GTail cyclotomic factors by combining the already checked six-prime scalar splitting with integer-coordinate scalar cancellation and the already checked selected cofactor. Use Step028's 43³ scalar example as a nonvacuous positive K³ receiver. No unsupported K⁴ cutoff, broad all-k prime valuation, q-adic completion, signed packet invention, or FLT7 descent.

## Target and fixed existing carriers

Work in the real preexisting sixth-degree cyclotomic integral ring

`R := SevenCyclotomicDegreeSixInt.Ring`.

For prime q, a supplied nonzero nonidentity seventh root r:ZMod q with r⁷=1, and a slot j:Fin6, write

`K_j := sixRootKernel r hr0 hr7 hr1 j : Ideal R`.

Step021 proves each K_j maximal/prime and the six slots pairwise comaximal. Step022 proves

```text
∏ j : Fin 6, K_j = cyclotomicScalarIdeal q = Ideal.span {(q:R)}.
```

Step020 proves the integer contraction of K_j is (q) in ℤ; Step024 proves multiplication by a nonzero natural scalar q is injective on **the actual R**, using six signed integral coordinates.

For canonical natural Tail input c,g with q∤c,g and q|T:=GTail 7 1 g c, let r=(c+g)/c in ZMod q and

```text
F_i := gtailCyclotomicFactor c g i
slot_i := sixInverseSlot i
U_i := gtailCyclotomicCofactor c g i
```

Step023 proves F_i belongs to K_slot_i and no wrong slot, Step025 proves U_i∉K_slot_i and

```text
U_i * F_i = (T:R).
```

Step028 proves scalar 43³ divisibility at (q,c,g)=(43,9,32598) and verifies **only** the previous K² membership of each F_i. This is the precise missing third-power bridge.

**Mandatory desired public theorem** under the above actual canonical Tail q-unit/support hypotheses, for every i:Fin6:

```text
F_i(c,g) ∈ (K_slot_i)^3 ↔ q^3 ∣ GTail 7 1 g c.
```

This is a bounded *selected factor* theorem, not \`(F_i)=K_i\`, not a valuation function, not a theorem about every prime ideal in R, and not a Fermat7 obstruction.

## Phase 0 — exact-source proof feasibility inventory

Source-inspect before implementation:
- `GTailCyclotomicSixRootOrbit`: `sixRootKernel_sup_eq_top`, maximal/prime, integer contraction;
- `GTailCyclotomicSixRootInterpolation`: `prod_sixRootKernel_eq_scalarIdeal`, `cyclotomicScalarIdeal` and signed coordinates;
- `GTailCyclotomicTailDepthOne`: `cyclotomic_natCast_mul_injective` and the **scalar-only** membership theorem for (q)*K;
- `GTailCyclotomicTailDepthTwo`: `gtailCyclotomicCofactor_mul_factor`, `gtailCyclotomicCofactor_not_mem_selected`, `gtailCyclotomicFactor_mem_square_iff` and \`Ideal.IsMaximal.mul_mem_pow\`;
- `GTailCyclotomicTailFactorProduct`: inverse index permutation, old element product;
- `GTailCyclotomicTailSecondDigit`: scalar cubic support and q43 32598 regression;
- old signed-depth oriented valuation owner **only for input contract comparison**, not as a proof dependency.

Inspect real Mathlib signatures for `Ideal.IsCoprime`, finite-product comaximality, \`Ideal.pow\`, \`Ideal.mul\`, `inf_eq_mul_of_isCoprime`, `Ideal.mem_span_singleton_mul`, product/pow associativity and `Ideal.IsMaximal.mul_mem_pow`. Avoid invented API names.

Write `source-inventory-029.md` recording the exact proof routes, carriers, local import costs, missing intermediate lemmas and what distinguishes this bare natural Tail source from the old signed-depth packet valuation owner.

Suggested source `DkMath/FLT/Seven/GTailCyclotomicTailDepthThree.lean`, importing Step028 directly and only small existing Mathlib owners if needed. Retain all prior Lean files and facades unchanged.

## Phase 1 — other-five-prime complement to one slot

For the supplied root r and index j define

```text
J_j := ∏ h ∈ Finset.univ.erase j, K_h : Ideal R.
```

Prove, with genuine Finset membership/reindexing and Step021/022 APIs:

1. `K_j * J_j = cyclotomicScalarIdeal q` from the **actual** six-kernel product and \`Finset.prod_erase_mul\`; commutativity permits either order, but prove it.
2. `K_j ⊔ J_j = ⊤`, as each other K_h is comaximal with K_j. Check a finite-product IsCoprime lemma or prove induction over erased slots. This is **not** inferred from K_j≠J_j merely by maximality without checking J_j nonmembership.
3. Consequently `K_j^n ⊔ J_j = ⊤` for positive n, in particular n=2 and n=3. Check a power-of-comaximal-ideals API or prove a small Bézout-power lemma.
4. For n=2 and n=3, establish the actual ideal inf/product identity

```text
K_j^n ⊓ cyclotomicScalarIdeal q
  = K_j^n * J_j
  = cyclotomicScalarIdeal q * K_j^(n-1).
```

**Proposed reasoning to validate in Lean, not a permitted assumption:**
- `(q)=K_j*J_j ⊆ J_j`;
- `K_j^n ⊆ K_j` for n≥1;
- `K_j^n ⊓ J_j = K_j^n*J_j` due to the proved comaximality of K_j^n and J_j;
- hence `K_j^n ⊓ (q) = K_j^n ⊓ J_j = K_j^n*J_j`, because the product is itself contained in (q);
- regroup ideal powers using `K_j*J_j=(q)`.

This lemma is the **key new algebraic gate**. It must not be replaced by the false global claim `K_j^n=(q^n)` or `(q)*K_j=(q²)`. Those ideals are generally distinct.

Prefer a compact generic lemma for two comaximal ideals I,J satisfying I*J=(q), with **the minimal actual hypotheses**, but a direct n=2/n=3 proof in this exact R is acceptable if Mathlib APIs or proof budget warrant it. Keep a single source of truth for the complement ideal to avoid rewriting dependent root proof certificates repeatedly.

Build this gate by itself before entering scalar contraction.

## Phase 2 — scalar K² and K³ contraction, without a DVR hypothesis

For any natural scalar n and chosen K_j, prove:

```text
(n:R) ∈ K_j^2 ↔ q²∣n
(n:R) ∈ K_j^3 ↔ q³∣n.
```

**Correct proof of the forward direction at power 2:**
- K_j² membership implies K_j membership, so by Step020 integer contraction q|n.
- Then embedded n belongs to the scalar ideal (q) as well.
- Apply the **proved Phase1 n=2 intersection identity** to obtain `(n:R)∈(q)*K_j`.
- Step024's already proved scalar-only `natCast_mem_scalar_mul_sixRootKernel_iff` gives q²|n.

At power 3:
- K_j³ membership similarly gives q|n; write n=q*m in naturals (or ℤ with a correct positivity transport).
- Membership in `K_j³ ⊓ (q)` and Phase1's n=3 identity gives `(n:R)∈(q)*K_j²`.
- Using the **actual** \`Ideal.mem_span_singleton_mul\` or equivalent, produce a source-ring element y∈K_j² such that `(n:R)=(q:R)*y`.
- Since n=q*m as naturals, `(n:R)=(q:R)*(m:R)`. **Cancel q only in the actual torsionfree six-coordinate R** via the existing \`cyclotomic_natCast_mul_injective\` (q≠0 from prime). Thus `(m:R)∈K_j²`.
- Apply the just-proved scalar power-two iff: q²|m; combine with n=q*m to obtain q³|n.

**Reverse directions** follow from q∈K_j, \`Ideal.pow_mem_pow\` and ideal closure for scalar q² or q³ multiples. This does not require the original Tail input.

If it is simpler to prove the q-power scalar contraction simultaneously by a short induction over positive k, such a proved generic lemma is acceptable **as an internal helper**. Do not expose a public general exact valuation API or an all-k theorem about selected F_i unless separately reviewed; the main Step029 contract remains powers 2 and 3. No arbitrary \`IsDomain\` assumption is to be invented.

A q43 all-slot test should show scalar 43³ lies in each K_j³, whereas scalar 43² does **not** lie in any K_j³ (the latter follows from the generic iff). These are useful nonvacuous tests of the contraction boundary.

## Phase 3 — actual selected GTail factor iff at power three

Reuse the Step025 actual U_i product, its nonmembership `U_i∉K_slot_i` and K maximality.

For any prime q and canonical admissible c,g:

```text
F_i(c,g) ∈ K_slot_i^3
  ↔ U_i(c,g)*F_i(c,g) ∈ K_slot_i^3
  ↔ ((GTail 7 1 g c:ℕ):R) ∈ K_slot_i^3
  ↔ q³∣GTail 7 1 g c.
```

The implication from product membership to factor membership requires **maximal-ideal saturation at exponent 3**, using the actual `Ideal.IsMaximal.mul_mem_pow` with \`U_i∉K\`. The forward implication is merely ideal multiplication closure, not a claim that U_i is a unit in R.

Pair with Step023's first-power selected membership and Step025's **already proved** second-power iff. Record all three levels distinctly. Do not infer a fourth-power cutoff, or an actual integer-valued K-adic valuation, without a new fourth-level theorem.

This is the **mandatory public acceptance gate**. If Phase1/2 fails, retain checked partial results and report Outcome C/partial with the exact missing ideal-power/coordinate lemma. A q43 \`decide\` of scalar arithmetic cannot substitute for K³ membership proof.

## Phase 4 — decisive q43 regression and guards

Use the same canonical data (q,c)=(43,9):

| Natural gap g | Scalar support | Expected selected ideal-depth gate |
| --- | --- | --- |
| 4 | 43|T, 43²∤T | F_i∈K, F_i∉K², hence F_i∉K³ |
| 1165 | 43²|T, 43³∤T | F_i∈K², F_i∉K³ |
| 32598 | 43³|T, 43⁴∤T | F_i∈K³; **K⁴ exclusion UNPROVED** |

Check:
- q43 selected root r=11 unchanged at all gaps, all six inverse slots [0,3,4,1,2,5] unchanged;
- each F_i at g=32598 in **actual K_assigned³** using the new generic iff and Step028 scalar cubic support;
- each F_i at g=1165 **not** in actual K_assigned³ from the new generic iff and the already checked scalar 43³ failure;
- all wrong slots still exclude F_i at first power;
- the previously checked derivative28/cofactor28, new Hensel digit17 and scalar q⁴ failure remain consistent;
- scalar q³ in all K³; scalar q² excluded from K³, via the generic contraction.
- Do not assert that F_i at g=32598 is *exactly* K-adic depth 3: that would require F_i∉K⁴, not covered by this step.
- Numeric calibration tuples are not Fermat7 solutions; do not introduce a hypothetical Fermat packet.

**Boundary controls:** q=7 has no nontrivial seventh root in ZMod7, q13 Gap sample lacks q|Tail, c=0 or g=0 fail the unit assumptions, and the Step023 unconditional source element product remains valid regardless.

## Phase 5 — deliverables, logs and strict STOP

Required:
- `DkMath/FLT/Seven/GTailCyclotomicTailDepthThree.lean`;
- `DkMathTest/FLT/Seven/GTailCyclotomicTailDepthThree.lean`;
- `source-inventory-029.md`, `report-029.md`;
- truthful post-028 `ROADMAP.md` addendum. Keep earlier reports/reviews intact.

Build sequential targeted production/test, then Step028/027 direct regressions with process-local `LEAN_NUM_THREADS=2`. Log every gate's exact theorem signatures, proof dependencies, failures and fixes, command/exit/warning, checked #print axioms for all new public declarations and direct import-cycle/neutral→FLT/forbidden-token audit. Do not expand all DkMathTest, use global proof-resource settings, import broad facades, edit old signed-depth owners or touch unrelated projects.

**Outcome B expected** for a new scalar K³ contraction and actual six-factor selected K³ iff with explicit q43 positive/negative cases. This is not a newly discovered general Dedekind/DVR theorem nor Fermat7 descent.
**Outcome C/partial** for any missing power/comaximality equality or invalid scalar cancellation; preserve source-checked lower-power results, identify the missing lemma and counterexample if any.
**Outcome A** only for a genuinely new, noncircular restriction on hypothetical primitive positive FLT7 solutions, source-compared to old signed packet owners. Classical ideal splitting and digit lifting remain Outcome B.

**STOP after Step029.** No unconditional all-k factor valuations, K⁴ exclusion, p-adic completion, Eisenstein→cyclotomic integral ring map, signed-depth packet creation, ideal class/unit-power extraction, primitive next Fermat tuple or unconditional FLT7 closure.
