# Instruction 030 — exact selected cyclotomic depth three via the fourth-power firewall

Date: 2026-10-10
Target branch: `feature/GTail-SelectiveGap-FLT7-261009-v0`
Working directory: `lean/dk_math`
Prerequisites: `review-029.md`, `report-029.md` and `source-inventory-029.md`.
**Scope: Step 030 only.** Add the bounded **fourth-power** source ideal receiver necessary to complete an *exact depth-three* statement for the previously checked q43,c9,g32598 input. Reuse Step029’s six-kernel complement, scalar cube contraction and selected factor cofactor. No general all-k ideal valuation, infinite Hensel lifting, FLT7 descent or new signed packet.

## Rationale, exact existing contracts

Steps 020–029 proved for the **actual existing** degree-six integral carrier

`R := SevenCyclotomicDegreeSixInt.Ring`

and each supplied nontrivial seventh root r in ZMod q (q prime):

```text
K_j := sixRootKernel r hr0 hr7 hr1 j : Ideal R
J_j := sixRootKernelComplement r hr0 hr7 hr1 j
K_j * J_j = cyclotomicScalarIdeal q = (q:R)
K_j ⊔ J_j = ⊤
(n:R) ∈ K_j³ ↔ q³ ∣ n                   -- any natural scalar n
K_j³ ⊓ (q:R) = (q:R)*K_j²
```

The source also has:
- `cyclotomic_natCast_mul_injective` from six signed coordinates (nonzero natural scalar q);
- `Ideal.IsMaximal.mul_mem_pow` as a real Mathlib maximal ideal power saturation API;
- the **actual** selected cofactor U_i with `U_i∉K_assigned` and `U_i*F_i=(GTail:R)`;
- `gtailCyclotomicFactor_mem_cube_iff` under prime q, q∤c,g and q|GTail;
- q43,c9,g32598 with `43³|GTail` but `43⁴∤GTail`, tested in Step028/029.

The missing implication is NOT `K⁴=(q⁴)` (false globally); rather, the new scalar-specific contraction needed to convert numerical scalar q⁴ nondivisibility into nonmembership of the actual factor in its fourth prime power.

**Primary target**, with exactly the canonical Tail q-unit/support hypotheses and each i:Fin6:

```text
gtailCyclotomicFactor c g i ∈
  sixRootKernel (gtailSevenTailRatio q c g)
    (gtailSevenTailRatio_ne_zero hc hT)
    (gtailSevenTailRatio_pow_seven hc hT)
    (gtailSevenTailRatio_ne_one hc hg)
    (sixInverseSlot i) ^ 4
  ↔ q ^ 4 ∣ GTail 7 1 g c.
```

**Bounded application**, using Step029 cube iff:
`q³|T ∧ ¬q⁴|T → F_i∈K_assigned³ ∧ F_i∉K_assigned⁴`.
Do not define an unproved general integer-valued K-valuation or state arbitrary all-k factor membership.

## Phase 0 — owner/API inventory

Read exact declarations/proof routes in:
- `DkMath.FLT.Seven.GTailCyclotomicTailDepthThree`: complement J_j, KJ=(q), K+J=top, \`sixRootKernel_pow_sup_complement\`, private \`pow_inf_mul_of_comaximal\`, scalar cube iff and selected factor cube iff;
- `GTailCyclotomicSixRootOrbit` / `GTailCyclotomicSixRootInterpolation`: genuine six root slots and integer scalar ideal;
- `GTailCyclotomicTailDepthOne`: multiplication-by-q injectivity via actual signed coordinates;
- `GTailCyclotomicTailDepthTwo`: genuine source cofactor product/nonmembership and maximal ideal power saturation;
- `GTailCyclotomicTailSecondDigit`: previously checked q³ scalar support and q⁴ nondivisibility as **numeric** regression;
- original `DkMath.Lib.NumberTheory.PolynomialHenselDigit` only to verify that finite digit lifting is already available, not to reimplement it;
- existing signed-packet valuation owner only for distinct input-contract comparison, never as a hidden inference;
- current Mathlib \`Ideal.mul_eq_inf_of_isCoprime\`, \`Ideal.pow_sup_eq_top\`, \`Ideal.mem_span_singleton_mul\`, \`Ideal.pow_le_self\`, \`Ideal.IsMaximal.mul_mem_pow\`, \`Ideal.pow_mem_pow\`.

Write `source-inventory-030.md` with exact contracts, proof gates, minimal imports and explicit restrictions. Suggested source owner:
`DkMath/FLT/Seven/GTailCyclotomicTailDepthFour.lean`,
directly importing Step029 only; no broad façade or source owner refactoring.

**Private helper note:** Step029's general \`pow_inf_mul_of_comaximal\` is \`private\`; do not refer to it as a public imported identifier or guess its compiler-generated name. It is acceptable to prove a small fourth-power-specific variant in the new owner, citing the exact previously checked argument. Avoid editing the Step029 owner merely to promote a helper unless there is a demonstrably necessary and approved source dependency reason.

## Phase 1 — actual fourth-power intersection with scalar principal ideal

Under supplied r, j:Fin6 define K=K_j, J=J_j and prove the precise equality

```text
K^4 ⊓ cyclotomicScalarIdeal q
   = cyclotomicScalarIdeal q * K^3.
```

A short source-checked route:
1. `K*J=(q)` from Step029's public theorem.
2. `K^4⊔J=⊤` from Step029's public theorem, so \`K^4⊓J=K^4*J\` by the real comaximal ideal inf/mul API.
3. \`K*J≤J\` and \`K^4≤K\` give both inclusions needed for
   \`K^4⊓(K*J)=K^4*J\`.
4. Reassociate commutative ideal multiplication and powers:
   \`K^4*J=(K*J)*K³=(q)*K³\`.

The equality must be proved **in the existing R** and without an \`IsDomain\`, \`IsDedekind\`, \`IsPrincipal\` or \`IsDVR\` premise. Do not assert \`K^4=(q^4)\`, nor \`(q)*K³=(q⁴)\`: both are generally false as whole ideals in the degree-six split setting.

The actual Step029 private general lemma is a valid mathematical proof pattern but cannot simply be imported by name. A small generic \`CommRing\` helper local to Step030, instantiated at n=4, is fine if that makes the Lean proof shorter. **STOP at an honest missing-lemma report if the comaximality/power equality cannot be kernel checked.**

## Phase 2 — integer scalar fourth-power contraction

Prove the uniform **actual natural-scalar** iff:

```text
(n:R) ∈ K_j^4 ↔ q^4∣n
```

for any n:ℕ, prime q with supplied nontrivial seventh root r and any j:Fin6.

Forward route, maintaining actual carriers and type correctness:
- \`K_j^4≤K_j\` and actual RingHom evaluation of the embedded natural n give q|n. Hence write \`n=q*m\` with m:ℕ, and prove \`(n:R)∈(q:R)\` with a legitimate scalar witness.
- From \`n∈K_j⁴∩(q)\` and Phase1's checked intersection obtain \`(n:R)∈(q:R)*K_j³\`.
- From \`Ideal.mem_span_singleton_mul\`, produce an actual source ring y∈K_j³ with \`(n:R)=(q:R)*y\`. Using n=q*m, obtain \`(n:R)=(q:R)*(m:R)\`.
- Invoke **Step024** \`cyclotomic_natCast_mul_injective q hq0\` (actual signed-coordinate proof) to conclude y=(m:R). Do NOT cancel q in ZMod q or assert cancellation in an arbitrary CommRing.
- Apply Step029's **public** \`natCast_mem_sixRootKernel_cube_iff\` to y and derive q³|m, hence q⁴|n.

Reverse route:
- Actual embedded q∈K_j from the root-indexed RingHom and \`ZMod.natCast_self\`.
- Thus q⁴∈K_j⁴ using \`Ideal.pow_mem_pow\`; any natural q⁴ multiple lies in K_j⁴ via ideal closure.

It is acceptable to factor out the already proven Step029 private \`scalar_support_of_kernel_mem\` proof **as a small local/private helper** if required; it is not a publicly accessible API. Prefer a direct use of \`mem_sixRootKernel_iff\` and \`map_natCast\` over more generic infrastructure.

Mandatory sanity checks for q43 across all six ideals:
`((43^4:ℕ):R)∈K_j^4`,
`((43^3:ℕ):R)∉K_j^4`,
and (0:R)∈K_j⁴.
No numerical \`decide\` on arbitrary ideal membership substitutes for the universal theorem.

## Phase 3 — actual Tail factor fourth-power iff

For canonical Tail conditions q prime, q∤c,g and q|T:
- `U_i∉K_assigned` and `U_i*F_i=(T:R)` are Step025 checked theorems.
- K_assigned maximality is Step021 checked.
- Invoke \`Ideal.IsMaximal.mul_mem_pow\` at **n=4**, and actual ideal product membership in the other direction to prove

`F_i∈K_assigned⁴ ↔ (T:R)∈K_assigned⁴`.

- Convert embedded scalar T via Phase2's actual scalar iff to obtain the target \`F_i∈K_assigned⁴ ↔ q⁴|T\`.

If available, add a narrowly scoped public **exact depth three** corollary:

```text
(hT3 : q³∣T) (hT4 : ¬q⁴∣T) :
  F_i∈K_assigned³ ∧ F_i∉K_assigned⁴
```

using Step029's already proved factor cube iff and the new factor fourth iff. This is an exact **bounded membership cutoff**, not a valuation function on all ring elements.

Do not infer individual factors generate the corresponding prime ideals, extract ideal classes, or claim a descent. It is essential that all six factors use the checked inverse-index permutation [0,3,4,1,2,5], not naive matching i=j.

## Phase 4 — numerical and non-applicable guards

Use q43,c9 and the same three gaps:
- g=4 has q|T but q²∤T; each selected F_i∉K⁴ (and F_i∈K, F_i∉K²) by generic theorems.
- g=1165 has q²|T but q³∤T; F_i∈K², F_i∉K³ and F_i∉K⁴.
- g=32598 has q³|T, q⁴∤T; **each** F_i∈K³ and F_i∉K⁴ by the newly proved universal criterion, giving the first genuinely checked \`K³ \\ K⁴\` calibration.
- all three retain root ratio 11, cofactor/derivative residue 28, inverse permutation and wrong-slot first-level exclusion;
- scalar 43⁴ in each K⁴ and scalar 43³ outside K⁴, via the generic scalar contraction.
- Step028's Hensel-digit27→17 calibration stays a **scalar** source, not a proof of ideal membership in itself.
- q7 nonidentity seventh-root exception, q13 Gap-only absence of q|Tail, g=0/c=0 unit-guard failure, and universal Step023 source element factorization should remain correctly separated. The numeric tuple a=5,b=8,c=9 is not an exact Fermat7 solution.

Do not calculate or claim a third Hensel correction, or K⁵ membership, to obscure the precise bounded goal. No new Fermat hypothesis is needed for the fourth-power theorem.

## Phase 5 — required artifacts and STOP

Required:
- `DkMath/FLT/Seven/GTailCyclotomicTailDepthFour.lean`;
- `DkMathTest/FLT/Seven/GTailCyclotomicTailDepthFour.lean`;
- `source-inventory-030.md`, `report-030.md`;
- a truthful **post-029** append to `ROADMAP.md`, preserving historical checkpoints.

Build sequential focused new production/test and Step029/028 direct test regressions with process-local `LEAN_NUM_THREADS=2`. Report all final exit codes, first failing proof gates/repairs, all new theorem signatures and \`#print axioms\` outputs, actual import DAG and neutral→FLT audit, forbidden-token scan, whitespace/style and numerical regressions. No all-suite clean rebuild, extra global \`set_option\` or proof resource-limit workarounds, editing of previous owners, public façades, signed-depth packet definitions, PR or merge.

**Outcome B expected** for genuine scalar K⁴ contraction plus actual six-factor K⁴ iff, yielding a checked exact third ideal-depth example. This is classical split-prime ideal arithmetic in a concrete integral carrier, not a new unconditional FLT7 restriction.
**Outcome C/partial** if the fourth-power intersection or scalar cancellation requires a missing valid premise or an unsupported API: report the exact counterexample or Lean type/proof obligation, preserving only established weaker endpoints.
**Outcome A** only for a separately source-compared noncircular restriction on a hypothetical primitive positive Fermat7 counterexample; none is inferred from bounded ideal depth or Hensel correction.

**STOP after Step030.** In particular, do not automatically proceed to K⁵ or a general all-k valuation hierarchy. After this bounded exact-depth-three checkpoint, recommend a distinct frontier reassessment: how (if at all) the Eisenstein Q² / focused GTail product and the degree-six cyclotomic prime-root addresses can be connected **with an actual source-typed arithmetic contract**, rather than silently assuming an Eisenstein→cyclotomic ring hom or a signed quotient-depth packet. No integral carrier transfer, class/unit extraction, primitive next Fermat tuple or unconditional FLT7 descent is authorized in this step.
