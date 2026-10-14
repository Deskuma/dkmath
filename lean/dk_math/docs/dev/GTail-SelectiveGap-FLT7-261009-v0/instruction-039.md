# Instruction 039 — focused Fermat-defect q² stability and non-Fermat Gap/Tail square countermodels

Date: 2026-10-11
Target branch: `feature/GTail-SelectiveGap-FLT7-261009-v0`
Working directory: `lean/dk_math`
Prerequisites: `review-038.md`, `report-038.md`, `source-inventory-038.md` and `frontier-038.md`.

**Scope: Step 039 only.** After the total conditional Gap/Tail route is checked, stop accumulating local ideal powers and ask a *different* rigorous question: **does that square routing really need the exact Fermat7Equation, or does it already follow from the weaker local condition that its global integer defect is divisible by q²?** Prove the true defect-sensitive branch theorem without secretly assuming hEq, and exhibit **actual positive primitive additive-focused NON-Fermat** witnesses of both square branches. Record why even this strengthened local information cannot reconstruct Step032's exact global balance or the old signed descent provider.

This is a substantive **necessity vs sufficiency / defect-stability** theorem, expected Outcome B. Not a proposed FLT7 contradiction, not a generic all-k defect/valuation formalism, and not permission to create a signed packet, rank-12 number field or new primitive solution.

## Phase 0 — exact-source proof overlap and type ledger

Read and cite the actual Lean signatures:
- `DkMath.FLT.Seven.GTailBridge.gtail_seven_defect` over arbitrary CommRing, with focus only:
  `g*T = 7ab(a+b)Q² + (a⁷+b⁷−c⁷)`;
- `DkMath.FLT.Seven.GTailGlobalBalanceFirewall.fermat7Equation_iff_focused_scalar_balance`: under focus, **the exact ZERO defect is equivalent to hEq**;
- `DkMath.FLT.Seven.GTailPrimeAllocationAudit` (Step010): \`not_prime_dvd_coordinate_product_of_quadratic\`, \`not_prime_dvd_endpoint_of_quadratic\` (**requires hEq**), \`prime_square_focused_allocation\` (**requires hEq**), and the separate head exclusion \`not_prime_dvd_gtail_seven_of_gap\` in neutral Lib;
- `DkMath.FLT.Seven.GTailFocusedPrimeRoute` (Step038): \`gap_ratio_eq_one\`, \`focused_prime_route\` and the hEq-conditional Tail receiver;
- `DkMath.FLT.Seven.GTailFocusedNormCyclotomicDepthBridge` and Step037 generic C receiver: note exactly which gates require a scalar budget, actual Tail support and q-unit inputs, and which do **not** need hEq;
- `DkMath.Lib.Cosmic.GTailSeven`: full semiring shell and \`add_pow_seven_eq_gap_add_interior\`;
- exact real Mathlib/Lean \`Int.natCast_dvd_natCast\`, \`exact_mod_cast\`, \`dvd_add\`, \`dvd_sub\`, \`Nat.Coprime\` and prime-square product cancellation APIs. \`Nat.Coprime.pow_left\` / \`Nat.Coprime.dvd_of_dvd_mul_left\` are **candidate names only** until #check/source confirms them. Check natural-to-integer casts before using any of these.

Core types:

```text
Q(a,b) : ℕ := a²+a*b+b²
T(c,g) : ℕ := GTail 7 1 g c

Δ(a,b,c) : ℤ := (a:ℤ)^7+(b:ℤ)^7−(c:ℤ)^7.
```

**Do not represent Δ as a natural subtraction**: it can be negative, especially in the q13 Gap countermodel. Work in ℤ for Δ and transport natural divisibility only after verifying casts. Do not replace \`q²∣Δ\` with Δ=0.

Create `source-inventory-039.md` with a source/target table for hEq, Δ=0, q|Q, q²|Δ, q²|g*T, Gap square, Tail square, valuation *equality*, canonical ratio and C receiver; identify the precise assumptions and which implications reverse. Suggested owner:
`DkMath/FLT/Seven/GTailFocusedDefectSquareFirewall.lean`,
direct import Step038 and the narrow actual \`GTailBridge\` module **only if its declaration is not already reachable**. Test:
`DkMathTest/FLT/Seven/GTailFocusedDefectSquareFirewall.lean`.

No edits to Step010–038, old signed owners, neutral Lib or facades.

## Gate 1 — typed integral defect equality and q² transport (mandatory)

Define a short named integer defect `focusedFermatDefect (a b c:ℕ):ℤ` as above, and prove:

```text
(hfocus : a+b=c+g) :
focusedFermatDefect a b c =
 (g:ℤ)*((T(c,g):ℕ):ℤ) -
 7*(a:ℤ)*(b:ℤ)*((a+b:ℕ):ℤ)*((Q(a,b):ℕ):ℤ)^2.
```

**Reuse** \`gtail_seven_defect\` and accurate casts/ring simplification. Do not re-prove the degree-seven power identity.

Then, for q:ℕ with `hQ:q|Q` (primality **not** essential to this algebra) and hfocus, prove

```text
(q:ℤ)^2 ∣ focusedFermatDefect a b c
   ↔ (q:ℤ)^2 ∣ (g:ℤ)*((T(c,g):ℕ):ℤ).
```

Reason: q|Q already forces q²|Q². The integer defect differs from g*T by a scalar multiple of Q². Both directions use actual \`dvd_add\` / \`dvd_sub\` and the checked equality, **not** hEq and **not** “q is invertible mod q².” Optionally add the equivalent **natural** consequence

```text
(q:ℤ)^2 ∣ Δ → q² ∣ g*T(c,g)
```

with checked \`Int\`↔\`Nat\` divisibility conversion. A q²-only claim is enough; no arbitrary prime-power/general valuation API in this step.

**Critical observation:** the new numerical controls below have Δ ≠ 0 **and** q²|Δ. Thus a square allocation theorem derived solely from q²|Δ cannot be treated as a new Fermat impossibility.

## Gate 2 — endpoint q-unit from *weaker defect support* (valuable strong gate)

The old Step010 endpoint theorem \`not_prime_dvd_endpoint_of_quadratic\` assumes **hEq**. A useful **new** weakening is:

```text
hq : Nat.Prime q
hcop : Nat.Coprime a b
hQ : q ∣ Q(a,b)
hΔ1 : (q:ℤ) ∣ focusedFermatDefect a b c
--------------------------------------
¬ q ∣ c.
```

Additive focus is actually not needed for this endpoint-only argument if proved through the **ordinary seventh-power sum identity**; omit it if the Lean proof is clean.

Suggested elementary proof:
1. From `hcop,hQ` get q∤a+b by the *existing neutral* quadratic coprimality theorem (source-check its exact statement).
2. Suppose q|c. The actual integer defect q|Δ and q|c imply q|(a⁷+b⁷) in ℤ; convert to natural divisibility carefully.
3. Existing \`add_pow_seven_eq_gap_add_interior\` says \`(a+b)^7=(a^7+b^7)+7ab(a+b)Q²\`, so q|(a+b)^7 from q|Q and q|(a⁷+b⁷).
4. Primality gives q|(a+b), contradicting Step1.

This is an **actual weakening of the endpoint hEq premise**, a legitimate noncircular algebraic helper. It does not show hEq or Δ=0.

If the endpoint without hEq is hard to elaborate, a theorem with hfocus and `q∤c` explicitly supplied is an acceptable **minimal square-route intermediate**, but **report the endpoint lemma as incomplete**. Do not silently call the old hEq-requiring endpoint theorem in a supposedly defect-only proof.

## Gate 3 — Gap/Tail *square routing* under q²|Δ but WITHOUT hEq (mandatory)

The main scientific gate:

```text
hq : Nat.Prime q
hq7 : q ≠ 7
hcop : Nat.Coprime a b
hQ : q ∣ Q(a,b)
hfocus : a+b=c+g
hΔ2 : (q:ℤ)^2 ∣ focusedFermatDefect a b c
[if Gate2 not available: hc : ¬ q ∣ c]
--------------------------------------
(q²∣g ∧ ¬q∣T(c,g) ∧ gtailSevenTailRatio q c g=1)
   ∨
(q²∣T(c,g) ∧ ¬q∣g).
```

**No hEq, no positivity, and no initial q|T** should be needed for the mathematical statement once the endpoint guard is proved. If positivity is only needed for an existing library lemma because of zero handling, inspect and isolate that true requirement rather than adding hEq.

Proof route:
- Gate1 q²|g*T from q²|Δ and q|Q; Gate2 q∤c.
- Split on q|g.
  - If q|g, apply the **existing neutral head-exclusion theorem** \`not_prime_dvd_gtail_seven_of_gap\`, requiring q prime, q≠7, q|g and q∤c, to get q∤T. From q²|g*T and q∤T prove q²|g by prime-power coprimality/cancellation. By Step038's actual `gap_ratio_eq_one`, the canonical ratio is exactly 1.
  - If q∤g, prove q²|T from q²|g*T by prime-square coprime cancellation. This is the **Tail** alternative.
- Use actual Mathlib coprime/prime-power lemmas or prove a tiny local helper for exponent **two only**. Check the exact APIs. Do **not** invoke Step010 \`prime_square_focused_allocation\`: it requires hEq and would make the new theorem circular.
- The two branches need not have equal scalar valuation budgets `v_q(g)+v_q(T)=2v_q(Q)`; q²|Δ alone gives a divisibility lower bound but not an **equality of exponents** in general.

**Acceptance discriminator:** source-grep/proof dependency audit must demonstrate that the new square-route proof DOES NOT consume \`Fermat7Equation\`, \`CounterexamplePack\`, Step038's hEq-dependent \`focused_prime_route\`, or any unconditional FLT7 result. The source can import those owners for other endpoints; the core proof must remain defect-only.

Gate3 is most valuable when Gate2's no-hEq q∤c is verified. If not, complete honest explicit-hc Gate3 and classify the missing automatic endpoint separately.

## Gate 4 — **two** strongly focused positive primitive NON-Fermat controls

The following tuples are **independently arithmetically calculated proposals** and **MUST** be rechecked in Lean. They are not Fermat7 solutions and do not furnish a global descent.

**Tail countermodel (existing Step032)**:
```text
q=43
(a,b,c,g)=(1166,1857,1858,1165)
a+b=c+g=3023; gcd(a,b)=1; 0<g<a,b<c<a+b.
Q=6,973,267;  v43(Q)=1
T=1,914,732,507,483,487,090,603; v43(T)=2
v43(g)=0
Δ=a⁷+b⁷−c⁷=2,642,627,963,860,178,152,897  [positive]
v43(Δ)=2; 43²|Δ; 43³∤Δ; Δ≠0.
43²|T, 43∤g; global scalar balance FAILS; ¬hEq.
```

**Gap countermodel (new candidate)**:
```text
q=13
(a,b,c,g)=(196,211,238,169)
a+b=c+g=407; gcd(a,b)=1; 0<g<a,b<c<a+b.
Q=124,293; v13(Q)=1
T=10,690,523,583,988,879; v13(T)=0
v13(g)=2
Δ=a⁷+b⁷−c⁷ [NEGATIVE], Δ≠0
v13(Δ)=2; 13²|Δ in ℤ; 13³∤Δ.
13²|g, 13∤T, c=238 unit mod13, canonical ratio=1.
global scalar balance FAILS; ¬hEq.
```

Avoid making up positive Δ for the second tuple or casting its subtraction to ℕ. For Δ in ℤ, \`Int.emod\` or divisibility of negative integers must be checked honestly.

For **both** tuples kernel-check:
- complete additive focus and the strict positive primitive coordinate geometry;
- q-prime,q≠7,q|Q, q²|Δ, q³∤Δ, Δ≠0;
- q² square route with its side-unit exclusion, correct canonical ratio on Gap;
- \`¬ Fermat7Equation\` and \`¬ exact scalar balance\` using Gate1/Step032, not a fictional hEq input;
- where inexpensive, \`padicValNat q g + padicValNat q T = 2*padicValNat q Q\` happens to hold **numerically for these two examples**, even though it is **not** a consequence of q²|Δ for arbitrary inputs. This stronger regression emphasizes that the Step010 *budget equality itself*, for a single selected prime, is compatible with non-Fermat data.
- q13 old small sample (14,29,30,13) has q|g but q²∤g; check it **does not** satisfy the new q²-defect premise. This protects against accidentally claiming raw q|g is enough.
- q43 small sample (5,8,9,4) is additive-focused but q²∤T and consequently **cannot** satisfy the defect q² hypothesis while q|Q; retain the Step032 correction.

**Optional**: use the genuine Step037 **native Tail receiver** on the q43 Tail model and show the real source elements' bounded C powers; the q13 Gap model should NOT be routed into the Tail receiver with canonical ratio=1. No need to import/rebuild the full q43 grid.

## Gate 5 — the exact deficit and noncircularity firewall

Prove or test on true source statements:

```text
hfocus : a+b=c+g
focusedFermatDefect a b c = 0 ↔ Fermat7Equation a b c
```

(The exact Nat/Int cast and subtraction use the **actual** Fermat7Equation definition; this is a corollary of Step032's iff, or direct integer-cast arithmetic.) This is not a new FLT theorem.

Compare with **strictly weaker** `q²|Δ` and the two positive primitive non-Fermat tuples; do not infer Δ=0 from any finite power divisibility. The new square-route theorem must be explicitly described as *defect-stable local necessity*, not a claim that every hypothetical Fermat7 input is impossible.

Document why neither the **Gap** nor **Tail** branch from the new weaker theorem closes globally:
- Gap ratio=1 is compatible with q13²|g non-Fermat data;
- Tail native C kernel and its mixed M powers are compatible with q43²|T non-Fermat data;
- no equivalence between two source images in C follows;
- \`AwayDescentClosureProvider\` still needs actual nextX/Y/Z, nextPack, nextRoute, \`carrier_match\`, and signed packet fields remain independent.

If an extra hypothesis seems to derive an FLT contradiction, check whether it already encodes Δ=0/hEq or a forbidden unconditional closure theorem before classifying any Outcome A.

## Deliverables, gates, focused builds and stop

Required:
- `DkMath/FLT/Seven/GTailFocusedDefectSquareFirewall.lean`;
- `DkMathTest/FLT/Seven/GTailFocusedDefectSquareFirewall.lean`;
- `source-inventory-039.md` and `report-039.md`;
- truthful post-038 `ROADMAP.md` append preserving all Step032 correction and historical reports/reviews;
- optional `frontier-039.md` documenting the extra global information needed beyond q² defect, source ideal square support and signed-packet gaps.

Build sequential with process-local `LEAN_NUM_THREADS=2`:
1. literal signed Δ and existing `gtail_seven_defect` identity, and q²-divisibility transfer;
2. weaker q|Δ endpoint-unit theorem (or exactly scoped explicit-hc fallback);
3. defect-only q² Gap/Tail split **without hEq and without q|T** as initial premise;
4. true q13 Gap and q43 Tail non-Fermat controls, exact defect 2-depth;
5. source/test focused build, Step038/037 direct regressions, all public \`#print axioms\`, import DAG/neutral Lib→FLT, forbidden-token/unsafe/whitespace and final warning audit.

Log all actual compiler commands/exits/warnings, intermediate failed APIs/repairs, numeric certificates, source theorem signatures, and **positive vs negative Δ sign**. If the candidate numeric values are incorrect, correct them and explain in the report; never forge a Fermat tuple. Avoid full clean all-suite build, global proof resource overrides, new general K-adic/all-k valuations, edits to older owners, class/unit theory, signed-descent packet, PR/rebase/merge.

**Outcome B expected:** actual **hEq-free defect-q² local routing** with two real positive primitive focused non-Fermat models, and explicit explanation why Step038's conditional square split is insufficient by itself to prove global FLT7.
**Outcome C/partial:** inability to prove endpoint unit without hEq or a failed exact integer/natural cancellation API; preserve strongest checked gate and name its missing hypothesis. A wrong numerical candidate is not grounds to invent a proof.
**Outcome A:** only an independently proved, noncircular restriction on positive primitive FLT7 tuples beyond such defect-congruence algebra; not anticipated here.

**STOP after Step039.** No automatic q³/q⁴ defect hierarchy, new Gap receiver, all-prime grid/spectrum, exact common ideal valuation, signed packet, new primitive counterexample or unconditional FLT7 descent. After this **defect stability** demonstration, the next research decision should target either a genuinely new global restriction that distinguishes Δ=0 from finite nonzero defect, or an actual old-provider reconstruction theorem with its explicit signed/carrier requirements.
