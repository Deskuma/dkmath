# Instruction 040 — finite prime-support aggregation and Archimedean zero-certificate frontier for the signed Fermat7 defect

Date: 2026-10-11
Target branch: `feature/GTail-SelectiveGap-FLT7-261009-v0`
Working directory: `lean/dk_math`
Prerequisites: `review-039.md`, `report-039.md`, `source-inventory-039.md`, `frontier-039.md`.

**Scope: Step 040 only.** After proving that a **single** local q² condition and even the corresponding q-budget can hold for genuinely nonzero signed Fermat defects, stop extending local prime depths. Prove a **finite multi-prime aggregation** statement and make the exactly missing **Archimedean magnitude bound** explicit. Then compare the total prime-support modulus against the actual Q and real positive/negative non-Fermat controls. This is a **conditional global zero certificate and capacity audit**, not an unconditional FLT7 proof and NOT an assertion that all prime-square support or the required size bound follow from primitive Fermat data.

## Why a different research direction is needed

Step039 source-checked the signed defect

```lean
focusedFermatDefect (a b c:ℕ) : ℤ :=
  (a:ℤ)^7+(b:ℤ)^7-(c:ℤ)^7
```

and, under focus `a+b=c+g` and q|Q, proved `(q:ℤ)^2|Δ ↔ q²|g*T`. It then derived a non-Fermat, hEq-free square Gap/Tail dichotomy; the endpoint q-unit was obtained from even weaker q|Δ. Two positive primitive focused tuples realize the two branches with **nonzero** signed Δ having q-adic depth exactly two, and their selected-prime budget equalities hold despite Δ≠0. A third model satisfies q²|Δ but not budget equality. These are strong insufficiency witnesses.

Step032/039 already proves `focusedFermatDefect a b c=0 ↔ Fermat7Equation a b c`, **without focus**. The mathematically different question now is:

> Can enough *distinct* local congruences be aggregated into a large enough integer modulus, so that a separate bound on |Δ| forces Δ=0?

The precise elementary mechanism is \`M|Δ ∧ |Δ|<M ∧ M>0 → Δ=0\`. The important work is to expose **where M comes from**, **which selected primes are actually covered**, and **which unproved magnitude bound would be needed**. Never disguise that final bound as something Steps010–039 already provide. A finite-local-to-global theorem with an explicit magnitude hypothesis is **not** an independent FLT7 obstruction.

## Gate 0 — actual source / Mathlib / radical ownership inventory

Inspect exact declarations and the smallest viable imports:

- `GTailFocusedDefectSquareFirewall.focusedFermatDefect`, `focusedFermatDefect_zero_iff`, `defect_square_iff_product_nat` and `defect_square_prime_route`;
- `GTailGlobalBalanceFirewall.fermat7Equation_iff_focused_scalar_balance` and actual `GTailBridge.gtail_seven_defect`;
- `DkMath.ABC.Rad.rad` defined **already** as \`n.factorization.support.prod (fun p => p)\`, `rad_dvd_nonzero`, `mem_support_factorization_iff`. Inspect its imports and overall import cost. Do not duplicate a second *general radical library* inside FLT, or add a heavy ABC umbrella import to this deep FLT owner merely for notation. The existing \`DkMath.ABC.Rad\` file imports \`DkMath.Basic\`, Nat factorization and Mathlib.Tactic; a targeted import is allowed **only if** its focused cost/import direction is justified. A small **private** proof based directly on \`Nat.primeFactors Q\` with an optional compatibility equality to the ABC radical in tests/docs is preferred if it avoids a new broad dependency;
- Mathlib \`Nat.primeFactors\`, \`Nat.mem_primeFactors\`, \`Nat.prod_factorization_pow_eq_self\`, \`Finset.prod_pow\`, \`Finset.prod_dvd_prod_of_dvd\`, appropriate finite pairwise-coprime product divisibility, \`Nat.Coprime.pow_left\`, \`Int.natCast_dvd_natCast\`, \`Int.natAbs_dvd_natAbs\` or checked equivalent, and \`Int.natAbs_pos\`;
- the previously checked actual signed positive/negative Δ numerical controls in Step039;
- existing primitive/descent packet contracts **read-only** for scientific scope; do not import their old signed modules directly for a simple integer divisibility criterion.

Document \`source-inventory-040.md\`: types, the precise standard library APIs (actual #check/source, not guesses), existing radical owner, direct/indirect import impact, zero Q edge cases, actual prime support and which hypotheses are **extra** compared with Step039. The generated source owner is
`DkMath/FLT/Seven/GTailFocusedDefectGlobalCapacity.lean`
directly importing Step039, plus the smallest justified Mathlib factorization module if required, and tests in
`DkMathTest/FLT/Seven/GTailFocusedDefectGlobalCapacity.lean`.

## Gate 1 — finite square modulus from distinct prime supports

For an arbitrary **Finset ℕ** S with actual prime certificates
`hs : ∀ p∈S, Nat.Prime p`
define a local finite-support modulus, for example

```lean
def squarePrimeSupportModulus (S : Finset ℕ) : ℕ :=
  ∏ p ∈ S, p^2
```

Mathematical endpoints to kernel check:

1. `0<squarePrimeSupportModulus S`, including S=∅ (empty product = 1).
2. `squarePrimeSupportModulus S = (∏ p∈S,p)^2` using checked finite product power API.
3. If \`(p:ℤ)^2 ∣ Δ\` for every p∈S, **then**
   \`(squarePrimeSupportModulus S:ℤ) ∣ Δ\`, or equivalently
   \`squarePrimeSupportModulus S ∣ Int.natAbs Δ\`.
   This must be proved using *pairwise coprimality* of distinct **prime squares**. A raw lemma saying “every factor divides, therefore their product divides” without coprimality is mathematically false, e.g. 4|4 and 4|4 does not yield 16|4. An actual Finset has no duplicates, but each element's primality is still needed. Check Mathlib's exact pairwise-coprime product lemma; if no convenient owner, prove a small local finite induction using a source-checked coprimality-of-prod lemma, NOT a new class-group or general factorization engine.
4. Conversely, if the entire product divides Δ, each (p:ℤ)^2 for p∈S divides Δ by the factor property. Thus an optional \`↔\` certificate is reasonable if it compiles cheaply.

Keep this theorem about *any signed Δ:ℤ*, with no Fermat, focus, primitive or q-root assumptions. The source owns the finitely aggregated integer divisor, not a conclusion about selected \(C\) prime ideals or their powers.

**Strict logical distinction:** \`∀p∈S,p²|Δ\` is a new **collective premise**, NOT a theorem derived from Step039's one chosen q and not from the hEq-conditional Step038 routing without actually assuming hEq. Do not extend a selected-prime existence theorem into “all p|Q” by a quantifier mistake.

## Gate 2 — exact global zero threshold and nonzero converse

For any signed integer \`z:ℤ\` and strictly positive natural \`m\`, prove both **source-checkable** statements:

```lean
(m:ℤ) ∣ z → z.natAbs < m → z=0

(m:ℤ) ∣ z → z≠0 → m ≤ z.natAbs
```

These may already exist in Mathlib; prefer a verified existing theorem if so. Check the exact coercion/absolute-value assumptions, including negative z, instead of proving with a false inequality on z itself.

Combine with Gate1 to prove the reusable **finite prime support zero certificate**:

```lean
(hs : ∀p∈S, Nat.Prime p)
(hlocal : ∀p∈S, (p:ℤ)^2 ∣ focusedFermatDefect a b c)
(hsize : (focusedFermatDefect a b c).natAbs < squarePrimeSupportModulus S)
--------------------------------------
Fermat7Equation a b c
```

Use Step039's \`focusedFermatDefect_zero_iff\` for the last step. **The theorem must not assume hEq or Δ=0**, and hsize must remain **visible in its signature** as an explicit Archimedean obligation. It is acceptable to return \`Δ=0\` with a separate elementary iff to avoid making a new FLT owner part of generic numeric infrastructure.

Also derive the honest **nonzero necessary lower bound**:
if \`∀p∈S,p²|Δ\` and \`Δ≠0\`, then \`M_S≤|Δ|\`.

This is the mathematical **capacity firewall**: any future global proof based only on those primes and square congruences must additionally establish \`|Δ|<M_S\` (or some other genuinely new global argument). It is not a proof that **no other** proof path could work.

## Gate 3 — canonical full-prime support of Q and comparison to radical/Q²

Assume actual \`Q=a²+a*b+b² ≠0\`. Define

```lean
S_Q := Nat.primeFactors Q : Finset ℕ
M_Q := squarePrimeSupportModulus S_Q
```

and prove:

1. Every p∈S_Q is prime and divides Q (from the actual \`Nat.mem_primeFactors\` contract; Q≠0 is essential).
2. \`M_Q = (S_Q.prod id)^2\`.
3. \`S_Q.prod id ∣ Q\`, hence \`M_Q ∣ Q²\` and in particular \`M_Q ≤ Q²\` (Q>0). Use the existing `ABC.Rad.rad_dvd_nonzero` only if an intentional narrow import makes sense, or prove an equally short local lemma from Mathlib's \`factorization\` in the new module. Record the overlap rather than claiming the radical is a new DkMath object.
4. If a deliberate targeted import of `DkMath.ABC.Rad` is justified, add the exact bridge
   \`M_Q = DkMath.ABC.rad Q ^ 2\`. If import cost/owner boundaries are unfavorable, state the same **mathematical identification** in source-inventory without creating an avoidable production dependency. Do not invent an alias from a different mathematical definition without proving equality.

Connect Gate2 to **all actual prime-square support of Q**:

```lean
(hQ0 : Q ≠ 0)
(hsupport : ∀ p ∈ Nat.primeFactors Q,
                  (p:ℤ)^2 ∣ focusedFermatDefect a b c)
(hsize : (focusedFermatDefect a b c).natAbs <
         squarePrimeSupportModulus (Nat.primeFactors Q))
---------------------------------------------------------
Fermat7Equation a b c
```

Do NOT derive \`hsupport\` just from p|Q, nor \`hsize\` from positivity, coprimality or focus. In a hypothetical exact Fermat7 equation \`hsupport\` is trivially true because Δ=0; **that circular statement adds no new mathematical information**.

**Key capacity observation:** the full radical-based modulus is at most Q². Thus any argument using only this modulus and the direct zero threshold needs an independently proved \`|Δ|<M_Q≤Q²\`. Whether this can ever be established *uniformly* for meaningful non-Fermat data is a separate, unproved analytic/global question. Avoid calling Q² a proven lower bound for |Δ| or claiming the inequality is always impossible.

## Gate 4 — real positive and negative signed controls, coverage vs size distinguished

Retest the Step039 true **non-Fermat** tuples:

**Tail q43:**
```text
(a,b,c,g)=(1166,1857,1858,1165)
Q=6,973,267 = 7·43·23167   (all distinct primes)
S_Q={7,43,23167}
M_Q=rad(Q)^2=Q²=48,626,452,653,289
|Δ|=2,642,627,963,860,178,152,897
|Δ| > M_Q > 0
43²|Δ; 7²∤Δ; 23167²∤Δ.
```

**Gap q13:**
```text
(a,b,c,g)=(196,211,238,169)
Q=124,293 = 3·13·3187   (all distinct primes)
S_Q={3,13,3187}
M_Q=rad(Q)^2=Q²=15,448,749,849
|Δ|=13,523,337,259,569,605
|Δ| > M_Q > 0
13²|Δ; 3²∤Δ; 3187²∤Δ.
```

These numerical values were **independently checked with integer arithmetic** while preparing the instruction; **Codex must verify all products/primality/support residues and absolute values in Lean** before treating them as certificates.

**CRITICAL:** These witnesses fail **BOTH** the all-prime-square-support premise and the Archimedean hsize premise. They are **not counterexamples** to the true \`all support + size → Δ=0\` theorem. The tests must separately demonstrate:
- local single-prime q² divisibility is real;
- **missing local coverage** for the other two prime factors of Q;
- even the **maximum potential radical-square modulus** of Q is far below |Δ| in these examples, so an additional magnitude bound is genuinely absent.
If useful, produce a simple abstract **integer** control \`z=M>0\` satisfying all prime-square congruences but z≠0, to show full congruence alone does not imply zero. Keep it as an abstract integer example, NOT a fabricated actual FLT7 defect realizing all those congruences.

Check negative Δ through \`Int.natAbs\`, not truncated natural subtraction or \`z<m\` which is vacuous for negative z.

## Gate 5 — precise research frontier and no silent FLT closure

Required \`frontier-040.md\` (or a clearly separated section in report) must compare:

| Data | What is proved | What is NOT yet proved |
| --- | --- | --- |
| single q²|Δ | Step039 hEq-free square Gap/Tail | Δ=0, other prime support, exact q-budget |
| all square support on S | M_S|Δ | a size bound or FLT equation |
| full prime support of Q | M_Q=rad(Q)²≤Q² | hsupport from weak source assumptions or |Δ|<M_Q |
| extra Archimedean bound | conditional zero certificate | a theorem deriving the bound for hypothetical primitive FLT7 data without assuming Δ=0 |
| Gap/Tail C ideal local receivers | typed local memberships, joint prime sums and lower powers | equality of source elements, exact global balance, primitive next pack |
| old away descent provider | still a signed reconstruction target only | nextX/Y/Z, new CounterexamplePack, AwayValuationTransferPacket, carrier_match |

The old \`AwayDescentClosureProvider\` specifically needs
`carrier_match : nextRoute.carrier = Int.natAbs p.normal.root.snd`; a conditional global zero certificate does **not** construct this recursion. Likewise the old RamifiedSignedRootDepthPacket has balanced signed-root identities, 7-units and normalized equation unrelated to a mere modulus-size estimate.

If \`M_Q≤Q²\` makes the particular global-bound strategy appear too weak, report that limitation openly. **Do not** silently improve the modulus by assuming higher q-adic defect divisibilities or a uniform ABC conjecture. The presence of an \`ABC.Rad\` module in DkMath does not itself prove an ABC conjecture or any FLT7 inequality.

## Deliverables / validation / STOP

Required:
- `DkMath/FLT/Seven/GTailFocusedDefectGlobalCapacity.lean`;
- `DkMathTest/FLT/Seven/GTailFocusedDefectGlobalCapacity.lean`;
- `source-inventory-040.md`, `report-040.md` and a concise `frontier-040.md` (or frontier subsection);
- truthful post-039 `ROADMAP.md` append, preserving the historical Step032 focus correction and all Step001–039 prior sources/reviews/reports.

Sequential focused builds with process-local `LEAN_NUM_THREADS=2`:
1. finite distinct-prime square product, pairwise coprimality and integer divisibility;
2. strict |Δ| threshold, nonzero converse and exact zero-defect-to-Fermat equality **with bound exposed**;
3. actual Q primeFactors support, M_Q≤Q² and optional checked ABC.Rad compatibility **without large import regression**;
4. positive Tail / negative Gap numeric support+size diagnostics and abstract all-support nonzero integer;
5. final source/test, Step039/038 direct regressions, all public \`#print axioms\`, import impact/neutral Lib→FLT, forbidden-token/unsafe/global-options/whitespace and final warning audit.

Report exact gate build commands/exits/warnings, theorem signatures, source owner/API references, all new public axiom results, any failed proof and repairs, **what assumptions still occur in the zero-certificate signature**, and numeric full-support / size conditions separately. Do not use \`sorry\`, \`admit\`, new \`axiom\`, \`unsafe\`, \`native_decide\`, unjustified \`False.elim\`, or global proof-resource-limit overrides. No full clean all-suite build, no old-owner edits, facade promotion, Git PR/rebase/merge.

**Outcome B expected:** accurate finite-local-to-global **conditional** zero criterion and a quantitative **capacity limitation** for the Q prime support. This is a genuine checked bridge from congruence to global equality under an **explicit independent size bound**, not a new FLT7 impossibility proof.
**Outcome C/partial:** if a particular Mathlib Finset coprime-product/API or radical edge condition blocks Lean, retain checked generic finite-modulus results and report the precise issue; never assume factorwise divisibility implies product without coprimality.
**Outcome A:** only if an additional **noncircular, source-derived global restriction** is proved, not simply restating \`|Δ|<M_Q\` as an hypothesis or relying on already assumed Fermat equality.

**STOP after Step040.** Do not iterate q³/q⁴ defect levels, build a new all-prime ideal grid, conjectural ABC/radical inequalities, signed reconstruction packets, new primitive counterexample, away descent or an unconditional FLT7 closure. After this source-typed capacity audit, reassess whether there is a provable new magnitude/prime-support theorem; if not, report the genuine remaining global gap rather than treating additional local theory as progress on the proof.
