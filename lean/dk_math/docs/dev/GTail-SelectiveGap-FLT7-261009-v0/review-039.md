# Review 039 — signed defect square stability without Fermat premise

Date: 2026-10-11
Branch: `feature/GTail-SelectiveGap-FLT7-261009-v0`
Decision: **APPROVED — Step 039 COMPLETE / Outcome B**

## Evidence, boundary and source ownership

Statically inspected actual GitHub files:
- `DkMath/FLT/Seven/GTailFocusedDefectSquareFirewall.lean` (111 lines);
- `DkMathTest/FLT/Seven/GTailFocusedDefectSquareFirewall.lean` (192 lines);
- `report-039.md`, `source-inventory-039.md`, `frontier-039.md`;
- existing `GTailBridge.gtail_seven_defect`, neutral seventh-power shell `add_pow_seven_eq_gap_add_interior`, `coprime_product_seven_quadratic`, `not_prime_dvd_gtail_seven_of_gap`, Step038 canonical `gap_ratio_eq_one`, Step032 exact Fermat balance iff, Step037 native Tail receiver, and previously audited signed descent-provider fields.

This is **GitHub static Lean proof-route inspection, not an independent Lean compilation**. Codex reports final production05 and test07 exit0/warning0, Step038/037 direct regressions08/09 exit0/warning0 (older targets can include cached replay), 46 examples, seven public declarations (one definition, six theorems) with `#print axioms` restricted to `propext`, `Classical.choice`, `Quot.sound` where used. Initial failed proof/cast builds01/02 and numeric tests06 are disclosed and repaired without changing mathematical contracts. No clean full-repository suite is claimed.

## The actual checked theorems

1. `focusedFermatDefect a b c : ℤ := (a:ℤ)^7 + (b:ℤ)^7 - (c:ℤ)^7`. Using **integer** subtraction is mathematically necessary: the Gap control has a negative defect. The source does not project the defect to a natural truncated difference.
2. `focusedFermatDefect_eq`: with only `a+b=c+g`, `Δ=(g:ℤ)*(GTail:ℤ)-7(a:ℤ)(b:ℤ)(a+b:ℤ)(Q:ℤ)^2`. This is a direct, correctly cast use of already checked `gtail_seven_defect`, not a recreated binomial factorization.
3. `defect_square_iff_product_int` and `defect_square_iff_product_nat`: assuming **only** focus and `q|Q` (not prime, hEq, positivity or coprimality), `(q:ℤ)^2|Δ ↔ (q:ℤ)^2|(g:ℤ)*(T:ℤ) ↔ q²|g*T`. The second scalar term is q²-divisible because q|Q and thus q²|Q². Both directions correctly use integer `dvd_add/dvd_sub` and `exact_mod_cast`. The theorem is true even if q is nonprime, though later branch cancellation requires prime.
4. `endpoint_unit_of_defect`: q prime, `Nat.Coprime a b`, q|Q and the *weaker* q|Δ imply q∤c, with **no additive-focus and no Fermat premise**. The proof uses actual neutral primitive quadratic coprimality (q∤a*b*(a+b)); otherwise q|c and q|Δ imply q|(a⁷+b⁷), and the preexisting exact seventh-power-sum shell plus q|Q yields q|(a+b)^7, contradicting prime-unit q∤a+b. This is a genuine hypothesis weakening of the old hEq-dependent Step010 endpoint theorem, not a Fermat impossibility theorem.
5. `defect_square_prime_route`: prime q≠7, primitive a,b, q|Q, focus and **q²|Δ** lead, without hEq or positivity or entry q|T, to
   `(q²|g ∧ q∤T ∧ ratio=1) ∨ (q²|T ∧ q∤g)`.
   The source gets q²|g*T via Step039's new iff, q∤c via its **own** endpoint theorem, then splits on q|g and reuses only the **equation-free neutral** `not_prime_dvd_gtail_seven_of_gap`; q² cancellation is genuine `Nat.Coprime.pow_left 2` and `dvd_of_dvd_mul_left`. The canonical Gap ratio=1 follows from Step038's hEq-free basic lemma. The proof does **not** call `focused_prime_route`, `prime_square_focused_allocation`, any hEq-dependent conditional unit or a CounterexamplePack theorem.
6. `focusedFermatDefect_zero_iff` proves `Δ=0 ↔ Fermat7Equation a b c` for arbitrary naturals a,b,c, **without** focus. This is a legitimate cast/normalization consequence of the exact definition, not a new FLT result.

## Numerical and negative controls

All following values are test-local kernel checks, not alleged positive FLT7 solutions:

- Tail at q43, `(a,b,c,g)=(1166,1857,1858,1165)`: positive primitive, strict focus and coprimality, Q=6,973,267; T=1,914,732,507,483,487,090,603; **positive nonzero** Δ=+2,642,627,963,860,178,152,897; v43(Q)=1, v43(g)=0, v43(T)=2, v43(|Δ|)=2, q²|T, q∤g. The native Step037 C kernel and bounded M²/M³/M⁴ supports coexist with **failure of** exact Fermat/global balance.
- Gap at q13, `(196,211,238,169)`: positive primitive, strict focus and coprimality, Q=124,293; T=10,690,523,583,988,879; **negative nonzero** Δ=−13,523,337,259,569,605; v13(Q)=1, v13(g)=2, v13(T)=0, v13(|Δ|)=2, q²|g, q∤T and canonical root=1. The Gap example is **not** passed to the native nontrivial Tail receiver.
- In **both** these specific controls, vq(g)+vq(T)=2vq(Q) happens to hold even though Δ≠0: a **single selected-prime valuation budget cannot recover the exact Fermat equation**.
- Additional q13 `(2198,2213,2214,2197)` is a positive primitive focused input with q²|Δ but v13(g)≥3 and v13(Q)=1, disproving a **general** equality of the selected-prime valuation budget from q²-defect support alone. This nuance is crucial: the first two examples are *examples*, not a theorem establishing the budget under weak hypotheses.
- Old q13 `(14,29,30,13)` and q43 `(5,8,9,4)` controls fail the new q²-defect premise; the second **does satisfy additive focus** (Step032 historical correction remains honored).
- The test checks the actual signs of Δ, exact degree-two valuations and q³ nondivisibility, nonzero defect and failure of both hEq and the focus-equivalent global balance. It uses the real `Int.natAbs` when evaluating the valuation of a negative defect.

## Scientific interpretation and next gate

**APPROVED — Outcome B.** The general square routing is robust under a **nonzero** Fermat defect congruent to zero modulo q²; this is a precise proof that these selected local contracts are *not sufficient* for global Fermat equality. It is an important negative-information result and a noncircular strengthening of the endpoint lemma's hypotheses. It does not disprove any Fermat equation or provide signed packet/descent fields.

Suggested Step040, a **global zero-certification/capacity audit**, not a new local prime depth or another C ideal:
- Use the actual signed Δ from Step039 and a finite family S of **pairwise distinct** primes. If p²|Δ for every p∈S, then the combined natural modulus `M_S := ∏ p∈S p²` divides `Int.natAbs Δ`; if additionally `|Δ|<M_S` and M_S>0, then Δ=0, hence Fermat7Equation. Conversely, **any nonzero Δ divisible by M_S must satisfy `M_S≤|Δ|`**. These are globally valid integer statements and can be proved without hEq. An assumption `|Δ|<M_S` is a genuinely **extra Archimedean bound**, not something supplied by Steps010–039.
- For S the **entire** prime-factor support of Q (assuming Q≠0), `M_S=rad(Q)^2≤Q²`, where DkMath already has `DkMath.ABC.Rad.rad` and `rad_dvd_nonzero`. Source-inventory and import-cost comparison is mandatory; prefer Mathlib factorization/Finset owners rather than introducing a heavyweight ABC import into the FLT production chain just for notation. A source-owned local name with a later exact bridge to the existing radical is acceptable if no duplicate public theory is introduced.
- Important **precalculated capacity diagnostics**, not Lean-verified Step039 results:
  * Tail Q=6,973,267 is squarefree with prime factors 7,43,23167; `rad(Q)^2=Q²=48,626,452,653,289`, while `|Δ|=2,642,627,963,860,178,152,897` (much larger).
  * Gap Q=124,293 is squarefree with factors 3,13,3187; `rad(Q)^2=Q²=15,448,749,849`, while `|Δ|=13,523,337,259,569,605`.
  * These examples **do NOT** satisfy square-divisibility at all prime factors of Q: Tail Δ is divisible by 43² but not 7² or 23167²; Gap Δ is divisible by 13² but not 3² or 3187². Do not misrepresent them as counterexamples to the full-support conditional zero criterion. They only reveal the *missing local coverage* and *missing magnitude bound*, separately.
- The major research question should be whether native Fermat-focused arithmetic can supply **both** sufficient prime coverage and a nontrivial upper bound making the modulus larger than the defect, rather than creating a tautological hEq-equivalent assumption.

The old `AwayDescentClosureProvider` still demands new primitive nextX/Y/Z, nextPack/nextRoute and exact `carrier_match`. No finite collection of local `Ideal C` membership statements creates those data by itself. The next task should not claim that the global size bound is known or that the CRT proof itself settles FLT7.

No PR/merge/rebase, signed-packet reconstruction, class/unit principalization, indefinite defect-q³ ladder, all-prime kernel grid, or unconditional FLT7 theorem authorized.
