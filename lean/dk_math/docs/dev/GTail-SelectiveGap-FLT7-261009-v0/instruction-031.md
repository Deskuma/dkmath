# Instruction 031 — typed Eisenstein-norm / GTail cyclotomic-depth synchronization

Date: 2026-10-10
Target branch: `feature/GTail-SelectiveGap-FLT7-261009-v0`
Working directory: `lean/dk_math`
Prerequisites: `review-030.md`, `report-030.md`, `source-inventory-030.md`.
**Scope: Step 031 only — a source-typed scalar bridge between the *existing* Eisenstein norm-square arithmetic and the *existing* six cyclotomic Tail-factor ideal-depth receivers.** This is a frontier reassessment after the bounded K³\\K⁴ checkpoint. Do **not** proceed to K⁵/all-k, make up an Eisenstein→cyclotomic integral RingHom, identify their prime ideals, create a signed-depth packet, or claim FLT7 descent.

## The genuine two-carrier problem

Actual distinct carriers, already kernel checked:
- Eisenstein integral ring `E := DkMath.NumberTheory.TraceOneQuadratic.TraceOneInt (-1)` with `α(a,b):E := gtailSevenNormCoord a b` and `norm α = ((Q(a,b):ℕ):ℤ)`, `Q(a,b)=a²+a*b+b²`. Step012 also proved `norm(α²)=((Q²:ℕ):ℤ)` and a selected Body integer norm-square readout.
- Eisenstein root slot at q≠3, q|Q and q∤b: `t=gtailSevenResidueRoot q a b` and the actual split prime ideal `P_t:=eisensteinResidueIdeal t (...) : Ideal E`. Step017 provides `α²∈P_t*P_t` and exclusion from the conjugate and scalar ideals.
- Cyclotomic degree-six source `R:=SevenCyclotomicDegreeSixInt.Ring` and for q prime with q∤c,g and q|T=GTail 7 1 g c, a canonical nontrivial root `r=(c+g)/c:ZMod q`. Steps023–030 provide actual factors `F_i(c,g):R` and selected ideals `K_(sixInverseSlot i):Ideal R`, with source-checked equivalences `F_i∈K² ↔ q²|T`, `F_i∈K³ ↔ q³|T`, `F_i∈K⁴ ↔ q⁴|T`.
- These do **not** produce a RingHom E→R, an ideal map P↔K, an equality of elements α²=F_i, nor a reconstruction of a signed quotient-depth packet. Their only currently justified common carriers are scalar natural/integer values and a shared finite field ZMod q. Treat those as the chosen *readout bridge*.

Existing primitive **hypothetical FLT7** arithmetic:
```text
hEq : Fermat7Equation a b c
hsum : a+b = c+g
Q := a²+a*b+b²
T := GTail 7 1 g c
hEq,hsum ⟹ g*T=7*a*b*(a+b)*Q²              -- GTailBridge
```
With positive a,b, coprime a,b, q prime, q≠7 and q|Q, Step010 \`padicValNat_focused_quadratic_budget\` already proves
`v_q(g)+v_q(T)=2*v_q(Q)`.
With further q|T, its \`prime_focused_support_exclusive\` rules out q|g, and \`not_prime_dvd_endpoint_of_quadratic\` provides q∤c. Step011 \`twentyOne_dvd_prime_sub_one_of_focused_tail\` already establishes 21|q−1 on the tail branch.

**IMPORTANT:** This is a conditional consequence of a **hypothetical positive primitive Fermat7 equation**, not a new global arithmetic obstruction or an actual numeric Fermat solution. Any proof must make the exact hEq and primitive/positivity assumptions visible and must not import a preexisting unconditional FLT7 closure/contradiction to close it.

## Phase 0 — source overlap audit and contract ledger

Inspect exact signatures and direct import graph:
- `DkMath.Lib.NumberTheory.GTailSevenNormReadout`: `gtailSevenNormCoord`, `norm_gtailSevenNormCoord`, `norm_gtailSevenNormCoord_sq`, `dvd_quadratic_iff_dvd_gtailSevenNormCoord`.
- `DkMath.Lib.NumberTheory.GTailSevenIdealSquareAddress`: `gtailSevenNormCoord_split_square_address` and `gtailSevenResidueRoot_*`.
- `DkMath.FLT.Seven.GTailNormReadoutAudit.focused_gtail_eq_norm_square` (integer scalar equality, explicit source types).
- `DkMath.FLT.Seven.GTailPrimeAllocationAudit`: `not_prime_dvd_coordinate_product_of_quadratic`, `not_prime_dvd_endpoint_of_quadratic`, `prime_focused_support_exclusive`, `padicValNat_focused_quadratic_budget` and `prime_square_focused_allocation`. Reuse, never duplicate.
- `DkMath.FLT.Seven.GTailPrimeOrderAudit`, Step011 when appropriate; \`GTailSevenPairedResidue\` already places both residue roots in the same ZMod q but **does not** give any integral ring hom between E and R.
- `GTailCyclotomicTailDepthTwo` (actual K² iff), `GTailCyclotomicTailDepthThree` (actual K³ iff), `GTailCyclotomicTailDepthFour` (actual K⁴ iff), selected source root/factor contracts.
- `DkMath.Lib.NumberTheory.PadicValNat.Vp_ge_one_iff`, `padicValNat_le_iff_dvd` and \`padicValNat.eq_zero_of_not_dvd\`: actual nonzero hypotheses, prime Fact, quotient conventions; confirm APIs by source/#check.
- Existing old signed carrier depth owner **for overlap only**; no signed packet reconstruction. Do not infer parity of its quotientExponent merely from the new scalar identity.

Write `source-inventory-031.md` with a comparison table **source ring / exact element / selected ideal / scalar map / extra hypotheses / lost data / owner**. Explain why the two finite-field evaluations with different integral domains do not define an E→R hom. Note what follows already from Step010 and avoid “new obstruction” language for its direct corollaries.

Suggested new narrow FLT owner:
`DkMath/FLT/Seven/GTailFocusedNormCyclotomicDepthBridge.lean`
direct import of Step030 and the **minimal** Step010/Step012/Step017 owners necessary for this theorem; no heavy FLT7 façade, generic closure theorem, global oriented factorization or unit/class theory. Tests:
`DkMathTest/FLT/Seven/GTailFocusedNormCyclotomicDepthBridge.lean`.

## Phase 1 — a genuinely satisfiable neutral scalar-budget firewall

Do this **before** an owner theorem that assumes Fermat7Equation. Use an abstract natural input `q,g,T,Q` with
`hq:Nat.Prime q`, `hg0:g≠0`, `hT0:T≠0`, `hQ0:Q≠0`,
`hgu:¬q∣g` and the **explicit verified budget premise**

```text
hbudget : padicValNat q g + padicValNat q T
          = 2 * padicValNat q Q.
```

Prove by \`padicValNat.eq_zero_of_not_dvd hgu\`:

```text
padicValNat q T = 2*padicValNat q Q.
```

Using exact \`padicValNat_le_iff_dvd hq hT0/ hQ0\`, derive **bounded scalar readouts**:

```text
q² ∣ T ↔ q ∣ Q
q⁴ ∣ T ↔ q² ∣ Q
q³ ∣ T ↔ q⁴ ∣ T
¬ (q³ ∣ T ∧ ¬ q⁴ ∣ T).
```

These equivalences follow by natural arithmetic on the checked doubled valuation; prove them, do not treat them as a consequence of mere q|Q or q|T without the budget and q-unit gap. \`padicValNat q 0\` conventions are why nonzero assumptions are explicit. The evenness consequence is a classical local arithmetic restriction already latent in the budget, not a Fermat contradiction by itself.

**Satisfiable control** separate from native GTail: q43,g4,Q43,T43² satisfies all abstract budget/unit/nonzero hypotheses; test the parity and square/fourth endpoints. Clearly label Q,T as arbitrary abstract scalar variables, NOT as `Q(5,8)` and `GTail(9,4)` for that control.

**Failure control:** if q|g, the identity \`v_q(g)+v_q(T)=2v_q(Q)\` does not force v_q(T) even. Exhibit an abstract numerical allocation with q-prime, genuine equality, q|g and **odd** v_q(T); keep an explicit test or a source comment to demonstrate why q∤g is essential. Likewise, no equality of p-adic valuations is inferred from just two unrelated ring elements with the same norm value.

This phase is reusable pure Nat arithmetic; it may be a **private helper in the new FLT owner** or a neutral Lib helper if it genuinely improves reuse without importing FLT modules. Avoid adding unnecessary public abstractions or rewriting older arithmetic owners.

## Phase 2 — derive the budget and all real q-unit conditions from the existing FLT contracts

In the hypothetical positive primitive focused tuple input, assume

```text
ha : 0<a
hb : 0<b
hcop : Nat.Coprime a b
hEq : Fermat7Equation a b c
hsum : a+b = c+g
hq : Nat.Prime q
hq7 : q≠7
hQ : q ∣ a²+a*b+b²
hT : q ∣ GTail 7 1 g c
```

Derive **rather than request anew**:
- q∤a,b,a+b from `not_prime_dvd_coordinate_product_of_quadratic`;
- q∤c from `not_prime_dvd_endpoint_of_quadratic`;
- q∤g from Step010 `prime_focused_support_exclusive` plus q|T;
- q≠3 from Step011/neutral `prime_ne_three_of_gtail` and the derived q∤c,g;
- g≠0 and T≠0 from Step010 positive focused-gap facts or a direct rewrite of positive product \`g*T=7ab(a+b)Q²\`; the source's private \`focused_gap_tail_ne_zero\` cannot be imported as a public declaration;
- Q≠0 from positivity a,b;
- exact valuation budget from `padicValNat_focused_quadratic_budget`.

Call Phase1 to prove the **conditional native arithmetic synchronization**:
```text
padicValNat q (GTail 7 1 g c) =
    2*padicValNat q (a²+a*b+b²)

q³ ∣ GTail 7 1 g c ↔ q⁴ ∣ GTail 7 1 g c

q⁴ ∣ GTail 7 1 g c ↔ q² ∣ a²+a*b+b².
```

The second result is a **no scalar exact-depth-three** condition under the full hypothetical equation assumptions. Do NOT claim it rules out the Fermat equation itself: it merely restricts a chosen Tail-side quadratic prime. The existing Step010 q² allocation already implies q²|T on this branch. Reuse that result rather than reprove it via a new abstract valuation calculation where possible.

If a smaller source-compatible explicit scalar balance assumption
`g*T=7ab(a+b)Q²` makes a useful standalone conditional lemma, add one *only if* it materially avoids vacuous testing and retains q-unit and nonzero premises. It cannot silently replace the exact Fermat hypothesis in the FLT-facing specialization.

## Phase 3 — actual two-carrier witness, joined ONLY through scalar data

Under the **same derived q-prime/unit/full exact input**, instantiate two independently checked endpoints:

**Eisenstein degree-two side:**
```text
α := gtailSevenNormCoord a b : TraceOneInt (-1)
norm α = (Q:ℤ)
α² ∈ P_t*P_t
α² ∉ conjugate(P_t)
α² ∉ eisensteinScalarIdeal q
```
from Step012 and Step017 \`gtailSevenNormCoord_split_square_address\` using q≠3, q|Q and q∤b. The actual \`P_t\` remains an `Ideal (TraceOneInt (-1))`.

**Cyclotomic degree-six side:**
```text
r := gtailSevenTailRatio q c g : ZMod q
F_i(c,g) : R
K_(sixInverseSlot i) : Ideal R
F_i(c,g) ∈ K_(sixInverseSlot i)^2
F_i(c,g) ∈ K_(sixInverseSlot i)^3 ↔
    F_i(c,g) ∈ K_(sixInverseSlot i)^4.
```
The first K² membership follows from checked Step010 q²|T and Step025 \`gtailCyclotomicFactor_mem_square_iff\`; the second uses Phase2 parity plus the separate Step029 K³ and Step030 K⁴ iff.

**Mandatory cross-carrier statement:** package this as a small, clearly typed theorem or two theorems with separately named Eisenstein and cyclotomic fields, with a common explicit scalar \`Q,T,q\`. Avoid an enormous nested dependent ideal type if it impedes Lean; separate exported endpoint theorems over the **same hypotheses** are acceptable and preferable to a new complicated record/structure.

If feasible, additionally connect norm-value divisibility:
```text
q⁴ | T ↔ (q:ℤ)^2 | norm (gtailSevenNormCoord a b).
```
Use checked Step012 norm equality and Int/Nat div-cast lemmas and Phase2's q⁴↔q²Q. This statement reads the same source norm **as an integer scalar**, not an equality of elements/ideals in E and R. Keep degree-two norm and degree-six ideal types visible.

**Substantive consistency theorem** (if prerequisite proofs compile):
For every selected i:Fin6,
`¬(F_i∈K_i^3 ∧ F_i∉K_i^4)`
under these exact positive primitive FLT-facing Tail hypotheses.

Note: such a statement is **not** a new unconditional FLT7 no-solution theorem. It is a corollary of the existing Step010 even-valuation budget once a real typed K³/K⁴ receiver is attached. Do not claim an independent obstruction unless a new condition not already implied by Step010 emerges and is noncircularly proven.

Do **not** state or prove `P_t=K_j`, `α²=F_i`, \`Ideal.map\`/comap across rings or any norm-to-principal-element lifting. These objects inhabit distinct rings.

## Phase 4 — honest q43 checks and counterexamples to missing premises

Non-Fermat q43 numeric sample: (a,b,c,g)=(5,8,9,4) has
`Q=129` and q43|Q, q43|T, q43∤b,c,g, distinct residue roots t37 and r11. It has **no exact Fermat7Equation**. Independently verify:
- Step017 Eisenstein `α(5,8)²∈P_37²` and conjugate/scalar exclusions;
- Step024/025 actual cyclotomic F_i(9,4)∈K_assigned, F_i∉K_assigned²;
- the joint scalar **balance** `g*T=7ab(a+b)Q²` fails in this data; hence the Phase2/Fermat-conditioned square/valuation implications cannot be applied. This is a critical countercheck against hidden assumptions.
- g=32598 has T of exact q43-adic depth 3 and all six F_i∈K³\\K⁴ by Step030, but does **not** satisfy the FLT-focused tuple relation a+b=c+g with a5,b8,c9; it cannot be used as a counterexample to the conditional evenness theorem.
- the abstract scalar satisfiable allocation in Phase1 should be recorded as a genuinely **satisfying instance of the budget contract**, without pretending it arises from a Fermat solution.
- characteristic q=3 has a repeated Eisenstein root and is excluded on the paired nontrivial Tail branch; q=7 has no nontrivial seventh root in ZMod7; q=13 gap-only cannot instantiate q|T and q∤g.
- zero endpoints and exact Fermat equation with zero coordinates must not be promoted into a positive primitive counterexample.

### No new FLT impossibility from absent positive examples

No positive counterexample to Fermat7 is known or expected; the conditional FLT-facing theorem should be proved from the exact input assumptions, not checked by \`decide\` over a fictional numeral tuple. Test its **theorem signature** universally using an \`example (ha...) : ... := theorem ...\` of the same full hypotheses. Use numeric q43 tests only for genuinely satisfiable neutral/codomain fragments and explicit missing-premise cases.

## Phase 5 — deliverables, build and STOP

Required:
- `DkMath/FLT/Seven/GTailFocusedNormCyclotomicDepthBridge.lean`;
- `DkMathTest/FLT/Seven/GTailFocusedNormCyclotomicDepthBridge.lean`;
- `source-inventory-031.md`, `report-031.md`;
- truthful **post-030** `ROADMAP.md` append; keep prior historical reports/reviews/ledger byte-stable.

Gates (in this order):
1. explicit abstract valuation-budget parity and q-power divisibility; test satisfiable/failed-unit controls;
2. derive *all* q-units, nonzero and budget from the actual Step010/011 FLT conditions;
3. instantiate actual Eisenstein α² split ideal support and actual cyclotomic K²/K³/K⁴ readouts, joined only through integer scalar conditions;
4. honest q43 mixed carriers without Fermat premise, Step030 and Step010/012/017 regressions;
5. focused Lean source/test build and selected prior tests, axiom/source/import audit.

Use sequential process-local `LEAN_NUM_THREADS=2`. Record all public theorem signatures, actual \`#print axioms\`, focused build exit codes, import reachability, no neutral Lib→FLT cycles, forbidden-token/whitespace/style checks and any failed proof attempt. Avoid importing the entire FLT façade or a generic impossibility/closure result merely to prove a conditional statement. Do not alter existing ring/carrier/norm owners, existing packet depth theorem, previous GTail owners or old constraint ledger; no clean all-suite build, PR, rebase or merge. Current feature branch remains diverged one commit behind develop; leave it as is unless separately requested.

**Outcome B expected:** source-typed **conditional norm-scalar/ideal-depth compatibility** plus an even-depth restriction, explicitly identified as a repackaging/application of the preexisting Step010 budget. This creates an honest bridge of proven scalar readouts **without** an E→R RingHom or novel FLT7 descent.
**Outcome C/partial:** a false q-unit transfer, invalid abstraction, undiscovered hidden Fermat dependency, nonzero/padic conversion failure or import cycle; report the exact blocker and preserve verified weaker statements.
**Outcome A:** only if a genuinely new, noncircular restriction is proved beyond the previous FLT7 valuation/order/signed-packet owners. Do not reclassify the classical parity budget as new merely because it is now expressed through ideal membership.

**STOP after Step031.** No K⁵/all-k factor valuation, generalized Hensel implementation, Eisenstein↔cyclotomic integral map/ideal equality, signed packet reconstruction, class/unit extraction, next primitive Fermat tuple or unconditional FLT7 closure.
