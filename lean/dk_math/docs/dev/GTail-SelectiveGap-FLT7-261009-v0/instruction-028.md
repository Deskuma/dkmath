# Instruction 028 — native GTail second Hensel digit via existing finite-depth API

Date: 2026-10-10
Target branch: `feature/GTail-SelectiveGap-FLT7-261009-v0`
Working directory: `lean/dk_math`
Prerequisites: `review-027.md`, `report-027.md` and `source-inventory-027.md`.
**Scope: Step 028 only — specialize the ALREADY implemented generic polynomial next-digit machinery at k=2 to the real native GTail shell, prove a one-digit q²→q³ lift, and test the new numeric successor to g=1165.** Do not implement a second general Hensel proof, all-k selected-cyclotomic-ideal valuation, q-adic completion, new prime packet or FLT7 descent.

## Key existing source, mandatory to inspect before writing code

`DkMath/Lib/NumberTheory/PolynomialHenselDigit.lean` is already implemented, including these ACTUAL generic contracts:

```text
polynomial_powLift_iff (P : ℤ[X]) {q k : ℕ} (x t : ℤ)
    (hq : 0 < q) (hk : 1 ≤ k) (hx : (q : ℤ)^k ∣ P.eval x) :
    (q : ℤ)^(k+1) ∣ P.eval (x + (q : ℤ)^k * t) ↔
      (q : ℤ) ∣ P.eval x / (q : ℤ)^k + t * P.derivative.eval x

existsUnique_polynomial_powLift_digit (P : ℤ[X]) {q k : ℕ} (x : ℤ)
    (hq : q.Prime) (hk : 1 ≤ k) (hx : (q : ℤ)^k ∣ P.eval x)
    (hd : ¬ (q : ℤ) ∣ P.derivative.eval x) :
    ∃! t : Fin q, (q : ℤ)^(k+1) ∣
      P.eval (x + (q : ℤ)^k * t.val)
```

There is also `polynomial_shift_preserves_dvd` and `exists_polynomial_exact_depth_digit`. The existing owner proves all these finite-depth facts, **without** any claim about an infinite p-adic completion. Do NOT reimplement its Taylor quotient, Bézout or induction, or claim Hensel next-digit discovery is new to the repository.

Step027 now provides the typed GTail polynomial `tailShellPoly (c:ℤ)`, evaluation bridge to the original natural `GTail 7 1 g c`, integer derivative `gtailDerivativeInt` and its field-cast identity. Step026 proves the **derivative is nonzero modulo q** under prime q, q∤c,g, q|T. Step025 proves the **bounded** selected factor K² iff scalar q² support, not any K³ statement.

The actual task is to connect these typed interfaces, not to create a new ring or alter any old definition.

## Core theorem to prove

Given `{q:ℕ} [Fact (Nat.Prime q)]`, natural c,g, and premises

```text
hc : ¬ q ∣ c
hg : ¬ q ∣ g
hT2 : q^2 ∣ GTail 7 1 g c
```

derive q|T (using q prime and q²|T), and instantiate the existing polynomial theorem at:

```text
P := tailShellPoly (c:ℤ)
x := ((c+g:ℕ):ℤ)
k := 2.
```

Prove the actual derivative guard
`¬ (q:ℤ) ∣ P.derivative.eval x`
using Step027's `gtailDerivativeInt_cast` and `gtail_shell_derivative_ne_zero`, with explicit conversions via ZMod integer cast zero iff divisibility. Do not regard integer and field derivatives as definally equal.

**Mandatory native endpoint:**

```text
∃! t : Fin q,
  q^3 ∣ GTail 7 1 (g + q^2*t.val) c.
```

The unique digit is a residue representative `t.val < q`. This is uniqueness among the first q natural digits, equivalently uniqueness modulo q, NOT uniqueness over all naturals.

Prefer an explicit thin adapter whose proof is a direct application of the existing `existsUnique_polynomial_powLift_digit` plus an exact equality of source polynomial evaluations and **the actual native natural GTail**. Avoid changing the statement to an unrelated polynomial-evaluation result.

If convenient, define `gtailSecondDigit` from the existing unique witness or as the explicit residue solution below, but **do not define a second generic digit framework**.

## Phase 0 — exact source inventory

Read:
- `DkMath.Lib.NumberTheory.PolynomialHenselDigit`, exact signatures above and actual integer division and positive-depth premises;
- `DkMath.FLT.Seven.GTailCyclotomicTailTaylorLift` (Step027): integer/natural evaluation, derivative cast and shift invariances;
- `GTailCyclotomicTailDerivative` (Step026): correct formal derivative, nonvanishing and unit guards;
- `GTailCyclotomicTailDepthTwo` (Step025): existing K² iff and q43 positive example;
- \`Polynomial.eval_add\` and integer/natural cast APIs used by Mathlib, `ZMod.intCast_zmod_eq_zero_iff_dvd`, `ZMod.natCast_zmod_val`, `Int.ediv` versus `Nat.div` compatibility.

Create `source-inventory-028.md` with a table identifying exact owners, actual carrier types (`ℤ[X]`, `ℤ`, `ZMod q` and natural native GTail), the transport lemmas required, source API overlap, and the **unproved** distinction between q³ scalar support and K³ ideal membership.

Suggested owner/test:
- `DkMath/FLT/Seven/GTailCyclotomicTailSecondDigit.lean` with direct imports of Step027 and the existing neutral `DkMath.Lib.NumberTheory.PolynomialHenselDigit`;
- `DkMathTest/FLT/Seven/GTailCyclotomicTailSecondDigit.lean`.

Do not modify the generic neutral polynomial API, previous GTail owners, signed-depth valuation owner or facades. If the generic owner introduces a larger transitive import closure, record its exact cost; avoid full umbrella import or global parallel builds.

## Phase 1 — transport native GTail evaluation and derivative nondivisibility

Provide a small strongly typed lemma (local/private if sufficient):

```text
(tailShellPoly (c:ℤ)).eval (((c+g:ℕ):ℤ))
  = ((GTail 7 1 g c:ℕ):ℤ).
```

For each d:ℕ, explicitly rewrite `x + (q:ℤ)^2 * (d:ℤ)` to the cast of `c+(g+q²*d)`; use source-correct natural/signed casts, not a broad \`simp\` that expands GTail.

Establish:
- q²|T in naturals -> `(q:ℤ)^2 | P.eval x`;
- q²|T -> q|T as a source natural divisibility result;
- q∤c,g and q|T -> **field derivative D≠0** by Step027;
- derivative cast to ZMod q -> `¬ (q:ℤ)|P.derivative.eval x`.

No prime/unit support should be silently added to the raw polynomial-evaluation cast lemma.

Build this gate before the uniqueness theorem.

## Phase 2 — the actual k=2 next digit

Use `existsUnique_polynomial_powLift_digit P (q:=q) (k:=2) x` with the checked:
- q-prime,
- 1≤2,
- q² integer polynomial evaluation divisibility,
- derivative nondivisibility.

Translate the generic \`Fin q\` existential-unique predicate to:

```text
∃! t:Fin q, q^3 ∣ GTail 7 1 (g+q²*t.val) c.
```

Be careful: Lean's \`ExistsUnique\` represents both existence and uniqueness proof for **the same native predicate**. A proof may use \`simpa only\` with a genuinely proved per-digit iff; do not assume that the integer polynomial evaluations rewrite by definitional equality into natural GTail.

As optional strengthening, and **only after** native ∃! succeeds, prove for any d:ℕ:

```text
q³ ∣ GTail 7 1 (g+q²*d) c
  ↔ ((GTail 7 1 g c / q²:ℕ):ZMod q)
      + (d:ZMod q)*D = 0
```

where `D := (tailShellPoly (c:ZMod q)).derivative.eval (c+g:ZMod q)`. The generic `polynomial_powLift_iff P (k:=2)` proves the integer counterpart. Conversion of the **integer quotient** \`P.eval x / (q:ℤ)^2\` to the **natural quotient** \`T/q²\` needs a genuine lemma under q²|T and q>0; no informal cancellation of q² in ZMod(q³).

A unique residue formula `δ₂=−(T/q²)/D` is useful but optional if it causes duplicative heavy algebra. If implemented, show both directions of the iff and that its representative equals the \`Fin q\` unique witness; avoid independent inconsistent digit definitions.

**Required at minimum:** the exact \`Fin q\` existence-uniqueness lift theorem and q43 calibration below. A correctly checked linear iff is a valuable optional addition.

## Phase 3 — canonical ratio and bounded ideal-square preservation

For any natural d:
- `g+q²*d ≡ g (mod q)` and q∤g stays true; Step027's \`gtail_shift_gap_unit\`, \`gtail_shift_ratio\` and \`gtail_shift_derivative\` apply by rewriting the increment as q*(q*d);
- the q²→q³ lift is automatically still q²-divisible;
- therefore Step025's **actual K² membership iff** places all six shifted factors in their selected kernel squares under the canonical source unit/Tail support inputs.

This last implication is entirely **bounded level two**. No inference `q³|T ↔ F_i∈K_i³` is authorized: the existing Step025 contract stops at exponent two. It is acceptable to keep this ideal receiver as a concrete regression rather than an extra public owner theorem.

## Phase 4 — mandatory q43 calibration: the next digit after 1165

The numeric candidate below was computed independently outside Lean; treat it as **proposed data to verify in actual Lean tests**, not a verified Step027 statement.

```text
q=43, c=9, starting g=1165
T(1165) = 2638461449052811747
43² | T(1165)
m₂ := T(1165)/43²; m₂ mod43 = 40
D = 28 in ZMod43
40 + 17*28 = 0 mod43
unique next digit = 17 in Fin43
g₂ = 1165 + 43²*17 = 32598
43³ | GTail 7 1 32598 9.
```

Validate:
1. These numeric residues and digit equation with \`decide\`/a checkable field expression;
2. **the actual next-gap 43³ divisibility via the generic native k=2 theorem**, not only computation of a huge number;
3. any d:Fin43 other than 17 does not satisfy the lift predicate, through the generic uniqueness proof; test d=16 or 0;
4. any natural correction d≡17 mod43 (e.g. d=60) gives another natural g but the *same unique residue class*, if the optional natural-digit iff is proved;
5. shifted g₂ retains q∤g, canonical ratio 11 and derivative 28;
6. Step025 generic theorem implies all six F_i(c,g₂)∈their selected K², **not K³**;
7. q43 c9 g4 still yields the Step027 first digit 27, g1=1165 and q² support, preserving the chain of two separately checked stages.

Further arithmetic observation to test if cheap: `43^4 ∤ GTail 7 1 32598 9` (independent calculation suggests the new scalar depth is exactly 3). This is only an optional **natural scalar** regression and is not an ideal-exponent theorem.

Boundaries:
- q=7 has no nontrivial scalar seventh root, so the simple canonical GTail receiver is unavailable even though the generic neutral PolynomialHenselDigit theorem may have other roots;
- q=13 Gap-side missing Tail support cannot satisfy these canonical premises;
- g=0/c=0 violate the unit contract, although original integer polynomial evaluation and Taylor identities remain true;
- no exact Fermat7 solution is manufactured by these congruence adjustments.

## Phase 5 — output, validation and stop

Required:
- `DkMath/FLT/Seven/GTailCyclotomicTailSecondDigit.lean`;
- `DkMathTest/FLT/Seven/GTailCyclotomicTailSecondDigit.lean`;
- `source-inventory-028.md`, `report-028.md`;
- truthful **post-027** `ROADMAP.md` append without editing past checkpoint reports.

Implement/build sequentially with process-local `LEAN_NUM_THREADS=2`:
1. native polynomial evaluation/derivative cast and k=2 support gate;
2. existing generic Hensel-digit specialization to native `∃! Fin q`;
3. optional explicit q³ linear iff / residue representative;
4. q43 numeric, canonical-ratio and Step025 bounded K² regressions;
5. focused production/test and Step027/026 regression, public \`#print axioms\`, import-cycle/neutral→FLT, forbidden-token/whitespace audits.

Log exact build commands and exit codes, intermediate elaboration repairs and all new public signature axioms. Do not run full clean \`DkMathTest\`, import an entire FLT facade, add proof-resource-limit workarounds, or alter the existing generic \`PolynomialHenselDigit\` owner.

**Expected Outcome B:** a genuine **native GTail k=2 adapter** to an already proved generic finite Hensel digit, with unique q³ correction and a nonvacuous g=1165→g=32598 calibration; no new all-k Hensel theorem is claimed.
**Outcome C/partial:** precise integer/natural cast or derivative-guard transport obstruction; preserve any correct earlier gate and report it.
**Outcome A:** only independently new noncircular consequences for hypothetical FLT7 solutions beyond the classical finite-digit theorem, not from polynomial congruence construction alone.

**STOP after Step028.** No all-k **ideal** valuation theorem, cyclotomic K³ claim, q-adic completion, Eisenstein/cyclotomic integral map, new signed-depth packet, principalization, unit-class lifting, primitive Fermat descent or unconditional FLT7 closure.
