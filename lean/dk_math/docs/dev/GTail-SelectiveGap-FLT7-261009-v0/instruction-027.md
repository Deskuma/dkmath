# Instruction 027 — one-step GTail Taylor correction and unique lift to q²

Date: 2026-10-10
Target branch: `feature/GTail-SelectiveGap-FLT7-261009-v0`
Working directory: `lean/dk_math`
Prerequisites: `review-026.md`, `report-026.md`, `source-inventory-026.md`.
**Scope: Step 027 only — a first-order integer Taylor congruence for the native GTail polynomial, then existence and uniqueness of the correction modulo a prime q that raises Tail divisibility from q to q².** No full Hensel lemma, all-k ideal valuation, q-adic completions, signed-root packet synthesis, Fermat solution or descent.

## Mathematical objective

Step026 proved a genuine formal derivative for the original seventh GTail homogeneous shell

```text
G_c(X) := tailShellPoly c = Σ_(j=0)^6 X^(6-j)*c^j
T_c(g) := GTail 7 1 g c = G_c(c+g), for c,g:ℕ.
(X-c)*G_c(X)=X^7-c^7
G_c(X)+(X-c)*G_c'(X)=7*X^6
```

For prime q and natural c,g with q∤c,g and q|T_c(g), Step026 gives a nonzero **field derivative**

`D := G_(c:ZMod q)'((c+g):ZMod q) ≠0`,

via the proven formula `D=7*(c+g)^6/g` and the existing nontrivial seventh-root Tail contract. Step025 separately gives the **exact second-ideal-power** characterization

`F_i(c,g)∈K_assigned² ↔ q²|T_c(g)`.

We now have two checked q43 Tail inputs:
- c=9,g=4: T=14491387, q=43 divides T but q² does not; D=28.
- c=9,g=1165: T=2638461449052811747, q² divides T; D=28.

**New conjectured explanatory relation to prove in Lean (do not treat as done):** since `1165=4+43*27`, a unique correction d=27 mod43 raises the q-local valuation by at least one while retaining the same residue root and derivative.

### Exact mandatory target

Define the genuine **integer derivative value** (not merely a modular derivative)
`Dint(c,g) := (tailShellPoly (c:ℤ)).derivative.eval (((c+g):ℕ):ℤ)`.

For natural q,c,g,d, prove the arithmetic modular Taylor statement

```text
(q:ℤ)^2 ∣
  (GTail 7 1 (g+q*d) c : ℤ) -
  (GTail 7 1 g c : ℤ) -
  ((q*d:ℕ):ℤ)*Dint(c,g).
```

This is an **exact divisibility theorem in ℤ** (or an equivalent clearly stated ModEq). It does not require prime q or q|T. It follows because all Taylor remainder terms carry at least two powers of the increment h=q*d. Every sign/cast must be correct for arbitrary g,d including zero.

Now under prime q, q∤c,g and q|T_c(g), let `m := T_c(g)/q : ℕ`. Convert the Taylor theorem into a **field-linear iff** valid for every d:ℕ:

```text
q² ∣ GTail 7 1 (g+q*d) c
  ↔ ((m:ℕ):ZMod q) + (d:ZMod q)*D = 0.
```

The quotient m is legitimate because `q|T_c(g)` and prime q≠0. Convert integer divisibility / ZMod casts with source-checked APIs, not by assuming informal cancellation of q in \`ZMod (q²)\` (q is NOT a unit there).

Since D≠0 in the field `ZMod q`, define the **unique correction residue**

`δ := -(m:ZMod q) / D`,

prove
`(m:ZMod q)+δ*D=0`
and for every d:ZMod q, that equation implies d=δ. For the actual lifted natural representative `d=δ.val`, obtain

```text
q² ∣ GTail 7 1 (g+q*δ.val) c.
```

The theorem is a *one-step* correction for a native GTail input, not a construction of an integral solution of the Fermat7 equation or a q-adic root of an arbitrary polynomial. The starting q-divisibility and q-unit premises remain explicit. The shifted g still satisfies q∤(g+q*d); its ratio and derivative remain equal modulo q to those of the starting input.

## Phase 0 — inspect the actual sources and APIs

Read exact signatures:
- `DkMath.FLT.Seven.GTailCyclotomicTailDerivative`: `tailShellPoly`, `tailShellPoly_eval_nat`, formal derivative, balance/formula and cofactor nonzero;
- `GTailCyclotomicTailDepthTwo`: actual second-power iff and both q43 calibrations;
- `GTailCyclotomicTailFactorProduct`: universal natural shell and six-factor element identity;
- `DkMath.Lib.Cosmic.GTailCyclotomic`, original depth-one native GTail;
- Mathlib \`Polynomial.eval_add\`, \`Polynomial.derivative\`, \`ModEq\`, \`ZMod.natCast_eq_zero_iff\`, \`Int.emod\`, \`Nat.dvd_div_iff_mul_dvd\`, integer/natural modulus casts, elementary Taylor divisibility lemmas; verify names with source and \`#check\`.
- Existing DkMath GN/GNomonic/Power derivative APIs for an *exact overlap* only; do not import analytic real-derivative packages or broaden task.

Write `source-inventory-027.md` naming the exact owner, derivative carrier ℤ versus ZMod q, how q² divisibility is transported without dividing q modulo q², and the minimal direct import plan.

Suggested new owner `DkMath/FLT/Seven/GTailCyclotomicTailTaylorLift.lean` importing Step026 directly plus targeted Mathlib modules only. A neutral generic polynomial Taylor lemma is optional if it is truly useful and does not induce neutral→FLT owner imports. No full FLT facade or heavy signed-valuation owner imports.

## Phase 1 — rigorous integer Taylor congruence

Primary proof gate: for arbitrary natural q,c,g,d, the **integer** Taylor difference is divisible by q². Suggested routes:

- Prove for arbitrary integral polynomial f (or just the finite 7-term G_c) that
  \`h² ∣ f(x+h)-f(x)-h*f'(x)\` in ℤ. This is a universally valid first Taylor remainder identity for integer coefficient polynomials. Then take \`x=c+g\`, \`h=q*d\`, and use \`tailShellPoly_eval_nat\`.
- Or prove the six finite monomial remainder divisibilities
  \`h² ∣ (x+h)^n-x^n-n*h*x^(n-1)\` for the exponents n≤6, and sum with coefficients c^j. Handle n=0, 1 without invalid predecessor rewriting. An explicit expansion with \`ring\` and a checked polynomial quotient is acceptable.
- Or apply a verified existing Mathlib polynomial \`derivative\`/evaluation mod-square lemma with its real premises.

Do not “prove” this using only an equality in \`ZMod q\`: **mod q loses the first-order correction term**. Work in integers or \`ZMod (q²)\` first, preserving the term q*d*Dint.

Mandatory boundary regressions: d=0, q=0 (if retained in generic lemma), c=0, g=0, and an arbitrary signed coefficient polynomial if generalized. q=0 in the full integer theorem is valid since h=0 and remainder=0, but later division/unique correction theorems require prime q.

Build this source gate independently before proceeding. If the generic integer Taylor theorem is too heavy, keep the narrow degree-six GTail specialization provided the proof is genuinely universal in q,c,g,d.

## Phase 2 — exact q² iff and derivative transport

From prime q, hT:q|T, set m=T/q. Prove the iff

`q²|T(g+q*d) ↔ (m:ZMod q)+(d:ZMod q)*D=0`.

Useful intermediate theorem: a natural/integer `N` with \`q|N\` satisfies \`q²|N ↔ ((N/q):ZMod q)=0\`. To relate the original Taylor congruence to the quotient by q, use integer **cancellation on exact multiples**, not a claimed ring-field division by \`(q:ZMod (q²))\`.

Prove the reduction of Dint(c,g) into ZMod q equals Step026's already defined
`(tailShellPoly (c:ZMod q)).derivative.eval ((c+g):ZMod q)`,
or source-check the correct \`Polynomial.map\`/derivative/evaluation commute lemma. Do **not** casually identify the ℤ polynomial and the finite-field polynomial as definally equal.

Keep the correct q∤g and q∤c hypotheses for field derivative nonvanishing. Only the integer Taylor theorem is unguarded.

## Phase 3 — unique first correction, not a hidden full Hensel lemma

Show \`D ≠ 0\` from the existing Step026 \`gtail_shell_derivative_formula\` plus \`gtail_selected_cofactor_ne_zero\`/the equality between derivative and selected cofactor, or the direct checked unit product. No extra q≠7 assumption is needed if derived from Tail's nontrivial seventh root, but retain an explicit guard only if Lean API budget makes it necessary and document the strengthening.

Define the correction `δ=−m/D:ZMod q`. Prove:
- \`m+δ*D=0\`;
- uniqueness of δ among all residues in ZMod q;
- the chosen natural representative \`δ.val\` gives q²|T(g+q*δ.val);
- the shifted g is congruent to g modulo q, keeps q∤g, keeps q|T, and yields the **same** canonical Tail ratio and derivative/cofactor residues in ZMod q.

The last ratio/derivative invariance theorem is a useful thin adapter, **not mandatory** if it requires significant dependent proof-certificate rewrites. Prefer typed scalar equalities over rewriting inside dependent ideal definitions.

A combined exact theorem
`q²|T(g+q*d) ↔ (d:ZMod q)=δ`
is desirable after both iff and uniqueness compile. It characterizes **all natural corrections** and their residue class, not just existence.

## Phase 4 — decisive q43, c9 calibration

Starting from q43,c9,g4:
- confirm \`T=14491387\`, q|T and q²∤T;
- q-quotient residue `m=T/43≡18 (mod43)`;
- source derivative residue `D=28` from Step026;
- solve `18+d*28=0` in ZMod43 to get **d=27**;
- \`g'=4+43*27=1165\`, and the unique-correction theorem gives `43²|GTail 7 1 1165 9`;
- q∤9,g' and same canonical ratio11/derivative28; Step025's **generic** theorem then yields all six actual factors `F_i(9,1165)∈K_(sixInverseSlot i)²`.
- for d=0, the iff correctly excludes 43²|T(4); for another d≠27 mod43, show the iff excludes depth two; this is necessary to verify **uniqueness**, not merely existence.
- The source natural tuple is not an exact Fermat7 solution. No complete p-adic root or solution of a global Diophantine equation is asserted.

Optional extra prime/test only if easy and satisfiable; do not invent GTail support data or break the focused build budget.

## Phase 5 — deliverables, stopping and classification

Required:
- `DkMath/FLT/Seven/GTailCyclotomicTailTaylorLift.lean`;
- `DkMathTest/FLT/Seven/GTailCyclotomicTailTaylorLift.lean`;
- `source-inventory-027.md`, `report-027.md`;
- truthful post-026 `ROADMAP.md` addition, not a rewrite of older reports.

Run sequential focused production/test builds and Step026/025 regressions with process-local `LEAN_NUM_THREADS=2`. Record each phase gate, exact commands/exit codes and repairs, checked source theorems, all new public \`#print axioms\`, import closure and no neutral→FLT cycles, no placeholder/new axiom/unsafe, 43-adic calibration and numerical guard failures. Do not full-rebuild DkMathTest or raise global limits. No edits of existing source owners, public facades, signed-depth packet files, old valuation or theorem ledgers; no PR or merge.

**Outcome B expected:** a genuine first-order Taylor congruence over ℤ, q²-divisibility criterion and **unique one-step q-adic correction** for the native GTail branch. This explains the observed g4→g1165 case without proving an arbitrary Hensel theorem, exact ideal depths beyond two, unit-class extraction or FLT7 impossibility.
**Outcome C / partial:** missing integer Taylor congruence, misuse of field division modulo q², failed derivative base-change, or an incorrect unique correction premise; report an exact obstruction/counterexample, retain earlier checked gates.
**Outcome A:** only for an independently compared noncircular restriction on hypothetical positive primitive Fermat7 solutions, not for the classical Taylor/Hensel correction mechanism.

**STOP after Step027.** No all-k induction, q-adic completeness, generalized Hensel lifting, K-adic valuation equality, cyclotomic/Eisenstein integer map, signed-depth packet reconstruction, principalization, unit powers, primitive next Fermat tuple, or FLT7 descent.
