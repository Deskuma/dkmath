# Instruction 026 — GTail shell derivative and uniform selected cofactor residue

Date: 2026-10-10
Target branch: `feature/GTail-SelectiveGap-FLT7-261009-v0`
Working directory: `lean/dk_math`
Prerequisites: `review-025.md`, `report-025.md`, `source-inventory-025.md`.
**Scope: Step 026 only.** Turn Step 025's checked **six identical nonzero selected-cofactor residues** into a generic theorem via a genuine polynomial derivative of the original GTail degree-seven shell. No new arbitrary ideal-adic valuation hierarchy, cyclotomic ring/class/unit transfer, signed packet reconstruction or FLT7 descent.

## The mathematical question

Step 025 now proves, for prime q and natural c,g satisfying q∤c,g and q|T, that each actual degree-six factor has the bounded squared-ideal depth

`F_i(c,g)∈K_(sixInverseSlot i)^2 ↔ q²|T`,

where `T=GTail 7 1 g c` and `K_j` is a packet-free maximal ideal from the canonical Tail root `r=(c+g)/c : ZMod q`.

It also proves that the actual other-five-factor cofactor

`U_i(c,g) := gtailCyclotomicCofactor c g i
           = ∏_(h≠i) ((c+g) - ζ^(h+1)*c)`

is **outside** K_(sixInverseSlot i). Both q43 calibrations, (c,g)=(9,4) and (9,1165), additionally show by actual RingHom evaluations that

`ev_(r^(sixInverseSlot(i)+1))(U_i)=28 ∈ ZMod43`

for **every** i:Fin6. The constant 28 is a tested instance, NOT a general theorem.

The new target is to explain this equality algebraically and differentiate the true homogeneous GTail shell, not to introduce a new polynomial unrelated to GTail.

Let over any suitable commutative coefficient ring

`G_c(X) := Σ_(j=0)^6 X^(6-j)*c^j`.

Step023 already proves `G_c(c+g)=GTail 7 1 g c` and the *source ring* factorization of this shell into six ζ-linear factors. The universal polynomial identity

`(X-c)*G_c(X)=X^7-c^7`

suggests after formal differentiation and evaluating a Tail zero mod q:

`g*G_c'(c+g) = 7*(c+g)^6.`

Because the six factors have **distinct root slots**, polynomial differentiation of their product at the selected zero suggests that the evaluated other-five-factor cofactor equals the derivative:

`ev_selected(U_i(c,g)) = G_c'(c+g).`

Therefore the key proposed theorem is

```text
(g : ZMod q) *
  eval_(selected root for i) (gtailCyclotomicCofactor c g i)
    = (7 : ZMod q) * ((c+g : ℕ) : ZMod q)^6,

and, under q∤g,

eval_selected(U_i) =
    (7 : ZMod q) * ((c+g : ℕ) : ZMod q)^6 / (g : ZMod q).
```

**These are unproved Step026 targets.** They are independent of the value of i and will imply nonzero cofactor residue if the 7, c+g and g residues are nonzero. A nontrivial seventh root rules out q=7, but prove that implication rather than silently assuming 7 is invertible.

The derivative is with respect to the **shell variable X**, holding c constant. Do not confuse it with a derivative in q, an ideal-adic valuation or a continuous derivative of the natural GTail as a function on ℕ.

## Phase 0 — source and Mathlib derivative inventory

Read exact existing signatures in:
- `GTailCyclotomicTailDepthTwo`: `gtailCyclotomicCofactor`, cofactor product and nonmembership, exact square-membership iff;
- `GTailCyclotomicTailFactorProduct`: source-ring six-factor product and `GTail_seven_one_eq_homogeneous_sum`;
- `GTailCyclotomicSixRootOrbit` / `GTailCyclotomicPrimeAddress`: six actual residues, power order=7, prime kernel and RingHom evaluation;
- `DkMath.Lib.Cosmic.GTailCyclotomic`: original degree-one tail shell, rather than an invented replacement;
- Mathlib `Polynomial.derivative`, `Polynomial.derivative_mul`, finite-product derivative, evaluation, geometric-sum factorization and polynomial factorization by roots, and `Polynomial.evalRingHom`. Verify API signatures by source/`#check`, not guessed names;
- existing GN / Cosmic derivative files only to check for a reusable exact identity. Avoid large imports for philosophical overlap.

Create `source-inventory-026.md` describing the smallest proof route, actual carrier types, existing shell source, degrees, the prime/ratio guard, and all still-missing derivative bridges.

Suggested owner `DkMath/FLT/Seven/GTailCyclotomicTailDerivative.lean` with a direct import of Step025 and a narrowly selected Polynomial Mathlib module. A separate **neutral Lib** derivative theorem is optional only if it adds a genuinely reusable uniform CommRing lemma and keeps neutral→FLT imports absent. Do not edit earlier owners, signed packet files, ring definitions or facades.

## Phase 1 — prove the formal derivative of the genuine GTail shell

Define an actual polynomial `tailShellPoly (c:ZMod q) : Polynomial (ZMod q)` as the six-degree finite sum with coefficients c^j:

```text
Σ j:Fin 7, Polynomial.X^(6-j.val) *
             Polynomial.C (c^(j.val)).
```

A generic CommRing version is welcome only if simpler.

Prove:
1. evaluation at any `x:ZMod q` is exactly the seven-term homogeneous sum;
2. the **polynomial identity**, not just values,
   `(Polynomial.X - Polynomial.C c)*tailShellPoly c
      = Polynomial.X^7 - Polynomial.C c^7`;
3. the derivative product identity, via real `Polynomial.derivative`,
   `tailShellPoly c + (X-Cc)*(tailShellPoly c).derivative
      = 7 * X^6`
   (with correct polynomial scalar casts);
4. specialize at `x=(c+g:ZMod q)` under q|GTail. Use Step023's checked natural shell identity/casts to get `tailShellPoly.eval x=0`, hence
   `(g:ZMod q) * (tailShellPoly c).derivative.eval x=7*x^6`.

No division by g is permitted until q∤g has been proved. At q=43,c9,g4 and g1165, check that the evaluated derivative has value 28 using the generic identity, not an independently assumed fact.

If an exact existing polynomial shell API is available, reuse it rather than defining a duplicate polynomial and proving equality by extensive normalization. At g=0 the formal polynomial identity still holds, but **the specialization that divides by g does not**.

## Phase 2 — identify the derivative with the selected actual cofactor

Construct a typed bridge between the **polynomial** shell and the **actual source-ring factorization** from Step023. The endpoint is for any admissible canonical Tail root and each i:Fin6:

```text
(evalCyclotomicFromSeventhRoot (sixSlotRoot r (sixInverseSlot i))
   ... (gtailCyclotomicCofactor c g i))
 = (tailShellPoly (c:ZMod q)).derivative.eval (c+g:ZMod q).
```

This is the primary new nontrivial connection and cannot be asserted solely from \`F_i∈K_j\`. A derivative-of-product identity is required.

Permissible proof routes, in order of simplicity:
- source-check a cyclotomic polynomial product theorem in `Polynomial (ZMod q)` to prove
  `tailShellPoly c = ∏_(h:Fin6) (X-C(s^(h+1)*c))`,
  then apply the actual polynomial derivative of the product and evaluate at the unique zero factor;
- specialize the known universal seventh homogeneous factor identity to polynomial variables in an appropriate commutative ring using a **reusable correctly typed generic lemma**, and apply product derivative;
- alternatively prove the evaluated cofactor identity directly from the six distinct roots and a formally verified degree≤6 polynomial equality (or a verified finite inverse-exponent calculation), then separately prove it equals the formal derivative. Do not replace the derivative endpoint with a mere unproved verbal identification.

Check the ordering carefully: i is the factor index, j=`sixInverseSlot i` is the receiving kernel, and the second-stage root is `s=r^(j+1)`. The factor vanishes exactly when `s^(i+1)=r`. Avoid erroneously using i=j for all six.

The source-ring equality of Step023 is a **value identity** for arbitrary R elements. It cannot simply be rewritten as a polynomial identity in `Polynomial (ZMod q)` without supplying the correct ring instantiation or proving a polynomial equality.

If the derivative/cofactor bridge is expensive, stop at the strongest correctly kernel-checked Phase1 theorem and report Outcome C/partial with the exact missing polynomial factorization API. Do not conceal the gap with six q43 computations.

## Phase 3 — uniform value and nonvanishing

Once Phase1 and Phase2 both compile, prove a clean universal theorem under prime q, q∤c, q∤g and q|T:

```text
g * ev_selected(U_i) = 7*(c+g)^6,
ev_selected(U_i) = 7*(c+g)^6/g,
ev_selected(U_i) ≠ 0.
```

To prove nonzero, establish:
- g≠0 and c≠0 in ZMod q from the source divisibility guards;
- X=c+g=r*c ≠0 from `r^7=1` and c≠0;
- q≠7 from the supplied nontrivial order-seven residue root (e.g. already checked orderOf and ZMod unit group cardinal), so 7≠0 in ZMod q.

If needed, prove q≠7 separately as a small reusable lemma under Tail hypotheses. Do not *add q≠7 without explanation* if it is implied by the existing roots; alternatively state it explicitly and record whether the API is weaker than mathematically possible.

Show that the new closed formula agrees with the previously proved `gtailCyclotomicCofactor_not_mem_selected`; it should **explain** the nonmember statement by an independent polynomial method, not redefine its ideal.

This derivative identity proves the selected shell root is simple **over the finite field**, but does not alone prove any power-two/power-three ideal membership or the existence of a lifted root in ZMod q².

## Phase 4 — exact nonvacuous regressions and boundaries

Mandatory q43 calibrations:

- q43,c9,g4: T=14491387, r=11, all six selected factor/cofactor evaluations as in Step025; derivative and selected cofactor must both equal **28**, and the formula `7*(13^6)/4` evaluates to 28 modulo 43.
- q43,c9,g1165: q²|T, r=11, and `g≡4 (mod 43)`. The derivative and all six selected cofactors must **still equal 28**, despite selected factors lying in K². This shows **mod-q simple polynomial root ≠ prohibition of deeper q-adic divisibility for the specific source element**; do not infer `F_i∉K²` merely from cofactor nonvanishing.
- preserve Step025's all-six signed ideal-square inclusions/exclusions for these two cases by regression, with no q43-only proof substituted for the generic derivative/cofactor theorem.
- g=0, c=0 and q7 are boundary cases for the quotient formula; the **polynomial** shell and unconditional Step023 six-factor identity remain valid.
- q13 Gap branch has no q|Tail; no chosen nontrivial root exists from that premise alone.
- the q43 tuple a5,b8 does not solve the exact Fermat7 equation. No Fermat premise is introduced in production.

Optional: a compact result relating the cofactor expression to the discriminant/simple-root condition for the seventh cyclotomic shell. Do **not** conflate root simplicity in \`ZMod q\` with a local exact ideal valuation or Hensel lifting without separate proofs.

## Deliverables and discipline

Required:
- `DkMath/FLT/Seven/GTailCyclotomicTailDerivative.lean`;
- `DkMathTest/FLT/Seven/GTailCyclotomicTailDerivative.lean`;
- `source-inventory-026.md`, `report-026.md`;
- truthful post-025 `ROADMAP.md` append, keeping historical reviews unchanged.

Build sequential focused gates with process-local `LEAN_NUM_THREADS=2`: (1) formal shell polynomial and derivative, (2) derivative/cofactor bridge, (3) uniform value/nonvanishing, (4) tests/Step025 and Step024 regressions. Record each final exit, intermediate compiler repairs, actual Mathlib APIs, all new public \`#print axioms\`, import-cycle and neutral→FLT audits, no placeholders/new axioms/unsafe, and test count. Do not launch a full clean test run or raise global resource limits.

**Outcome B expected:** a source-checked differentiated homogeneous GTail shell and a generic formula for the selected cyclotomic five-factor cofactor, explaining q43's common residue 28 and its nonvanishing. This is a **new explanatory/readout bridge**, not FLT7 descent.
**Outcome C/partial:** the derivative-cofactor bridge cannot be justified in actual polynomial/source carriers; report the exact gate and retain correct partial theorems.
**Outcome A:** only an independently new, noncircular FLT7 necessary obstruction after overlap comparison. Differential identities or simple roots alone are not A.

**STOP after Step026.** Do not introduce all-k ideal valuations, q-adic/Hensel lifting, cyclotomic class/unit powers, signed-depth packet synthesis, primitive Fermat counterexample/descent, or unconditional FLT7 closure.
