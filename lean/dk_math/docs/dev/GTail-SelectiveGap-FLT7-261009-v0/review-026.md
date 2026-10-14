# Review 026 — formal GTail derivative and selected cyclotomic cofactor

Date: 2026-10-10
Branch: `feature/GTail-SelectiveGap-FLT7-261009-v0`
Decision: **APPROVED — Step 026 COMPLETE / Outcome B**

## Review scope and verification level

Static GitHub source/proof-route review:
- `DkMath/FLT/Seven/GTailCyclotomicTailDerivative.lean` (204 lines);
- `DkMathTest/FLT/Seven/GTailCyclotomicTailDerivative.lean` (163 lines);
- `report-026.md` and `source-inventory-026.md`;
- prior Step 023 actual six-factor element product, Step 025 actual selected cofactor and exact second-level membership, Steps 018–022 root kernels.

This reviewer **did not independently run Lean**. Codex reports final successful focused builds of production/test and Step 025/024 regression tests, 33 checked examples, seventeen public axiom audits confined to `propext`, `Classical.choice` and `Quot.sound`, and no introduced axioms or placeholders.

## Audited mathematical statements and proof contracts

1. `tailShellPoly c := Σ j:Fin7, X^(6-j.val) * C (c^j.val)` is a genuine `Polynomial A` for arbitrary `CommRing A`. Its evaluation at `c+g` is identified, with correct natural casts, with the **existing native** `GTail 7 1 g c`. This is not an unrelated substitute definition.
2. `tailShellPoly_mul` proves `(X-C c)*G_c = X^7-C(c^7)` by actual polynomial expansion for all commutative rings. `tailShellPoly_derivative_identity` differentiates **in X, holding c constant**, using true `Polynomial.derivative` APIs; hence `G_c+(X-Cc)*G_c' = 7 X^6`. No unjustified division by a gap or `X-c` occurs.
3. `gtail_shell_derivative_balance` specializes the identity at `X=c+g` **only after** q|GTail is converted into a polynomial zero in ZMod q. The division theorem `gtail_shell_derivative_formula` additionally requires q∤g and explicitly proves g nonzero in the field. The derivative formula itself does **not** need q∤c; this tighter contract is preserved.
4. The **private** universal homogeneous six-factor certificate is rechecked by Lean as a polynomial algebra `linear_combination` proof rather than imported as an unavailable private theorem or turned into an axiom. `tailShellPoly_eq_root_product` is an actual polynomial identity, not merely equality after one finite-field evaluation. It assumes the seven-term geometric sum vanishes, with correct factor powers 1..6.
5. `tailShellPoly_derivative_eq_erased_product` uses the genuine polynomial derivative product rule after removing one selected linear factor and proving it evaluates to zero. The theorem does not require unwarranted pairwise distinctness for this purely formal identity.
6. `eval_selected_cofactor_eq_tailShellPoly_derivative` correctly distinguishes **factor index i** from **receiving kernel index sixInverseSlot i**. Actual source-ring RingHom evaluation maps the five other integral factors to the five corresponding polynomial root factors; this is a checked bridge, not a conclusion from ideal membership alone.
7. `gtail_selected_cofactor_balance`, `gtail_selected_cofactor_formula`, and `gtail_selected_cofactor_uniform` prove for all six selected slots that the *actual source cofactor* evaluates to `7*(c+g)^6/g` in ZMod q. `gtail_selected_cofactor_ne_zero` verifies all relevant units: q∤g, q∤c, canonical r≠0 so c+g≠0, and q≠7 from the nontrivial seventh-root assumption. Nonvanishing does not rely on reusing the old prime-factor cofactor exclusion theorem.
8. Both q43 c9/g4 and c9/g1165 examples yield cofactor residue **28 uniformly over six indices** and polynomial derivative 28. They simultaneously retain respectively `F_i∉K_i²` and `F_i∈K_i²` (the previously checked Step 025 theorem). This demonstrates why **a simple root of the finite-field polynomial is compatible with deeper ideal membership for the chosen input element**; no root-lifting or new exact ideal valuation is claimed.
9. q7 root degeneracy, gap=0, c=0 and q13 Gap-only boundaries are tested separately. For zero rings or characteristic collapse, the arbitrary-CommRing polynomial identity is **not** described as a statement that the polynomial has degree exactly six.
10. The new FLT owner imports only Step 025 and targeted Polynomial derivative Mathlib; tests import the new owner. Codex reports standard-only public axioms, no `sorry`, `admit`, new `axiom`, `unsafe`, `native_decide`, `False.elim`, unexpected full FLT facade, reverse neutral→FLT owner import, or new cycles in the scanned closure. Existing source/ring/signed-packet files were not edited.

## Mathematical scope and recommended Step 027

**APPROVED / Outcome B.** This is an actual, reusable **formal-derivative/cofactor readout** of the original degree-seven GTail, not an analytic derivative in a continuously variable natural number, Hensel lifting, an all-k prime-ideal valuation theorem or a new obstruction to Fermat7.

The two q43 examples suggest a narrowly bounded and genuinely new **first Hensel/Taylor correction**, before attempting full q-adic/Hensel infrastructure:

Let `T_c(g)=GTail 7 1 g c = G_c(c+g)` as an integer-valued natural polynomial. Given prime q, natural c,g with q∤c,g and q|T_c(g), formal differentiation gives nonzero derivative residue `D=G_c'(c+g) ∈ ZMod q`. For any natural correction d, the genuine integer polynomial congruence
```text
T_c(g+q*d) ≡ T_c(g) + q*d*G_c'(c+g) (mod q²)
```
should hold. Since q|T_c(g), let `m=T_c(g)/q`; then
```text
q² | T_c(g+q*d) ↔ (m:ZMod q)+(d:ZMod q)*D=0.
```
Since D≠0, there is **one unique residue** `d:ZMod q` satisfying the equation. Its natural representative gives an explicit *one-step* square-depth correction, **not** a full Hensel lift or a new Fermat solution.

At q=43,c=9,g=4:
```text
m mod43 = 18, D=28, unique d=27,
g'=4+43*27=1165,
43²|T_c(1165).
```
This exactly explains Step 024/025's previously discovered guard-failure case and retains the canonical ratio modulo43 (r=11), along with the derivative/cofactor residue 28.

This Step 027 is a suggested **new proof target**, not a Step 026 theorem. An exact modular-Taylor source lemma and a **unique** linear equation solution in ZMod q must be independently kernel checked, with careful handling of natural/integer casts, polynomial evaluation at q² and quotient by q only when q|T. The q43 calibration must follow from the generic theorem, not substitute finite `decide` for it. No all-k induction, arbitrary Hensel lemma, `ZMod q²` ring hom from the cyclotomic ring, unit-power class or FLT7 descent is authorized.

No PR, branch merge or facade promotion authorized.
