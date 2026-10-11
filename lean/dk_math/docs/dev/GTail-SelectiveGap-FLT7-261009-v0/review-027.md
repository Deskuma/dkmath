# Review 027 — native GTail one-step Taylor lift and unique first correction

Date: 2026-10-10
Branch: `feature/GTail-SelectiveGap-FLT7-261009-v0`
Decision: **APPROVED — Step 027 COMPLETE / Outcome B**

## Reviewed source and verification boundary

GitHub static source inspection of:
- `DkMath/FLT/Seven/GTailCyclotomicTailTaylorLift.lean` (167 lines);
- `DkMathTest/FLT/Seven/GTailCyclotomicTailTaylorLift.lean` (127 lines);
- `report-027.md` and `source-inventory-027.md`;
- prior Step 026 formal polynomial derivative and selected-cofactor theorem; Step 025 exact square-depth equivalence;
- existing neutral `DkMath.Lib.NumberTheory.PolynomialHenselDigit.lean` on this feature branch, whose `polynomial_powLift_iff` and `existsUnique_polynomial_powLift_digit` already implement finite-depth Hensel digits for arbitrary integer polynomials.

**Reviewer did not independently execute Lean.** Codex reports sequential focused final source/test builds and Steps 026/025 regressions successful, 25 checked examples, 16 public axiom audits confined to standard `propext`, `Classical.choice`, `Quot.sound`. Intermediate elaboration failures and repairs are disclosed.

## Proof audit

1. `gtailDerivativeInt` is the **integer** evaluation of the exact existing native GTail shell formal derivative, not a real analytic derivative or an arbitrary replacement polynomial.
2. `tailShellPoly_integer_taylor` proves an actual universal **integer** divisibility `h² | G_c(x+h)-G_c(x)-h*G_c'(x)` using an explicit integral polynomial quotient witness verified by `ring`. It supports signed c,x,h and includes h=0; neither prime nor q-unit premises are secretly assumed.
3. `gtail_integer_taylor` substitutes x=c+g, h=q*d and uses the prior `tailShellPoly_eval_nat` to obtain the **original native** GTail shift modulo q² for all naturals q,c,g,d, including q=0/d=0 boundaries. The factor h²=q²*d² is accounted for by an integer witness.
4. `gtailDerivativeInt_cast` proves the actual integer-to-ZMod derivative transport by expanding the finite shell and casts. It does not mistake integral and finite-field polynomial types for definitional equality.
5. `gtail_lift_sq_iff_linear` uses the real integer equation T=q*(T/q), the integer Taylor witness and nonzero prime q to cancel a scalar factor **in integers**, before translating a q-divisibility claim into zero in ZMod q. No invalid cancellation of nonunit q in ZMod(q²) occurs.
6. `gtailFirstCorrection := -(T/q)/D` is a bare definition, while existence/uniqueness theorems require q-prime, q∤c,g, q|T; D≠0 is inherited from Step 026's actual selected-cofactor derivative identity and nonvanishing. `gtail_lift_sq_iff_correction` correctly states uniqueness **modulo q**, not uniqueness among all natural d. `gtail_first_correction_lifts` uses the representative `.val`.
7. Shift adapters show g+q*d and g have equal residue, gap q-unit status, same canonical Tail ratio, same derivative and q-divisible Tail. They do not rewrite inside dependent ideal proofs or manufacture a signed root packet.
8. The concrete q43,c9,g4 example proves starting T=14491387, m mod43=18, D=28, unique correction δ=27, resulting g=1165 and q²|T(1165). The actual six factor-square inclusions are then derived via Step 025's **generic theorem**, not a finite ZMod shortcut. d=26,0 are excluded, d=70 is included since 70≡27 (mod43).
9. Existing `PolynomialHenselDigit` already has the general mechanism for any positive finite depth and integer polynomial. The Step027 contribution is a **native GTail and selected cyclotomic ideal-square typed adapter**, not a newly discovered/general Hensel theorem. This distinction is correctly reported.
10. Final production/test source adds two definitions and fourteen theorems, no added axioms, placeholders, unsafe operations or cycles in the checked local owner closure. No global complete build was asserted.

## Boundaries and Step 028 recommendation

**APPROVED — Outcome B.** One-step digit selection is kernel checked. This does not prove any Fermat7 impossibility, an integral Eisenstein-to-cyclotomic map, full p-adic convergence or all-k equality between natural Tail valuations and bare-root prime-ideal exponents.

For the next step, prefer a **single k=2 native adapter to existing `PolynomialHenselDigit`** instead of duplicating its general induction. The source theorem
`existsUnique_polynomial_powLift_digit (P:ℤ[X]) (q k:ℕ) (x:ℤ)`
requires q prime, 1≤k, q^k|P.eval x and q∤P.derivative.eval x. This exactly matches the native polynomial P=tailShellPoly(c:ℤ), x=c+g at k=2 under q²|GTail and q∤c,g. A new lean theorem should transport its `Fin q` next digit to `g+q²*d` for **q³ divisibility**, and explicitly compare the unique digit with the linear correction `-(T/q²)/D` modulo q. It must not reprove a new generic Hensel induction.

Independent arithmetic feasibility check (**not Lean evidence**): at q43,c9,g1165, `T/q² mod43=40`, `D=28`; unique digit `d=17` solves `40+17*28=0 mod43`. The natural next gap is `1165+43²*17=32598`, with q³|T(32598) (to be checked by Lean). d=60 is the same residue class; d=0 and d=16 should not lift. Retain unchanged first-order canonical ratio11 and derivative28. This advances the actual arithmetic to a **third scalar divisibility level** while keeping source/power comparisons separate and avoiding a general K³ theorem.

A different next task — identifying bare-root K³ memberships with q³|T — is **not** implied by this scalar one-step correction. That would need new ideal-power contraction or appropriate local ideal structure and is deliberately deferred.

No PR, merge, facade promotion or FLT7 descent claim.
