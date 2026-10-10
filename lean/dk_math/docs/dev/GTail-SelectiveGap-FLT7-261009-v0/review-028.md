# Review 028 — native GTail k=2 Hensel digit and cubic scalar support

Date: 2026-10-10
Branch: `feature/GTail-SelectiveGap-FLT7-261009-v0`
Decision: **APPROVED — Step 028 COMPLETE / Outcome B**

## Inspection and verification limit

Static GitHub source/proof-route inspection of:
- `DkMath/FLT/Seven/GTailCyclotomicTailSecondDigit.lean` (105 lines);
- `DkMathTest/FLT/Seven/GTailCyclotomicTailSecondDigit.lean` (149 lines);
- `report-028.md` and `source-inventory-028.md`;
- earlier Step 025–027 typed Tail shell, derivative, one-digit and prime-square endpoints;
- actual existing neutral `DkMath.Lib.NumberTheory.PolynomialHenselDigit.lean`.

This reviewer **did not independently rebuild Lean**. Codex reports 28 checked examples, ten public theorem axiom prints with standard logical foundations only, final focused builds of the new source/test and Step027/026 regressions successful. Intermediate errors/fixes and repeated final audits are documented. No all-suite build is asserted.

## Audit of mathematical correctness and API ownership

1. `gtail_second_shift_eval` genuinely identifies the integer polynomial evaluation at `x+q²*d` with the **original native natural** `GTail 7 1 (g+q²*d) c`, including zero-boundary inputs. Integer/natural casts are explicitly normalized, not assumed definitionally equal.
2. `gtail_support_of_square` and `gtail_integer_square_support` transport natural q² support into the exact integer polynomial premise at k=2 and derive first q support. No primality is required for those raw support lemmas.
3. `gtail_integer_derivative_not_dvd` turns the checked Step027 integer-to-`ZMod q` derivative equality and Step026 nonvanishing into **integer nondivisibility by q**, under the explicit q-prime and c/g q-unit support premises. The derivative condition is not inferred from scalar q² support alone.
4. `existsUnique_gtail_second_digit` directly **specializes** the existing `existsUnique_polynomial_powLift_digit` from `PolynomialHenselDigit` at `P=tailShellPoly(c:ℤ)`, `k=2`, `x=(c+g:ℤ)`. The proof constructs a typed intermediate `∃! t:Fin q` and transports the **same predicate** through `gtail_second_lift_predicate`. This is not a duplicate general Hensel algorithm.
5. `gtail_second_lift_iff_linear` uses the existing `polynomial_powLift_iff` at k=2 and `Int.natCast_ediv` to move its integer quotient to the natural scalar `T/q²`. Only **after** integer divisibility does it apply the `ZMod q` zero/divisibility interface. It does not divide by q² in `ZMod(q³)`.
6. The new second-shift gap-unit, ratio and derivative lemmas specialize Step027's checked shift adapters at increment `q*(q*d)`. The canonical ratio and simple-field derivative remain invariant but no dependent ideal equality, Hensel q-adic completion or signed-root packet is fabricated.
7. Concrete q43,c9,g1165: `T/q²≡40`, derivative D=28, `40+17*28=0`, so digit 17 gives `g'=1165+43²*17=32598` and `43³|T(g')`. A checked example also shows `43⁴∤T(g')`, establishing **scalar** exact depth three only. The generic `∃!` proof excludes digits 0 and 16; a separate generic linear iff covers all natural d with residue 17, including d=60.
8. The all-six `F_i(9,32598)∈K_assigned²` regression uses the **previous Step025 theorem** after reducing scalar cubic to square support. This is not a proof of any `F_i∈K³` or `F_i∉K⁴`. The q43, g4→1165 first-digit chain is preserved.
9. Prime-seven/no nontrivial root, q13 Gap-only, degenerate c/g, and the false exact Fermat7 example remain distinct. No new global FLT7 argument has been introduced.
10. Reported source/test closure adds only the new owner and preexisting neutral Hensel owner relative to Step027, with no additional Mathlib modules, reverse neutral→FLT owner import, new cycles, placeholders, unsafe or nonstandard axioms. Existing generic Hensel code and old signed-depth owners remain unchanged.

## Scientific classification and Step029 proof opportunity

**APPROVED / Outcome B.** Step028 provides a nonvacuous *native GTail typed adapter* to a preexisting finite Hensel method. It neither proves a new general Hensel theorem nor advances beyond second power for the actual cyclotomic prime ideals.

**Recommended Step029: bounded third-power ideal receiver.** The six-fold splitting from Step022 gives `K_j * J_j = (q)`, where `J_j=∏_{h≠j}K_h` is **comaximal** with K_j by Step021. For positive n, source-check/prove the ideal intersection identity

```text
K_j^n ∩ (q) = K_j^n * J_j = (q)*K_j^(n-1).
```

Reason: `(q)=K_j J_j⊆J_j`; `K_j^n⊆K_j` for n≥1 and `K_j^n+J_j=⊤`, whence `K_j^n∩J_j=K_j^n J_j`. **This is a mathematical proof sketch, not a checked Step028 theorem.** Verify the precise ideal-inf/product identities and finite coprimality in Mathlib.

At n=2,3, with nonzero-scalar injectivity from Step024 and integer contraction `K_j∩ℤ=(q)` from Step020, this suggests a bounded **scalar contraction**

```text
(n:R) ∈ K_j^3 ↔ q³ | n.
```

The reverse is easy from embedded q∈K; the forward needs the actual intersection/product identity, principal-ideal multiplication membership and cancellation. Combining with Step025's genuine five-factor cofactor `U_i∉K_assigned`, the real product `U_i F_i = T`, and Mathlib `Ideal.IsMaximal.mul_mem_pow` at exponent 3 should yield

```text
F_i(c,g) ∈ K_assigned^3 ↔ q³ | GTail 7 1 g c,
```

under the usual canonical Tail q-unit/support conditions. This would upgrade the Step028 q43,g32598 example from scalar q³ support to **actual six-factor K³ membership**, while the g1165 example would be excluded at the third power. A fourth-power scalar/nonmembership statement is **separate** and must not be asserted merely from checked scalar `43⁴∤T`; it needs another verified level of contraction.

The proof could potentially generalize to all finite powers, but a bounded n=3 theorem is the primary next acceptance gate. Do not invent an unproved DVR, Dedekind-domain or class-group structure to obtain it.

No PR, merge, facade promotion or FLT7 descent is authorized. Branch currently has an unrelated develop divergence (one new develop commit); do not silently rebase or merge.
