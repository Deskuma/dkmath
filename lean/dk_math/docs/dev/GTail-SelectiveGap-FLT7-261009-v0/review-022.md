# Review 022 — six-root interpolation and exact scalar ideal splitting

Date: 2026-10-10
Branch: `feature/GTail-SelectiveGap-FLT7-261009-v0`
Decision: **APPROVED — Step 022 COMPLETE / Outcome B, including optional six-ideal product**

## Evidence and scope of verification

Inspected pushed GitHub sources and reports:
- `DkMath/FLT/Seven/GTailCyclotomicSixRootInterpolation.lean` (156 lines);
- `DkMathTest/FLT/Seven/GTailCyclotomicSixRootInterpolation.lean` (122 lines);
- `report-022.md`, `source-inventory-022.md`, earlier Steps 019–021 and the actual `SevenCyclotomicDegreeSixInt.coordinates` source.

Review is **static source/proof-route inspection**, not an independent local Lean rebuild. Codex reports successful focused production/test (including the mandatory intersection and optional product gates), Step 021/020 test regressions, 24 examples, and 15 new public declaration axiom inspections with no nonstandard/sorry axioms. Earlier failed elaborations are documented and corrected without weakened theorems.

## Mathematical audit

1. The existing source is the **actual** `SevenCyclotomicDegreeSixInt.Ring = QuadraticAlgebra SevenRealCubicInt (-1) (alpha-1)`; its additive equivalence `coordinates : Ring ≃+ (Fin 6→ℤ)` gives six signed integral coordinates in the declared order `(re.fst,re.snd,re.thd,im.fst,im.snd,im.thd)`.
2. `sixPowerCoefficients` and `sixPowerCoordinates` are explicit integer-formula maps. Both compositions are proved equal to the identity **for every commutative ring** using per-index polynomial arithmetic. No unproved determinant, q-unit, rational inverse or floating-point matrix lemma is used.
3. `sixPowerPolynomial q z` is a genuine `Polynomial (ZMod q)` constructed from six integer-linear combinations of the actual signed coordinates. Coefficients and `natDegree≤5` are proved using existing Polynomial APIs.
4. `evalCyclotomic_eq_sixPowerPolynomial` identifies the actual packet-free degree-six `RingHom` evaluation at any supplied **nontrivial** seventh root with this degree≤5 polynomial. The proof uses the checked inverse relation `s⁻¹=s⁶`, `s⁷=1`, the seven-term geometric sum zero, and an explicit `linear_combination` certificate on arbitrary signed coordinates. It is not a q43-only calculation.
5. `mem_all_sixRootKernel_iff_coordinates_zero` combines Step 021's six distinct scalar roots with Mathlib `Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero`; a polynomial of degree≤5 vanishing at six distinct field elements is zero. Actual coefficient extraction and the **proved** inverse coefficient map recover all six signed coordinates as zero in `ZMod q`. The reverse direction is also checked.
6. `coordinates_natCast_mul` separately proves multiplication by the embedded natural scalar acts coordinatewise; additive equivalence alone would not license this. `mem_cyclotomicScalarIdeal_iff` constructs the **actual integral ring quotient element** via `coordinates.symm` to characterize membership in the principal scalar ideal by six integer divisibilities, for any natural q and arbitrary signed source element.
7. `iInf_sixRootKernel_eq_scalarIdeal` is an **arbitrary-element ideal extensionality theorem** converting common kernel membership into all-coordinate q-divisibility and then the scalar principal ideal. It is neither a sample calculation nor an assertion about the distinct degree-two Eisenstein or integer-ring ideals.
8. **Only after** the intersection theorem was built, `prod_sixRootKernel_eq_scalarIdeal` invokes `Ideal.prod_eq_iInf_of_pairwise_isCoprime` with Step 021's actual pairwise maximal/comaximal kernel theorem. The Finset-universal-product / iInf bridge is explicit. Thus both checked generic endpoints hold:

```text
(⨅ i:Fin 6, sixRootKernel r hr0 hr7 hr1 i)
  = cyclotomicScalarIdeal q
(∏ i:Fin 6, sixRootKernel r hr0 hr7 hr1 i)
  = cyclotomicScalarIdeal q
```

for prime q with a supplied root r satisfying r≠0, r^7=1 and r≠1; they do **not** assert a root for arbitrary prime q.
9. The q43 regressions use signed coordinates `⟨⟨−2,3,−4⟩,⟨5,−6,7⟩⟩`, verified transformed coefficients `[-5,13,2,5,-2,-6]` and field-evaluation values `[17,29,11,18,34,21]`. The signed scalar multiple `ofReal(-43)+zeta*ofReal86` is in all six kernels and scalar (43). The actual Tail linear factor `F(9,4)` is only in the first kernel, hence **not** in the all-six intersection or product and not scalar-divisible by 43. There is no contradiction with q|GTail: the Tail polynomial and the *individual factor* are different ring elements.
10. q=13 Gap branch and q=7 characteristic-seven exception remain properly guarded. The finite q43 sample explicitly fails `Fermat7Equation 5 8 9`. No class group, exact ideal valuations, Eisenstein-to-cyclotomic integer ring map or Fermat descent was inferred.
11. Codex's recorded 15 axiom lists contain only `propext`, `Classical.choice`, `Quot.sound` as applicable; no `sorryAx`/extra axioms. Neutral→FLT owner direction and new-module import graph are reported clean, alongside source placeholder/unsafe/whitespace scans. No independent full Lean build was performed.

## Mathematical scope / next frontier

**APPROVED — Outcome B.** We have the correct **conditional six-prime splitting of a scalar q** in the existing degree-six cyclotomic order. The roots are explicitly supplied; q may not be seven and no admissible r is produced from an arbitrary q. The theorem does not yet classify all prime ideals of the order or measure exact powers of each K_i inside a general element.

The highest-value next task is to reconnect this six-slot machinery to the **original exact GTail polynomial**, instead of accumulating unneeded abstract quotient infrastructure:

```text
F_i(c,g) := ofReal(c+g) - zeta^(i+1)*ofReal c
candidate: ∏ (i:Fin6), F_i(c,g)
       = ofReal ((GTail 7 1 g c : ℕ) : SevenRealCubicInt)
```

This is the classical homogeneous seventh cyclotomic factorization, but needs to be **independently proved in this actual integral carrier** for all naturals c,g, including g=0. A proof may use the existing `zeta_isPrimitiveRoot` and a verified cyclotomic-polynomial/geometry identity, or explicit integral-coordinate algebra. Source-inspect existing generic cyclotomic factorization theorems first to avoid duplication. Evaluate each F_i at Step 021's six roots: the factor/index alignment is a **permutation** governed by §(i+1)(j+1)≡1 mod7§, **not** the naive diagonal i=j. This would give an exact, typed six-factor bridge from GTail to the preexisting cyclotomic prime slots, without asserting principalization or descent.

Alternatively, an exact CRT equivalence §R/(q) ≃+* (Fin6→ZMod q)§ now looks feasible from Step 022's interpolation; it is optional future infrastructure, not required before checking the Tail product identity.

No PR/branch merge/facade promotion or unconditional FLT7 closure is authorized.
