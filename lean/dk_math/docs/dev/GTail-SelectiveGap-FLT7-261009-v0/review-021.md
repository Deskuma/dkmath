# Review 021 — six nontrivial seventh-root prime slots

Date: 2026-10-10
Branch: `feature/GTail-SelectiveGap-FLT7-261009-v0`
Decision: **APPROVED — Step 021 COMPLETE / Outcome B**

## Material and verification scope

Inspected GitHub pushed sources:
- `DkMath/FLT/Seven/GTailCyclotomicSixRootOrbit.lean` (152 lines);
- `DkMathTest/FLT/Seven/GTailCyclotomicSixRootOrbit.lean` (109 lines);
- `report-021.md`, `source-inventory-021.md`;
- Step 020 packet-free kernel owners and the existing degree-six carrier, including its *actual* six-integral-coordinate additive equivalence.

**Static GitHub proof-route/source audit only.** Codex reports final successful focused builds of the new production/test targets, Step 020 and Step 019 regressions, 24 Lean examples and 18 public symbol axiom printouts. These were **not independently rerun** by the reviewer.

## Findings

1. `sixSlotRoot r i := r^(i.val+1)` with `i:Fin 6` has the intended exponent range 1..6. `seventhRoot_orderOf` uses the **prime-exponent** `orderOf_eq_prime` with `r^7=1`, `r≠1`. No q-prime hypothesis is added to the pure order arguments unnecessarily.
2. `sixSlotRoot_pow_seven`, `sixSlotRoot_ne_zero`, `sixSlotRoot_ne_one` have explicit appropriate hypotheses. The injectivity proof uses Mathlib `pow_injOn_Iio_orderOf` with both exponents strictly below order seven, rather than illegitimate monoid cancellation. Thus the six supplied nontrivial seventh roots are genuinely distinct.
3. `sixRootKernel` specializes Step 020's **actual degree-six kernel** using the proved root certificates. Maximality, primality, integer ideal contraction `(q)` and quotient cardinal q are **reused** as specializations, not reconstructed from unproved assertions.
4. `sixRootKernel_ne` applies the already verified Step 020 actual separating-element witness to the injective powered roots. Pairwise `sixRootKernel_sup_eq_top` uses genuinely maximal unequal ideals and the checked Mathlib `Ideal.isCoprime_of_isMaximal` theorem. Nothing about the *intersection of all six kernels* is smuggled into this proof.
5. `gtailCyclotomicLinearFactor_mem_sixRootKernel_iff` combines Step 020's exact zero-iff-root criterion with injectivity and `sixSlotRoot r 0=r`. The source proof repairs a tempting overbroad rewrite that would also rewrite the root base. Separate slot-zero membership and five-other-slot exclusion use exactly this checked iff. Conditions q∤c,g and q|GTail are all visible; q|Q, Fermat equation and signed packets are not required.
6. At q43,r11, the six root values are `[11,35,41,21,16,4]`. Evaluation of F(9,4) through the actual six RingHoms gives `[0,42,31,39,41,20]`, and tests verify the all-index membership iff and unique-index existence. The first value alone is zero. Numerical (q|Q,T) does not fabricate an exact FLT7 solution: `¬Fermat7Equation 5 8 9` is explicitly checked.
7. q13 Gap, q7 ramified and q3/q5 **separate degree-two Eisenstein** exceptions are not confused with the new degree-six six-root orbit. F(0,0)=0 belongs to every slot, confirming the q∤c uniqueness guard cannot simply be dropped.
8. The report honestly defers classification of *all* nontrivial seventh roots (beyond the explicitly constructed six), Galois covariance, intersection with the scalar ideal, full six-ideal product, exact ideal exponents and descent. The existing signed-packet `Fin 3` real-Galois phase construction is not passed off as identical to the new bare-root `Fin 6` indexing.
9. Codex's final logs record production/test exit 0, Step 020 and Step 019 regressions exit 0, 18 public declarations with standard-only axiom lists, and no added `sorry`, `admit`, new `axiom`, `unsafe`, `native_decide` or import cycles in the new owners. An intermediate `rw` orientation failure was corrected without weakening the theorem.

## Outcome and next mathematical gate

**APPROVED — Outcome B**. The six explicit degree-one prime slots are legitimate and pairwise comaximal, and the natural Tail linear factor belongs to **exactly one slot**. There is still no proof that their intersection or product equals the scalar principal ideal in the degree-six ring.

The exact degree-six carrier already has a particularly helpful proven source:

```text
SevenCyclotomicDegreeSixInt.coordinates :
    Ring ≃+ (Fin 6 → ℤ)
SevenCyclotomicDegreeSixInt.rankOverIntegers_eq_six :
    Module.rank ℤ Ring = 6
SevenCyclotomicDegreeSixInt.ofReal_alpha :
    ofReal alpha = 1 + zeta + zetaInv
```

A proposed Step 022 is a **finite interpolation/coordinate reconstruction** gate: express arbitrary six integral source coordinates as a polynomial in the scalar seventh root of degree at most five after reducing by the geometric sum. Evaluate at six distinct roots. Six zeros in a field force the degree-at-most-five polynomial to vanish; then an **integrally invertible basis-change matrix** should recover vanishing of the six original coordinates modulo q. Finally equate common kernel membership with scalar q-divisibility, thereby proving the intersection ideal identity `⨅ i, K_i = (q)`. Pairwise comaximality could then provide `∏ i, K_i = (q)` by a **separate** finite-ideal theorem.

An independently calculated candidate change-of-basis matrix, taking coefficient order `(re.fst,re.snd,re.thd,im.fst,im.snd,im.thd)` to coefficients of powers 0..5 of ζ, is:

```text
[ 1  0  1  0  1  1 ]
[ 0  0  0  1  1  2 ]
[ 0 -1 -1  0  1  1 ]
[ 0 -1 -2  0  0  0 ]
[ 0 -1 -2  0  0 -1 ]
[ 0 -1 -1  0  0 -1 ]
det = -1  (independent symbolic calculation; NOT a Lean result)
```

This matrix follows from `alpha=1+ζ+ζ^6` and `1+ζ+...+ζ^6=0`; its signs and *all six evaluation formulas must be checked in Lean before any downstream claims*. The symbolic determinant alone does **not** prove any ideal equality. Step 022 should separate: (A) genuine carrier polynomial reduction and invertible coordinate change, (B) six-root interpolation, (C) exact intersection, (D) optional product. Stop honestly at the first failed gate. No new ring, artificial UFD/class assumptions or signed packet fabrication.

No PR/merge/facade promotion or unconditional FLT7 inference is authorized.
