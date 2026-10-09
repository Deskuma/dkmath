# Review 015 — split Eisenstein scalar-prime ideal factorization

Date: 2026-10-10
Branch: `feature/GTail-SelectiveGap-FLT7-261009-v0`
Decision: **APPROVED — Step 015 COMPLETE / Outcome B; optional product equality verified in source**

## Evidence and review scope

Reviewed pushed GitHub sources:
- `DkMath/Lib/NumberTheory/GTailSevenSplitIdeal.lean` (137 lines);
- `DkMathTest/NumberTheory/GTailSevenSplitIdeal.lean` (147 lines);
- `report-015.md` and `source-inventory-015.md`;
- Step 014 `GTailSevenResidueIdeal`, plus upstream norm, conjugate and lattice contracts;
- existing Step 010–011 prime support/branch order receivers (for scope decisions).

**This is a static GitHub Lean code, proof-route, numerical-regression and report review.** The focused builds, 19 examples and axiom audit are Codex's recorded local runs, **not independently repeated by this reviewer**.

## Mathematical contract review

1. `eisensteinResidue_root_ne_conjugate` proves supplied roots `t` and `1-t` are distinct for a prime q≠3 using `4*(t²-t+1)=(2t-1)²+3`. Prime q is actually used to infer q=3 from the vanishing of 3 in `ZMod q`. No q=7 or FLT hypotheses are introduced.
2. `scalar_dvd_traceOne_neg_one_iff` handles **arbitrary signed integral elements** `z=⟨x,y⟩` and arbitrary integer n: divisibility by the embedded scalar n is equivalent to n|x and n|y. The quotient witness is constructed in the actual `TraceOneInt(-1)` ring; neither natural-only α nor norm divisibility is substituted.
3. `eisensteinScalarIdeal q` is literally `Ideal.span {ofInt(-1)(q:ℤ)}`. `mem_eisensteinScalarIdeal_iff` uses the correctly oriented `Ideal.mem_span_singleton`: embedded scalar q divides the element z.
4. `mem_eisensteinResidueIdeals_iff_coordinates` rewrites both kernel memberships into independent ZMod evaluations, subtracts to force the second coordinate to vanish using **field** zero-product and distinct roots, then forces the first coordinate to vanish. Integer-cast-zero iff returns q-divisibility of both integer coordinates. Both directions are supplied, with no implicit nonnegative-coordinate restriction.
5. `eisensteinResidueIdeals_inf_eq_scalar` is proved by **extensionality for every ring element**. This is more than testing the selected α and properly identifies the intersection as the scalar principal ideal.
6. `eisensteinResidueIdeals_ne_of_root_ne_conjugate` constructs the real membership witness `tau(-1)-ofInt(-1)n` from an integer lift of t. Distinct images of two ring homs alone would not suffice to prove different kernels; the source correctly gives a witness.
7. `eisensteinResidueIdeals_sup_eq_top` instantiates Step 014's verified maximality of both root kernels and uses Mathlib `Ideal.isCoprime_of_isMaximal`. `eisensteinResidueIdeals_mul_eq_scalar` applies `Ideal.mul_eq_inf_of_coprime` to this **proven** comaximality and composes with the checked intersection equality. The optional product gate genuinely passed, without a new axiom.
8. At q=43, roots 37/7 give `P37∩P7=(43)`, `P37*P7=(43)`, `P37+P7=R`. The selected α(5,8) belongs to one root kernel but not the other and does not belong to the scalar ideal. Signed-coordinate z=⟨-43,86⟩ checks generic reconstruction, not merely finite `decide`.
9. At q=5, no root was fabricated; the main theorem explicitly requires an existing root. At q=3, t=2=1-t, z=⟨1,1⟩ belongs to the common kernel but not to the scalar ideal (3). Therefore **the intersection formula without separation is false**. This example does **not** refute a standalone ramified product identity `P²=(3)`; no assertion concerning that identity has been proved or refuted in Step 015.

## Recorded tests and axiom boundary

Codex reports final successful incremental focused builds of the production and test targets and the Step 014 test regression (all final exit 0). Ten public declarations, consisting of one definition and nine theorems, have standard-only axiom lists (`[propext]`, `[propext, Quot.sound]` or `[propext, Classical.choice, Quot.sound]`). Source/graph scans found no added `sorry`, `axiom`, `unsafe`, circular FLT7 impossibility route, or reverse neutral→FLT import. A full all-test rebuild was not executed in Step 015.

## Next-step research selection

The new theorem is **a conditional split-prime factorization in the exact degree-two integral `TraceOneInt(-1)` ring**, not a statement about the degree-seven cyclotomic order, roots/units of FLT7, or primitive Fermat descent.

A narrowly scoped next experiment should resolve the **ramified q=3 boundary** that the Step 015 report explicitly distinguishes from the split case. A plausible, independently testable calculation in this ring is:

```text
τ := tau (-1),      τ²=τ-1,      τ*(1-τ)=1;
π := 1+τ,          π²=3τ,        norm π=3.
P := ker(ev_(2:ZMod 3)) .
Potential:  P = span {π},  P² = span {ofInt(-1) 3}.
```

These are **proposed Step 016 results**, not Step 015 theorems. The second equality is compatible with `P∩P=P ≠ (3)`. Both directions of ideal equality require checked source proofs; the mere equality `π²=3τ` and numerical membership are not by themselves enough. Compare available existing ramified-ideal theorems before new code.

Alternatively, a later step can lift Step 015's q-split orientation to the Step 012 squared element α² and Step 010/011 prime allocations. Neither bridge follows automatically from scalar norm divisibility.

## Decision

**APPROVED — Outcome B.** Authorize Step 016 as a focused, non-FLT ramified-three ideal-square calibration. The new split identity is fully proved under a supplied separated root; **no blanket product identity for all primes** is licensed. Do not merge or create a PR, assert a class-group/unit theorem, or announce FLT7 closure.
