# Review 014 — root-guarded Eisenstein kernel ideals

Date: 2026-10-10
Branch: `feature/GTail-SelectiveGap-FLT7-261009-v0`
Decision: **APPROVED — Step 014 COMPLETE / Outcome B**

## Reviewed evidence and limits

Static GitHub inspection of:
- `DkMath/Lib/NumberTheory/GTailSevenResidueIdeal.lean` (141 lines);
- `DkMathTest/NumberTheory/GTailSevenResidueIdeal.lean` (150 lines);
- `report-014.md`, `source-inventory-014.md` and project roadmap;
- Steps 012–013 norm/conjugation/root evaluation and existing `TraceOneResidueType` and lattice criteria.

The reviewer did **not independently run Lean**. Codex's report records final passing focused builds of the two new targets and Step 013 regression, 20 examples, and public axiom prints for all 16 new declarations, using only standard foundations.

## Proof-route conclusions

1. `eisensteinResidueRingHom t ht` is a real `TraceOneInt (-1) →+* ZMod q`, not merely a chosen function. Its operations use the prior `eisensteinResidueEval_add` and guarded `_mul`; `ht : t²-t+1=0` is explicit. The map preserves 0, 1, embedded integers and the integral generator `tau`.
2. `eisensteinResidueIdeal t ht := RingHom.ker (...)` is genuinely typed as an `Ideal` in the **same** integral TraceOne ring. The iff identifies its membership with zero evaluation; the root proof is not disguised as root existence for every modulus.
3. `norm_cast_eq_eisensteinResidue_product` applies the hom to the pre-existing element identity `z*conj z = ofInt(-1) (norm z)`. This yields `((norm z:ℤ):ZMod q) = ev_t(z) * ev_(1-t)(z)` for **all integral z** and any supplied root. No new norm definition or polynomial substitution bypasses the carrier.
4. `prime_dvd_norm_iff_mem_eisensteinResidueIdeals` requires prime q, uses the integer-cast divisibility equivalence and the prime-field zero-product law, and correctly concludes a **disjunction**, not both-kernel membership or unique prime ideal factorization.
5. Embedded scalar q belongs to each root kernel, and `eisensteinResidueRingHom_surjective` constructs a preimage of each residue by an embedded integer. Prime q then licenses `RingHom.ker_isMaximal_of_surjective`; this maximality is an actually checked extra theorem, not a claim from the kernel's name.
6. At q=43, canonical t=37 and conjugate t=7: `alpha(5,8)` belongs to P37 but not P7, while its conjugate belongs to P7 but not P37. A concrete witness proves **P37≠P7**. Both ideals contain embedded 43, while embedded 43 does not divide alpha as an element; the source keeps scalar-element divisibility and ideal membership distinct.
7. At q=3, the two parameter roots coincide at 2 and hence the ideals coincide. No distinctness/comaximality theorem is asserted here. A nonroot parameter t=0 (mod 43) fails multiplication preservation at the generator, demonstrating why the polynomial guard is essential.
8. Static overlap review finds the existing `TraceOneResidueType.residueMap` retaining two reduced coordinates in a `QuadraticAlgebra`. The new chosen scalar-slot hom is explicitly extensionally identified with Step 013 evaluation; it uses a smaller source import closure, rather than claiming an unrelated field/quotient carrier.
9. Codex reports initial test-only notation/rewrite/lint repairs, final warnings/errors absent, the new declarations' axiom lists within `[propext, Classical.choice, Quot.sound]`, no source placeholders/new axioms/unsafe, no neutral→FLT imports and no cycles. Reported focused builds do not represent an independently completed full test-suite rebuild.

## Next mathematical gate: split ideal factorization, under hypotheses

The confirmed maximal ideals are now legitimate candidates for a **new optional split-prime theorem** in this exact Eisenstein order. The essential missing lemma is a **two-evaluation coordinate reconstruction**:

For prime q and a *supplied distinct root pair* `t,1-t` of `t²-t+1=0`, zero evaluation of an arbitrary `z=⟨x,y⟩` at **both** roots forces q to divide x and y. Indeed subtracting `x+yt=0` and `x+y(1-t)=0` yields `y*(2t-1)=0`; distinctness makes `2t-1` a nonzero field element, so y=0 and then x=0 modulo q. This should identify

```text
P_t ⊓ P_(1-t) = Ideal.span {ofInt (-1) (q:ℤ)}.
```

Distinct maximality should give `P_t ⊔ P_(1-t)=⊤`, then a checked Mathlib comaximal-ideal theorem can identify `P_t * P_(1-t) = P_t ⊓ P_(1-t)`. No such intersection/product result exists in Step 014. A generic `q≠3` plus ht is expected to imply roots distinct; prove it rather than assuming an unproved classification. Do not assert it for q=3: for z=⟨1,1⟩ the repeated-root kernel includes z but scalar (3) does not divide z. Hence `P_t∩P_(1-t)=(3)` is false at the ramified root.

This proposed Step 015 result would be a *conditional split ideal factorization in TraceOneInt(-1)*, not a theorem about FLT7 cyclotomic ideals or unit classes, and not a solution to the norm-to-element-square converse.

## Decision

**APPROVED — Outcome B.** Authorize a focused, independent Step 015 split-prime ideal product/intersection verification after exact Mathlib ideal API inspection. No PR, merge, facade promotion, cyclotomic/prime-power transfer, or FLT7 closure claim.
