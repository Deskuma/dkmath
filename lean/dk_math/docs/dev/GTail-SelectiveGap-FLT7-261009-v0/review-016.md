# Review 016 — ramified-three Eisenstein kernel and squared principal ideal

Date: 2026-10-10
Branch: `feature/GTail-SelectiveGap-FLT7-261009-v0`
Decision: **APPROVED — Step 016 COMPLETE / Outcome B**

## Evidence and verification scope

Static GitHub source/proof-route inspection of:
- `DkMath/Lib/NumberTheory/GTailSevenRamifiedThreeIdeal.lean` (141 lines);
- `DkMathTest/NumberTheory/GTailSevenRamifiedThreeIdeal.lean` (108 lines);
- `report-016.md`, `source-inventory-016.md`, and the Step 015 split-ideal owner;
- `TraceOneLatticeLanding` used for the arbitrary signed-coordinate divisibility direction.

**No independent Lean build was performed by this reviewer.** Codex reports final passing production and test targets, an unchanged Step 015 regression, 26 examples and all 17 new public-declaration axiom prints within the standard foundations.

## Mathematical findings

1. The actual `TraceOneInt (-1)` multiplication is used with `τ=tau(-1)` and `τ²=τ-1`. The generator `π=1+τ=⟨1,1⟩` has integer norm 3 and satisfies the *element-level* equality `π*π=ofInt(-1) 3*τ`. This is not merely a scalar norm-square calculation.
2. `τ*(1-τ)=1` is checked by actual ring arithmetic. This explicit inverse yields the two element divisibilities `3|π²` and `π²|3`; the proof does not manufacture a generic unit, UFD or Euclidean-domain instance.
3. `mem_eisensteinThreeRamifiedIdeal_iff_coordinates` reduces the actual evaluation kernel at the repeated root 2 (mod 3) to `3|(z.fst-z.snd)` for **every signed integral** `z`. No natural-coordinate restriction or spurious primitive Fermat input is present.
4. `eisensteinThreeGenerator_dvd_iff_coordinates` uses the existing **nonzero-norm lattice landing criterion** with `norm π=3 ≠0`. The two conjugate-product coordinates are `2*z.fst+z.snd` and `-z.fst+z.snd`; their joint 3-divisibility is shown equivalent to divisibility of `z.fst-z.snd). The proof is a genuine quotient/coordinate criterion, not the false converse `3|norm z → 3|z`.
5. The common kernel `P=ker(ev_(2:ZMod3))` is identified as the **principal ideal `span{π}`** by ideal extensionality and `Ideal.mem_span_singleton`, not just by testing `π∈P`.
6. `Ideal.span_singleton_mul_span_singleton` gives `P²=(π²)`, and mutual actual element divisibility shows `(π²)=(3)`. Thus the checked main endpoint `eisensteinThreeRamifiedIdeal_mul_self` establishes `P*P=eisensteinScalarIdeal 3` with **no** split-case `mul_eq_inf_of_coprime` dependency.
7. The same tests show `P∩P=P`, `P≠(3)` (witness π), and `P⊔P≠⊤`. These results coexist correctly with `P²=(3)`. The old Step 015 characteristic-three intersection counterexample remains valid, and does not invalidate the now-proven separate product formula.
8. Nonvacuous signed regressions include `z=⟨-2,1⟩`, a literal quotient by π, `z=⟨-43,86⟩`, and an excluded nonmember `⟨1,0⟩`. The q=43 split and q=5 inert tests were replayed unchanged by Codex.
9. Reports describe final successful targeted builds and standard-axiom-only checks. The initial compiler/linter repairs were to literal cast rewriting, lint syntax and test `inf_idem _`, not weakened mathematical hypotheses. No unsafe/placeholder source, newly added axiom, or neutral→FLT import was found in the supplied new files.

## Status / scope boundary

**APPROVED / Outcome B** establishes a classical ramified-prime identity in the existing **degree-two** `TraceOneInt(-1)` ring. It does not establish prime-ideal factorization in a seventh cyclotomic carrier, unit-power extraction, valuation of arbitrary ideals, or a new positive primitive Fermat solution/descent.

The combined checked local picture is:

```text
split q=43:   (43)=P37*P7 = P37∩P7 ; P37 ≠ P7
ramified q=3: (3)=P*P ;             P∩P = P ≠ (3)
inert q=5:   no root of t²-t+1 in ZMod5 (finite regression)
```

## Step 017 direction — return to the original GTail norm square

Before investing in a general prime-ideal valuation theory or cyclotomic transfer, attach the now-checked degree-two ideal identities to the **existing element square** `α²` from the GTail selected Body.

- At q=3, for any integral z, `3|norm z` implies `z∈P` from the Step 014 norm/kernel criterion at the repeated root, hence `z²∈P²=(3)`: **embedded scalar 3 divides z² as an element**. This is a satisfiable, nontrivial ramified square-lifting theorem and **does not** claim 3|z.
- At a supplied split prime with separated roots, `z∈P_t` and `z∉P_bar` imply `z²∈P_t²` and `z²∉P_bar` by ideal multiplication and primality of the maximal conjugate kernel. At q=43, `α=⟨5,8⟩` gives an explicit contrast: 43|norm α, while the scalar 43 does **not** divide α² (whose coordinates are `⟨-39,144⟩`). Do not misinfer split scalar divisibility from a norm square.
- Optionally prove a thin FLT7-facing adapter from Step 010/011 q-local prerequisites only after the neutral results, without confusing squared ideal support with the scalar GTail g/T factor allocation.

These Step 017 conclusions are **targets**, not Step 016 theorems. An ideal membership `z²∈P_t²` alone is **not** an exact P-adic valuation/exponent claim, and equality of scalar norm values is not an element-level square-unit reconstruction.

**Decision: APPROVED / Outcome B.** Proceed only with a focused, neutral square-support calibration, and stop before any unrestricted cyclotomic prime bridge or FLT7 closure claim. No PR/merge/facade promotion authorized.
