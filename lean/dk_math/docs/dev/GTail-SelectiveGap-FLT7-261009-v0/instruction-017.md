# Instruction 017 — ideal-square support of the selected GTail Eisenstein norm factor

Date: 2026-10-10
Target branch: `feature/GTail-SelectiveGap-FLT7-261009-v0`
Working directory: `lean/dk_math`
Prerequisite: `review-016.md`, `report-016.md`, `report-015.md`, `report-012.md`
**Scope: Step 017 only — neutral, nonvacuous square-support theorems. No generic ideal valuation system, cyclotomic carrier bridge, FLT7 descent or closure.**

## Goal and discipline

Return from the checked ideal structures to the **actual squared element** `α(a,b)^2` occurring in the GTail selected interior Body, where `α=gtailSevenNormCoord a b : TraceOneInt (-1)` and `norm α = a²+a*b+b² = Q` (with correct integer cast).

There is a meaningful split/ramified distinction in this ring:

- **Ramified 3:** `P=ker(ev_2)`, `P²=(3)` (Step 016). Candidate: for arbitrary integral signed z, `(3:ℤ) ∣ norm z` forces the *embedded scalar ring element* `ofInt (-1) 3` to divide **z²**. Do not infer that it divides z.
- **Split prime with two distinct roots:** if z belongs to `P_t` but not `P_(1-t)`, then z² lies in `P_t²` but **not** in the other prime ideal or the scalar principal ideal (q). Do not equate this ideal membership to an exact P-adic valuation or a principal ideal square equality.

The two claims must be mathematically separable and satisfiable without any Fermat7 hypothesis.

## Phase 0 — inventory and overlap

Read exact current source/signatures in:
- `DkMath.Lib.NumberTheory.GTailSevenNormReadout` and `GTailSevenEisensteinResidue`;
- `DkMath.Lib.NumberTheory.GTailSevenResidueIdeal` (root-guarded RingHom, norm-divisor↔kernel disjunction, maximality, α orientation);
- `DkMath.Lib.NumberTheory.GTailSevenSplitIdeal` (kernel product/intersection, scalar q-coordinate criterion);
- `DkMath.Lib.NumberTheory.GTailSevenRamifiedThreeIdeal` (P=(π), P²=(3), π norm3, inverse of τ);
- `DkMath.NumberTheory.TraceOneQuadratic` and current Mathlib ideal multiplication/prime membership API;
- `DkMath.FLT.Seven.GTailPrimeAllocationAudit` and `GTailPrimeOrderAudit` for later **source-only** optional owner bridging.

Write `source-inventory-017.md` with precise import graph and the differences between scalar divisibility of `norm z`, ideal membership of `z²`, embedded-scalar ring-element divisibility of `z²`, and an **unproved** exact ideal-adic exponent claim. Check actual Mathlib names via source or `#check`; do not guess `Ideal.mul_mem_mul`/prime API signatures.

Suggested neutral owner: `DkMath/Lib/NumberTheory/GTailSevenIdealSquareAddress.lean`. Never import FLT7 modules into it.

## Phase 1 — arbitrary integral ramified square lift

Prove an endpoint for every `z : TraceOneInt (-1)`:

```text
(3:ℤ) ∣ norm z  →  ofInt (-1) 3 ∣ z*z
```

A transparent proof chain is:

1. Instantiate Step 014 `prime_dvd_norm_iff_mem_eisensteinResidueIdeals` at prime3, t=2, using Step 016 `eisensteinThreeRoot`. Conjugate t is also 2 in ZMod3, so **both disjunctive ideal addresses are the same P**. Handle dependent root proof arguments by the already checked kernel membership iff, not an invalid proof-term rewrite.
2. Show `z∈P` (optionally make a reusable norm-divisor↔P iff).
3. Use actual ideal multiplication to prove `z*z∈P*P`.
4. Rewrite by Step 016 `eisensteinThreeRamifiedIdeal_mul_self : P*P=eisensteinScalarIdeal 3`.
5. Convert membership in the scalar principal ideal into `ofInt (-1) 3 ∣ z*z`, using existing `Ideal.mem_span_singleton` or the signed-coordinate criterion.

Keep no implicit positivity, natural-coordinate or Fermat premise. An optional converse `ofInt (-1) 3 ∣ z² → (3:ℤ)∣norm z` must have a full proof (via norm multiplicativity plus prime square divisibility, or P's actual primality), not a verbal argument.

Add an adapter `3 ∣ Q(a,b) → ofInt (-1) 3 ∣ (gtailSevenNormCoord a b)^2` for arbitrary naturals a,b, using Step 012's typed norm equality. It is neutral even when the original Fermat equation is false.

## Phase 2 — separated split-square address

For q prime and a **supplied** root t with `ht:t²-t+1=0` and `htdiff:t≠1-t`, let `P_t=eisensteinResidueIdeal t ht` and `P_bar=eisensteinResidueIdeal (1-t) (eisensteinResidue_conjugate_root t ht)`. If `z∈P_t` but `z∉P_bar`, prove:

```text
z*z ∈ P_t*P_t
z*z ∉ P_bar
z*z ∉ eisensteinScalarIdeal q
```

Use real ideal multiplication for the first. For the second, use the prime-ideal instance from Step 014's proved maximality under q prime; prime membership of a square forces membership of z. For the third, use Step 015's **separated-root** equality of the intersection with the scalar principal ideal. Do not replace the original hypotheses by q|norm z alone: that condition yields a disjunction, not a predetermined orientation.

Optionally instantiate this at canonical α(a,b) with q|Q, q∤b, q≠3, using Step 014's checked membership/nonmembership. A second optional generalization may show the product of the same ideal has the appropriate membership under z^2 notation. Do not infer `z²∉P_t³`, exact order two, or `(z²)=P_t²`.

## Phase 3 — mandatory nonvacuous calibration

**Ramified q=3:** Take `π=eisensteinThreeGenerator=⟨1,1⟩`. Verify normπ=3, embedded 3 does **not** divide π, embedded 3 **does** divide π², π∈P but π∉(3), and π²∈P²=(3). Check a signed integral example such as z=⟨-2,1⟩ with numeric norm verified in Lean, using the generic new theorem rather than a literal finite check alone.

**Split q=43:** Take `α=gtailSevenNormCoord 5 8=⟨5,8⟩`. Verify:
- normα=129=3*43;
- α²=⟨-39,144⟩ and norm(α²)=129²;
- α∈P37, α∉P7, α²∈P37*P37, α²∉P7;
- the scalar embedded 43 **does not divide α²** (neither coordinate is divisible by 43), despite 43|normα and 43²|norm(α²).

This is a concrete counterexample to the **unqualified** implication `q|norm z → embedded q | z²` at split primes. It does not refute the special, proved ramified q=3 implication.

Recheck the q=3 repeated-root and q=5 no-root boundaries. Do not assert that every prime supplies a root, or import a cyclotomic carrier or class-group framework to perform this local computation.

## Phase 4 — optional FLT7-facing reader

Only after Phases 1–3 compile, compare with Step 010/011 existing results. An optional **tiny** `DkMath/FLT/Seven/GTailIdealSquareAudit.lean` with a direct test may combine, under an explicit positive primitive hypothetical `Fermat7Equation`, `a+b=c+g` and `3∣Q`, the already checked `9∣g` routing from Step 011 (q=3 has 21∤2 and 3≠7) with the neutral `ofInt(-1)3∣α²`. These are **separate carrier constraints**, not a new arithmetic contradiction or a transport of the selected ideal into the scalar gap/Tail factor.

If the adapter adds only duplication, has a heavy/cyclic import, or would invite a false equality of norm-prime support and a chosen cyclotomic prime, **skip it and document why**. No required FLT owner in this step.

## Validation, deliverables and stop

Required:
- `DkMath/Lib/NumberTheory/GTailSevenIdealSquareAddress.lean`;
- `DkMathTest/NumberTheory/GTailSevenIdealSquareAddress.lean`;
- `source-inventory-017.md` and `report-017.md`;
- truthful post-016 `ROADMAP.md` addendum.

Build created modules/tests and Steps 016/015 focused regressions **sequentially** with process-local `LEAN_NUM_THREADS=2`. Record exact commands/exit codes and public `#print axioms`, plus source import closure and forbidden-placeholder/unsafe scans. Do not modify historical theorem statements or facades; no huge all-test run, Legendre optimization, speculative norm-square unit inversion, PR or merge.

**Outcome B expected:** a neutral ramified scalar square-lift and oriented split ideal-square support, with distinct nonvacuous tests, no FLT7 closure. **Outcome C:** an overstrong implication fails or needs a missing root, separation, prime or orientation premise; give the smallest counterexample. **Outcome A:** only independently verified new FLT7 obstruction after overlap audit, not another restatement of standard norm/ideal behavior.

**STOP after Step 017.** Record the still-open actual GTail-to-FLT7 carrier/descent frontier separately from these neutral algebraic successes.
