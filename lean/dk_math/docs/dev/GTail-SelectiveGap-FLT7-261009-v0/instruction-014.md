# Instruction 014 — bundled Eisenstein residue maps and oriented kernel ideals

Date: 2026-10-10
Target branch: `feature/GTail-SelectiveGap-FLT7-261009-v0`
Working directory: `lean/dk_math`
Prerequisites: `review-013.md`, `report-013.md`, `source-inventory-013.md`.
Scope: **Step 014 only — neutral, root-guarded ring homomorphisms and ideal kernels. Not an ideal factorization of (q), not FLT7 closure.**

## Mission

The Step 013 `eisensteinResidueEval` has already been proved additive, multiplicative *under* `t²-t+1=0`, and compatible with conjugation. Package these exact laws into **genuine bundled ring homomorphisms**

```text
TraceOneInt (-1) →+* ZMod q
```

and use their kernels to record which of the two conjugate residue slots contains a given Eisenstein element.

Derive a **neutral norm-product identity in the residue ring**, valid on actual arbitrary integral elements, then a prime-q criterion

```text
q ∣ norm(z)  ↔  z ∈ ker(ev_t) ∨ z ∈ ker(ev_(1-t)).
```

This is a stronger, well-typed form of the Step 012 norm-divisor readout. The kernels are ideals by construction. At split primes, orient the two ideals using the already proved q=43 evaluation example. Do not infer a principal-ideal product `(q)=P*Pbar` or any statement about cyclotomic/unit classes merely from the existence of these kernels.

## Phase 0 — detailed API/overlap inventory

Read actual source and confirm types, imports and theorem names in:
- `DkMath.Lib.NumberTheory.GTailSevenEisensteinResidue` and `GTailSevenNormReadout`;
- `DkMath.NumberTheory.TraceOneQuadratic`;
- existing `DkMath.NumberTheory.TraceOneResidueType.residueMap`, with codomain `QuadraticAlgebra (ZMod q) ...`;
- `DkMath.Lib.NumberTheory.QuadraticResidueType` split/ramified predicates, including q=3 special behavior;
- existing `TraceOneLatticeLanding`, `EisensteinLatticeLanding`;
- Mathlib `RingHom`, `RingHom.ker`, `Ideal` membership, `ZMod` integer-cast/divisibility and `RingHom` kernel/maximality APIs;
- Steps 010–013 reports and the project frontier.

Write `source-inventory-014.md` listing the actual declarations, whether a suitable composed `residueMap`/QuadraticAlgebra evaluation already exists, and why the new chosen-root evaluation does or does not duplicate it. Use `QuadraticAlgebra.lift` or an existing composition instead of hand-building another hom if that yields the same *definitional/certified* map with smaller dependencies.

## Phase 1 — package the chosen-root evaluation as RingHom

In a narrow **neutral** module, suggested
`DkMath/Lib/NumberTheory/GTailSevenResidueIdeal.lean`, define:

```lean
def eisensteinResidueRingHom {q : ℕ}
    (t : ZMod q) (ht : t ^ 2 - t + 1 = 0) :
    TraceOneInt (-1) →+* ZMod q := ...
```

Prefer to reuse:
- `eisensteinResidueEval_add`;
- `eisensteinResidueEval_mul` with `ht`;
- the literal first/second coordinates of `0`, `1`, and embedded integer `ofInt (-1) n`.

Prove the hom agrees with the previously tested `eisensteinResidueEval`, maps `ofInt` to the integer cast, maps `tau (-1)` to t, and respects `conj z` by switching to 1-t. The quadratic relation for 1-t is a direct ring consequence of ht; use the *same* guarded interface.

**No q-primality premise is needed just for a RingHom from a root in ZMod q**, nor for the polynomial norm-product identity. Do not infer root existence for arbitrary q; the entire construction is parameterized by an explicit root proof.

## Phase 2 — typed ideal kernels and exact norm product

Let `P_t := RingHom.ker (eisensteinResidueRingHom t ht)` and similarly `P_(1-t)`; these are genuine ideals in the existing `TraceOneInt (-1)`.

Prove a transparent membership iff:

```text
z ∈ P_t  ↔  eisensteinResidueEval t z = 0.
```

Use `traceOne_mul_conj`, `eisensteinResidueEval_conj` and `RingHom.map_mul` to derive the **normalization-correct** identity for arbitrary `z : TraceOneInt (-1)`:

```text
((norm z : ℤ) : ZMod q) =
    eisensteinResidueEval t z * eisensteinResidueEval (1-t) z
```

for a root t. Make clear that `norm z` is an integer and casting it to `ZMod q` is legitimate even for negative values.

When `hq : Nat.Prime q`, instantiate `Fact hq` and apply the field's zero-product property to prove:

```text
(q : ℤ) ∣ norm z
  ↔  z ∈ P_t ∨ z ∈ P_(1-t).
```

The integer cast-zero/divisibility equivalence must be applied in the *correct direction*. This theorem **requires an existing root t**; it is not a universal splitting theorem for inert primes.

As a separate positive result, consider proving that each `P_t` contains the embedded scalar q and that the hom is surjective (every residue class has an integer representative). If the exact available Mathlib API makes it straightforward, conclude that `P_t` is maximal (and hence prime) since its image is the field `ZMod q`. Treat maximality as a **separately checked optional gate**, not an assertion based only on naming `RingHom.ker`. Avoid introducing a new ideal-class/number-field hierarchy or a surrogate axiom.

## Phase 3 — orientation, distinctness and repeated root

For prime q, natural a,b with `q∣Q(a,b)`, `¬q∣b`, and q≠3, take the Step 013 canonical `t=gtailSevenResidueRoot q a b`.

Using the **already proved** zero/nonzero evaluation theorems:
- `alpha(a,b) ∈ P_t`;
- `alpha(a,b) ∉ P_(1-t)`;
- optionally `conj(alpha(a,b)) ∈ P_(1-t)` and `conj(alpha(a,b)) ∉ P_t`, using the prior conjugation-evaluation law;
- hence `P_t ≠ P_(1-t)`.

Do not claim equality or comaximality of ideals solely from different evaluations without a proof. A maximality theorem, if successfully proved, may be used to infer comaximality of distinct maximal ideals, but that is optional and does not establish their product equals (q).

**Characteristic-three boundary:** q=3, a=b=1 has canonical t=2=1-t, so both evaluations and both chosen kernels coincide. Test it explicitly. Do not describe all q=3 norm-divisible elements as having two distinct oriented ideals.

## Phase 4 — actual finite regressions and missing-premise checks

Mandatory satisfiable regressions:
- q=43,a=5,b=8, Q=129=3*43, t=37 and 1-t=7 in ZMod 43;
- `alpha=gtailSevenNormCoord 5 8`: membership in `P_37`, nonmembership in `P_7`, both from *bundled* hom/kernel membership; norm α=129 and q|norm α;
- evaluate `conj alpha` in each ring hom if included: nonzero at 37, zero at 7;
- scalar embedded 43 belongs to both ideals, but scalar 43 does **not** divide alpha as an Eisenstein ring element; these statements live in different types and must not be conflated;
- q=3,a=b=1: same root/slot and kernel identity, no false distinctness;
- a nonroot parameter: multiplication preservation or RingHom may **not** be asserted without ht. A small concrete counterexample to unguarded multiplication preservation (if easy) is useful; do not fabricate a `RingHom` at a parameter failing the quadratic equation.

Avoid large finite decision tactics on arbitrary q; use the previous proven numeric root calibration and field arithmetic.

## Phase 5 — honest mathematical stop

The two kernels are actual ideals. **Do not yet assert** any of the following unless separately proved with the correct ring, ideal and carrier contracts:

- `(ofInt(-1) q) = P_t * P_(1-t)` as ideals;
- unique-prime-factor distribution of a particular algebraic element;
- PID/UFD or class-number assertions;
- arbitrary norm-square value implies the original element is a square/unit-square;
- a selected scalar GTail q-support identifies a chosen cyclotomic ideal or existing typed ramified-root packet;
- positive FLT7 descent, next primitive Fermat tuple, or unconditional FLT7 closure.

The exact norm-factor residue identity and kernel membership are **neutral facts**, not a proof of new FLT7 incompatibility. If full ideal factorization is an attractive later topic, report what precise missing lemma remains in `report-014.md` without silently implementing it.

## Deliverables and focused validation

Required:
- `DkMath/Lib/NumberTheory/GTailSevenResidueIdeal.lean`;
- `DkMathTest/NumberTheory/GTailSevenResidueIdeal.lean`;
- `source-inventory-014.md`;
- `report-014.md`;
- accurate post-013 section in project `ROADMAP.md`.

Create an FLT7 owner/test **only if** a tiny hypothesis-supplying adapter is independently useful; the principal new theorems should remain neutral. Do not alter earlier source proof statements to make the new module compile.

Build **only created focused modules** and replay Step 013 regression sequentially with process-local `LEAN_NUM_THREADS=2`:

```text
LEAN_NUM_THREADS=2 lake build DkMath.Lib.NumberTheory.GTailSevenResidueIdeal
LEAN_NUM_THREADS=2 lake build DkMathTest.NumberTheory.GTailSevenResidueIdeal
LEAN_NUM_THREADS=2 lake build DkMathTest.NumberTheory.GTailSevenEisensteinResidue
```

Record exact commands and exit codes, all new public `#print axioms`, source/graph closure, implementation repairs and mathematical limitations. Audit no `sorry`, `admit`, extra `axiom`, `unsafe`, `False.elim`/circular FLT7 impossibility use, or neutral-to-FLT import cycles. Do not run the full expensive all-test suite, unrelated Legendre calibration, public facade promotion, PR or branch merge.

Outcome:
- **B** (expected): neutral RingHom, checked ideal kernels, residue norm-product/prime-divisor criterion, and distinctness at split-root inputs, without a new obstruction or descent.
- **C**: a target kernel/ideal inference or exception fails; report exact missing premise or concrete counterexample and retain only honestly checked weaker endpoints.
- **A** only for independently compared new arithmetic restrictions beyond a norm/ideal presentation; **not** unconditional FLT7.

**STOP after Step 014.**
