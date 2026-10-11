# Instruction 021 — six nontrivial seventh-root prime slots and selective Tail support

Date: 2026-10-10
Target branch: `feature/GTail-SelectiveGap-FLT7-261009-v0`
Working directory: `lean/dk_math`
Prerequisites: `review-020.md`, `report-020.md`, `source-inventory-020.md`.
**Scope: Step 021 only.** Convert the **already proved** packet-free single-root cyclotomic prime address into a finite six-root orbit with pairwise distinct/comaximal ideals, and prove that the actual GTail Tail factor is supported at exactly one indexed root. **Do not assert the six-ideal product (q), ideal-adic valuations, ring-to-ring transport or FLT7 descent.**

## Mathematical target and limits

Work throughout in the actual degree-six ring

```text
R := SevenCyclotomicDegreeSixInt.Ring
K_s := seventhRootKernel s hs0 hs7 hs1 : Ideal R
```

for a supplied prime q and `r : ZMod q` with

```text
hr0 : r≠0
hr7 : r^7=1
hr1 : r≠1
```

No `RamifiedSignedRootDepthPacket` is constructed or required.

From these hypotheses and the primality of the exponent seven, `orderOf r = 7`. Its six positive proper powers `r^1,...,r^6` are **pairwise distinct and all nonzero/nonidentity seventh roots**. Each gives a separate packet-free maximal/prime kernel K_i. From Step 020, two distinct root kernels are unequal and maximal; thus they are **pairwise comaximal**.

A natural Tail factor under q-prime, q∤c,g and q|GTail has canonical root `r=gtailSevenTailRatio q c g`, so its linear factor

```text
F(c,g) := gtailCyclotomicLinearFactor c g
        = ofReal(c+g) - zeta * ofReal c
```

belongs to the root slot `i=0` (power r¹=r), and not to any of the other five root slots. This is a **neutral, satisfiable finite-field/cyclotomic addressing statement**, not a positive Fermat7 solution or a new obstruction.

**IMPORTANT STOP:** pairwise comaximality does **not by itself** prove

```text
Ideal.span {(q:R)} = ∏ i : Fin 6, K_(r^(i+1)).
```

Such a factorization needs a separately checked equality of the **intersection of all six kernels** with scalar (q) (or equivalent coordinate interpolation/CRT). Do not silently claim that equality or a complete classification of all prime ideals of R. Even if existing packet-indexed code proves a product for separately furnished signed packets, it is not available for this new bare-root input without a typed adapter.

## Phase 0 — exact owner/API audit

Inspect:
- `DkMath.FLT.Seven.GTailCyclotomicPrimeAddress`: actual `seventhRootKernel`, maximality, primality, separating element, kernel-ne, Tail unique address;
- `DkMath.FLT.Seven.GTailCyclotomicLocalEval`: actual root RingHom and gtailCyclotomicLinearFactor;
- `DkMath.Lib.NumberTheory.GTailSevenPairedResidue` and `GTailSevenPrimeOrder`: root construction, order-seven interface, order API;
- `SevenRamifiedFusionGlobalOrientedPrimeFactorization`: existing **signed-packet-indexed** `cyclicKernel` and its Galois phases; inspect for mathematical overlap but **do not import** this owner merely to restate it;
- `SevenRamifiedFusionCyclotomicConjugatePrimePair`: existing conjugation-related packet-indexed prime pairs;
- actual Mathlib `orderOf_eq_prime`, powers of finite-order elements, `Fin 6` injection, pairwise predicates/`Finset`, maximal ideal comaximality API (check names with `#check`/source).

Write `source-inventory-021.md` with exact Lean symbols, proof prereqs, source owner import plan, order/separation exceptions and the missing equality needed for any future six-ideal product. The main owner should import Step 020 directly; avoid a public FLT facade or earlier signed-packet global factorization owner unless demonstrably necessary.

## Phase 1 — six powered roots as a genuine finite orbit

Suggested source `DkMath/FLT/Seven/GTailCyclotomicSixRootOrbit.lean`.

For q prime and r satisfying hr0/hr7/hr1, define a small transparent helper indexed by `i : Fin 6`:

```text
sixthSlotRoot r i := r^(i.val+1) : ZMod q.
```

The name is illustrative; avoid ambiguity with “sixth root of unity”: these are **the six nonidentity seventh roots**.

Prove in modest separate theorems:
- `orderOf r = 7`, with the existing prime-exponent order API and the supplied r premises.
- For every `i : Fin 6`: `root_i^7=1`, `root_i≠0`, `root_i≠1`.
- For any `i≠j : Fin 6`: `root_i≠root_j`. Prefer a generic finite-order power lemma after source-checking it. If manual, use `1 ≤ i.val+1 ≤6` and order seven to control exponent differences, avoiding an invalid use of simple cancellation in an arbitrary monoid.
- `root_0 = r`; the six concrete powers should be presented in ascending exponent order.

Do not overclaim that there are six roots for q=7 or an arbitrary q without a nontrivial seventh root; the entire API is **conditional on a supplied r**. Nor should the proof require q|Q or any Fermat equation: it is finite group arithmetic.

## Phase 2 — six actual distinct maximal prime kernels

Construct a succinct typed indexed ideal API, e.g.

```text
sixRootKernel r ... (i:Fin 6) : Ideal R :=
  seventhRootKernel (sixRoot r i) (proved_nonzero i) (proved_pow7 i) (proved_ne_one i).
```

Prove:
- membership iff evaluation zero, using the **existing** Step 020 definition;
- for every i, the kernel is maximal and prime, with integer contraction (q) and residue degree/cardinality q if useful, by specializing Step 020. Do not prove those structurally a second time.
- for i≠j, K_i≠K_j by `seventhRootKernel_ne` applied to Phase 1's genuine distinctness.
- for i≠j, `K_i ⊔ K_j = ⊤` using their actual maximality and checked Mathlib distinct-maximal comaximal theorem (same proof pattern as Step 015 / old packet-indexed pair). It is fine to state the mathematically equivalent `Ideal.IsCoprime` predicate if that is the actual API; include a readable theorem relating it to sup-top if useful.

Avoid a new class-group/prime-spectrum hierarchy; these are six explicit ideals in **one existing integral ring**.

## Phase 3 — exact selective Tail support among the six slots

For prime q, naturals c,g and hypotheses

```text
hc : ¬ q ∣ c
hg : ¬ q ∣ g
hT : q ∣ GTail 7 1 g c
r := gtailSevenTailRatio q c g
```

the existing Step 018/019 results provide hr0/hr7/hr1 for r.

Prove:
- `F(c,g) ∈ K_0`, identifying `r^1=r` through actual exponents and existing Step 019 kernel membership.
- `∀ i:Fin 6, i≠0 → F(c,g) ∉ K_i`, using Step 020's zero-iff-unique-root or `gtailCyclotomicLinearFactor_unique_address` and Phase 1 distinctness.
- optional compact iff `F(c,g) ∈ K_i ↔ i = 0` or `∃! i : Fin 6, F(c,g)∈K_i`. This is **uniqueness within this six-element root-indexed set only**, not a claim of uniqueness among every possible degree-six prime ideal at q.

The result must **not** require q|Q or a positive primitive Fermat equation. That quadratic constraint belongs to the separate Eisenstein address; our Tail root orbit exists from the Tail q-prime conditions alone. Do not confuse the root orbit with the \`Fin 3\` Galois *phase* index from the old signed-packet owner.

If a clean theorem `every nonidentity seventh root s equals r^(i+1) for some i` follows cheaply from orderOf r=7 and cardinality, it is a useful OPTIONAL completeness theorem. This must be proven, not assumed from the six supplied roots; the finite set contains six explicit roots but a separate surjectivity/root-classification statement is needed to call it *all* admissible roots. A direct finite-field polynomial root bound can also discharge it; do not guess a theorem name.

## Phase 4 — mandatory concrete and boundary regressions

At q=43, with r=11 and Tail data c=9,g=4:
- prove successive powers for i=0,...,5 are exactly `[11,35,41,21,16,4]` modulo 43, and no two coincide;
- verify each has seventh power one and is nonidentity; every corresponding kernel has maximal/prime status from the generic theorem;
- check **all six distinct kernels**, at least via the generic pairwise-ne theorem; check their pairwise comaximality using a generic theorem as well;
- prove F(9,4) belongs exactly to the i=0 kernel, not i=1..5; check a few explicit eval values including s=35, and invoke the **generic** root-indexed theorem for the full finite collection;
- preserve q43's neutral congruences q|Q/T and `¬Fermat7Equation 5 8 9` when relevant, without making the equation a production premise;
- q=13 Gap branch has ratio 1, q∤T, so this six-nontrivial-root Tail packet cannot be constructed from q|Q alone;
- q=7 has no **nontrivial** seventh root in ZMod7; its separate ramified zeta↦1 RingHom remains valid but is not a member of this six-root API;
- q=3 repeated and q=5 inert observations are **Eisenstein degree-two** boundaries; do not transfer those labels to the degree-six carrier without proof.

Sanity: for c=0 (nonunit), F(0,0)=0 belongs to all six ideals; that is why the q∤c hypothesis is essential to exactly-one-root support. No exact ideal valuation follows from the membership statement.

## Phase 5 — Galois comparison optional, not a hidden dependency

Source-inspect the existing `SevenCyclotomicDegreeSixInt.rotateEquiv_zeta` (ζ↦ζ²) and `star_zeta` (ζ↦ζ⁻¹). The multiplicative transformations of root exponents (2 and -1 mod 7) generate six residue roots. If this can be stated as a small extensional equality of **whole RingHom** evaluations without pulling in a broad signed-packet closure, an optional source-Galois covariance theorem may be worthwhile.

But note: equality on ζ's image alone is **not sufficient**; the real-cubic alpha evaluation must be transported consistently with the actual ring automorphism. Do not claim `eval_r ∘ rotateEquiv = eval_(r²)` or a corresponding ideal.map equality without a proper proof at both coordinates. It is acceptable to **defer** such covariance explicitly; Phases 1–4 are the required target.

Do not derive any six-ideal product equality from the Galois relation alone.

## Deliverables / validation / STOP

Required:
- `DkMath/FLT/Seven/GTailCyclotomicSixRootOrbit.lean`;
- `DkMathTest/FLT/Seven/GTailCyclotomicSixRootOrbit.lean`;
- `source-inventory-021.md`, `report-021.md`;
- truthful post-020 `ROADMAP.md` addendum.

Run sequential incremental focused builds with process-local `LEAN_NUM_THREADS=2` for created targets and Step 020/019 regression; log final exit codes and repairs, number of examples, source declarations, `#print axioms`, source/import-cycle/forbidden-token audits, and any change to source closure. No unrelated full build, Legendre proof work, public facade promotion, PR or merge.

**Outcome B expected:** fully checked packet-free six powered-root ideals, pairwise distinct/maximal/comaximal, and exactly-one Tail factor support among those six, independent of a Fermat equation. **Outcome C:** a false completeness, orientation, q-unit or group-order inference; record the missing hypothesis/counterexample and preserve checked lesser endpoints. **Outcome A:** only if a genuinely independent source-compared FLT7 obstruction follows, not from reindexing existing root kernels.

**STOP after Step 021.** Do not attempt the six-ideal product formula, new P-adic valuations, Eisenstein→cyclotomic integral mapping, signed-root packet fabrication, ideal class/unit powers, primitive next Fermat tuple or unconditional FLT7 conclusion.
