# Instruction 018 — paired finite-residue receiver for GTail Tail primes

Date: 2026-10-10
Target branch: `feature/GTail-SelectiveGap-FLT7-261009-v0`
Working directory: `lean/dk_math`
Prerequisites: `review-017.md`, `report-017.md`, `report-011.md`.
Scope: **Step 018 only — a neutral shared-residue-field bridge; not an integral Eisenstein-to-seventh-cyclotomic ring embedding, ideal map or FLT7 closure.**

## Mission and central warning

Steps 012–017 proved genuine norm, residue-ring-hom and ideal-square statements for the ring `TraceOneInt (-1)` with generator τ²=τ-1. The FLT7 owner also has an explicit degree-six cyclotomic carrier `SevenCyclotomicDegreeSixInt.Ring = QuadraticAlgebra SevenRealCubicInt (-1) (alpha-1)` with ζ²-(alpha-1)ζ+1=0 and ζ^7=1. **These are different algebraic carriers, different base rings and different quadratic relations.**

Do NOT quietly cast/transport an ideal or an element from `TraceOneInt(-1)` into the degree-six carrier. Nothing in Step 017 constructs that ring hom. A correct alternative is to put two *independent* roots into the **same finite field** `ZMod q` when q lies on the GTail **Tail** side. Shared scalar residue data is not a ring embedding between the source integral rings.

Under entirely satisfiable **neutral** hypotheses

```text
Nat.Prime q, q≠7
q ∣ Q(a,b)                Q=a²+a*b+b²
q ∣ GTail 7 1 g c         Tail-side
q∤b, q∤c, q∤g
```

construct and verify two explicitly typed residues:

```text
t := -(a : ZMod q)/(b : ZMod q)
r := ((c : ZMod q)+(g : ZMod q))/(c : ZMod q)

t²-t+1=0
r^7=1, r≠1, r≠0
1+r+r²+r³+r⁴+r⁵+r⁶=0
```

The first t defines the **already checked Eisenstein RingHom** in Step 014 and its oriented ideal; the second is a **seventh cyclotomic polynomial root in the scalar field only**. Do not infer a full degree-six cyclotomic RingHom until an explicit real-cubic base evaluation and compatibility with ζ's relation are built and checked.

This is a precise re-expression of the order-3/order-7 intersection mechanism; **Outcome B** is the expected mathematical classification, unless a genuinely new restriction is proved independently. No descent is expected.

## Phase 0 — source and algebraic-carrier feasibility inventory

Source-inspect **exact** declarations in:
- `DkMath.Lib.NumberTheory.GTailSevenPrimeOrder`: `seven_dvd_prime_sub_one_of_gtail`, `twentyOne_dvd_prime_sub_one_of_quadratic_gtail` and the existing seventh-ratio proof;
- `DkMath.Lib.NumberTheory.GTailSevenEisensteinResidue`: `gtailSevenResidueRoot` and its polynomial / nonzero-conjugate receiver;
- `DkMath.Lib.NumberTheory.GTailSevenResidueIdeal` and `GTailSevenIdealSquareAddress`: selected-root RingHom/kernel and ideal-square contracts;
- `DkMath.Lib.Cosmic.GTailNat` and `GTailSeven`: exact natural-to-field factorization and selected Body;
- `DkMath.FLT.Seven.GTailPrimeAllocationAudit` and `GTailPrimeOrderAudit`: local endpoint/gap units and guarded Tail-side constraints;
- `DkMath.FLT.Seven.SevenRamifiedFusionCyclotomicDegreeSixCarrier`: degree-six carrier, exact base relation and seventh root;
- `DkMath.FLT.Seven.SevenRamifiedFusionCyclotomicRamifiedPrime`: **different** q=7 ramified ideal/evaluation and carrier, not the q=3 Eisenstein prime;
- current Mathlib seventh cyclotomic polynomial (`Polynomial.cyclotomic 7 ...`), geometric sums and field/root API. Use `#check`/source to verify actual lemma names; do not invent one.

Create `source-inventory-018.md` with a small table comparing: Eisenstein ring, full degree-six cyclotomic ring, the real-cubic base, and shared `ZMod q`. Record the defining equations, available maps, actual missing map, and exact existing Step 011 overlap. If existing code contains a genuinely compatible **residue** mapping of the degree-six ring at a nonseven q, inspect its full premises and choose a *small* adapter, not an assumption.

**Mathematical non-identification:** Do not assert that an arbitrary embedded root of the Eisenstein polynomial can simply be sent to ζ7. Do not claim a Q-algebra embedding from Q(sqrt(-3)) into Q(ζ7) without reconciling their field structures. If a strong "no embedding" theorem is desirable, state it as an **unproved future formalization target**, not an automatic Lean fact or a prerequisite.

## Phase 1 — neutral paired residue construction

Suggested owner `DkMath/Lib/NumberTheory/GTailSevenPairedResidue.lean`. Import only narrow neutral GTail and existing Step 013–014 receiver modules, plus needed Mathlib; **never import FLT.Seven** into neutral.

Define a transparent `gtailSevenTailRatio q c g` if useful (field instance under `[Fact (Nat.Prime q)]`) or use the literal ratio in theorem statements.

From q∣T and q∤c, show `r^7=1` by the **existing** neutral exact tail identity cast into `ZMod q`. From q∤g show `r≠1`. From r^7=1 derive r≠0. Prove the **seven-term cyclotomic geometric sum vanishes**:

```text
r^6+r^5+r^4+r^3+r²+r+1=0.
```

Use the algebraic polynomial identity `(r-1)*(1+r+...+r^6)=r^7-1` and field cancellation. Do not conclude the sum is zero from r^7=1 **without** r≠1. An optional equivalent statement via actual `Polynomial.cyclotomic 7 ℤ` evaluation is desirable only if its normalization and import cost are checked.

For the same q and a,b with q∣Q and q∤b, reuse the Step 013 root certificate `t²-t+1=0`, and the already checked `eisensteinResidueRingHom t ht : TraceOneInt(-1)→+*ZMod q` / chosen ideal. Prove the root pair exists and is actually carried in the **same finite field**.

Keep the root proof as a theorem, a small structure with explicit proofs, or a `∃ t r:ZMod q, ...` depending on smallest useful API. If constructing a structure, its fields must make **no hidden Fermat hypothesis** and no phantom degree-six carrier map. Maintain a separate reusable theorem for the seventh root and its geometric sum, rather than bundling everything into a monolith.

No prime-order 3/7 duplicate proof is required: Step 011 already proves 21|q-1 with both coordinate units. Reuse that theorem for a backward-compatibility check when q∤a is available, rather than restating a large order argument.

## Phase 2 — oriented Eisenstein address, no ideal transfer

Prove a thin neutral theorem under q-prime, q∣Q, q∤b and q≠3:
- the selected alpha(a,b) lies in the **chosen** Eisenstein kernel P_t and not in the conjugate P_(1-t), by reusing Step 014;
- the selected alpha² lies in P_t² and not in scalar (q), by reusing Step 017;
- the second residue r is an independent nontrivial seventh root. The result can be a correctly typed conjunction/packet but **must not** be described as an equality/transport between the two rings or a class/ideal identification.

If this is a pure API conjunction with no new proof content, classify it explicitly as such and avoid unnecessary additional public wrappers. The main deliverable is the **finite field seventh-root witness** plus the source-backed carrier-boundary inventory.

## Phase 3 — mandatory nonvacuous calibration and false-branch checks

**Tail-side actual numbers, not Fermat solutions:** q=43, (a,b,c,g)=(5,8,9,4). Check:
- a+b=c+g, Nat.Coprime a b; Q=129=3*43; q∣Q and q∣GTail 7 1 4 9;
- q∤a*b*c*g;
- t=37, 1-t=7; r=(9+4)/9=11 in ZMod43;
- t²-t+1=0, r^7=1, r≠1, r≠0, `1+r+...+r^6=0`;
- alpha lies in P37 not P7, and its square has Step 017's checked oriented ideal-square support;
- `21∣43-1`, but `¬Fermat7Equation 5 8 9`. The original natural exact equation must **not** be assumed in neutral tests.

**Gap branch:** q=13, (a,b,c,g)=(14,29,30,13) has q|Q and q|g but q∤T. Do **not** derive seventh root r≠1 with r^7=1 from q|Q alone. A finite sample should check this failure or clearly report which premise is absent. q=3 repeated Eisenstein root, q=5 inert missing root and q=7 excluded seventh-root boundary remain explicit without forced generic root existence.

**Failure witness if seven-root guard is dropped:** r=1 in any field satisfies r^7=1 but does not force the sum of seven powers to vanish when characteristic≠7 (e.g. ZMod43). Add a small finite test. This distinguishes nontrivial cyclotomic root from merely an element of seventh-power one.

## Phase 4 — optional FLT7 owner adapter only after neutral proof

If useful, a tiny `DkMath/FLT/Seven/GTailPairedResidueAudit.lean` may derive the neutral packet's prime/unit premises from the **existing** Step 010/011 tail-side exact Fermat carrier:

```text
Nat.Coprime a b
Fermat7Equation a b c
a+b=c+g
Nat.Prime q, q≠7, q∣Q, q∣T
```

Derive q∤a,b by Step 010 coprimality, q∤c by Step 010 endpoint-unit theorem and q∤g by exclusive support. Then apply the neutral construction. Do **not** require positivity if the existing exact local premises can discharge everything, and do not import an FLT impossibility endpoint. This conditional wrapper is an **input receiver only**, not a new FLT7 necessary restriction; expected Outcome B.

If source closure is too large or the result would merely restate Step 011 without new typed field root witnesses, omit optional owner and document the reason.

## Phase 5 — deliverables, validation, stop

Required:
- `DkMath/Lib/NumberTheory/GTailSevenPairedResidue.lean`;
- `DkMathTest/NumberTheory/GTailSevenPairedResidue.lean`;
- `source-inventory-018.md`, `report-018.md`, and a truthful post-017 `ROADMAP.md` entry.

Optional only when justified: narrow owner/test from Phase 4.

Build created targets sequentially/incrementally with `LEAN_NUM_THREADS=2`, then replay Step 017 neutral and Step 011 prime-order regressions as practical. Record exact command/exit, all new public signatures and `#print axioms`, satisfiable numeric tests, shared-field vs distinct-carrier limitations, source diff/forbidden placeholder audit, and import cycle check. Avoid costly complete tests, public facade promotion, unrequested PR/merge and modifications to existing ring/cyclotomic owner definitions.

**Outcome B (expected):** a checked common finite-field root pair and guarded typed Eisenstein residue address, with **no unproved ring-to-ring embedding**, cyclotomic ideal identification, unit class or descent.
**Outcome C:** a proposed finite-field or carrier inference fails or requires a missed unit/nontrivial-root premise; record an explicit corrected contract/counterexample.
**Outcome A:** only a genuinely new independent FLT7 obstruction surviving comparison with Step 011 and existing typed carriers; existence of two roots or an order-21 consequence by itself is **not** A.

**STOP after Step 018.** Do not assert a map into the degree-six ring, build general q-adic ideal valuations or start a next primitive Fermat packet.
