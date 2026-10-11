# Instruction 011 — finite-field order-3/order-7 intersection at a focused GTail prime

Date: 2026-10-10
Branch: `feature/GTail-SelectiveGap-FLT7-261009-v0`
Working directory: `lean/dk_math`
Prerequisites: `review-010.md`, `report-010.md`, `source-inventory-010.md`
Scope: **Step 011 only. No FLT7 closure, descent, Norm/unit-class transport or new facade promotion.**

## Mission

From Step 010's exclusive support of a prime q dividing the quadratic `Q=a²+a*b+b²`, identify an **additional restriction that applies specifically when q is carried by the normalized GTail T**, not by the gap g.

Target: on the **T side**, a prime q≠7 dividing both Q and T under the appropriate q-unit hypotheses must satisfy `21 ∣ (q - 1)` (or equivalent `q % 21 = 1`). The reason must be two *independently nontrivial finite-field multiplicative orders*: order 3 from Q, order 7 from the tail. This condition must **not** be asserted universally for all primes of Q; on the g side no nontrivial seventh root is available.

Prove **nonvacuous neutral residue/order theorems first**, without any Fermat equation. Only afterward expose a small FLT7-facing T-branch corollary, keeping it separate from the exact hypothesis's consistency question.

## Phase 0 — inventory and implementation discipline

Before editing inspect exact signatures in:
- `DkMath/Lib/Cosmic/GTailSevenPrimeAllocation.lean`, `GTailCyclotomic.lean`, `GTailNat.lean`;
- `DkMath/FLT/Seven/GTailPrimeAllocationAudit.lean`, `GTailBridge.lean`;
- Mathlib `ZMod` field instances, `Units`, `orderOf`, `orderOf_dvd_card_univ`, finite group cardinality and roots of unity;
- existing narrow DkMath prime/cyclotomic/order lemmas; inspect but **do not import** typed FLT7 root-depth/Norm/unit-carrier owners to shortcut the scalar proof.

Create `source-inventory-011.md`: exact existing endpoints, required nonzero assumptions, prime exceptions 3 and 7, suitable existing finite-group order API, and minimal import closure. Avoid inventing an order lemma name if an exact Mathlib theorem exists.

## Phase 1 — nonvacuous neutral order-seven theorem

For prime q, q≠7, q∤c, q∤g and q∣`GTail 7 1 g c`, prove `7 ∣ q - 1`.

Suggested method: work in `ZMod q` with `Fact (Nat.Prime q)`; define the ratio `r=(c+g)/c` as a **unit** with appropriate nonzero proof, and show
- `r^7 = 1` from `(c+g)^7 = c^7 + g*T` and `q∣T`;
- `r ≠ 1` from `q∤g`;
- hence `orderOf r = 7` since 7 is prime;
- `orderOf r ∣ |(ZMod q)ˣ| = q-1` via finite group Lagrange.

Show why `r` is nonzero: its seventh power is one, so it cannot be zero. Do not silently use a field division operation before the prime field and nonzero denominator are established.

The order-seven lemma must not require q∣Q, an FLT equation, or `a+b=c+g`. A separate result should note that its conclusion excludes q=3 (since 7 does not divide 2), enabling the next phase without an extra q≠3 assumption if convenient.

## Phase 2 — neutral order-three theorem

For prime q≠3 with q∣`Q=a²+a*b+b²` and q∤a,b, prove `3 ∣ q - 1`.

In `ZMod q`, use the unit ratio `s=a/b`, the quadratic equation `s²+s+1=0`, and the factorization `s³-1=(s-1)(s²+s+1)` to establish `s³=1`.

Then show `s≠1`: if a=b mod q, the quadratic value becomes `3*b²`, impossible for prime q≠3 and q∤b. Hence `orderOf s=3`, and Lagrange yields `3∣q-1`.

The prime q=3 is a genuine exception: modulo 3 the quadratic has a repeated root equal to one. **Do not** apply the nontrivial order-three conclusion at q=3.

## Phase 3 — neutral order-21 intersection

Combine Phases 1 and 2. Under
```text
Nat.Prime q, q ≠ 7
q ∣ a²+a*b+b²
q ∣ GTail 7 1 g c
¬q∣a, ¬q∣b, ¬q∣c, ¬q∣g
```
prove `21 ∣ q-1`. Derive q≠3 from the order-seven conclusion if doing so is convenient. Use Coprime 3 7 to combine the two divisibilities, with no unjustified multiplication of arbitrary divisors.

This theorem must be **neutral and satisfiable**. It should make no use of `Fermat7Equation`, positive Fermat candidates, or typed FLT7 cyclotomic carriers.

### Required complete modular calibration

Test q=43, (a,b,c,g)=(5,8,9,4):
- a+b=c+g, Coprime a b;
- Q=129=43*3; 43∣Q;
- 43∣GTail 7 1 4 9; 43∤a*b*c*g;
- 21∣43-1 (indeed 42∣42);
- `(a^7+b^7)%43 = c^7%43`;
- `¬Fermat7Equation 5 8 9`.

Use `decide` or bounded arithmetic for finite concrete claims. This is a **nonvacuous modular** calibration and emphatically not an exact positive Fermat solution.

### Contrast: g side

For q=13, (a,b,c,g)=(14,29,30,13), test:
- a+b=c+g, Coprime a b, q∣Q and q∣g;
- q∤c, q∤T by Step 010's head-unit theorem;
- 21∤q-1.

It deliberately shows that **order 21 is not forced on the g branch** from neutral data. Check values in Lean, and if a finite calibration is wrong, correct or replace it rather than weaken the mathematical theorem.

## Phase 4 — FLT7-facing, branch-guarded corollary

Only after the neutral proofs compile, attach to Step 010's exact branch, under:
```text
0<a, 0<b, Nat.Coprime a b
Fermat7Equation a b c
a+b=c+g
Nat.Prime q, q≠7, q∣Q, q∣T
```
the consequence `21∣q-1`. Derive q∤a,b and q∤c from existing Step 010 theorems, and q∤g from `prime_focused_support_exclusive` or its head-unit exclusion. **Do not require q∤g as a hidden extra assumption** if the Step 010 result can discharge it. Keep direct narrow imports; no broad Seven facade.

Optionally use contraposition to formulate a clean necessary routing statement: if q∣Q but `¬21∣q-1`, then q must be on the gap side, hence q²∣g by Step 010. This is a candidate **separate branch-sensitive** consequence: prove it only if the neutral order lemma and existing exact square allocation make it straightforward.

## Phase 5 — report and safeguards

Suggested modules:
- `DkMath/Lib/NumberTheory/GTailSevenPrimeOrder.lean` (or a better narrow neutral location);
- `DkMath/FLT/Seven/GTailPrimeOrderAudit.lean`;
- corresponding small `DkMathTest` regression modules;
- `source-inventory-011.md`, `report-011.md` and an accurate project `ROADMAP.md` update.

Build only created modules/tests and the relevant Step 010 regressions, sequentially and incrementally with `LEAN_NUM_THREADS=2`. Record exact exit statuses, statement signatures, axiom lists and import dependencies. Use `#print axioms` for all new public theorems; do not add `sorry`, `admit`, axioms, unsafe code, pre-proved FLT7 impossibility endpoints or ex-falso proof routes. Preserve the separation of satisfiable neutral examples and contradictory exact FLT7 assumptions.

**Outcome B expected:** fully checked neutral order mechanism and correctly guarded conditional prime-address consequence, but no contradiction/descent. If the q=3 or q=7 boundary invalidates an overstrong statement, record Outcome C and the repaired prerequisites; do not hide exceptions. Claim Outcome A only for a genuinely new independent FLT7 obstruction verified against existing named local theorems.

**STOP after Step 011.** Do not attempt number-field Norm/unit carrier conversion, global order constraints on the g branch, construction of a new Fermat packet, broad all-test runs, PR or merge.
