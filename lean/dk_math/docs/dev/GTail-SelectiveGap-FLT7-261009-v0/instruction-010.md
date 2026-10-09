# Instruction 010 — q-local square allocation in the GTail seven bridge

Date: 2026-10-09
Branch: `feature/GTail-SelectiveGap-FLT7-261009-v0`
Working directory: `lean/dk_math`
Prerequisites: `review-009.md`, `report-009.md`, `constraint-ledger-006.md`.
Scope: **Step 010 only. Do not attempt FLT7 closure, q-order 21 or descent.**

## Objective

For a primitive positive hypothetical Fermat7 solution with `a+b=c+g`, use the proved exact product

```text
g*T = 7*a*b*(a+b)*Q^2
T = GTail 7 1 g c
Q = a^2 + a*b + b^2
```

to investigate the **prime-q allocation of Q²**, where q is prime, q≠7 and q∣Q. The first goal is a q-adic valuation balance. A second, separate goal is to exclude splitting q between both g and T under a correctly proved local endpoint-unit condition. These are necessary constraints, not an FLT7 contradiction.

## Phase 0 — identify reusable sources

Read the exact declarations in `GTailBridge`, `GTailConstraintAudit`, `GTailSevenArithmetic`, `GTailCongruence`, `GTailNat`, `GTailPadic`, `Lib.NumberTheory.PadicValNat`, and the Step 008–009 modules. Inspect existing FLT7 prime support / cyclotomic source declarations but avoid importing the heavy Seven façade or unrelated closure owners. Record exact overlap, carrier/index convention, signatures and minimal import graph in `source-inventory-010.md`.

## Phase 1 — neutral head-unit prime exclusion

Over naturals prove a new lemma, or reuse a suitable existing lemma, equivalent to:

```text
Nat.Prime q, q ≠ 7, q ∣ g, ¬q ∣ c
  → ¬ q ∣ GTail 7 1 g c
```

When q∣g, the normalized tail is congruent to its constant coefficient `7*c^6` modulo q. The head is a q-unit given q≠7 and q∤c. Reuse `GTail_not_dvd_of_head_unit_of_prime_dvd_x` or the established congruence API instead of expanding every Pascal coefficient.

Satisfiable tests with the actual GTail:
- q=13,g=13,c=2, where q∣g but q∤T;
- q=43,g=3,c=1, where q∤g and q∣T (as `GTail 7 1 3 1 = 5461 = 43*127`).
Use Lean to check the concrete values. Do not add a hypothetical Fermat equation to either test.

Suggested neutral owner: `DkMath/Lib/Cosmic/GTailSevenPrimeAllocation.lean`.

## Phase 2 — local q-unit consequences in the primitive exact branch

With `0<a`, `0<b`, `Nat.Coprime a b`, `hEq : Fermat7Equation a b c`, `hsum : a+b=c+g`, `hq : Nat.Prime q`, `hq7 : q ≠ 7` and `hqQ : q∣Q`, prove:

1. `¬q∣a*b*(a+b)` from `coprime_product_seven_quadratic`, hence `¬q∣a+b`.
2. **Derive `¬q∣c`**, rather than assuming it. Via the exact Step 005/Step 004 power bridge and q∣Q, prove q divides the difference between `(a+b)^7` and `c^7` (use an additive identity to avoid truncated subtraction). If q∣c, primality would give q∣a+b, contradiction.
3. Using Phase 1, prove `q∣g → ¬q∣T`. From the product and q∣Q, derive `q∣g ∨ q∣T`. Together these constrain q to exactly one of the two left-hand factors.

Do not claim global `Nat.Coprime g c` or `Nat.Coprime g Q` from primitive a,b. The proposed result is strictly **local to q∣Q**. If a premise cannot be discharged from the actual equation, document it and give a corrected theorem rather than a hidden assumption.

## Phase 3 — valuation budget and square-factor allocation

Prove under the same explicit hypotheses:

```text
padicValNat q g + padicValNat q T = 2 * padicValNat q Q
```

Use q≠7 to show q∤7, plus Phase 2 to show q∤ab(a+b). Prove g≠0 from focused height, T≠0 from positivity of the exact product, and supply the prime Fact/nonzero hypotheses required by valuation multiplicativity.

**Only after proving the Phase 2 exclusion**, upgrade the balanced valuation into:

```text
(q^2 ∣ g ∧ ¬q∣T) ∨ (q^2 ∣ T ∧ ¬q∣g)
```

because q∣Q makes `v_q(Q)≥1`, the sum is at least two, and exclusion forces all positive valuation onto one factor. A plain product-divisibility assertion cannot justify this upgrade. If any part fails, retain the correct weaker budget and report the smallest blocker (Outcome C for the attempted stronger assertion).

## Phase 4 — calibration, overlap, audit

Prefer a small satisfiable neutral **abstract-product** valuation lemma, independent of Fermat. For instance q=43, abstract factors g=43²,T=7,A=B=C=1,Q=43 satisfy `g*T=7*A*B*C*Q²`. They are not a claim that T is the GTail of such an FLT packet. Show also why valuation equality alone does not ban a mixed q allocation in an arbitrary product, and distinguish the actual GTail head-unit exclusion.

Compare with named existing FLT7 prime-support and local cyclotomic results. A fresh coordinate-specific necessary statement is not automatically a new independent obstruction; do not claim novelty without precise source and hypothesis comparison. Defer the order-21 question and Norm/unit carrier transport to later separate instructions.

## Deliverables and stop

Suggested:
- `DkMath/Lib/Cosmic/GTailSevenPrimeAllocation.lean` and focused neutral test;
- `DkMath/FLT/Seven/GTailPrimeAllocationAudit.lean` and focused owner test;
- `source-inventory-010.md`, `report-010.md`, truthful `ROADMAP.md` update.

Run low-memory incremental, sequential focused builds for actual created modules and Step 009 regressions, with `LEAN_NUM_THREADS=2`. Report commands, exit statuses, full signatures, `#print axioms` outputs, exact prerequisite differences and any repaired false conjectures. No added `sorry`, `admit`, `axiom`, `unsafe`, or circular FLT7 impossibility endpoint. No full costly all-test suite, Legendre edits, façade promotion, PR, merge or outside proof-corpus search.

**STOP after Step 010.** Outcome B for checked allocation but no FLT7 closure, Outcome C for a disproved or insufficiently justified upgrade, Outcome A only for a separately validated genuinely new noncircular FLT7 restriction (still not closure).
