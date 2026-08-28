# PUU-L036 — Successor-Pair Minimizer Deletion / Tied-Pair Fresh-Prime Obstruction

## 0. Purpose

PUU-L034 found genuine positive-offset information from coupling consecutive square anchors. PUU-L035 then proved the exact fresh-prime first-hit transition law:

```text
H_(insert q S)^+(n) = H_S^+(n)
  ↔ ¬ q ∣ (n² + H_S^+(n)),
```

with strict delay exactly when the fresh prime deletes the old first-hit seat.

This checkpoint should combine those two results at the **pair minimizer** level. It is intended as the final information audit of the current first-hit/basis-growth route, not as another numerical primorial expansion.

Preferred module:

```lean
DkMath.NumberTheory.PrimorialUniverse.SquareAnchorOffsetSuccessorPairFreshPrimeTransport
```

Preferred import:

```lean
import DkMath.NumberTheory.PrimorialUniverse.SquareAnchorOffsetFreshPrimeFirstHitTransport
```

Remain entirely provider-side.

---

## 1. Pair minimizer seats

Use the existing abbreviations conceptually:

```text
H0 = H_S^+(n)
H1 = H_S^+(n+1)
P  = min H0 H1
```

Do not introduce an opaque graph abstraction unless it materially simplifies the proofs.

Expose a theorem saying that an old side is a pair minimizer exactly when its first hit equals `P`.

Suggested simple predicates are acceptable:

```lean
def IsLeftPairMinimizer ... : Prop := H0 = P
def IsRightPairMinimizer ... : Prop := H1 = P
```

or avoid the definitions and state the equalities directly.

---

## 2. Exact pair persistence criterion under fresh insertion

Let `P'` be the successor-pair positive first hit for `insert q S`.

Prove pointwise monotonicity by reusing L035:

```text
P ≤ P'.
```

Then prove the exact persistence criterion:

```text
P' = P
↔
  (H0 = P ∧ ¬ q ∣ (n² + H0))
  ∨
  (H1 = P ∧ ¬ q ∣ ((n+1)² + H1)).
```

Interpretation: the pair persists iff at least one old minimizing side survives the fresh-prime insertion.

Equivalent formulations are acceptable if they preserve this exact semantics.

Also expose the strict-delay dual:

```text
P < P'
↔
  (H0 = P → q ∣ (n² + H0))
  ∧
  (H1 = P → q ∣ ((n+1)² + H1)).
```

In words: **every old pair minimizer must be deleted** in order to move the pair forward.

Do not prove this by finite enumeration; derive it from L034 min semantics and the L035 single-anchor deletion-delay law.

---

## 3. Tied-pair simultaneous deletion theorem

Assume

```text
H_S^+(n) = H_S^+(n+1) = h.
```

If fresh insertion strictly delays the pair, prove that the fresh prime divides both old minimizing raw seats:

```text
q ∣ n² + h
q ∣ (n+1)² + h.
```

Then derive the key arithmetic obstruction:

```text
q ∣ 2*n + 1.
```

The proof should use

```text
((n+1)² + h) - (n² + h) = 2*n + 1
```

in an appropriate Nat/Int divisibility form. Avoid ad hoc numerical reasoning.

Checkpoint-facing theorem shape:

```lean
theorem freshPrime_dvd_successor_increment_of_tied_pair_delay ... :
  q ∣ 2 * n + 1
```

Naming may vary.

---

## 4. Persistence when the fresh prime misses the successor increment

Derive the contrapositive provider theorem:

```text
H0 = H1
¬ q ∣ (2*n+1)
→ P' = P.
```

This is the main structural result of L036.

Also derive the useful size corollary:

```text
H0 = H1
2*n+1 < q
→ P' = P
```

using primality only as needed for positivity/nontriviality; `q > 2*n+1 > 0` makes divisibility impossible.

This is **not** a Legendre shell-width theorem. `2*n+1` appears here only as the exact difference of consecutive squares and as the simultaneous-deletion obstruction.

---

## 5. Untied branch boundary

Record explicitly that if `H0 ≠ H1`, the old pair has a unique minimizing side. In that case a fresh prime can delay the pair by deleting that one minimizing seat; no `q ∣ 2*n+1` conclusion follows from pair delay alone.

If convenient, prove the two exact unique-minimizer specializations:

```text
H0 < H1 → (P < P' ↔ q ∣ n² + H0)
H1 < H0 → (P < P' ↔ q ∣ (n+1)² + H1)
```

These are useful but secondary to the tied-pair theorem.

---

## 6. Finite regression

Use a small visible regression only to validate the public API. Do not make the checkpoint depend on another large brute-force primorial scan.

A suitable target is to locate a tied pair in one of the already implemented bases (`{2,3}`, `{2,3,5}`, or `{2,3,5,7}`) and demonstrate:

```text
fresh q misses 2*n+1
→ tied pair persists
```

If no convenient tied pair/fresh-prime example exists without unnecessary computation, a symbolic regression theorem exercising the exact API is acceptable.

The theorem-level obstruction is more important than a large numeric example.

---

## 7. Information verdict

Preferred Outcome A if the tied-pair obstruction is formalized:

```text
Outcome A — TIED-PAIR FRESH-PRIME OBSTRUCTION FOUND

A fresh prime can strictly delay an equal-minimum successor pair only if it
also divides the intrinsic successor increment 2*n+1.
```

This is stronger information than L035 single-seat deletion because simultaneous pair deletion creates an additional divisibility constraint that does not exist for one anchor alone.

However, do **not** claim:

- that every pair becomes tied;
- that pair radii have a uniform bound;
- that repeated basis growth must terminate;
- that a finite coverage obstruction is proved;
- any Legendre conclusion.

If the exact pair persistence criterion reduces to L035 without yielding the tied-pair divisibility obstruction, record Outcome B instead.

---

## 8. Branch-closeout gate

Treat L036 as the final information audit of the current first-hit/basis-growth route.

After L036, do **not** automatically continue to longer anchor windows or larger primorial regressions.

The report must end by classifying the branch state:

```text
A. provider obstruction seed found, but no uniform coverage theorem;
B. pair×basis-growth adds no further information and route closes;
C. a genuinely basis-independent finite coverage obstruction was unexpectedly proved.
```

In cases A or B, recommend closing this branch as a successful finite-provider study and moving any further attack to a separately scoped branch.

---

## STOP

Do not introduce:

- Legendre imports or consumers;
- `SquareCell`, `SquareOffset`, `escapingSquareOffsets`;
- a consumer shell-width assumption;
- Jacobsthal / maximum-wheel-gap machinery;
- longer 3+ anchor windows;
- another large primorial scan as the main theorem;
- PNT / RH / asymptotic density;
- PowerSwap / GN / CosmicFormula integration;
- claims of uniform termination or bounded delay.

Keep the checkpoint finite, exact, and focused on the new simultaneous-deletion obstruction.