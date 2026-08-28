# PUU-L007 — Fresh-Prime Lift / Unique Deletion

## 0. Current checkpoint

Branch:

```text
wip/number-theory-primorial-unit-universe-260827-v0
```

PUU-L006 completed the one-period survivor layer:

```text
finite prime basis S
  ↓
period M(S)
  ↓
one-period survivor seats
  ↓
not reserved ↔ coprime to M(S)
  ↓
reflection r ↦ M(S)-r
```

The next checkpoint must formalize the local replication mechanism when one fresh prime scale `q` is added.

This is the first checkpoint where the primorial wheel begins to self-replicate.

Do **not** yet prove the global cardinal recurrence for the whole next wheel.  PUU-L007 is the **per-old-survivor unique-deletion theorem**.  The whole-wheel decomposition/cardinality recurrence belongs to PUU-L008.

---

## 1. Mathematical target

Let `S : Finset ℕ` be a finite prime basis and let

```text
M := finitePrimeBasisProduct S.
```

Let `q` be a fresh ordinary prime:

```text
Nat.Prime q
q ∉ S
```

and let `r` be one old wheel survivor:

```text
IsPrimeBasisWheelSurvivor S r.
```

For `0 ≤ j < q`, define the `q` lifts of `r` by

```text
r + j*M.
```

Because `r` survived the old basis and the old reservation pattern is periodic modulo `M`, **every lift still survives all primes in `S`**.

Adding the new prime `q` changes exactly one thing: among the `q` lifts, exactly one is divisible by `q`.

Thus each old survivor produces

```text
q lifts
  ↓
exactly one deleted by q
  ↓
q-1 surviving lifts for S ∪ {q}
```

The unique-deletion theorem is the core of PUU-L007.

---

## 2. New module

Create a focused module such as:

```text
DkMath/NumberTheory/PrimorialUniverse/FreshPrimeLift.lean
```

Import only the currently needed PrimorialUniverse layer plus Mathlib support required for modular/coprime arithmetic.

Export it through:

```text
DkMath/NumberTheory/PrimorialUniverse.lean
```

Do not import Legendre, PowerSwap, GN/CosmicFormula, analytic number theory, or old PrimitiveStructure residual-ledger modules.

---

## 3. Suggested vocabulary

A minimal lift definition is useful:

```lean
def primeBasisWheelLift (S : Finset ℕ) (r j : ℕ) : ℕ :=
  r + j * finitePrimeBasisProduct S
```

Naming may change if a cleaner public API emerges, but keep the semantics explicit.

Do not yet define a global wheel recursion structure or generic category/lattice abstraction.

---

## 4. Required theorem packet

### 4.1 Product after adjoining a fresh prime

For `q ∉ S`, expose the exact product formula:

```text
finitePrimeBasisProduct (insert q S)
  = q * finitePrimeBasisProduct S
```

(up to multiplication order if the canonical simplifier prefers `M*q`).

This theorem should not require `q` to be the numerically next prime; freshness is enough.

### 4.2 Fresh prime is coprime to the old period

From

```text
IsFinitePrimeBasis S
Nat.Prime q
q ∉ S
```

prove

```text
Nat.Coprime q (finitePrimeBasisProduct S)
```

or the symmetric orientation.

This is the arithmetic reason the progression

```text
r, r+M, r+2M, ..., r+(q-1)M
```

hits every residue modulo `q` exactly once.

### 4.3 Old reservation status is unchanged along every lift

For any `j`, prove a theorem equivalent to

```text
ReservedByPrimeBasis S (primeBasisWheelLift S r j)
  ↔
ReservedByPrimeBasis S r
```

by reusing PUU-L005 periodicity rather than reproving prime-by-prime divisibility.

Therefore, if `r` is an old survivor, every lift is still unreserved by all primes in `S`.

### 4.4 Lift range inside the enlarged period

If

```text
IsPrimeBasisWheelSurvivor S r
j < q
```

then prove

```text
0 < primeBasisWheelLift S r j
```

and

```text
primeBasisWheelLift S r j
  < finitePrimeBasisProduct (insert q S).
```

This is needed so surviving lifts are genuine one-period survivors of the enlarged basis.

### 4.5 Unique q-deleted lift

Main arithmetic theorem:

```text
∃! j : ℕ,
  j < q ∧
  q ∣ primeBasisWheelLift S r j
```

under assumptions:

```text
IsFinitePrimeBasis S
Nat.Prime q
q ∉ S
IsPrimeBasisWheelSurvivor S r
```

The proof may use whichever Mathlib modular API is cleanest:

- `Nat.ModEq`,
- modular inverse from coprimality,
- `ZMod q`,
- a permutation-of-residues theorem,
- or an elementary coprime argument.

Do not hard-code a closed formula for the deleted index unless it genuinely simplifies the Lean API.  Existence-and-uniqueness is the mathematical invariant needed downstream.

### 4.6 Enlarged-basis reservation iff q deletes the lift

For an old survivor `r` and `j < q`, prove the conceptual bridge:

```text
ReservedByPrimeBasis (insert q S) (primeBasisWheelLift S r j)
  ↔
q ∣ primeBasisWheelLift S r j
```

because no old basis prime can reserve the lift.

This theorem is important: it states that **the only new deletion channel in the lifted fiber is the fresh prime q**.

### 4.7 Unique deleted lift in the enlarged wheel

Package 4.5 and 4.6 into the semantic theorem:

```text
among j < q, exactly one lifted seat is reserved by insert q S
```

or equivalently:

```text
∃! j : ℕ,
  j < q ∧
  ReservedByPrimeBasis (insert q S) (primeBasisWheelLift S r j)
```

This is the principal PUU-L007 theorem.

---

## 5. Optional but desirable local replication count

If the finite-set proof is small and natural, define the surviving lift-index set for one fixed old survivor and prove its cardinality is `q - 1`.

For example conceptually:

```text
{j < q | the lift is not reserved by insert q S}.card = q - 1
```

This is **desirable but not required for Outcome A** if it causes a disproportionate amount of Finset plumbing.

The global theorem

```text
|next wheel survivors| = (q-1) * |old wheel survivors|
```

must **not** be forced into PUU-L007.  That is the main target of PUU-L008, where disjointness and completeness of all lift fibers can be handled cleanly.

---

## 6. Concrete `{2,3} → {2,3,5}` regression

Use the existing old wheel

```text
S = {2,3}
M = 6
survivors = {1,5}
q = 5.
```

The two lift fibers are:

```text
r = 1:
  1, 7, 13, 19, 25
  deleted by 5: 25

r = 5:
  5, 11, 17, 23, 29
  deleted by 5: 5
```

Thus the remaining seats are exactly the familiar 30-wheel residues:

```text
1, 7, 11, 13, 17, 19, 23, 29.
```

PUU-L007 does not need to prove the entire eight-element Finset equality if that belongs more naturally to PUU-L008, but include at least visible regression theorems identifying the two unique deleted indices/points:

```text
r=1  -> deleted j=4 / point 25
r=5  -> deleted j=0 / point 5
```

A small extra regression proving representative surviving lifts is welcome.

---

## 7. Semantic boundary

Keep the following distinctions explicit in docstrings/report.

1. `q` is a **fresh prime**, not necessarily the next prime numerically.
2. The `q` lifts are copies of one old survivor seat across the enlarged period.
3. Old-prime reservation does not change along a lift fiber.
4. Exactly one lift is newly deleted by `q`.
5. Therefore the local branch factor is `q-1`.
6. This is not yet the global next-wheel decomposition/cardinality theorem.
7. Survivor still means “unreserved by the finite basis”, not “ordinary prime”.
8. No Legendre or prime-density conclusion follows at this checkpoint.

---

## 8. Stop conditions / outcomes

### Outcome A+

Complete:

- fresh-prime product/coprime lemmas,
- old-reservation lift invariance,
- lift range,
- unique `q`-divisible lift,
- enlarged-basis reservation iff `q`-divisibility,
- semantic unique-deletion theorem,
- concrete 6→30 regression,
- optional local `q-1` count if inexpensive.

Then stop and report.  Do not proceed to PUU-L008 automatically.

### Outcome B

If existence of the deleted index is easy but uniqueness requires missing Mathlib infrastructure, isolate the strongest exact modular theorem reached and report the missing bridge.  Do not replace uniqueness with brute-force bounded search.

### Outcome C

If the proposed unique-deletion claim encounters a mathematical counterexample under the stated assumptions, stop immediately and report the smallest counterexample and which assumption is insufficient.

---

## 9. Verification / report

As with previous checkpoints:

- focused module build,
- PrimorialUniverse facade build,
- full project build according to the current repository workflow,
- `git diff --check`,
- no new `admit` / `axiom` / `native_decide`,
- no unintended widening into later PUU layers.

Create a report in the same dev-doc directory describing:

- exact public declarations,
- proof route for unique deletion,
- whether local `q-1` cardinality was included,
- concrete 6→30 regression,
- precise boundary before PUU-L008.
