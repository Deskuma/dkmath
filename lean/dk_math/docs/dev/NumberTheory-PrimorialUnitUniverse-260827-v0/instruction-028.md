# PUU-L028 — Square-Anchor Block Quotient / Old-Period Monodromy

## 0. Status / purpose

PUU-L027 completed the one-step square-anchor successor transport on a fixed old basis:

```text
r_n = n mod M
carry_n in {0,1}
C_{n+1} - C_n = carry_n - M^{-1}
R_{n+1} - R_n = M^{-1}
Pplus_{n+1}  - Pplus_n  = carry_n
Pminus_{n+1} - Pminus_n = carry_n - 2*M^{-1}
```

where `M = finitePrimeBasisProduct S` and all affine phase coordinates are read in `ZMod q` for a fresh prime `q`.

This checkpoint should not merely iterate the successor theorem mechanically.  First identify the closed form of the dynamic plus sheet, then derive the exact transport over one whole old period and finally connect that monodromy to the enlarged fresh-prime period `q*M`.

Remain entirely inside `DkMath.NumberTheory.PrimorialUniverse`.  Do not import Legendre consumers.

Preferred module:

```lean
DkMath.NumberTheory.PrimorialUniverse.SquareAnchorPhasePeriodTransport
```

Preferred import:

```lean
import DkMath.NumberTheory.PrimorialUniverse.SquareAnchorPhaseSuccessorTransport
```

Export through `DkMath.NumberTheory.PrimorialUniverse` and update the facade docstring.

---

## 1. Old-period block quotient

Let

```text
M := finitePrimeBasisProduct S.
```

The canonical representative from L027 is

```text
r_n = n % M.
```

Define, or expose directly without a new definition if cleaner, the Euclidean block quotient

```lean
def squareAnchorPhaseBlockQuotient
    (S : Finset ℕ) (n : ℕ) : ℕ :=
  n / finitePrimeBasisProduct S
```

and prove the exact decomposition

```text
n = r_n + Q_n * M.
```

Preferred theorem shape:

```lean
squareAnchorPhaseRepresentative_add_blockQuotient
```

or the equivalent orientation.

This is ordinary Euclidean division; keep it provider-side and explicit.

---

## 2. Plus-sheet quotient normal form

The main new closed form is

```text
Pplus_n = Q_n   in ZMod q.
```

Preferred theorem:

```lean
squareAnchorFreshPrimePlus_eq_blockQuotient
```

with conclusion

```lean
squareAnchorFreshPrimePlus S q n =
  (squareAnchorPhaseBlockQuotient S n : ZMod q)
```

under only the assumptions required to invert the old period modulo the fresh prime (`hS`, `hq`, `hqS`).

Derive this from

```text
Pplus_n = C_n + R_n
        = (-r_n + n) * M^{-1}
```

and the Euclidean decomposition.  Do not prove it by induction on the L027 successor law.

Mathematical reading:

```text
the dynamic plus sheet is exactly the old-period block number, reduced modulo q.
```

This should explain why the plus-sheet successor increment equals the carry.

---

## 3. Carry as quotient increment

Make the connection explicit in natural numbers:

```lean
squareAnchorPhaseBlockQuotient_succ
```

with conclusion equivalent to

```text
Q_(n+1) = Q_n + carry_n.
```

Since `carry_n ∈ {0,1}`, this identifies the L027 carry as the exact change of old-period block index.

If convenient, also prove the iff forms:

```text
carry_n = 0 ↔ Q_(n+1) = Q_n
carry_n = 1 ↔ Q_(n+1) = Q_n + 1.
```

Do not add unrelated quotient arithmetic.

---

## 4. One whole old-period transport

Prove the exact shift by one old period:

```lean
squareAnchorPhaseRepresentative_add_period
```

```text
r_(n+M) = r_n.
```

Then derive:

```lean
squareAnchorFreshPrimeCenter_add_period
```

```text
C_(n+M) = C_n.
```

```lean
squareAnchorFreshPrimeRadius_add_period
```

```text
R_(n+M) = R_n + 1.
```

and the two dynamic phase sheets:

```lean
squareAnchorFreshPrimePlus_add_period
```

```text
Pplus_(n+M) = Pplus_n + 1.
```

```lean
squareAnchorFreshPrimeMinus_add_period
```

```text
Pminus_(n+M) = Pminus_n - 1.
```

These are central theorems of L028.

Prefer direct proofs from the closed forms / Euclidean decomposition rather than summing `M` successor steps.

Mathematical reading:

```text
one full revolution of the old anchor coordinate fixes the center,
but rotates the two phase sheets by +1 and -1 on the fresh-prime index circle.
```

---

## 5. k-period monodromy

Generalize the previous result to `k` old periods:

```lean
squareAnchorFreshPrimeCenter_add_mul_period
squareAnchorFreshPrimeRadius_add_mul_period
squareAnchorFreshPrimePlus_add_mul_period
squareAnchorFreshPrimeMinus_add_mul_period
```

Preferred conclusions in `ZMod q`:

```text
C_(n+kM)      = C_n
R_(n+kM)      = R_n + k
Pplus_(n+kM)  = Pplus_n + k
Pminus_(n+kM) = Pminus_n - k.
```

The exact argument order is flexible.

This is the finite monodromy law of the square-anchor phase pair over the old-period circle.

---

## 6. Fresh-prime enlarged-period closure

For fresh prime `q`, use

```text
finitePrimeBasisProduct (insert q S) = q * M
```

(up to the repository's canonical multiplication orientation) and the `k=q` monodromy law to prove exact closure:

```lean
squareAnchorFreshPrimeCenter_add_enlarged_period
squareAnchorFreshPrimeRadius_add_enlarged_period
squareAnchorFreshPrimePlus_add_enlarged_period
squareAnchorFreshPrimeMinus_add_enlarged_period
```

Conceptually:

```text
X_(n + q*M) = X_n
```

for all four `ZMod q` coordinates, since `(q : ZMod q) = 0`.

At minimum, prove the plus/minus closure and one theorem explicitly identifying `q*M` with the inserted-basis period.

This is the key Phase E3 bridge:

```text
old-period monodromy repeated q times
    =
closure at the fresh-prime enlarged period.
```

Do not overstate this as a global orbit-period minimality theorem.  It proves a period, not necessarily the least period.

---

## 7. Optional orbit traversal theorem

Only if it is clean and short, record that for `0 ≤ k < q`, the plus-sheet values along

```text
n, n+M, ..., n+(q-1)M
```

are translated by the distinct residues `k : ZMod q`.

A possible theorem is injectivity of

```text
k ↦ squareAnchorFreshPrimePlus S q (n + k*M)
```

on `Fin q` or on naturals `< q`.

Likewise for the minus sheet.

This is optional for L028.  Do not let finite-orbit packaging obscure the required normal form and monodromy theorems.

---

## 8. Visible regression

Use

```text
S = {2,3}
M = 6
q = 5.
```

Record through public L028 APIs that:

```text
Pplus_4 = 0
Pplus_10 = 1
Pplus_16 = 2
...
Pplus_34 = 0   in ZMod 5
```

and correspondingly the minus sheet moves by `-1` per old period.

At minimum verify:

```text
Pplus_(4+6) - Pplus_4 = 1
Pminus_(4+6) - Pminus_4 = -1
Pplus_(4+30) = Pplus_4
Pminus_(4+30) = Pminus_4.
```

Route the regression through public period-transport theorems rather than detached arithmetic alone.

---

## 9. Report

Create:

```text
lean/dk_math/docs/dev/NumberTheory-PrimorialUnitUniverse-260827-v0/
  primorial-unit-universe-square-anchor-period-monodromy-260828.md
```

The report must state explicitly:

1. L027 gave the one-step carry law; L028 gives a closed block-quotient normal form and whole-period transport.
2. `Pplus_n` is exactly the old-period quotient `n / M` modulo `q`.
3. one old-period turn fixes the center and shifts the phase pair by `(+1,-1)`.
4. `k` old-period turns give `(+k,-k)`.
5. `q` old-period turns close because the enlarged fresh-prime period is `q*M`.
6. this is an exact compatibility theorem between anchor dynamics and fresh-prime tower growth.
7. no square-shell escape or prime-existence conclusion is claimed.

---

## 10. A+ rubric

Outcome A+ if the implementation establishes:

1. exact Euclidean representative/quotient decomposition;
2. `Pplus_n = n / M` in `ZMod q`;
3. carry = block-quotient successor increment;
4. center invariance under `+M`;
5. radius shift `+1` under `+M`;
6. plus/minus monodromy `(+1,-1)` under `+M`;
7. generalized `(+k,-k)` under `+k*M`;
8. closure under `+q*M` / inserted-basis period;
9. the `6 -> 30` visible regression;
10. facade export + docstrings + report.

---

## STOP

Do **not** add in L028:

- Legendre or `escapingSquareOffsets`;
- square-shell escape existence;
- a claim that `q*M` is the least period;
- Jacobsthal / wheel-gap bounds;
- neutral-seat primality/compositeness;
- PowerSwap / GN / CosmicFormula;
- PNT / RH;
- prime powers;
- asymptotic density;
- arbitrary consumer counting.

L028 is specifically the block-quotient normal form and old-period monodromy theorem, culminating in exact closure at the fresh-prime enlarged period.
