# PUU-L012 — Successor Square-Shell Transition / Fresh-Threshold Two-Seat Audit

## Goal

PUU-L011 completed the dictionary

```text
SquareOffsetCovered
  ↔ bounded-prime reservation
  ↔ failure of projected wheel survival
```

and reduced Legendre to projected-wheel escape for every `n ≥ 2`.

The next step must **not** assume that a prime-free/full-cover square shell at `n`
automatically propagates to `n+1`.  Instead, formalize the exact successor-shell
transition and isolate the genuine missing propagation theorem.

Implement this checkpoint in the Legendre consumer layer.

Preferred module:

```text
DkMath/NumberTheory/Legendre/PrimorialWheelSuccessor.lean
```

Import only what is needed, preferably:

```lean
import DkMath.NumberTheory.Legendre.PrimorialWheelBridge
```

Export it from `DkMath.NumberTheory.Legendre`.

---

## 1. Exact bounded-prime basis transition

For `q = n + 1`, prove the exact transition of `primeScalesUpTo`.

Preferred theorem shape:

```lean
theorem primeScalesUpTo_succ_eq
    (n : ℕ) :
    primeScalesUpTo (n + 1) =
      if Nat.Prime (n + 1) then
        insert (n + 1) (primeScalesUpTo n)
      else
        primeScalesUpTo n
```

Equivalent split theorems are acceptable:

```lean
Nat.Prime (n+1) → primeScalesUpTo (n+1) = insert (n+1) (primeScalesUpTo n)
¬ Nat.Prime (n+1) → primeScalesUpTo (n+1) = primeScalesUpTo n
```

Do not introduce a new prime enumeration API.

---

## 2. Old-basis view of the successor shell

Introduce a small predicate if useful:

```lean
def SuccessorOldBasisReserved (n r : ℕ) : Prop :=
  ReservedByPrimeBasis (primeScalesUpTo n) ((n + 1) ^ 2 + r)
```

Record the exact anchor shift

```text
(n+1)^2 + r = n^2 + (2*n + 1 + r).
```

Preferred theorem:

```lean
theorem successorOldBasisReserved_iff_shiftedOffset
    {n r : ℕ} :
    SuccessorOldBasisReserved n r ↔
      ReservedByPrimeBasis (primeScalesUpTo n)
        (n ^ 2 + (2 * n + 1 + r))
```

Also record the range transformation:

```text
SquareOffset (n+1) r
  ⇒ 2*n + 2 ≤ 2*n + 1 + r
  ∧ 2*n + 1 + r ≤ 4*n + 3.
```

The report must explicitly contrast this shifted interval

```text
[2*n+2, 4*n+3]
```

with the old square-shell interval

```text
[1, 2*n].
```

This distinction is the main propagation frontier.

---

## 3. Exact successor cover decomposition

Prove that successor coverage is old-basis coverage plus the possible fresh
threshold prime `q = n+1`.

Preferred generic theorem:

```lean
theorem squareOffsetCovered_succ_iff_old_or_threshold
    {n r : ℕ} :
    SquareOffsetCovered (n + 1) r ↔
      SuccessorOldBasisReserved n r ∨
        (Nat.Prime (n + 1) ∧ (n + 1) ∣ r)
```

The fresh-prime term should be reduced from

```text
(n+1) ∣ (n+1)^2 + r
```

to `(n+1) ∣ r`.

Equivalent formulations are acceptable.

---

## 4. Fresh threshold prime deletes exactly two square-shell offsets

Under

```lean
hq : Nat.Prime (n + 1)
hr : SquareOffset (n + 1) r
```

prove

```text
(n+1) ∣ r ↔ r = n+1 ∨ r = 2*(n+1).
```

Hence obtain the prime-threshold cover form

```lean
SquareOffsetCovered (n+1) r
↔ SuccessorOldBasisReserved n r
   ∨ r = n+1
   ∨ r = 2*(n+1)
```

under `hq` and `hr`.

Interpretation: the newly admitted threshold prime contributes exactly two
reserved offsets in its own successor square shell.

This is **not** the PUU-L007 `q`-lift unique-deletion theorem; these are two
different finite geometries.  Do not conflate them.

---

## 5. Composite successor case

If `¬ Nat.Prime (n+1)`, prove that no new basis direction appears:

```lean
SquareOffsetCovered (n+1) r
↔ SuccessorOldBasisReserved n r.
```

This gives a clean prime/composite transition split.

---

## 6. Projected-survivor transition

For `1 ≤ n` (so `2 ≤ n+1`), use PUU-L011 rather than reproving primality.

Prime-threshold case, preferred form:

```text
projected survivor at shell (n+1,r)
↔ ¬ SuccessorOldBasisReserved n r
   ∧ r ≠ n+1
   ∧ r ≠ 2*(n+1)
```

under `Nat.Prime (n+1)` and `SquareOffset (n+1) r`.

Composite case:

```text
projected survivor at shell (n+1,r)
↔ ¬ SuccessorOldBasisReserved n r.
```

The projected survivor must be the existing

```lean
IsPrimeBasisWheelSurvivor (primeScalesUpTo (n+1))
  (squareShellWheelProjection (primeScalesUpTo (n+1)) (n+1) r)
```

or an equivalent existing API expression.

---

## 7. Full-cover / hole frontier

Package the exact successor full-cover criterion.

For prime `q=n+1`:

```text
SquareOffsetsFullyCovered (n+1)
↔ ∀ r, SquareOffset (n+1) r →
     SuccessorOldBasisReserved n r
     ∨ r = n+1
     ∨ r = 2*(n+1).
```

For composite `n+1`:

```text
SquareOffsetsFullyCovered (n+1)
↔ ∀ r, SquareOffset (n+1) r →
     SuccessorOldBasisReserved n r.
```

If ergonomically useful, introduce a named predicate for the old-basis shifted
window, but keep it small.

Also provide the corresponding escape/non-full-cover formulation if it follows
cleanly.

---

## 8. Propagation audit — mandatory semantic conclusion

Do **not** prove or state

```text
SquareOffsetsFullyCovered n → SquareOffsetsFullyCovered (n+1)
```

unless it genuinely follows from the implemented hypotheses.

The report must state exactly what the old full-cover hypothesis controls:

```text
n^2 + s,  1 ≤ s ≤ 2*n,
```

while successor old-basis coverage requires control of

```text
n^2 + s,  2*n+2 ≤ s ≤ 4*n+3.
```

Therefore the direct propagation step requires a genuinely new theorem about
reservation/survivor occurrence in the shifted window.  If the implementation
finds a stronger exact equivalence, record it, but do not hide this interval
mismatch behind cardinality language.

This checkpoint is successful even if the result is a sharp frontier rather
than a propagation proof.

Recommended outcome wording:

```text
Outcome A+ — SUCCESSOR TRANSITION DECOMPOSED / PROPAGATION FRONTIER ISOLATED
```

provided the exact transition API above is completed.

---

## 9. Regression

Add at least one visible small transition.

Good candidates:

- `n = 4`, successor `5` is prime:
  - old basis `{2,3}`
  - new basis `{2,3,5}`
  - threshold prime `5` covers successor offsets `5` and `10`.
- optionally `n = 5`, successor `6` is composite:
  - bounded basis is unchanged from `≤5` to `≤6`.

The regression should exercise the general transition theorem rather than only
`norm_num` isolated arithmetic.

---

## STOP

Do not implement in PUU-L012:

- a proof of Legendre's conjecture,
- an unproved square-hole propagation theorem,
- Jacobsthal/max-gap bounds,
- full wheel-gap recursion,
- asymptotic prime density,
- Euler-phi as the main proof route,
- PowerSwap,
- GN/CosmicFormula,
- PNT/RH.

This checkpoint is the exact `n → n+1` transition audit and nothing beyond it.

---

## Report

Create:

```text
lean/dk_math/docs/dev/NumberTheory-PrimorialUnitUniverse-260827-v0/
  primorial-unit-universe-successor-square-shell-transition-260827.md
```

The report must distinguish:

1. old shell coverage,
2. shifted successor window coverage by the old basis,
3. the two fresh-threshold seats when `n+1` is prime,
4. the actual remaining propagation frontier.
