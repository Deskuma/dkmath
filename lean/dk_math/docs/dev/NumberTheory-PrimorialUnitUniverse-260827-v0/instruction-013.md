# PUU-L013 — Successor Old-Basis Escape / Fresh-Threshold Deletion Capacity

## Goal

PUU-L012 decomposed the exact `n → n + 1` square-shell transition.  This
checkpoint packages the **old-basis escaping offsets** in the successor shell
as a finite set and proves that a fresh prime threshold can destroy **at most
one old-basis escape**.

The key sharpening is that, for `2 ≤ n` and prime `q = n + 1`, the first
threshold seat `r = q` is already reserved by the old basis (in fact by `2`).
Therefore the only threshold seat that can remove an old-basis survivor is
`r = 2*q`.

This is a finite transition/capacity theorem.  It is not yet the theorem that
the shifted window contains enough old-basis escapes.

## Module

Preferred new module:

```text
DkMath/NumberTheory/Legendre/PrimorialWheelSuccessorEscape.lean
```

Import:

```lean
import DkMath.NumberTheory.Legendre.PrimorialWheelSuccessor
```

Export it through `DkMath.NumberTheory.Legendre`.

## 1. Old-basis escape Finset

Define the successor-shell offsets escaping the old basis, preferably:

```lean
noncomputable def successorOldBasisEscapingOffsets (n : ℕ) : Finset ℕ :=
  (squareOffsets (n + 1)).filter
    (fun r => ¬ SuccessorOldBasisReserved n r)
```

Provide the exact membership theorem:

```lean
@[simp] theorem mem_successorOldBasisEscapingOffsets ... :
  r ∈ successorOldBasisEscapingOffsets n ↔
    SquareOffset (n + 1) r ∧
    ¬ SuccessorOldBasisReserved n r
```

Optionally provide the shifted-window spelling via
`successorOldBasisReserved_iff_shiftedOffset`.

## 2. Actual projected-successor escape Finset

Package the offsets that are actual projected survivors for the enlarged
basis, e.g.

```lean
noncomputable def successorProjectedEscapingOffsets (n : ℕ) : Finset ℕ :=
  (squareOffsets (n + 1)).filter
    (fun r =>
      IsPrimeBasisWheelSurvivor (primeScalesUpTo (n + 1))
        (squareShellWheelProjection
          (primeScalesUpTo (n + 1)) (n + 1) r))
```

Provide its exact membership theorem.

Do not redefine `escapingSquareOffsets`; this is specifically the projected
wheel presentation needed for the transition audit.

## 3. First threshold seat is already old-reserved

For a prime threshold with `2 ≤ n`, prove:

```lean
theorem successorOldBasisReserved_firstThreshold
    {n : ℕ}
    (hn : 2 ≤ n)
    (hq : Nat.Prime (n + 1)) :
    SuccessorOldBasisReserved n (n + 1)
```

Mathematical content:

```text
(n+1)^2 + (n+1) = (n+1)(n+2)
```

and `n + 1` is an odd prime, so `2 ∣ n + 2`; since `2 ≤ n`, prime `2` belongs
to `primeScalesUpTo n`.

Equivalent proof routes are fine.  Keep the theorem semantic rather than
hard-coding one proof tactic.

Corollary:

```lean
n + 1 ∉ successorOldBasisEscapingOffsets n
```

under the same hypotheses.

## 4. Prime-threshold exact set deletion

Use PUU-L012
`successorProjectedSurvivor_iff_primeThreshold` plus the previous theorem to
prove the exact Finset identity:

```lean
theorem successorProjectedEscapingOffsets_eq_erase_secondThreshold
    {n : ℕ}
    (hn : 2 ≤ n)
    (hq : Nat.Prime (n + 1)) :
    successorProjectedEscapingOffsets n =
      (successorOldBasisEscapingOffsets n).erase (2 * (n + 1))
```

Equivalent orientation is fine.

This is the central theorem of PUU-L013:

```text
old-basis escapes
      ↓ fresh prime q=n+1
only possible old-survivor deletion = r = 2q
```

The theorem must not say that `2q` actually is an old-basis escape in every
prime-threshold case.

## 5. Deletion capacity / cardinality consequence

Prove a cardinality inequality or exact erase-card formula sufficient to
obtain:

```lean
theorem successorProjectedEscapingOffsets_nonempty_of_two_le_oldEscapeCard
    {n : ℕ}
    (hn : 2 ≤ n)
    (hq : Nat.Prime (n + 1))
    (hcard : 2 ≤ (successorOldBasisEscapingOffsets n).card) :
    (successorProjectedEscapingOffsets n).Nonempty
```

The intended meaning is: a fresh prime threshold can remove at most one
old-basis escaping seat, so two old escapes force one actual successor escape.

Prefer a reusable lower bound such as

```text
oldEscape.card ≤ projectedEscape.card + 1
```

or the corresponding `card_erase` statement if natural in Lean.

## 6. Composite successor exact identity

Using PUU-L012 `successorProjectedSurvivor_iff_composite`, prove that for
`1 ≤ n` and `¬ Nat.Prime (n + 1)`:

```lean
theorem successorProjectedEscapingOffsets_eq_old_of_composite ... :
  successorProjectedEscapingOffsets n =
    successorOldBasisEscapingOffsets n
```

Hence:

```text
old-basis escape nonempty
  ↔ actual successor projected escape nonempty
```

in the composite case.

## 7. Optional twin-prime characterization — stretch only

If the Mathlib route is short and stable, it is valuable to characterize the
only possible deleted old survivor:

```lean
¬ SuccessorOldBasisReserved n (2 * (n + 1))
  ↔ Nat.Prime (n + 3)
```

under `2 ≤ n` and `Nat.Prime (n + 1)`.

Reason:

```text
(n+1)^2 + 2(n+1) = (n+1)(n+3).
```

Thus the second threshold seat is an old-basis survivor exactly in the twin
prime case `(n+1, n+3)`.

This theorem is **optional** for PUU-L013 A+.  Do not let prime-divisor API
engineering delay the required deletion-capacity result.

## 8. Visible regression

For `n = 4`, `q = 5`:

```text
successor old-basis escaping offsets include 10
5 itself is already old-reserved
10 = 2*5 is deleted by the fresh threshold prime
```

Prefer a regression showing the set-level deletion or at least membership /
non-membership through the general theorems.

## Outcome A+ rubric

PUU-L013 is A+ if it establishes:

1. old-basis successor escape Finset + membership theorem;
2. actual projected-successor escape Finset + membership theorem;
3. first threshold seat is already old-reserved for `2 ≤ n`;
4. prime-threshold exact set identity = old escapes with only `2*(n+1)` erased;
5. fresh-threshold deletion capacity at most one;
6. `oldEscape.card ≥ 2 → actual successor escape nonempty`;
7. composite successor exact set equality;
8. visible regression;
9. facade export and semantic report.

## STOP

Do **not** prove or assume in this checkpoint:

- that every shifted window has an old-basis escape;
- that every shifted window has two old-basis escapes;
- `SquareOffsetsFullyCovered n → SquareOffsetsFullyCovered (n+1)` or its negation;
- a Jacobsthal/max-gap bound;
- full wheel-gap recursion;
- Legendre conjecture;
- PowerSwap;
- GN/CosmicFormula;
- PNT/RH.

The next frontier after PUU-L013 should be stated explicitly as:

```text
composite successor:
  need ≥ 1 old-basis escape in the shifted successor window

prime successor:
  need ≥ 2 old-basis escapes in the shifted successor window
```

That lower-bound problem is the new mathematical provider; PUU-L013 only
proves the threshold deletion capacity needed to formulate it correctly.

## Report

Create:

```text
lean/dk_math/docs/dev/NumberTheory-PrimorialUnitUniverse-260827-v0/
  primorial-unit-universe-successor-escape-deletion-capacity-260827.md
```

The report must distinguish:

- two threshold-covered offsets in the successor shell;
- only one of those can possibly be a **new deletion of an old-basis escape**;
- the second seat `2*(n+1)` is not asserted to be old-unreserved in every
  prime-threshold case;
- this checkpoint sharpens the propagation frontier but does not solve it.
