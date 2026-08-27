# PUU-L014 — Twin-Threshold Exception / Exact Old-Escape Classification

## Goal

PUU-L013 proved the exact prime-threshold deletion identity

```text
projected successor escapes
  = old-basis successor escapes.erase (2 * (n + 1)).
```

It also proved the useful sufficient implication

```text
oldEscape.card ≥ 2 → projectedEscape.Nonempty.
```

This checkpoint must sharpen that sufficient bound into the **exact** successor
criterion.  In particular, do not treat `oldEscape.card ≥ 2` as logically
necessary in every prime-threshold case.

For a prime threshold `q = n + 1`, the only possible old-basis escape deleted
by the enlarged basis is the second threshold seat `r = 2*q`.  Its absolute
point is

```text
q^2 + 2*q = q * (q + 2).
```

The key new theorem is that this seat escapes the old bounded basis exactly
when `q + 2 = n + 3` is also prime.  Thus the only non-prime exceptional
old-basis escape is the twin-prime semiprime seat.

This is an exact classification/audit checkpoint.  It does **not** prove that
a successor shell has any actual escaping offset.

## Module

Preferred new module:

```text
DkMath/NumberTheory/Legendre/PrimorialWheelTwinThreshold.lean
```

Import:

```lean
import DkMath.NumberTheory.Legendre.PrimorialWheelSuccessorEscape
```

Export it through `DkMath.NumberTheory.Legendre`.

## 1. Connect projected successor escapes to the existing Legendre escape set

For `1 ≤ n`, prove the exact Finset equality

```lean
theorem successorProjectedEscapingOffsets_eq_escapingSquareOffsets
    {n : ℕ} (hn : 1 ≤ n) :
    successorProjectedEscapingOffsets n =
      escapingSquareOffsets (n + 1)
```

Use the existing membership theorem for `escapingSquareOffsets` and PUU-L011
`not_squareOffsetCovered_iff_projection_survivor` / the projected-survivor
bridge.  Do not redefine `escapingSquareOffsets`.

This theorem identifies the new projected-wheel presentation with the existing
Legendre consumer vocabulary.

## 2. Second threshold seat iff twin prime

For `2 ≤ n` and prime `q = n + 1`, prove preferably both an absolute
reservation spelling and a Finset membership spelling:

```lean
theorem secondThreshold_not_oldReserved_iff_twinPrime
    {n : ℕ}
    (hn : 2 ≤ n)
    (hq : Nat.Prime (n + 1)) :
    (¬ SuccessorOldBasisReserved n (2 * (n + 1))) ↔
      Nat.Prime (n + 3)
```

and/or

```lean
theorem secondThreshold_mem_oldEscape_iff_twinPrime
    {n : ℕ}
    (hn : 2 ≤ n)
    (hq : Nat.Prime (n + 1)) :
    2 * (n + 1) ∈ successorOldBasisEscapingOffsets n ↔
      Nat.Prime (n + 3)
```

Mathematical content:

```text
(n + 1)^2 + 2*(n + 1) = (n + 1)*(n + 3).
```

- If `n + 3` is prime, every prime divisor from the old basis would have to be
  one of the two prime factors `n + 1` or `n + 3`, both outside
  `primeScalesUpTo n`.
- Conversely, if `n + 3` is composite, choose a prime divisor of `n + 3` and
  show it is at most `n`; hence it belongs to the old basis and reserves the
  second threshold seat.

Equivalent stable Mathlib routes are fine.  Do not introduce a general twin
prime theory.

## 3. Every other old-basis escape is an actual successor escape

Package the exact consequence of PUU-L013:

```lean
theorem mem_successorProjectedEscapingOffsets_iff_old_ne_second
    {n r : ℕ}
    (hn : 2 ≤ n)
    (hq : Nat.Prime (n + 1)) :
    r ∈ successorProjectedEscapingOffsets n ↔
      r ∈ successorOldBasisEscapingOffsets n ∧
        r ≠ 2 * (n + 1)
```

This should be a direct Finset consequence of
`successorProjectedEscapingOffsets_eq_erase_secondThreshold`.

Then provide the prime specialization:

```lean
theorem prime_of_mem_successorOldBasisEscape_ne_second
    {n r : ℕ}
    (hn : 2 ≤ n)
    (hq : Nat.Prime (n + 1))
    (hr : r ∈ successorOldBasisEscapingOffsets n)
    (hne : r ≠ 2 * (n + 1)) :
    Nat.Prime ((n + 1)^2 + r)
```

Reuse PUU-L011 `squareOffset_prime_iff_projection_survivor`; do not reprove the
bounded-prime primality argument.

## 4. Exact old-escape decomposition

Prove an exact set-level classification.  A preferred shape is

```lean
theorem successorOldBasisEscapingOffsets_eq_projected_union_twinSeat
    {n : ℕ}
    (hn : 2 ≤ n)
    (hq : Nat.Prime (n + 1)) :
    successorOldBasisEscapingOffsets n =
      successorProjectedEscapingOffsets n ∪
        (if Nat.Prime (n + 3) then
          {2 * (n + 1)}
        else
          ∅)
```

Equivalent orientation or a pair of `if_pos` / `if_neg` theorems is fine.

It is also valuable to expose the same theorem in existing Legendre language:

```text
old-basis successor escapes
  = escapingSquareOffsets (n + 1)
    ∪ optional twin-prime semiprime seat.
```

This is the central semantic theorem of PUU-L014.

## 5. Exact nonemptiness frontier — replace the coarse `≥ 2` wording

Prove the exact erase criterion:

```lean
theorem successorProjectedEscapingOffsets_nonempty_iff_exists_old_ne_second
    {n : ℕ}
    (hn : 2 ≤ n)
    (hq : Nat.Prime (n + 1)) :
    (successorProjectedEscapingOffsets n).Nonempty ↔
      ∃ r ∈ successorOldBasisEscapingOffsets n,
        r ≠ 2 * (n + 1)
```

Then sharpen by twin-prime branch.

### Twin-prime threshold

If `Nat.Prime (n + 3)`, the second seat really is in the old escape set, so:

```text
projectedEscape.Nonempty ↔ 2 ≤ oldEscape.card.
```

A theorem with this exact content is preferred.

### Non-twin prime threshold

If `¬ Nat.Prime (n + 3)`, the second seat was old-reserved already, so:

```text
projectedEscape = oldEscape
```

and therefore

```text
projectedEscape.Nonempty ↔ oldEscape.Nonempty.
```

These are the **exact** threshold-sensitive criteria.  They supersede the
coarser statement “prime successor needs at least two old escapes”, which is
only a uniform sufficient condition.

## 6. Optional exact cardinality formula

If short and stable, prove

```text
oldEscape.card =
  projectedEscape.card + (if Nat.Prime (n + 3) then 1 else 0).
```

A pair of branch theorems is equally acceptable:

```text
Nat.Prime (n+3)  → old.card = projected.card + 1
¬ Nat.Prime (n+3) → old.card = projected.card
```

Do not let this optional formula delay the set-level classification.

## 7. Visible regressions

Include at least one twin-prime threshold and, if convenient, one non-twin
prime threshold.

Recommended twin regression:

```text
n = 4, q = 5, q+2 = 7 prime
second threshold r = 10
10 ∈ oldEscape
10 ∉ projectedEscape
```

This should reuse PUU-L013 where possible.

A non-twin prime threshold such as `q = 7` (`n = 6`, `q+2 = 9` composite) is
valuable if numerically convenient:

```text
second threshold r = 14 is already old-reserved
there is no deletion at r = 14
```

## Outcome A+ rubric

PUU-L014 is A+ if it establishes:

1. projected successor escape set = existing `escapingSquareOffsets (n+1)`;
2. second threshold old escape iff `Nat.Prime (n+3)`;
3. projected membership iff old membership away from the second seat;
4. every old escape away from the second seat gives an actual prime shell
   point by reusing L011;
5. exact old-escape decomposition = actual escape set plus optional twin seat;
6. exact nonemptiness criterion `∃ old escape ≠ second seat`;
7. twin/non-twin branch criteria distinguishing when `card ≥ 2` is actually
   necessary and when one old escape suffices;
8. visible regression(s), facade export, and semantic report.

## STOP

Do **not** prove or assume in this checkpoint:

- that `successorOldBasisEscapingOffsets n` is always nonempty;
- any lower bound on its cardinality for arbitrary `n`;
- Legendre conjecture;
- square-hole propagation;
- Jacobsthal/max-gap bounds;
- full wheel-gap recursion;
- PowerSwap;
- GN/CosmicFormula;
- PNT/RH.

The point of PUU-L014 is to determine whether the remaining shifted-window
provider is genuinely new information or merely Legendre escape plus one
explicit exceptional composite seat.

## Report

Create:

```text
lean/dk_math/docs/dev/NumberTheory-PrimorialUnitUniverse-260827-v0/
  primorial-unit-universe-twin-threshold-escape-classification-260827.md
```

The report must explicitly state:

- `oldEscape.card ≥ 2` from PUU-L013 is a **sufficient** prime-threshold
  criterion, not a necessary one in all cases;
- the only possible non-prime old-basis escape is the second threshold seat;
- that seat survives the old basis exactly at a twin-prime threshold;
- after removing this explicit exception, the remaining provider is exactly
  the ordinary Legendre escaping-offset problem.