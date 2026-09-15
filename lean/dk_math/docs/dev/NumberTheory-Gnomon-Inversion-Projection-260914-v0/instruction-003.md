# instruction-003 — GNIP-003 Legendre open unit-gnomon bridge

## Goal

Connect the existing Legendre square-cell vocabulary to the approved neutral gnomon layer.

This checkpoint should prove that the offsets inside the open interval between consecutive squares are exactly the open interior of one unit square gnomon.

Do **not** attempt to prove Legendre's conjecture, full-cover failure, fresh-prime existence, or any new capacity estimate here.

The purpose is coordinate identification and frontier restatement only.

## Read first

```text
DkMath/Gnomon/Algebra.lean
DkMath/Gnomon/CosmicBridge.lean
DkMath/NumberTheory/Legendre/Basic.lean
DkMath/NumberTheory/Legendre/Frontier.lean
DkMath/NumberTheory/Legendre/MultiGaugeBridge.lean
```

Existing definitions to preserve:

```lean
def SquareCell (n m : ℕ) : Prop :=
  n ^ 2 < m ∧ m < (n + 1) ^ 2

def SquareOffset (n r : ℕ) : Prop :=
  1 ≤ r ∧ r ≤ 2 * n

def squareOffsets (n : ℕ) : Finset ℕ :=
  Finset.Icc 1 (2 * n)
```

Neutral gnomon source:

```lean
def DkMath.Gnomon.oddGnomon (n : ℕ) : ℕ :=
  2 * n + 1
```

Cosmic bridge:

```text
oddGnomon n = GTail 2 1 1 n
```

---

## Target module

Preferred new module:

```text
DkMath/NumberTheory/Legendre/GnomonBridge.lean
```

Import only what is needed, preferably:

```lean
import DkMath.Gnomon.CosmicBridge
import DkMath.NumberTheory.Legendre.Frontier
```

or a smaller dependency if `Basic` suffices for the main statements.

Update:

```text
DkMath/NumberTheory/Legendre.lean
```

to export the new bridge.

Namespace:

```lean
namespace DkMath.NumberTheory.Legendre
```

Use qualified `DkMath.Gnomon.*` names where helpful to avoid ambiguity.

---

## 1. Open unit-gnomon offset equivalence

Prove the exact predicate identity:

```lean
theorem squareOffset_iff_open_oddGnomon
    {n r : ℕ} :
    SquareOffset n r ↔
      1 ≤ r ∧ r < DkMath.Gnomon.oddGnomon n
```

This should be elementary from

```text
SquareOffset n r = 1 ≤ r ∧ r ≤ 2*n
oddGnomon n      = 2*n+1.
```

This theorem is the main semantic bridge.

Interpretation:

```text
r = 0                : lower square anchor, excluded
1 ≤ r < oddGnomon n  : open unit-gnomon interior
r = oddGnomon n      : upper square anchor, excluded
```

---

## 2. Finite-set identity

Prove the shell itself is exactly the open finite gnomon interval:

```lean
theorem squareOffsets_eq_Ico_oddGnomon
    (n : ℕ) :
    squareOffsets n =
      Finset.Ico 1 (DkMath.Gnomon.oddGnomon n)
```

Do not introduce a duplicate finite-set definition unless it materially improves later APIs.

Useful corollary, only if clean:

```lean
theorem card_open_oddGnomon_offsets (n : ℕ) :
    (Finset.Ico 1 (DkMath.Gnomon.oddGnomon n)).card = 2 * n
```

Prefer deriving this from `squareOffsets_eq_Ico_oddGnomon` and existing `card_squareOffsets` rather than reproving interval cardinality independently.

---

## 3. Upper-boundary theorem

Expose the excluded upper endpoint as the next square:

```lean
theorem square_add_oddGnomon_eq_next_square
    (n : ℕ) :
    n ^ 2 + DkMath.Gnomon.oddGnomon n = (n + 1) ^ 2
```

This should reuse `DkMath.Gnomon.square_add_oddGnomon`, not re-run `ring` unless theorem orientation forces a trivial normalization.

Optional lower-boundary theorem is unnecessary because `n^2 + 0 = n^2` is just simplification.

---

## 4. SquareCell restatement

Restate the existing coordinate theorem using the open unit-gnomon interior:

```lean
theorem squareCell_iff_exists_open_oddGnomon_offset
    (n m : ℕ) :
    SquareCell n m ↔
      ∃ r,
        1 ≤ r ∧
        r < DkMath.Gnomon.oddGnomon n ∧
        m = n ^ 2 + r
```

Prove this by transporting through existing

```text
squareCell_iff_exists_squareOffset
```

and `squareOffset_iff_open_oddGnomon`.

Do not directly redo the square arithmetic unless necessary.

---

## 5. Cosmic unit-shell restatement

Using GNIP-001, prove a Cosmic-coordinate alias:

```lean
theorem squareOffset_iff_open_GTail_two_one_unit
    {n r : ℕ} :
    SquareOffset n r ↔
      1 ≤ r ∧
      r < DkMath.CosmicFormula.GTail 2 1 1 n
```

This should be a rewrite through

```text
DkMath.Gnomon.oddGnomon_eq_GTail_two_one_unit
```

and the open-gnomon theorem.

Mathematical reading:

```text
Legendre square-shell width = degree-two unit Cosmic shell.
```

Do not generalize this to arbitrary degree in this checkpoint.

---

## 6. Legendre conjecture restatement

Add an exact equivalence, not a new conjecture:

```lean
theorem legendreConjecture_iff_open_oddGnomon_prime
    : LegendreConjecture ↔
      ∀ n : ℕ, 0 < n →
        ∃ p r,
          Nat.Prime p ∧
          1 ≤ r ∧
          r < DkMath.Gnomon.oddGnomon n ∧
          p = n ^ 2 + r
```

Equivalent quantifier/order variants are acceptable if cleaner, but keep the meaning explicit:

```text
for every positive square anchor n,
a prime lies at an interior offset of its unit gnomon.
```

Derive this from existing `LegendreConjecture` and the square-cell restatement.  This theorem is a reformulation only and must be documented as such.

---

## 7. Support-escape restatement

For GNIP-004 preparation, also restate the existing provider frontier:

```lean
theorem squareAnchoredSupportEscape_iff_open_oddGnomon
    : SquareAnchoredSupportEscape ↔
      ∀ n : ℕ, 0 < n →
        ∃ r,
          1 ≤ r ∧
          r < DkMath.Gnomon.oddGnomon n ∧
          SupportDisjointFrom
            (primeScalesUpTo n)
            (n ^ 2 + r)
```

This theorem is especially important: it identifies the currently missing Legendre provider as an escaping seat **inside the open unit gnomon**.

Do not claim the right-hand side is proved unconditionally; this is an iff restatement of the existing provider predicate.

---

## 8. Concrete regressions around 30

Kernel-check at least:

```text
oddGnomon 30 = 61
squareOffsets 30 = Finset.Ico 1 61
(squareOffsets 30).card = 60
30^2 + 61 = 31^2
```

If the finite-set equality is inconvenient to `norm_num`, instantiate the generic theorem instead of brute-force evaluation.

Also check the next shell value if useful:

```text
oddGnomon 31 = 63
```

These are geometry/arithmetic regressions only.  Do not infer a prime theorem from `61` being prime.

---

## 9. Scope boundaries

Do not in GNIP-003:

```text
prove LegendreConjecture
prove SquareAnchoredSupportEscape
prove full-cover failure
add new capacity / pair-overlap estimates
change primeScalesUpTo
change MultiGauge transitions
analyze 30 -> 31 prime-basis preservation
connect CosmicSquareScaling
introduce analytic sqrt/log/rpow
```

Those belong to GNIP-004 or the resumed Legendre campaign.

Do not modify existing `SquareCell`, `SquareOffset`, or `squareOffsets` definitions merely to make the bridge prettier.

---

## 10. Validation

Run from `lean/dk_math`:

```text
lake build DkMath.NumberTheory.Legendre.GnomonBridge
lake build DkMath.NumberTheory.Legendre
lake build DkMath.Gnomon
```

Also run:

```text
git diff --check
```

Scan changed Lean source for:

```text
sorry
admit
axiom
```

Report pre-existing warnings separately.

---

## 11. Deliverable report

Create:

```text
docs/dev/NumberTheory-Gnomon-Inversion-Projection-260914-v0/report-003.md
```

Report:

1. Outcome.
2. Files added/changed.
3. Final theorem names.
4. Whether `SquareOffset` was exactly identified with the open unit-gnomon interior.
5. Whether `squareOffsets` was identified at finite-set level.
6. Whether `SquareCell` was restated through gnomon offsets.
7. Whether the Cosmic `GTail 2 1 1 n` restatement was established.
8. Whether `LegendreConjecture` and `SquareAnchoredSupportEscape` were restated exactly.
9. 30/31 regressions.
10. Build results and warnings.
11. Whether GNIP-004 preservation / inversion-projection analysis is now justified.

Outcome policy:

```text
A — OPEN GNOMON BRIDGE COMPLETE
    Predicate, finite-set, square-cell, Cosmic, and frontier restatements all established.

B — CORE BRIDGE COMPLETE / FRONTIER RESTATEMENT PARTIAL
    Open gnomon geometry is proved but one frontier equivalence is blocked by API shape.
    Record exact blocker; do not rewrite old definitions to force it.

C — EXISTING API ALREADY SUBSUMES TARGET
    If an exact existing theorem already provides these statements, reuse it and avoid duplication.
```
