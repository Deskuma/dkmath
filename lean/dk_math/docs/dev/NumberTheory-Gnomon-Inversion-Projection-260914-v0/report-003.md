# GNIP-003 report — Legendre open unit-gnomon bridge

## 1. Outcome

**A — OPEN GNOMON BRIDGE COMPLETE.**

The existing Legendre square-offset and square-cell coordinates are exactly
identified with the open interior of the neutral unit square gnomon.  The
finite-set, Cosmic, Legendre-conjecture, and support-escape forms are all
proved as exact restatements.  No new prime-existence or Legendre result is
claimed.

## 2. Files added or changed

```text
DkMath/NumberTheory/Legendre/GnomonBridge.lean   added
DkMath/NumberTheory/Legendre.lean                exports GnomonBridge
docs/dev/NumberTheory-Gnomon-Inversion-Projection-260914-v0/report-003.md
                                                   added
```

The existing `SquareCell`, `SquareOffset`, and `squareOffsets` definitions
were not modified.

## 3. Final theorem names

```text
squareOffset_iff_open_oddGnomon
squareOffsets_eq_Ico_oddGnomon
card_open_oddGnomon_offsets
square_add_oddGnomon_eq_next_square
squareCell_iff_exists_open_oddGnomon_offset
squareOffset_iff_open_GTail_two_one_unit
legendreConjecture_iff_open_oddGnomon_prime
squareAnchoredSupportEscape_iff_open_oddGnomon
```

## 4. Open-gnomon predicate and finite shell

The main coordinate identity is:

```text
SquareOffset n r
  ↔ 1 ≤ r ∧ r < DkMath.Gnomon.oddGnomon n.
```

The finite shell identity is:

```text
squareOffsets n = Finset.Ico 1 (DkMath.Gnomon.oddGnomon n).
```

The corresponding cardinality is transported from the existing
`card_squareOffsets` theorem:

```text
(Finset.Ico 1 (DkMath.Gnomon.oddGnomon n)).card = 2 * n.
```

The upper endpoint is identified through the neutral theorem
`DkMath.Gnomon.square_add_oddGnomon`:

```text
n^2 + DkMath.Gnomon.oddGnomon n = (n+1)^2.
```

## 5. Square-cell restatement

`squareCell_iff_exists_open_oddGnomon_offset` transports the existing
`squareCell_iff_exists_squareOffset` theorem and proves:

```text
SquareCell n m ↔
  ∃ r, 1 ≤ r ∧ r < DkMath.Gnomon.oddGnomon n ∧ m = n^2 + r.
```

No square arithmetic or old coordinate definition was duplicated.

## 6. Cosmic unit-shell restatement

Using the GNIP-001 theorem
`DkMath.Gnomon.oddGnomon_eq_GTail_two_one_unit`, the bridge proves:

```text
SquareOffset n r ↔
  1 ≤ r ∧ r < DkMath.CosmicFormula.GTail 2 1 1 n.
```

This is restricted to the degree-two unit shell as required.

## 7. Legendre and support-frontier restatements

The theorem
`legendreConjecture_iff_open_oddGnomon_prime` is an exact reformulation of
the existing `LegendreConjecture` definition:

```text
LegendreConjecture ↔
  ∀ n, 0 < n →
    ∃ p r, Nat.Prime p ∧ 1 ≤ r ∧
      r < DkMath.Gnomon.oddGnomon n ∧ p = n^2 + r.
```

The theorem
`squareAnchoredSupportEscape_iff_open_oddGnomon` similarly restates the
existing provider predicate inside the open gnomon:

```text
SquareAnchoredSupportEscape ↔
  ∀ n, 0 < n →
    ∃ r, 1 ≤ r ∧ r < DkMath.Gnomon.oddGnomon n ∧
      SupportDisjointFrom (primeScalesUpTo n) (n^2 + r).
```

Neither right-hand side is proved unconditionally here.

## 8. Concrete regressions

Kernel-checked examples include:

```text
oddGnomon 30 = 61
squareOffsets 30 = Finset.Ico 1 61
(squareOffsets 30).card = 60
30^2 + 61 = 31^2
oddGnomon 31 = 63
```

These are arithmetic and coordinate regressions only.  No primality claim is
derived from the value `61`.

## 9. Dependencies and validation

`DkMath.NumberTheory.Legendre.GnomonBridge` imports only:

```text
DkMath.Gnomon.CosmicBridge
DkMath.NumberTheory.Legendre.Frontier
```

Validation from `lean/dk_math`:

```text
lake build DkMath.NumberTheory.Legendre.GnomonBridge
Build completed successfully (8687 jobs).

lake build DkMath.NumberTheory.Legendre
Build completed successfully (8774 jobs).

lake build DkMath.Gnomon
Build completed successfully (8658 jobs).

git diff --check
passed with no diagnostics.
```

The changed Lean source was scanned for `sorry`, `admit`, and `axiom`; no
matches were found and no new axiom was introduced.  The required builds
emitted no warnings.

One initial focused elaboration attempt required explicit namespace openings
for `DkMath.NumberTheory.Primitive` and
`DkMath.NumberTheory.StructuralArithmetic` in the new module; this was a
resolved import/namespace issue, not a mathematical or API blocker.

## 10. GNIP-004 status

The coordinate bridge now justifies GNIP-004 preservation/inversion-projection
analysis as a next scoped checkpoint.  That analysis remains unimplemented:
there is no full-cover failure, fresh-prime provider, capacity estimate, or
30→31 preservation claim in GNIP-003.
