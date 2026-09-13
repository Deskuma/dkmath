# CGE-012 — Exact Parity Margin / Maximal Anchor Window Transport

## Scope

CGE-012 packages the completed CGE-011 finite signed parity ledger as a
nonnegative margin and transports it across balanced windows in a fixed finite
prime world.  It also removes the arbitrary admissible-window search for fixed
`(n, P)` by selecting the maximal anchor-safe window.  No universal positivity
provider, Strong Goldbach theorem, or new inclusion-exclusion layer is added.

## Implemented declarations

Owner module:

`DkMath/NumberTheory/Goldbach/BalancedSignedCRTMargin.lean`

Facade export:

`DkMath/NumberTheory/Goldbach.lean`

The public declarations are:

- `goldbachSignedParityMargin`
- `goldbachSignedParityMargin_eq_survivors_card`
- `goldbachSignedParityMargin_pos_iff_survivors_nonempty`
- `goldbachWindowSurvivors_subset_of_window_le`
- `goldbachWindowSurvivors_card_mono_window`
- `goldbachSignedParityMargin_mono_window`
- `goldbachMaxAnchorWindow`
- `goldbachMaxAnchorWindow_le_n`
- `goldbachMaxAnchorWindow_safe`
- `goldbachMaxAnchorWindow_maximal`
- `goldbachSignedParityMargin_le_maxAnchorWindow`
- `goldbachSignedParityMargin_exists_admissible_iff_max_positive`
- `goldbachPairAt_of_maxAnchorWindow_margin_pos`

## Exact results

The margin is defined by

```text
(balancedOffsets n w).card + signedEvenTailCRT
  - (signedSingleCRT + signedOddTailCRT)
```

Under `2 ≤ n`, `KnownPrimeScales S`, the finite bound on `S`, and the anchor
`P < n - w`,

```text
goldbachSignedParityMargin n w S
  = (goldbachWindowSurvivors n w S).card.
```

Consequently, positivity is equivalent to survivor nonemptiness.  For a fixed
`S`, survivor inclusion and cardinality monotonicity under `w₁ ≤ w₂` are proved
without CRT or anchor assumptions.  The signed margin monotonicity is then
proved when the larger window satisfies the finite anchor; the smaller anchor
is derived from `w₁ ≤ w₂`.

The one-seat recurrence was deferred.  It is optional in the stage contract and
is not needed for the exact transport or maximal-window result.

The maximal window is exactly

```text
goldbachMaxAnchorWindow n P :=
  min (n - (P + 1)) (squareBody P - n)
```

Under `P < n` and `n ≤ squareBody P`, the safety theorem proves

```text
wMax ≤ n ∧ P < n - wMax ∧ n + wMax ≤ squareBody P.
```

Every `w` satisfying `P < n - w` and `n + w ≤ squareBody P` is proved to be
at most `wMax`.  Therefore every admissible positive margin is bounded by the
maximal-window margin, and

```text
(∃ w, P < n - w ∧ n + w ≤ squareBody P ∧
  0 < goldbachSignedParityMargin n w S)
↔ 0 < goldbachSignedParityMargin n
    (goldbachMaxAnchorWindow n P) S.
```

For `S = primeScalesUpTo P`, the one-way endpoint wrapper
`goldbachPairAt_of_maxAnchorWindow_margin_pos` produces `GoldbachPairAt n`
from positive maximal margin under the explicit feasibility assumptions.  No
converse for a fixed `P` is stated.

## Kernel regressions

The audit file
`DkMathTest/NumberTheory/GoldbachBalancedReflectionAudit.lean` checks with
`decide +kernel`:

| `(n, P)` | maximal window | checked margins |
|---|---:|---|
| `(15, 5)` | `9` | `w=8: 3`, `w=9: 3` |
| `(50, 7)` | `13` | `w=10: 2`, `w=13: 2` |
| `(22, 7)` | `14` | `w=9: 1`, `w=14: 1` |
| `(68, 11)` | `56` | `w=15: 1`, `w=56: 4` |

The maximal-window survivor cardinality for `(68, 11)` is also checked as `4`.
The audit includes concrete applications of the exact margin identity, the
admissible-window search reduction, and the maximal-window endpoint wrapper.

## Verification

Passed:

```text
lake build DkMath.NumberTheory.Goldbach DkMathTest.NumberTheory.GoldbachBalancedReflectionAudit
lake build DkMath
git diff --check
```

The focused build completed successfully at `8738 jobs`, and the full
`DkMath` build completed successfully at `9861 jobs`.  The new
public declarations were added to the audit's `#print axioms` section.  No
new axiom, `sorryAx`, `sorry`, `admit`, `native_decide`, `unsafe`, or explicit
axiom was introduced.  The non-sorry warning filter was empty on the final
full-build log.

## Outcome

**A — EXACT PARITY MARGIN / MAX-WINDOW TRANSPORT**

The exact margin/cardinality identity, fixed-world window monotonicity, safe
and maximal anchor window, and admissible-window search reduction are all
kernel-checked.  The remaining provider question is deliberately unchanged:
positivity of the maximal margin for a universally chosen `P` is outside
CGE-012.
