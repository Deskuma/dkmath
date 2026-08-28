# PUU-L015 — Old-Escape Frontier Equivalence Audit / Anti-Relabeling Check

## Goal

PUU-L014 completely classified the difference between
`successorOldBasisEscapingOffsets n` and the actual Legendre escape set in the
successor shell.  Before trying to prove a lower bound for the old-basis escape
set, this checkpoint must determine whether that proposed provider is genuinely
stronger structural information or merely Legendre's conjecture rewritten in
new vocabulary.

The purpose is an **equivalence audit**.  Do not prove Legendre's conjecture in
this checkpoint.

## Module

Preferred module:

```text
DkMath/NumberTheory/Legendre/PrimorialWheelOldEscapeFrontier.lean
```

Import:

```lean
import DkMath.NumberTheory.Legendre.PrimorialWheelTwinThreshold
```

Export it through `DkMath.NumberTheory.Legendre`.

## 1. Package the exact local old-escape criterion

Define a proposition for `n >= 2` that exactly captures when the successor
shell has an actual escape using only the old-basis escape data and the
prime/twin-threshold classification.

A recommended definition is:

```lean
def SuccessorOldEscapeCriterion (n : ℕ) : Prop :=
  if Nat.Prime (n + 1) ∧ Nat.Prime (n + 3) then
    2 ≤ (successorOldBasisEscapingOffsets n).card
  else
    (successorOldBasisEscapingOffsets n).Nonempty
```

Equivalent formulations are acceptable, including nested `if`s or a branch
predicate, provided the theorem statements remain readable.

The semantic meaning must be:

```text
composite successor:
  oldEscape.Nonempty

prime, non-twin successor:
  oldEscape.Nonempty

prime, twin successor:
  oldEscape.card >= 2
```

Do not state `card >= 2` as necessary outside the twin branch.

## 2. Local exact equivalence with the real escape set

For `2 <= n`, prove:

```lean
theorem successorOldEscapeCriterion_iff_escapingSquareOffsets_nonempty
    {n : ℕ} (hn : 2 ≤ n) :
    SuccessorOldEscapeCriterion n ↔
      (escapingSquareOffsets (n + 1)).Nonempty
```

Use the existing branch theorems, not fresh arithmetic:

- composite branch:
  `successorProjectedEscapingOffsets_eq_old_of_composite`
- prime non-twin branch:
  `successorProjectedEscapingOffsets_nonempty_iff_old_of_not_twinPrime`
- prime twin branch:
  `successorProjectedEscapingOffsets_nonempty_iff_two_oldEscape_of_twinPrime`
- projected/Legendre identification:
  `successorProjectedEscapingOffsets_eq_escapingSquareOffsets`

This theorem is the local anti-relabeling test.

## 3. Equivalent prime-witness spelling

Using the existing Legendre bridge, prove the equivalent local prime form:

```lean
theorem successorOldEscapeCriterion_iff_exists_prime_in_successor_squareCell
    {n : ℕ} (hn : 2 ≤ n) :
    SuccessorOldEscapeCriterion n ↔
      ∃ p, Nat.Prime p ∧ SquareCell (n + 1) p
```

Prefer reuse of `squareCell_iff_exists_squareOffset`,
`squareOffset_prime_iff_projection_survivor`, or the existing
`escapingSquareOffsets` frontier rather than duplicating primality arguments.

## 4. Global provider proposition

Package the global old-escape frontier from the first nontrivial successor
level:

```lean
def SuccessorOldEscapeProvider : Prop :=
  ∀ n : ℕ, 2 ≤ n → SuccessorOldEscapeCriterion n
```

Then prove that this provider is equivalent to the corresponding Legendre
statement for all square cells with anchor at least `3`:

```lean
theorem successorOldEscapeProvider_iff_legendre_from_three :
  SuccessorOldEscapeProvider ↔
    ∀ m : ℕ, 3 ≤ m → ∃ p, Nat.Prime p ∧ SquareCell m p
```

The index change is `m = n + 1`.

## 5. Full Legendre equivalence

Use explicit small anchors to bridge `m = 1` and `m = 2`, and prove:

```lean
theorem legendreConjecture_iff_successorOldEscapeProvider :
  LegendreConjecture ↔ SuccessorOldEscapeProvider
```

The reverse direction may discharge the small cases directly:

```text
n = 1 : witness 2
n = 2 : witness 5 (or 3)
```

Use whichever witness satisfies the existing `SquareCell` definition cleanly.

This theorem is expected to show that **an arbitrary proof of the global
old-escape provider would already be a proof of Legendre**.

## 6. Diagnostic corollaries

Provide concise theorem-level diagnostics such as:

```lean
theorem oldEscapeProvider_is_not_weaker_than_legendre :
  SuccessorOldEscapeProvider → LegendreConjecture
```

and the converse if useful.

The report must explicitly classify the outcome:

```text
If the global old-basis escape lower bound is exactly equivalent to Legendre,
then it is not by itself a new provider.  Further progress must come from an
independent structural theorem about wheel geometry / square-anchor orbit that
implies the criterion without assuming or re-encoding square-shell escape.
```

## 7. Visible regressions

Include at least two small branch examples, preferably:

- `n = 3`, successor `4` composite: old/projected escape equivalence;
- `n = 4`, successor `5` twin threshold: old escape contains the exceptional
  seat `10`, and actual escape requires another old escape.

The regression should go through the general APIs where practical.

## Outcome A+ rubric

PUU-L015 is A+ if it establishes:

1. a branch-exact `SuccessorOldEscapeCriterion`;
2. local iff with `(escapingSquareOffsets (n+1)).Nonempty` for `2 <= n`;
3. local iff with existence of a prime in the successor square cell;
4. global `SuccessorOldEscapeProvider`;
5. equivalence with Legendre from anchor `3`;
6. full equivalence with `LegendreConjecture` after explicit small cases;
7. no new existence theorem is smuggled in;
8. facade export and semantic report.

## STOP

Do **not** in this checkpoint attempt:

- to prove `SuccessorOldEscapeProvider`;
- to prove a lower bound on `successorOldBasisEscapingOffsets`;
- Jacobsthal/max-gap bounds;
- full wheel-gap recursion;
- square-hole propagation;
- prime density or PNT;
- PowerSwap;
- GN/CosmicFormula;
- RH.

The next step must depend on the audit result.

If the provider is equivalent to Legendre, the next research checkpoint must
seek an **independent wheel/square-orbit invariant** that implies the local
criterion.  Do not continue by merely renaming the same escape proposition.

## Report

Create:

```text
lean/dk_math/docs/dev/NumberTheory-PrimorialUnitUniverse-260827-v0/
  primorial-unit-universe-old-escape-frontier-equivalence-audit-260827.md
```

The report must distinguish:

- exact local classification supplied by PUU-L014;
- local/global equivalence versus a genuine new provider;
- what theorem would still be mathematically new after this audit.
