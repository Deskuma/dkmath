# CGE-012 — Exact Parity Margin / Maximal Anchor Window Transport

## 0. Stage contract

This stage continues `wip/goldbach-cross-gap-exchange-260913-v0` after CGE-011.

CGE-011 completed the finite inclusion-exclusion side of the Goldbach balanced-window ledger. In particular, under the explicit finite prime-world anchor assumptions, production API now identifies

```text
SignedSingleCRTSum = WindowIncidence
SignedEvenTailCRT  = WindowEvenTailMass
SignedOddTailCRT   = WindowOddTailMass
EvenTail = OverlapExcess + OddTail
```

and provides the exact iff

```text
goldbachWindowSurvivors.Nonempty
↔ SignedSingle + SignedOddTail < Window + SignedEvenTail.
```

The purpose of CGE-012 is **not** to add another inclusion-exclusion layer. The finite Pascal/CRT tail is complete. This stage packages the strict-budget slack as an exact margin, proves that it is exactly the survivor cardinality, and studies how that margin transports when the balanced window grows while the prime world is held fixed.

The second goal is to remove arbitrary window choice from the anchor-local search: for fixed `(n,P)`, define the largest balanced window satisfying both the left-anchor and `SquareBody` horizon inequalities, prove it is maximal, and prove every smaller admissible-window survivor transports to that maximal window.

This remains finite and conditional. Do **not** assert Strong Goldbach, a universal positive margin, or a universal choice of `P`.

## 1. Existing production API to reuse

Reuse the current declarations rather than duplicating them.

From `BalancedCapacity.lean` / `BalancedReflection.lean`:

```text
goldbachBalancedOffsets
goldbachWindowSurvivors
goldbachWindowIncidence
goldbachWindowOverlapExcess
goldbachWindowIncidenceConservation
goldbachWindowSurvivors_nonempty_iff_incidence_lt
goldbachPairAt_of_goldbachWindowSurvivor
```

From `BalancedSignedCRTIncidence.lean`:

```text
goldbachSignedSingleCRTSum
goldbachSignedSingleCRTSum_eq_windowIncidence
```

From `BalancedSignedCRTParityTail.lean`:

```text
goldbachSignedEvenTailCRTSum
goldbachSignedOddTailCRTSum
goldbachSignedEvenTailCRTSum_eq_overlapExcess_add_oddTailCRT
goldbachWindowSurvivors_nonempty_iff_exact_signed_parity_budget
goldbachPairAt_of_exact_signed_parity_budget
```

From the square-shell layer:

```text
squareBody
```

Keep the CGE-008/CGE-011 endpoint hypothesis `2 ≤ n` explicit where the signed CRT normalization requires it.

## 2. Suggested owner module

Add a small owner module, candidate path:

```text
DkMath/NumberTheory/Goldbach/BalancedSignedCRTMargin.lean
```

Export it from:

```text
DkMath/NumberTheory/Goldbach.lean
```

Candidate declaration names below are suggestions, not pre-existing API contracts. If Lean ergonomics favor different names, use them and record the final names in `report-012.md`.

## 3. Define the exact signed parity margin

Define the nonnegative finite slack of the exact signed parity budget.

Candidate:

```lean
def goldbachSignedParityMargin
    (n w : ℕ) (S : Finset ℕ) : ℕ :=
  (goldbachBalancedOffsets n w).card +
      goldbachSignedEvenTailCRTSum n w S -
    (goldbachSignedSingleCRTSum n w S +
      goldbachSignedOddTailCRTSum n w S)
```

This `Nat.sub` is acceptable only because the stage must prove that the subtraction is nontruncated under the exact ledger. Do not treat the raw definition itself as evidence of nonnegativity.

The decisive theorem is:

```text
goldbachSignedParityMargin n w S
  = (goldbachWindowSurvivors n w S).card.
```

Candidate theorem shape:

```lean
theorem goldbachSignedParityMargin_eq_survivors_card
    {n w P : ℕ} {S : Finset ℕ}
    (hn : 2 ≤ n)
    (hS : KnownPrimeScales S)
    (hbound : ∀ ⦃r : ℕ⦄, r ∈ S → r ≤ P)
    (hanchor : P < n - w) :
    goldbachSignedParityMargin n w S =
      (goldbachWindowSurvivors n w S).card
```

Preferred proof route:

```text
SignedSingle = Incidence
SignedEven   = OverlapExcess + SignedOdd
Survivors + Incidence = Window + OverlapExcess
```

Then close the arithmetic exactly. The theorem should expose that the parity-budget slack is not merely a sufficient statistic: it is the exact number of surviving seats.

Also provide the immediate positivity form:

```text
goldbachSignedParityMargin n w S > 0
↔ (goldbachWindowSurvivors n w S).Nonempty.
```

This should be a corollary of the cardinal identity, not a separate counting argument.

## 4. Fixed-world window inclusion

The next structural fact is independent of CRT arithmetic: for a **fixed** finite prime world `S`, increasing `w` only enlarges the balanced offset set, while `GoldbachSurvives n S t` itself does not depend on `w`.

Prove a set inclusion theorem of the form

```text
w₁ ≤ w₂
→ goldbachWindowSurvivors n w₁ S ⊆ goldbachWindowSurvivors n w₂ S.
```

This theorem should require no anchor and no primality-world assumptions if the underlying definitions permit it.

Then prove cardinal monotonicity:

```text
w₁ ≤ w₂
→ card (goldbachWindowSurvivors n w₁ S)
  ≤ card (goldbachWindowSurvivors n w₂ S).
```

Using the margin/cardinality theorem, lift this to signed parity margin monotonicity whenever the finite-world anchor hypotheses needed for both margins are available.

A useful shape is:

```lean
theorem goldbachSignedParityMargin_mono_window
    {n P w₁ w₂ : ℕ} {S : Finset ℕ}
    (hn : 2 ≤ n)
    (hS : KnownPrimeScales S)
    (hbound : ∀ ⦃r : ℕ⦄, r ∈ S → r ≤ P)
    (hw : w₁ ≤ w₂)
    (hanchor₂ : P < n - w₂) :
    goldbachSignedParityMargin n w₁ S ≤
      goldbachSignedParityMargin n w₂ S
```

Derive the smaller-window anchor from `hw` and `hanchor₂`; do not ask callers to provide redundant hypotheses if `omega` can close them safely.

Firewall: this monotonicity is for a **fixed world `S`**. It says nothing about simultaneously increasing `P`, because enlarging the prime world may remove survivors.

## 5. Optional but desirable: one-seat recurrence

If straightforward, prove the exact one-step transport before the balanced window saturates.

When the next offset `w+1` still lies in the base Goldbach offset range, the new window differs by one seat. A candidate condition is an arithmetic hypothesis equivalent to

```text
w + 1 < n - 1
```

(use the cleanest Nat form Lean prefers; for example a form such as `w + 2 < n` if correct for the implementation).

Target content:

```text
card Survivors(n,w+1,S)
  = card Survivors(n,w,S)
    + if GoldbachSurvives n S (w+1) then 1 else 0.
```

An equivalent set decomposition is acceptable and may be easier to maintain.

If proved, also transport it to the signed parity margin under the anchor hypotheses.

This recurrence is desirable but not mandatory for Outcome A. Do not spend the stage on difficult Finset normalization if monotonicity and maximal-window reduction are already complete.

## 6. Define the maximal anchor-local window

For fixed center `n` and shell parameter `P`, the two endpoint constraints are

```text
P < n - w
n + w ≤ squareBody P.
```

Under the natural feasibility assumptions `P < n` and `n ≤ squareBody P`, define the largest natural `w` satisfying both constraints.

Candidate:

```lean
def goldbachMaxAnchorWindow (n P : ℕ) : ℕ :=
  min (n - (P + 1)) (squareBody P - n)
```

Do not change the formula silently. If Nat edge cases require a different but equivalent normalization, document it in the report.

Prove **safety** under explicit feasibility assumptions:

```text
P < n
n ≤ squareBody P
```

implies, for `wMax := goldbachMaxAnchorWindow n P`,

```text
wMax ≤ n
P < n - wMax
n + wMax ≤ squareBody P.
```

The first item may be redundant but is useful for directly feeding existing wrappers.

Then prove **maximality**:

```text
P < n - w
n + w ≤ squareBody P
→ w ≤ goldbachMaxAnchorWindow n P.
```

Use exact Nat arithmetic; do not weaken this to an asymptotic or informal bound.

## 7. Max-window reduction theorem

Combine fixed-world monotonicity with maximality.

For an arbitrary finite prime world `S` bounded by `P`, under

```text
2 ≤ n
KnownPrimeScales S
∀ r ∈ S, r ≤ P
P < n
n ≤ squareBody P
```

prove that any admissible smaller window has margin at most the maximal-window margin:

```text
P < n - w
n + w ≤ squareBody P
→ goldbachSignedParityMargin n w S
  ≤ goldbachSignedParityMargin n (goldbachMaxAnchorWindow n P) S.
```

Then package the existential search reduction:

```text
(∃ w,
    P < n - w ∧
    n + w ≤ squareBody P ∧
    0 < goldbachSignedParityMargin n w S)
↔
0 < goldbachSignedParityMargin n (goldbachMaxAnchorWindow n P) S.
```

The reverse direction uses the maximal window itself and its safety theorem. This is an exact finite search reduction for `w`; it is **not** a positivity theorem.

For `S = primeScalesUpTo P`, add a convenient one-way endpoint wrapper:

```text
0 < goldbachSignedParityMargin n (goldbachMaxAnchorWindow n P)
      (primeScalesUpTo P)
→ GoldbachPairAt n
```

under the required feasibility hypotheses. Reuse the existing survivor/SquareBody bridge; do not build a new primality argument.

Do **not** state the converse `GoldbachPairAt n → margin > 0` for a fixed `P`: a Goldbach pair may lie outside this chosen anchor window.

## 8. Required kernel regressions

Extend `DkMathTest.NumberTheory.GoldbachBalancedReflectionAudit.lean`.

Keep the existing fixed-window CGE-011 values and add maximal-window regressions.

### 8.1 `(n,P) = (15,5)`

Expected maximal window:

```text
goldbachMaxAnchorWindow 15 5 = 9
```

Check safety and maximality for the previously used `w=8`.

Expected survivor/margin values:

```text
margin at w=8 = 3
margin at w=9 = 3
```

### 8.2 `(n,P) = (50,7)`

Expected:

```text
goldbachMaxAnchorWindow 50 7 = 13
margin at w=10 = 2
margin at w=13 = 2
```

This verifies that increasing the admissible window need not create a new survivor at every step.

### 8.3 `(n,P) = (22,7)`

Expected:

```text
goldbachMaxAnchorWindow 22 7 = 14
margin at w=9 = 1
margin at w=14 = 1
```

### 8.4 `(n,P) = (68,11)`

Expected:

```text
goldbachMaxAnchorWindow 68 11 = 56
margin at w=15 = 1
margin at w=56 = 4
```

This is the most important transport regression: the fixed world acquires three additional surviving seats as the balanced window grows. It demonstrates that the margin is a genuine transport quantity, not merely a renamed boolean.

If convenient, kernel-check the actual surviving offsets at the maximal window:

```text
{15, 21, 39, 45}
```

Treat this as a regression only, not as production mathematics.

For each target, use `decide +kernel` or equivalent kernel-checkable finite evaluation consistent with repository policy.

## 9. Structural interpretation to record, not overstate

The report should explicitly distinguish three facts:

1. `goldbachSignedParityMargin` is exactly survivor cardinality under the finite anchor.
2. For fixed `S`, the margin is monotone in the window width.
3. `goldbachMaxAnchorWindow` eliminates the arbitrary finite search over admissible `w` for fixed `(n,P,S)`.

None of these proves that the maximal margin is positive for every `n` or for any universally chosen `P`.

The next unresolved provider problem after this stage should therefore become sharper:

```text
For which choices of P relative to n can one prove
0 < margin(n, maxAnchorWindow(n,P), primeScalesUpTo P)?
```

Do not attempt to solve that universal question in CGE-012.

## 10. Firewalls / non-goals

Do not add any of the following:

- Strong Goldbach;
- a universal positive-margin theorem;
- `∀ n, ∃ P` with positive margin;
- a converse from `GoldbachPairAt n` to positive margin for a fixed `P`;
- monotonicity in `P` without proof (the prime world changes);
- analytic density, RH/CFBRC, AKS, probabilistic heuristics, or external prime-distribution input;
- a new inclusion-exclusion layer beyond CGE-011;
- coprimality as a replacement for primality;
- `sorry`, `admit`, `native_decide`, `unsafe`, or new axioms.

Keep all previous coarse capacity and bounded-layer APIs intact. This stage adds a transport/optimization layer; it does not delete earlier forms.

## 11. Verification

Run at least:

```text
lake build DkMath.NumberTheory.Goldbach DkMathTest.NumberTheory.GoldbachBalancedReflectionAudit
lake build DkMath
git diff --check
```

Audit the new public declarations with `#print axioms` where practical. Report any `sorryAx`, new axiom, warning, or forbidden construct immediately.

## 12. Report

Add:

```text
lean/dk_math/docs/dev/goldbach-cross-gap-exchange-260913/report-012.md
```

Record:

- final declaration names;
- whether signed parity margin = survivor cardinality is exact;
- whether fixed-world window monotonicity is proved;
- whether the one-seat recurrence was proved or deferred;
- exact `goldbachMaxAnchorWindow` definition;
- safety and maximality theorems;
- whether the existential admissible-window search reduces to the maximal window;
- target regressions for `15/5`, `50/7`, `22/7`, `68/11`;
- build/audit results;
- Outcome A/B/C.

Preferred outcome labels:

```text
A — EXACT PARITY MARGIN / MAX-WINDOW TRANSPORT
B — MARGIN IDENTITY ONLY
C — STRUCTURAL / ENGINEERING ONLY
```

The decisive success condition for Outcome A is: exact margin = survivor cardinality, fixed-world window monotonicity, and a proved maximal admissible anchor window with the search-reduction theorem.
