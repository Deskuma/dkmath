# CGE-009 — Exact Signed CRT Incidence / Single-Layer Capacity

## 0. Stage contract

This stage continues `wip/goldbach-cross-gap-exchange-260913-v0` after CGE-008.

CGE-008 established, under an explicit finite prime-world anchor, the exact identities

```text
goldbachSignedPairCRTSum   = goldbachWindowPairOverlapCount
goldbachSignedTripleCRTSum = goldbachWindowTripleOverlapCount
```

The remaining coarse term in the current Pascal provider is the **single-prime incidence**. CGE-004 only has the upper bound

```text
card (goldbachWindowBlockedSeats n w r)
  ≤ (if r ∣ 2*n then 1 else 2) * (w / r + 1)
```

which forgets the actual starting residues of the forbidden progressions.

The goal of CGE-009 is to give the `r = 1` layer the same exact signed-CRT treatment already completed for the `r = 2,3` layers.

This is still a finite, balanced-window, anchor-local stage. Do **not** assert Strong Goldbach, a universal survivor theorem, or a universal strict budget.

## 1. Existing production API to reuse

Reuse the current production declarations rather than duplicating their mathematics.

From `BalancedReflection.lean` / `BalancedCapacity.lean`:

```text
goldbachBalancedOffsets
goldbachWindowBlockedSeats
goldbachWindowIncidence
goldbachObstructionSupportIn
goldbachWindowSurvivors
goldbachWindowIncidenceConservation
goldbachWindowSurvivors_nonempty_iff_incidence_lt
```

From `PrimeWorld.lean`:

```text
goldbachForbiddenResidues
goldbach_card_forbidden
goldbach_obstructed_iff_mem_forbidden
```

From `BalancedSignedCRTOverlap.lean` / `BalancedSignedCRTExact.lean`:

```text
goldbachProgressionSeats
goldbachProgressionWindowCount
mem_goldbachProgressionSeats_iff_balanced_modEq
goldbach_signed_pair_raw_iff_support
goldbachSignedPairCRTSum
goldbachSignedTripleCRTSum
goldbachSignedPairCRTSum_eq_windowPairOverlapCount
goldbachSignedTripleCRTSum_eq_windowTripleOverlapCount
```

From `BalancedPascalOverlap.lean`:

```text
goldbachWindowSurvivor_of_incidence_le_of_pairMinusTriple_budget
```

From CGE-003:

```text
goldbachPairAt_of_goldbachWindowSurvivor
```

The existing CGE-008 endpoint normalization requires `2 ≤ n`; keep that hypothesis explicit where needed.

## 2. Suggested owner module

Add a small owner module, candidate path:

```text
DkMath/NumberTheory/Goldbach/BalancedSignedCRTIncidence.lean
```

Export it from:

```text
DkMath/NumberTheory/Goldbach.lean
```

Candidate declaration names below are suggestions, not pre-existing API contracts. If a cleaner Lean name is preferable, use it and record the final names in `report-009.md`.

## 3. Canonical single-prime signed residues

Introduce the canonical natural representatives of the one-prime forbidden classes.

Candidate:

```lean
def signedSingleResidues (n r : ℕ) : Finset ℕ :=
  (Finset.range r).filter (fun t =>
    (t : ZMod r) ∈ goldbachForbiddenResidues n r)
```

Provide the expected membership theorem:

```text
t ∈ signedSingleResidues n r
↔ t < r ∧ (t : ZMod r) ∈ goldbachForbiddenResidues n r.
```

For prime/nonzero `r`, prove a safe cardinal statement. Prefer the exact form if straightforward:

```text
card (signedSingleResidues n r)
  = card (goldbachForbiddenResidues n r)
  = if r ∣ 2*n then 1 else 2.
```

At minimum, prove the bound `≤ 2`, but exact cardinality is desirable because the family is intended to be the canonical natural representative of the existing `ZMod r` forbidden set.

Important firewall: when `r ∣ 2*n`, the two signs collapse and there is one canonical residue, not two labels with multiplicity.

## 4. Exact one-prime progression count

Define the exact one-prime signed CRT count in the same normalization used by CGE-008.

Candidate:

```lean
def goldbachSignedSingleCRTCount (n w r : ℕ) : ℕ :=
  ∑ t₀ ∈ signedSingleResidues n r,
    goldbachProgressionWindowCount (min (n - 2) w) t₀ r
```

The intended meaning is the exact number of balanced seats whose residue modulo `r` is one of the forbidden signed classes.

Prove the one-prime analogue of the CGE-008 progression/support identification. A useful intermediate finite set is acceptable, e.g. balanced seats `t` with `r ∈ goldbachObstructionSupportIn n t S`, or directly `goldbachWindowBlockedSeats n w r`.

Target production theorem, candidate shape:

```lean
theorem goldbachSignedSingleCRTCount_eq_windowBlockedSeats_card
    {n w P : ℕ} {S : Finset ℕ}
    (hn : 2 ≤ n)
    (hS : KnownPrimeScales S)
    (hbound : ∀ ⦃r : ℕ⦄, r ∈ S → r ≤ P)
    (hanchor : P < n - w)
    {r : ℕ} (hr : r ∈ S) :
    goldbachSignedSingleCRTCount n w r =
      (goldbachWindowBlockedSeats n w r).card
```

The exact signature may differ if a smaller hypothesis set suffices.

The proof should use the same structural ingredients as CGE-008: canonical residue `t % r`; `mem_goldbachProgressionSeats_iff_balanced_modEq`; raw forbidden residue membership; the anchor-local proper-obstruction firewall; and mutually inverse finite maps / cardinal antisymmetry if needed.

Do not recover the old coarse `w / r + 1` estimate and call it exact. The point of this stage is to retain the actual progression start `t₀`.

## 5. Exact signed single sum = incidence

Define the world sum:

```lean
def goldbachSignedSingleCRTSum (n w : ℕ) (S : Finset ℕ) : ℕ :=
  ∑ r ∈ S, goldbachSignedSingleCRTCount n w r
```

Then sum the per-prime exact theorem and prove:

```text
goldbachSignedSingleCRTSum n w S
  = goldbachWindowIncidence n w S.
```

Candidate theorem shape:

```lean
theorem goldbachSignedSingleCRTSum_eq_windowIncidence
    {n w P : ℕ} {S : Finset ℕ}
    (hn : 2 ≤ n)
    (hS : KnownPrimeScales S)
    (hbound : ∀ ⦃r : ℕ⦄, r ∈ S → r ≤ P)
    (hanchor : P < n - w) :
    goldbachSignedSingleCRTSum n w S =
      goldbachWindowIncidence n w S
```

This is the main CGE-009 theorem.

After it is proved, the first three finite Pascal/CRT layers should read:

```text
SignedSingleCRTSum = Incidence
SignedPairCRTSum   = PairOverlap
SignedTripleCRTSum = TripleOverlap
```

Record this explicitly in the module docstring/report, but do not infer any unproved higher-layer identity.

## 6. Comparison-free exact signed CRT survivor provider

Use CGE-008 plus the new single-layer identity to remove the **coarse incidence bound** from the provider.

Prove a generic sufficient theorem of the form:

```lean
theorem goldbachWindowSurvivor_of_exact_signed_crt_budget
    {n w P : ℕ} {S : Finset ℕ}
    (hn : 2 ≤ n)
    (hS : KnownPrimeScales S)
    (hbound : ∀ ⦃r : ℕ⦄, r ∈ S → r ≤ P)
    (hanchor : P < n - w)
    (hbudget :
      goldbachSignedSingleCRTSum n w S <
        (goldbachBalancedOffsets n w).card +
          (goldbachSignedPairCRTSum n w S -
            goldbachSignedTripleCRTSum n w S)) :
    (goldbachWindowSurvivors n w S).Nonempty
```

The intended proof is:

```text
SignedSingle = Incidence
SignedPair   = PairOverlap
SignedTriple = TripleOverlap
PairOverlap - TripleOverlap ≤ OverlapExcess
```

then reuse the existing CGE-005/CGE-004 provider.

This theorem is **sufficient only**. Do not state an iff. For support size `≥ 4`, pair-minus-triple can underpay the true overlap excess, so failure of this budget does not imply absence of a survivor.

## 7. Anchor-local Goldbach wrapper

For `S = primeScalesUpTo P`, add the expected conditional endpoint:

```lean
theorem goldbachPairAt_of_exact_signed_crt_budget
    {n w P : ℕ}
    (hn : 2 ≤ n)
    (hw : w ≤ n)
    (hanchor : P < n - w)
    (hhorizon : n + w ≤ squareBody P)
    (hbudget :
      goldbachSignedSingleCRTSum n w (primeScalesUpTo P) <
        (goldbachBalancedOffsets n w).card +
          (goldbachSignedPairCRTSum n w (primeScalesUpTo P) -
            goldbachSignedTripleCRTSum n w (primeScalesUpTo P))) :
    GoldbachPairAt n
```

Use the existing `primeScalesUpTo` prime certification/bounds; do not add a new primality mechanism.

## 8. Required regressions

Extend the existing Goldbach balanced-reflection audit.

### 8.1 Target 30

For `n=15`, `w=8`, `P=5`, `S=primeScalesUpTo 5 = {2,3,5}`, kernel-check:

```text
SignedSingleCRTSum = Incidence = 9
SignedPairCRTSum   = PairOverlap = 3
SignedTripleCRTSum = TripleOverlap = 0
Window = 9
9 < 9 + (3 - 0)
```

Replay this through the new exact signed CRT provider.

### 8.2 Mixed-sign target `n = 50`

For `n=50`, `w=10`, `P=7`, `S=primeScalesUpTo 7 = {2,3,5,7}`, kernel-check at least:

```text
single count at r=2 = 6
single count at r=3 = 7
single count at r=5 = 3
single count at r=7 = 3
SignedSingleCRTSum = Incidence = 19
SignedPairCRTSum   = PairOverlap = 12
SignedTripleCRTSum = TripleOverlap = 2
Window = 11
```

Retain the contrast:

```text
coarse capacity = 21
21 < 11 + (12 - 2)   -- false
19 < 11 + (12 - 2)   -- true
```

Then replay the new exact signed CRT provider for this fixed target. Since `7 < 50 - 10` and `50 + 10 ≤ squareBody 7` also hold, it is acceptable and desirable for the audit to close the **fixed** `GoldbachPairAt 50` through the new conditional production wrapper.

This is only a regression/example, not a universal theorem.

## 9. Firewalls / non-goals

Do not add any of the following in CGE-009:

- Strong Goldbach;
- `∀ n, ∃` universal window survivor;
- a universal exact signed CRT strict budget;
- an iff between the pair-minus-triple budget and survivor existence;
- analytic density, RH/CFBRC, AKS, or probabilistic input;
- coprimality as a replacement for primality;
- hidden assumptions that every finite world is `primeScalesUpTo P`;
- a higher Pascal layer beyond what is needed here;
- `sorry`, `admit`, `native_decide`, `unsafe`, or new axioms.

The coarse CGE-004 capacity theorem must remain available. CGE-009 adds a sharper exact finite count; it does not delete the simpler upper bound.

## 10. Verification

Run at least:

```text
lake build DkMath.NumberTheory.Goldbach DkMathTest.NumberTheory.GoldbachBalancedReflectionAudit
lake build DkMath
git diff --check
```

Audit new public declarations with `#print axioms` where practical. Report any `sorryAx`, new axiom, warning, or forbidden construct immediately.

## 11. Report

Add:

```text
lean/dk_math/docs/dev/goldbach-cross-gap-exchange-260913/report-009.md
```

Record final declaration names; whether single progression ↔ blocked seats is exact; whether `SignedSingleCRTSum = Incidence` is proved; whether the comparison-free exact signed CRT survivor wrapper is proved; target-15 values; target-50 values, especially `21` coarse versus `19` exact; build/audit results; and Outcome A/B/C.

Preferred outcome labels:

```text
A — EXACT SIGNED CRT INCIDENCE
B — PARTIAL SINGLE-LAYER IDENTIFICATION
C — STRUCTURAL / ENGINEERING ONLY
```

The decisive success condition is an exact production theorem identifying the signed single CRT world sum with `goldbachWindowIncidence` under explicit finite anchor hypotheses.