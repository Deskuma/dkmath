# CGE-011 — Full Alternating Pascal Tail / Parity-Split Signed CRT

## 0. Stage contract

Continue `wip/goldbach-cross-gap-exchange-260913-v0` after CGE-010.

CGE-009/010 established the first finite signed-CRT / Pascal layers:

```text
SignedSingleCRTSum = WindowIncidence
SignedPairCRTSum   = PairOverlap
SignedTripleCRTSum = TripleOverlap
SignedQuadrupleCRT = QuadrupleOverlap
```

and CGE-010 proved the bounded identity

```text
support.card - 1
  = (choose support.card 2 - choose support.card 3)
    + choose support.card 4
```

only under the visible support bound `support.card ≤ 4`.

That bound is essential.  At support size five,

```text
choose 5 2 = 10
choose 5 3 = 10
choose 5 4 = 5
support.card - 1 = 4
```

so the four-layer expression gives `5`, not `4`.  Do not export an unconditional
four-layer payment.

The goal of CGE-011 is to replace truncated alternating subtraction by the
**full finite Pascal tail split by parity**, entirely in `Nat` if practical.
The preferred exact local identity is

```text
EvenTailMass = OverlapExcess + OddTailMass
```

where

```text
EvenTailMass = sum of choose(k,j) over even j ≥ 2
OddTailMass  = sum of choose(k,j) over odd  j ≥ 3.
```

Equivalently, in classical notation,

```text
Σ_{even j≥2} C(k,j) = (k-1) + Σ_{odd j≥3} C(k,j).
```

This identity is valid for every finite support size, including `k=0,1`, and
avoids unsafe intermediate `Nat` subtraction.

The stage remains finite, balanced-window, and anchor-local.  Do **not** assert
Strong Goldbach, a universal survivor theorem, a universal strict budget, or
any analytic/density statement.

## 1. Existing production API to reuse

Reuse the current declarations rather than duplicating them.

From `BalancedCapacity.lean`:

```text
goldbachObstructionSupportIn
goldbachWindowLocalOverlapExcess
goldbachWindowOverlapExcess
goldbachWindowIncidence
goldbachWindowSurvivors_nonempty_iff_incidence_lt
```

From `BalancedSignedCRTIncidence.lean`:

```text
goldbachSignedSingleCRTSum
goldbachSignedSingleCRTSum_eq_windowIncidence
goldbachPairAt_of_exact_signed_crt_budget
```

From `BalancedSignedCRTExact.lean` / `BalancedSignedCRTOverlap.lean`:

```text
goldbachProgressionSeats
goldbachProgressionWindowCount
mem_goldbachProgressionSeats_iff_balanced_modEq
goldbach_signed_pair_raw_iff_support
```

From `BalancedSignedCRTQuadruple.lean`:

```text
goldbachPrimeQuadruples
signedQuadrupleResidues
goldbachWindowQuadrupleSupportSeats
goldbachSignedQuadrupleCRTCount
goldbachWindowQuadrupleOverlapCount
```

The quadruple implementation is a useful template, but CGE-011 should provide
a generic finite-subset layer instead of adding fifth, sixth, seventh modules
one by one.

Keep the CGE-008 endpoint normalization hypothesis `2 ≤ n` explicit where the
progression/window equivalence requires it.

## 2. Suggested owner module

Add a focused owner module, candidate path:

```text
DkMath/NumberTheory/Goldbach/BalancedSignedCRTParityTail.lean
```

and export it from:

```text
DkMath/NumberTheory/Goldbach.lean
```

Candidate declaration names below are suggestions, not pre-existing API
contracts.  Record final names in `report-011.md`.

## 3. Generic finite prime-subset / signed CRT layer

Generalize the CGE-010 four-element subset construction to an arbitrary finite
subset `Q ⊆ S`.

A natural family is:

```lean
def signedSubsetResidues (n : ℕ) (Q : Finset ℕ) : Finset ℕ :=
  (Finset.range (Q.prod id)).filter (fun t =>
    ∀ r ∈ Q, (t : ZMod r) ∈ goldbachForbiddenResidues n r)
```

and the associated balanced-window count:

```lean
def goldbachSignedSubsetCRTCount
    (n w : ℕ) (Q : Finset ℕ) : ℕ :=
  ∑ t₀ ∈ signedSubsetResidues n Q,
    goldbachProgressionWindowCount (min (n - 2) w) t₀ (Q.prod id)
```

Also introduce the generic support-seat set:

```lean
def goldbachWindowSubsetSupportSeats
    (n w : ℕ) (S Q : Finset ℕ) : Finset ℕ :=
  (goldbachBalancedOffsets n w).filter (fun t =>
    ∀ r ∈ Q, r ∈ goldbachObstructionSupportIn n t S)
```

Prove the exact generic count theorem under the same finite anchor firewall used
by CGE-008/010:

```text
goldbachSignedSubsetCRTCount n w Q
  = card (goldbachWindowSubsetSupportSeats n w S Q)
```

for `Q ⊆ S`, with `KnownPrimeScales S`, the world upper bound, `P < n-w`, and
`2 ≤ n` explicit.

Prefer a theorem that works for every finite `Q`, including `Q = ∅`, if this
comes for free.  If positivity of `Q.prod id` makes the empty case awkward,
then require `Q.Nonempty` or `1 ≤ Q.card`; do not hide the boundary.

Important firewalls:

- `Q` is a set of primes, not an ordered tuple and not a multiset;
- collapsed `±n` residues are deduplicated by the residue `Finset`;
- do not multiply sign-label counts and call that a CRT cardinality;
- retain the anchor-local proper-obstruction equivalence.

## 4. Generic Pascal layer by subset cardinality

Define the `j`-th overlap count using the existing obstruction support:

```lean
def goldbachWindowJOverlapCount
    (n w : ℕ) (S : Finset ℕ) (j : ℕ) : ℕ :=
  ∑ t ∈ goldbachBalancedOffsets n w,
    Nat.choose (goldbachObstructionSupportIn n t S).card j
```

Then define the signed CRT world sum over `j`-element prime subsets:

```lean
def goldbachSignedJCRTSum
    (n w : ℕ) (S : Finset ℕ) (j : ℕ) : ℕ :=
  ∑ Q ∈ S.powersetCard j,
    goldbachSignedSubsetCRTCount n w Q
```

Prove the generic double-count identity:

```text
goldbachSignedJCRTSum n w S j
  = goldbachWindowJOverlapCount n w S j.
```

This theorem is the main structural generalization of CGE-008/010.  It should
specialize conceptually to the existing pair/triple/quadruple layers, but do
not delete or rename those established APIs in this stage.

If useful, add compatibility lemmas for `j=2,3,4` that recover the existing
counts.  Keep them lightweight.

## 5. Parity-split Pascal tail — no truncated subtraction

Define local even/odd tail masses at one seat.  Either a `Nat.choose` sum or a
powerset-cardinality definition is acceptable.  A powerset formulation may be
simpler and more robust:

```text
Even tail: subsets of support with even cardinality and cardinality ≥ 2
Odd tail:  subsets of support with odd  cardinality and cardinality ≥ 3
```

Candidate APIs:

```lean
def goldbachWindowLocalEvenTailMass ... : ℕ := ...
def goldbachWindowLocalOddTailMass  ... : ℕ := ...
```

and their window sums:

```lean
def goldbachWindowEvenTailMass ... : ℕ := ...
def goldbachWindowOddTailMass  ... : ℕ := ...
```

Prove the pure local identity for every finite support size:

```text
EvenTailMass = LocalOverlapExcess + OddTailMass.
```

Then sum it over the balanced window:

```text
goldbachWindowEvenTailMass n w S
  = goldbachWindowOverlapExcess n w S
    + goldbachWindowOddTailMass n w S.
```

This identity must be unconditional in the support cardinality.  In particular
it must cover support sizes `0,1,2,3,4,5,...` without a world-card bound.

A recommended proof strategy is to avoid alternating `Nat` subtraction
entirely.  For a finite support set `U`:

```text
all even-card subsets = all odd-card subsets          -- for U.Nonempty
EvenTail + 1         = all even-card subsets          -- remove ∅
OddTail  + U.card    = all odd-card subsets           -- remove singletons
```

with `U=∅` handled separately.  A binomial-sum proof is also acceptable if it
stays robust and does not introduce hidden integer coercion complications.

## 6. Signed CRT parity-tail sums

Define world-level signed CRT sums directly over finite prime subsets, not by a
hard-coded maximum degree.

Candidate shapes:

```lean
def goldbachSignedEvenTailCRTSum (n w : ℕ) (S : Finset ℕ) : ℕ :=
  ∑ Q ∈ S.powerset.filter (fun Q => 2 ≤ Q.card ∧ Even Q.card),
    goldbachSignedSubsetCRTCount n w Q

def goldbachSignedOddTailCRTSum (n w : ℕ) (S : Finset ℕ) : ℕ :=
  ∑ Q ∈ S.powerset.filter (fun Q => 3 ≤ Q.card ∧ Odd Q.card),
    goldbachSignedSubsetCRTCount n w Q
```

Equivalent definitions via the generic `j`-layer are acceptable.

Prove exact identities under the finite prime-world anchor:

```text
goldbachSignedEvenTailCRTSum = goldbachWindowEvenTailMass
goldbachSignedOddTailCRTSum  = goldbachWindowOddTailMass.
```

Combining these with CGE-009 should give the exact first-layer/tail picture:

```text
SignedSingleCRTSum = Incidence
SignedEvenTailCRT  = OverlapExcess + SignedOddTailCRT
```

under the stated finite anchor hypotheses.

## 7. Exact parity-budget normal form for survivor existence

Use the exact incidence conservation and the parity-tail identity to eliminate
subtraction completely.

Target theorem shape:

```lean
theorem goldbachWindowSurvivors_nonempty_iff_exact_signed_parity_budget
    {n w P : ℕ} {S : Finset ℕ}
    (hn : 2 ≤ n)
    (hS : KnownPrimeScales S)
    (hbound : ∀ ⦃r : ℕ⦄, r ∈ S → r ≤ P)
    (hanchor : P < n - w) :
    (goldbachWindowSurvivors n w S).Nonempty ↔
      goldbachSignedSingleCRTSum n w S +
          goldbachSignedOddTailCRTSum n w S <
        (goldbachBalancedOffsets n w).card +
          goldbachSignedEvenTailCRTSum n w S
```

This should be an **iff** if all preceding identities are exact.  The theorem
is only a finite normal form; it does not prove the strict inequality for
arbitrary `n`.

This is preferable to the previous truncated expression
`Pair - Triple + Quadruple - ...`, because every quantity remains nonnegative
and no intermediate `Nat` truncation occurs.

## 8. Anchor-local Goldbach wrapper

For `S = primeScalesUpTo P`, add the corresponding sufficient endpoint:

```lean
theorem goldbachPairAt_of_exact_signed_parity_budget
    {n w P : ℕ}
    (hn : 2 ≤ n)
    (hw : w ≤ n)
    (hanchor : P < n - w)
    (hhorizon : n + w ≤ squareBody P)
    (hbudget :
      goldbachSignedSingleCRTSum n w (primeScalesUpTo P) +
          goldbachSignedOddTailCRTSum n w (primeScalesUpTo P) <
        (goldbachBalancedOffsets n w).card +
          goldbachSignedEvenTailCRTSum n w (primeScalesUpTo P)) :
    GoldbachPairAt n
```

Reuse the existing window-survivor → SquareBody certification bridge.  Do not
introduce a new primality argument.

## 9. Required arithmetic / kernel regressions

Extend `GoldbachBalancedReflectionAudit.lean`.

### 9.1 Preserve earlier targets

For the already established examples, kernel-check the parity form:

```text
(n,w,P)=(15,8,5):
  Window=9, Incidence=9, EvenTail=3, OddTail=0
  9 + 0 < 9 + 3

(n,w,P)=(50,10,7):
  Window=11, Incidence=19, EvenTail=12, OddTail=2
  19 + 2 < 11 + 12

(n,w,P)=(22,9,7):
  Window=10, Incidence=18, EvenTail=14, OddTail=5
  18 + 5 < 10 + 14
```

The `n=22` values should agree with the CGE-010 layers:

```text
EvenTail = Pair + Quadruple = 13 + 1 = 14
OddTail  = Triple            = 5
```

### 9.2 Mandatory support-size-five firewall / target

Add a regression with a genuine support-size-five seat.  Use

```text
n = 68
w = 15
P = 11
S = primeScalesUpTo 11 = {2,3,5,7,11}
```

unless the implementation discovers a cleaner equivalent target.

Expected balanced support-card sequence for `t=0..15`:

```text
1,1,5,1,2,2,1,2,3,2,2,1,3,3,2,0
```

Expected exact totals:

```text
Window      = 16
Incidence   = 31
Covered     = 15
Overlap     = 16
Pair        = 25
Triple      = 13
Quadruple   = 5
Quintuple   = 1
EvenTail    = 25 + 5 = 30
OddTail     = 13 + 1 = 14
```

Kernel-check the local support-size-five arithmetic:

```text
C(5,2)=10, C(5,3)=10, C(5,4)=5, C(5,5)=1
EvenTail = 10+5 = 15
OddTail  = 10+1 = 11
15 = 4 + 11
```

and preserve the CGE-010 firewall:

```text
Pair - Triple + Quadruple = 5   -- overpays support excess 4
```

while the full parity split is exact.

For the full target, kernel-check:

```text
31 + 14 < 16 + 30
```

and, since the anchor/horizon conditions hold,

```text
11 < 68 - 15
68 + 15 ≤ squareBody 11
```

it is desirable to replay the fixed conditional endpoint
`GoldbachPairAt 68` through the new parity-budget wrapper.

This is a finite regression only, not a universal Goldbach theorem.

## 10. Firewalls / non-goals

Do not add any of the following in CGE-011:

- Strong Goldbach;
- `∀ n, ∃` universal survivor/provider theorem;
- a proof that the parity budget is universally strict;
- a claim that full signed CRT counting by itself proves Goldbach;
- an analytic density, RH/CFBRC, AKS, probabilistic, or asymptotic input;
- coprimality as a primality substitute;
- an infinite alternating series;
- a hidden maximum support-card assumption;
- duplicated hard-coded quintuple/sextuple modules if the generic subset layer
  suffices;
- `sorry`, `admit`, `native_decide`, `unsafe`, or new axioms.

The exact parity-budget iff is a **finite re-expression of survivor existence**
under explicit anchor hypotheses.  It is not an existence proof until the
strict arithmetic inequality is supplied.

Retain the CGE-004 coarse capacity API and the CGE-005/010 truncated APIs for
backward compatibility and auditing; CGE-011 adds the generic exact normal
form rather than deleting earlier layers.

## 11. Verification

Run at least:

```text
lake build DkMath.NumberTheory.Goldbach DkMathTest.NumberTheory.GoldbachBalancedReflectionAudit
lake build DkMath
git diff --check
```

Audit new public declarations with `#print axioms` where practical.  Report
any `sorryAx`, new axiom, warning, or forbidden construct immediately.

## 12. Report

Add:

```text
lean/dk_math/docs/dev/goldbach-cross-gap-exchange-260913/report-011.md
```

Record:

- final generic subset/CRT declaration names;
- whether generic `j`-layer CRT = Pascal overlap was proved;
- whether the unconditional finite parity-tail identity was proved;
- whether signed even/odd CRT sums were exactly identified with the parity
  overlap masses;
- whether the exact parity-budget survivor iff was proved;
- whether the anchor-local `GoldbachPairAt` wrapper was proved;
- target-15, target-50, target-22 values;
- target-68 support-size-five values and whether `GoldbachPairAt 68` replayed;
- build/audit results;
- Outcome A/B/C.

Preferred outcome labels:

```text
A — FULL FINITE PARITY-SPLIT CRT/PASCAL TAIL
B — PARTIAL GENERIC SUBSET / PARITY IDENTIFICATION
C — STRUCTURAL / ENGINEERING ONLY
```

The decisive CGE-011 success condition is an unconditional finite identity

```text
EvenTailMass = OverlapExcess + OddTailMass
```

for arbitrary support cardinality, together with the exact signed-CRT
identification of those finite tail masses under the explicit anchor firewall.