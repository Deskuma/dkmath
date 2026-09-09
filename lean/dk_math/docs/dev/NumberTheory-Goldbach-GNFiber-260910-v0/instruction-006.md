# instruction-006 — Goldbach Overlap Ledger / Pair-Overlap Transplant

Date: 2026-09-10  
Branch: \`wip/NumberTheory-Goldbach-GNFiber-260910-v0\`  
Executor target: Luna Codex  
Status: implementation instruction

## 0. Purpose

Astra completed the fixed-center GN reformulation, finite proper-obstruction reduction,
paired CRT world, exact full-period cardinality, PCK bridge, and conditional capacity closure.

It also kernel-refuted the naive universal route

\`\`\`text
goldbachIncidence n (goldbachSmallPrimes n) < n - 1
\`\`\`

at \`n = 6\`.

The next checkpoint must **not** try to repair that false inequality by a looser estimate.
Instead, transplant the already successful Legendre/Primitive overlap-accounting pattern
into the Goldbach vocabulary.

The first target is an exact finite conservation law:

$$
\operatorname{Incidence}(n)
=
\operatorname{Covered}(n)
+
\operatorname{OverlapExcess}(n).
$$

Combining with the already proved

$$
\operatorname{Survivors}(n)
+
\operatorname{Covered}(n)
=
n-1
$$

should yield

$$
\boxed{
\operatorname{Survivors}(n)
+
\operatorname{Incidence}(n)
=
(n-1)+\operatorname{OverlapExcess}(n).
}
$$

This is a bookkeeping theorem, not a Goldbach proof.  Its role is to expose exactly
how obstruction overlap pays for incidence overcounting.

After the exact ledger is complete, add a Goldbach-native unordered prime-pair overlap
ledger analogous to the existing Legendre \`PairOverlap\` layer.

Stop after the pair-overlap upper bound.  Do **not** attempt the final universal escape
provider in this checkpoint.

---

## 1. Read first

Current Goldbach owners:

\`\`\`text
DkMath/NumberTheory/Goldbach/Basic.lean
DkMath/NumberTheory/Goldbach/Obstruction.lean
DkMath/NumberTheory/Goldbach/PrimeWorld.lean
DkMath/NumberTheory/Goldbach/Cardinality.lean
DkMath/NumberTheory/Goldbach/Capacity.lean
DkMath/NumberTheory/Goldbach/Conservation.lean
DkMath/NumberTheory/Goldbach/Signature.lean
DkMath/NumberTheory/Goldbach/Limitations.lean
DkMath/NumberTheory/Goldbach.lean
\`\`\`

Current exact APIs to reuse:

\`\`\`lean
goldbachOffsets
goldbachSmallPrimes
GoldbachProperObstructed
GoldbachSurvives
goldbachSurvivors
goldbachBlockedSeats
goldbachCoveredSeats
goldbachIncidence

goldbachCoveredSeats_eq_filter
goldbach_survivors_add_covered
goldbach_covered_le_incidence
goldbachPairAt_iff_covered_card_lt
goldbach_six_capacity_values
\`\`\`

Do not duplicate these definitions.

---

## 2. Existing pattern sources

These are **design references**.  Prefer translating the generic combinatorics into
Goldbach-native declarations rather than creating a hard dependency from Goldbach
to the Legendre facade.

### 2.1 Legendre exact overlap excess

File:

\`\`\`text
DkMath/NumberTheory/Legendre/Wave.lean
\`\`\`

Reference declarations:

\`\`\`lean
squareCoverOverlapExcess
squareCoverIncidenceCount_eq_two_mul_add_overlapExcess_of_fullyCovered
\`\`\`

The idea is:

$$
\sum_{\text{seat}} |\operatorname{support}(\text{seat})|
=
|\operatorname{covered\ seats}|
+
\sum_{\text{seat}}
\left(|\operatorname{support}(\text{seat})|-1\right),
$$

where natural subtraction makes the excess zero for an uncovered seat.

Unlike the Legendre full-cover theorem, the Goldbach version should be proved
**without assuming full cover**, because \`goldbachCoveredSeats\` already explicitly
tracks which seats are covered.

### 2.2 Legendre pair-overlap ledger

File:

\`\`\`text
DkMath/NumberTheory/Legendre/PairOverlap.lean
\`\`\`

Reference declarations:

\`\`\`lean
squareOffsetPrimePairMultiplicity
squarePrimePairs
squarePrimePairOverlapCount
squarePrimePairOverlapCount_eq_sum_local_pairMultiplicity
squareCoverOverlapExcess_le_squarePrimePairOverlapCount
\`\`\`

Translate this pattern to proper Goldbach obstructions.

### 2.3 Legendre exact incidence conservation

File:

\`\`\`text
DkMath/NumberTheory/Legendre/ParitySafeIncidenceBalance.lean
\`\`\`

Reference:

\`\`\`lean
paritySafeIncidenceConservation
\`\`\`

Conceptual form:

$$
H+B+U=C+X.
$$

Do not import its Legendre-specific candidate/wave types.  Use it only as a structural
model for the Goldbach conservation identity.

### 2.4 Later sources — reconnaissance only in this checkpoint

Do not implement these yet unless needed for a trivial helper.

\`\`\`text
DkMath/NumberTheory/Primitive/PrimeWorldRefinement.lean
  exists_unique_reserved_child_and_other_children_survive

DkMath/NumberTheory/Primitive/PeriodicPrimeWorld.lean
  supportDisjointFrom_centered_mirror_iff
\`\`\`

These are candidates for the checkpoint after pair-overlap, when product-wave /
short-fiber localization is studied.

---

## 3. New module A — Goldbach overlap ledger

Preferred file:

\`\`\`text
DkMath/NumberTheory/Goldbach/Overlap.lean
\`\`\`

Preferred imports:

\`\`\`lean
import DkMath.NumberTheory.Goldbach.Capacity
import Mathlib.Tactic
\`\`\`

Use the existing namespace:

\`\`\`lean
namespace DkMath.NumberTheory
\`\`\`

### 3.1 Obstruction support of one offset

Add an executable finite support:

\`\`\`lean
def goldbachObstructionSupport (n u : ℕ) : Finset ℕ :=
  (goldbachSmallPrimes n).filter
    (fun r => GoldbachProperObstructed n r u)
\`\`\`

Prove the membership theorem:

\`\`\`lean
@[simp] theorem mem_goldbachObstructionSupport {n u r : ℕ} :
    r ∈ goldbachObstructionSupport n u ↔
      r ∈ goldbachSmallPrimes n ∧ GoldbachProperObstructed n r u
\`\`\`

### 3.2 Local and global overlap excess

Preferred definitions:

\`\`\`lean
def goldbachLocalOverlapExcess (n u : ℕ) : ℕ :=
  (goldbachObstructionSupport n u).card - 1

def goldbachOverlapExcess (n : ℕ) : ℕ :=
  ∑ u ∈ goldbachOffsets n, goldbachLocalOverlapExcess n u
\`\`\`

If \`noncomputable\` is necessary because of implementation choices, justify it.
Prefer computable definitions if possible.

### 3.3 Support/cardinality bridge

Prove that a seat is covered exactly when its obstruction support is nonempty.

Suggested theorem:

\`\`\`lean
theorem goldbach_mem_covered_iff_support_nonempty {n u : ℕ} :
    u ∈ goldbachCoveredSeats n (goldbachSmallPrimes n) ↔
      u ∈ goldbachOffsets n ∧
        (goldbachObstructionSupport n u).Nonempty
\`\`\`

or an equivalent theorem with \`0 < card\`.

Also prove a direct incidence-as-support-sum theorem:

\`\`\`lean
theorem goldbachIncidence_eq_sum_support_cards (n : ℕ) :
    goldbachIncidence n (goldbachSmallPrimes n) =
      ∑ u ∈ goldbachOffsets n, (goldbachObstructionSupport n u).card
\`\`\`

Use finite double counting.  Do not use an unproved cardinality heuristic.

### 3.4 Main exact overlap identity

Target:

\`\`\`lean
theorem goldbachIncidence_eq_covered_add_overlapExcess (n : ℕ) :
    goldbachIncidence n (goldbachSmallPrimes n) =
      (goldbachCoveredSeats n (goldbachSmallPrimes n)).card +
        goldbachOverlapExcess n
\`\`\`

This should hold for every \`n\`, with no Goldbach/full-cover hypothesis.

Reason seatwise:
for \`k = support.card\`,

\`\`\`text
k = (if 0 < k then 1 else 0) + (k - 1).
\`\`\`

The finite sum of the indicator is the covered-seat cardinality.

### 3.5 Exact Goldbach incidence conservation

Combine the new theorem with existing:

\`\`\`lean
goldbach_survivors_add_covered
\`\`\`

to prove:

\`\`\`lean
theorem goldbachIncidenceConservation (n : ℕ) :
    (goldbachSurvivors n (goldbachSmallPrimes n)).card +
        goldbachIncidence n (goldbachSmallPrimes n) =
      (n - 1) + goldbachOverlapExcess n
\`\`\`

This is the preferred user-facing conservation theorem.

### 3.6 Reformulated fixed-center criterion

Derive:

\`\`\`lean
theorem goldbachPairAt_iff_incidence_lt_offsets_add_overlap (n : ℕ) :
    GoldbachPairAt n ↔
      goldbachIncidence n (goldbachSmallPrimes n) <
        (n - 1) + goldbachOverlapExcess n
\`\`\`

This is logically equivalent to the existing fixed-center statement, so the docstring
must explicitly say that it does **not** prove Goldbach.  Its value is structural:
the missing seat is exposed as the excess of overlap payment over incidence demand.

### 3.7 Regression at center six

The existing theorem gives:

\`\`\`text
covered = 4
incidence = 5
survivors = 1
\`\`\`

Add kernel regressions:

\`\`\`lean
theorem goldbach_six_overlap_excess :
    goldbachOverlapExcess 6 = 1 := by
  decide +kernel

theorem goldbach_six_incidence_conservation :
    (goldbachSurvivors 6 (goldbachSmallPrimes 6)).card +
        goldbachIncidence 6 (goldbachSmallPrimes 6) =
      (6 - 1) + goldbachOverlapExcess 6 := by
  -- preferably use the generic conservation theorem, not decide
\`\`\`

The point of this regression is to turn the Astra counterexample to strict incidence
into the smallest positive example of overlap conservation.

---

## 4. New module B — Goldbach pair-overlap ledger

Preferred file:

\`\`\`text
DkMath/NumberTheory/Goldbach/PairOverlap.lean
\`\`\`

Import:

\`\`\`lean
import DkMath.NumberTheory.Goldbach.Overlap
import Mathlib.Tactic
\`\`\`

### 4.1 Local unordered pair multiplicity

\`\`\`lean
def goldbachOffsetPrimePairMultiplicity (n u : ℕ) : ℕ :=
  Nat.choose (goldbachObstructionSupport n u).card 2
\`\`\`

Prove the local combinatorial inequality:

\`\`\`lean
theorem goldbach_support_sub_one_le_pairMultiplicity {n u : ℕ} :
    (goldbachObstructionSupport n u).card - 1 ≤
      goldbachOffsetPrimePairMultiplicity n u
\`\`\`

The proof may mirror the short arithmetic proof in Legendre \`PairOverlap.lean\`.
Do not import the Legendre theorem only to instantiate it.

### 4.2 Canonical unordered small-prime pairs

\`\`\`lean
def goldbachPrimePairs (n : ℕ) : Finset (ℕ × ℕ) := by
  classical
  exact ((goldbachSmallPrimes n).product (goldbachSmallPrimes n)).filter
    (fun pair => pair.1 < pair.2)
\`\`\`

Add the exact membership theorem.

### 4.3 Pair-overlap offsets

\`\`\`lean
def goldbachPrimePairOverlapOffsets (n p q : ℕ) : Finset ℕ :=
  (goldbachOffsets n).filter
    (fun u =>
      GoldbachProperObstructed n p u ∧
      GoldbachProperObstructed n q u)
\`\`\`

### 4.4 Global pair-overlap count

\`\`\`lean
def goldbachPrimePairOverlapCount (n : ℕ) : ℕ :=
  ∑ pair ∈ goldbachPrimePairs n,
    (goldbachPrimePairOverlapOffsets n pair.1 pair.2).card
\`\`\`

Prove the exact double-count theorem:

\`\`\`lean
theorem goldbachPrimePairOverlapCount_eq_sum_local_pairMultiplicity (n : ℕ) :
    goldbachPrimePairOverlapCount n =
      ∑ u ∈ goldbachOffsets n,
        goldbachOffsetPrimePairMultiplicity n u
\`\`\`

### 4.5 Pair ledger dominates overlap excess

Target:

\`\`\`lean
theorem goldbachOverlapExcess_le_primePairOverlapCount (n : ℕ) :
    goldbachOverlapExcess n ≤ goldbachPrimePairOverlapCount n
\`\`\`

This is the checkpoint endpoint.

Do **not** claim that this inequality alone yields a Goldbach pair.

---

## 5. Explicit stop boundary

After proving

\`\`\`lean
goldbachOverlapExcess_le_primePairOverlapCount
\`\`\`

stop and write \`report-006.md\`.

Do not yet implement:

- a universal upper/lower bound forcing \`GoldbachCapacityEscape\`;
- a claim that pair overlap alone closes Goldbach;
- a product-modulus occupancy theorem with endpoint exceptions unless it falls out
  as a very small helper;
- a mirror theorem centered at arbitrary \`n\`;
- a new axiom/provider;
- a theorem equivalent to \`StrongGoldbach\` disguised as a new assumption.

The next design review will decide whether to move to:

\`\`\`text
pair overlap
  -> sign-pattern / CRT product waves
  -> near/far product modulus split
  -> PrimeWorld refinement / mirror
  -> short-fiber localization
\`\`\`

or whether a different conservation invariant is required.

---

## 6. Dependency hygiene

Preferred dependency direction:

\`\`\`text
Goldbach.Capacity
      ↓
Goldbach.Overlap
      ↓
Goldbach.PairOverlap
\`\`\`

Then update:

\`\`\`text
DkMath/NumberTheory/Goldbach.lean
\`\`\`

to import the two new modules.

Do not make \`Goldbach\` import the full \`DkMath.NumberTheory.Legendre\` facade.
If a truly generic finite combinatorial lemma should be shared, either:

1. prove a small Goldbach-local copy for this checkpoint, or
2. extract only that lemma into an obviously generic lower-level module,
   but only if the extraction is small and does not perturb existing public theorems.

Avoid broad refactoring.

---

## 7. Tests and audit

Update:

\`\`\`text
DkMathTest/NumberTheory/GoldbachGNFiber.lean
docs/dev/NumberTheory-Goldbach-GNFiber-260910-v0/AxiomAudit.lean
docs/dev/NumberTheory-Goldbach-GNFiber-260910-v0/declaration-index.md
docs/dev/NumberTheory-Goldbach-GNFiber-260910-v0/README.md
\`\`\`

Add focused kernel regressions at least for:

\`\`\`text
n = 2
n = 6
n = 10
\`\`\`

For \`n = 6\`, verify overlap excess exactly \`1\`.

Required builds from \`lean/dk_math\`:

\`\`\`bash
./lean-build.sh DkMath.NumberTheory.Goldbach.Overlap
./lean-build.sh DkMath.NumberTheory.Goldbach.PairOverlap
./lean-build.sh DkMath.NumberTheory.Goldbach
./lean-build.sh DkMathTest.NumberTheory.GoldbachGNFiber
lake env lean docs/dev/NumberTheory-Goldbach-GNFiber-260910-v0/AxiomAudit.lean
\`\`\`

If the root build is affordable, also run:

\`\`\`bash
./lean-build.sh DkMath
\`\`\`

Report existing root \`sorry\` warnings separately from new declarations.

---

## 8. Report requirements

Create:

\`\`\`text
docs/dev/NumberTheory-Goldbach-GNFiber-260910-v0/report-006.md
\`\`\`

Include:

1. files changed;
2. exact new definitions/theorems;
3. whether the incidence/covered/overlap identity is unconditional;
4. center-six regression;
5. pair-overlap exact double count;
6. whether any Legendre module had to be imported directly;
7. build results;
8. axiom audit result;
9. explicit statement that Goldbach remains unproved;
10. recommendation for the next checkpoint.

If any proposed theorem is false, do not weaken it silently.
Record the counterexample in \`Limitations.lean\` or the report and stop at the
strongest exact theorem that Lean accepts.
