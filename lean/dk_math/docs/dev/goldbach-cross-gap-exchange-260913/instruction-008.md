# CGE-008: Exact Signed CRT ↔ Pascal Overlap Identification

## 0. Scope contract

This stage is **finite, balanced-window local, and anchor-local only**.

CGE-007 built the general signed CRT residue families and executable pair/triple progression sums, but intentionally left the comparison with the Pascal overlap counts as explicit hypotheses.  CGE-008 must close exactly that boundary under the endpoint-separation hypotheses already used by the balanced SquareBody pipeline.

Do **not** add or assume:

- Strong Goldbach,
- a universal survivor theorem,
- a universal strict budget,
- analytic density / RH / CFBRC input,
- AKS as a primality converse,
- coprimality as a primality substitute,
- a theorem claiming that the final budget holds for every center,
- a hidden comparison axiom between signed CRT sums and Pascal overlap.

The intended result is an exact finite counting identification, not an existence theorem.

---

## 1. Existing production API to reuse

Use the existing files and theorem names; do not duplicate their definitions.

### CGE-003 / CGE-004

- `goldbachBalancedOffsets`
- `goldbachObstructionSupportIn`
- `goldbachWindowPairOverlapCount`
- `goldbachWindowTripleOverlapCount`
- `goldbachWindowIncidence`
- `goldbachWindow_incidence_le_residue_capacity`
- `goldbachWindowSurvivor_of_incidence_le_of_pairMinusTriple_budget`
- `goldbachPairAt_of_goldbachWindowSurvivor`

### CGE-005

- `goldbachWindowPairOverlap_sub_triple_le_overlap`
- the pair-minus-triple survivor provider

### CGE-006

- `goldbachPrimeTriples`

### CGE-007

- `signedPairResidues`
- `signedTripleResidues`
- `goldbachProgressionSeats`
- `goldbachProgressionWindowCount`
- `goldbachSignedPairCRTCount`
- `goldbachSignedTripleCRTCount`
- `goldbachStrictPrimePairs`
- `goldbachSignedPairCRTSum`
- `goldbachSignedTripleCRTSum`
- `goldbach_signed_pair_count_eq_progression_sum`
- `goldbach_signed_triple_count_eq_progression_sum`
- `goldbach_signed_pair_raw_iff_support`
- `goldbachWindowSurvivor_of_signed_crt_budget`

The CGE-007 report explicitly records the current boundary:

```text
the general theorem identifying the signed world sums with the Pascal overlap
counts was not asserted.
```

CGE-008 exists to remove that comparison-hypothesis boundary, under explicit anchor-local hypotheses.

---

## 2. Mathematical target

Let `S` be a finite known-prime world.  Assume a finite upper anchor `P` such that every `r ∈ S` satisfies `r ≤ P`, and assume

```text
P < n - w.
```

For every balanced seat `t`, these hypotheses force both reflection endpoints above every world prime.  Therefore the proper-divisor endpoint exception disappears, and CGE-007 already gives the exact pointwise bridge

```text
raw forbidden residue at r
  ↔
r ∈ goldbachObstructionSupportIn n t S.
```

For a strict pair `p < q`, the seats at which both primes are in the obstruction support must therefore be exactly the balanced seats belonging to one of the canonical signed CRT residue progressions modulo `p*q`.

Likewise for a strict triple `p < q < r`, the seats at which all three primes lie in the support must be exactly the balanced seats belonging to one of the canonical signed CRT residue progressions modulo `p*q*r`.

The main target is therefore

```text
goldbachSignedPairCRTSum n w S
  = goldbachWindowPairOverlapCount n w S

goldbachSignedTripleCRTSum n w S
  = goldbachWindowTripleOverlapCount n w S
```

under the explicit finite-world prime/bound/anchor hypotheses.

No center-aligned assumption is allowed in the general theorem.

---

## 3. Recommended implementation file

Suggested owner:

```text
DkMath/NumberTheory/Goldbach/BalancedSignedCRTExact.lean
```

Export it from:

```text
DkMath/NumberTheory/Goldbach.lean
```

Candidate theorem names below are **new candidate names**, not existing repository declarations.  Rename if a clearer repository-consistent name is found.

---

## 4. CGE-008-A: one residue progression is exactly one congruence class in the window

First isolate the generic arithmetic fact used by both pair and triple layers.

For `0 < M` and `t₀ < M`, prove that membership in

```text
goldbachProgressionSeats (min (n - 1) w) t₀ M
```

is equivalent to

```text
t ∈ goldbachBalancedOffsets n w ∧ t % M = t₀
```

or an equivalent formulation strong enough to use in both directions.

Candidate theorem shape:

```lean
theorem mem_goldbachProgressionSeats_iff_balanced_modEq
    {n w t₀ M t : ℕ}
    (hM : 0 < M) (ht₀ : t₀ < M) :
    t ∈ goldbachProgressionSeats (min (n - 1) w) t₀ M ↔
      t ∈ goldbachBalancedOffsets n w ∧ t % M = t₀ := ...
```

If the exact shape needs a harmless `t ≤ min (n-2) w` or range formulation because of `goldbachOffsets = range (n-1)`, keep the theorem exact and document the normalization.

Do not weaken this to one direction if both directions are readily provable.

---

## 5. CGE-008-B: exact pair-seat characterization

For `p < q`, `p,q ∈ S`, `KnownPrimeScales S`, all world primes `≤ P`, and `P < n-w`, define or prove an exact finite set equality between:

1. balanced seats whose support contains both `p` and `q`;
2. the union of `goldbachProgressionSeats` over `signedPairResidues n p q`.

A helper set is acceptable, for example a candidate

```lean
def goldbachWindowPairSupportSeats
    (n w : ℕ) (S : Finset ℕ) (p q : ℕ) : Finset ℕ :=
  (goldbachBalancedOffsets n w).filter (fun t =>
    p ∈ goldbachObstructionSupportIn n t S ∧
    q ∈ goldbachObstructionSupportIn n t S)
```

Then prove an exact equality / exact cardinality theorem.

The key directions must be explicit:

- **support → signed residue:** use `goldbach_signed_pair_raw_iff_support` coordinatewise, then `t % (p*q)` is a member of `signedPairResidues n p q`;
- **signed residue progression → support:** reduce the progression seat modulo `p` and `q`, recover forbidden membership, then use the same raw/support iff theorem.

Because the residues in `signedPairResidues` are canonical representatives below `p*q`, distinct residue progressions inside the same modulus must be disjoint.  Prove the needed uniqueness rather than silently summing overlapping sets.

Expected count theorem, candidate name:

```lean
theorem goldbachSignedPairCRTCount_eq_pairSupportSeats_card ... :
  goldbachSignedPairCRTCount n w p q =
    (goldbachWindowPairSupportSeats n w S p q).card := ...
```

---

## 6. CGE-008-C: exact triple-seat characterization

Repeat the same construction for strict triples `p < q < r`.

Candidate helper:

```lean
def goldbachWindowTripleSupportSeats
    (n w : ℕ) (S : Finset ℕ) (p q r : ℕ) : Finset ℕ :=
  (goldbachBalancedOffsets n w).filter (fun t =>
    p ∈ goldbachObstructionSupportIn n t S ∧
    q ∈ goldbachObstructionSupportIn n t S ∧
    r ∈ goldbachObstructionSupportIn n t S)
```

Prove that its cardinality is exactly

```text
goldbachSignedTripleCRTCount n w p q r.
```

This theorem is fully signed and must **not** assume `GoldbachCenterAlignedWorld`.

The existing center-aligned singleton theorem remains a regression / specialization, not a dependency of the general proof.

---

## 7. CGE-008-D: exact global pair sum = Pascal pair overlap

For a finite known-prime world `S`, prove the double-count identity

```text
goldbachSignedPairCRTSum n w S
  = goldbachWindowPairOverlapCount n w S.
```

The clean combinatorial interpretation is:

- summing over strict unordered prime pairs counts, for every seat `t`, the number of `2`-element subsets of its obstruction support;
- that local number is exactly `Nat.choose support.card 2`.

You may prove this by one of:

- a `Finset.sum_comm` double count;
- a sigma/powerset bijection;
- a local strict-pair cardinality lemma followed by summation.

Do not import a theorem whose domain is the old full Goldbach fiber unless the balanced-window restriction is proved explicitly.

Candidate theorem name:

```lean
theorem goldbachSignedPairCRTSum_eq_windowPairOverlapCount
    {n w P : ℕ} {S : Finset ℕ}
    (hS : KnownPrimeScales S)
    (hbound : ∀ ⦃r : ℕ⦄, r ∈ S → r ≤ P)
    (hanchor : P < n - w) :
    goldbachSignedPairCRTSum n w S =
      goldbachWindowPairOverlapCount n w S := ...
```

If `w ≤ n` is needed by a helper theorem, add it explicitly.  Do not hide it.

---

## 8. CGE-008-E: exact global triple sum = Pascal triple overlap

Likewise prove

```text
goldbachSignedTripleCRTSum n w S
  = goldbachWindowTripleOverlapCount n w S.
```

under the same finite known-prime / world-bound / anchor conditions.

Candidate theorem name:

```lean
theorem goldbachSignedTripleCRTSum_eq_windowTripleOverlapCount ...
```

Again, this must be the general signed theorem, not only the center-aligned case.

---

## 9. CGE-008-F: remove the comparison hypotheses from the signed provider

CGE-007 currently has the conditional bridge

```text
goldbachWindowSurvivor_of_signed_crt_budget
```

with explicit hypotheses of the form

```text
SignedPairSum ≤ PairOverlap
TripleOverlap ≤ SignedTripleSum.
```

Under the CGE-008 anchor-local hypotheses, derive a new provider theorem in which these comparison hypotheses disappear because they are production equalities.

Candidate shape:

```lean
theorem goldbachWindowSurvivor_of_exact_signed_crt_budget
    {n w P : ℕ} {S : Finset ℕ} {C : ℕ}
    (hS : KnownPrimeScales S)
    (hbound : ∀ ⦃r : ℕ⦄, r ∈ S → r ≤ P)
    (hanchor : P < n - w)
    (hincidence : goldbachWindowIncidence n w S ≤ C)
    (hbudget : C <
      (goldbachBalancedOffsets n w).card +
        (goldbachSignedPairCRTSum n w S -
          goldbachSignedTripleCRTSum n w S)) :
    (goldbachWindowSurvivors n w S).Nonempty := ...
```

Then add a residue-capacity corollary replacing `C` by the existing width-local capacity sum.

Finally, for `S = primeScalesUpTo P`, add the anchor-local conditional `GoldbachPairAt n` bridge by reusing CGE-003/CGE-005.  Keep all SquareBody hypotheses explicit:

```text
w ≤ n
P < n-w
n+w ≤ squareBody P
```

This remains conditional on the finite strict signed-CRT budget.  Do not assert that the budget always holds.

---

## 10. Audits / regressions

Extend the existing balanced reflection audit rather than creating a disconnected toy file unless there is a build-time reason.

### A. target-30 exact replay

For

```text
n = 15
w = 8
S = {2,3,5}
P = 5
```

kernel-check:

```text
SignedPairCRTSum   = 3
PairOverlap        = 3
SignedTripleCRTSum = 0
TripleOverlap      = 0
```

and replay the exact-provider budget

```text
10 < 9 + (3 - 0).
```

The new provider theorem must close the same conditional `GoldbachPairAt 15` replay **without supplying pair/triple comparison hypotheses manually**.

### B. mixed-sign `n=50` exact replay

For

```text
n = 50
w = 10
S = {2,3,5,7}
P = 7
```

kernel-check the already observed values:

```text
SignedPairCRTSum   = 12
PairOverlap        = 12
SignedTripleCRTSum = 2
TripleOverlap      = 2
```

This is the key non-center-aligned regression proving that the exact theorem is genuinely signed.

Retain the firewall:

```text
Capacity = 21
Window = 11
Pair-Triple = 10
21 < 11 + 10   -- false, equality at the boundary
```

Do **not** derive a survivor or Goldbach result from this case.

### C. endpoint-exception firewall

Include at least one small example showing why the anchor hypothesis is necessary.  Outside `P < n-w`, raw forbidden membership may correspond to an endpoint equal to the obstructing prime and therefore fail to be a proper obstruction.

The audit should demonstrate that the exact signed/support identification is not advertised without endpoint separation.

---

## 11. What not to optimize in this stage

Do not spend this checkpoint trying to fix the `n=50` failed budget by:

- choosing a different `w`,
- changing the residue capacity formula,
- adding fourth/higher Pascal layers,
- using analytic prime estimates,
- adding a search over `P`,
- special-casing centers.

First remove the CGE-007 comparison hypotheses cleanly.  Budget sharpening is the next mathematical question only after the signed CRT counts are known to be the actual Pascal pair/triple counts.

---

## 12. Verification

Required:

```text
lake build DkMath.NumberTheory.Goldbach DkMathTest.NumberTheory.GoldbachBalancedReflectionAudit
lake build DkMath
git diff --check
```

Audit new production declarations with `#print axioms` as appropriate.

No new `sorry`, `admit`, `native_decide`, `unsafe`, or `axiom` declaration.

---

## 13. Report and outcome labels

Write:

```text
lean/dk_math/docs/dev/goldbach-cross-gap-exchange-260913/report-008.md
```

Use one of:

### Outcome A — EXACT SIGNED CRT / PASCAL IDENTIFICATION

Both general pair and triple signed sums are proved equal to their balanced-window Pascal overlap counts under explicit anchor-local hypotheses, and the provider no longer needs comparison assumptions.

### Outcome B — PARTIAL EXACT IDENTIFICATION

One side is exact but the other still needs an explicit comparison hypothesis.  State precisely which direction remains open and why.

### Outcome C — STRUCTURAL BLOCKER

The signed progression sum and Pascal overlap count are not equal even under the intended endpoint-separation hypotheses.  Supply a concrete kernel-checked counterexample and identify the missing multiplicity / boundary term.  Do not patch the mismatch by adding an assumption that restates the desired equality.

---

## 14. Success criterion

CGE-008 succeeds when the general finite signed CRT geometry is no longer merely an executable proxy for pair/triple overlap, but is proved to be the **same balanced-window counting object** under the existing anchor-local proper-obstruction firewall.

The intended pipeline after Outcome A is:

```text
signed CRT arithmetic
  = exact pair/triple Pascal overlap
  → pair-minus-triple overlap payment
  → window survivor criterion
  → SquareBody prime certification
  → conditional GoldbachPairAt
```

The remaining unsolved problem would then be only the strict finite budget itself, not a mismatch between CRT geometry and the overlap ledger.
