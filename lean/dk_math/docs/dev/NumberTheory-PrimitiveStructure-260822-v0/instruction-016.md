# Codex Instruction — PRIM-L009 Pair-Overlap Budget / Second-Order Cover Constraint

Branch: `wip/number-theory-primitive-structure-260822-v0`

Project: DkMath NumberTheory Primitive Structure

## Current verified state

PRIM-L008 is complete.

The Legendre application layer now contains all of the following exact finite statements.

For every positive modulus `m`:

```text
(squareWaveOffsets n m).card
  = (n^2 + 2*n) / m - n^2 / m
  = (2*n) / m + squareWaveCarry n m
```

with:

```text
0 ≤ squareWaveCarry n m ≤ 1
```

and the carry is exactly the remainder-crossing event

```text
m ≤ (n^2 % m) + ((2*n) % m).
```

For every old prime wave:

```text
squareCoverIncidenceCount n
  = squareCoverBaselineIncidence n
      + squareAnchorCarryCount n
```

where the baseline is the sum of complete local periods and the carry count is the total square-anchor boundary correction.

Under full cover:

```text
squareCoverBaselineIncidence n + squareAnchorCarryCount n
  = 2*n + squareCoverOverlapExcess n.
```

The pair-overlap API already gives, for distinct primes `p`, `q`:

```text
squarePrimePairOverlapOffsets n p q
  = squareWaveOffsets n (p*q)
```

and therefore exact quotient occupancy and the local sparsity theorem

```text
2*n < p*q
  -> (squarePrimePairOverlapOffsets n p q).card ≤ 1.
```

The remaining question in this checkpoint is how the overlap-excess term is controlled by the finite collection of prime-pair intersections.

---

# Goal

Construct a second-order finite overlap ledger.

The key combinatorial fact is local:

```text
if one offset has k distinct old-prime supports,
then its overlap excess is k - 1,
while it determines C(k,2) unordered distinct prime pairs.
```

Hence:

```text
k - 1 ≤ C(k,2)
```

for every `k`, with the natural-number truncated subtraction convention also valid at `k = 0`.

After summing over the square window, obtain:

```text
squareCoverOverlapExcess n ≤ squarePrimePairOverlapCount n.
```

Then combine this with the PRIM-L008 full-cover budget to derive the second-order necessary condition

```text
squareCoverBaselineIncidence n + squareAnchorCarryCount n
  ≤ 2*n + squarePrimePairOverlapCount n
```

under `SquareOffsetsFullyCovered n`.

Finally rewrite the pair-overlap ledger through the already-proved product-wave occupancy formulas.

This checkpoint must remain a necessary-condition / audit layer. Do **not** try to prove the resulting inequality impossible.

---

# Preferred location

Continue in:

```text
DkMath/NumberTheory/Legendre.lean
```

for this checkpoint so the existing local definitions remain directly available.

The file is becoming large, but do not perform a declaration move/refactor in the same checkpoint. A later cleanup may split the application analysis into sibling modules after the theorem surface stabilizes.

---

# Required reconnaissance

Before coding, inspect the current Lean 4.32 / Mathlib APIs around:

```text
Nat.choose
Nat.choose_two_right
Nat.choose_two_left
Finset.product
Finset.filter
Finset.card_product
Finset.sum_comm
Finset.sum_filter
Finset.card_filter
Finset.offDiag
Finset.powersetCard
```

The exact names above are search hints only.

Search specifically for an existing theorem expressing the number of unordered two-element subsets / pairs of a finite set as `Nat.choose s.card 2`.

Prefer current Mathlib combinatorics over a custom pair-count framework.

If the unordered-pair API is unexpectedly expensive, an ordered-distinct-pair fallback is acceptable only if reported explicitly and if the resulting theorem still gives a valid second-order upper bound. Prefer the unordered `p < q` formulation.

---

# Required implementation surface

Names below are preferred, not mandatory. Report final declaration names.

## 1. Canonical unordered old-prime pairs

Define one copy of each distinct pair of old prime directions.

Preferred representation:

```lean
noncomputable def squarePrimePairs (n : ℕ) : Finset (ℕ × ℕ) := by
  classical
  exact ((primeScalesUpTo n).product (primeScalesUpTo n)).filter
    (fun pair => pair.1 < pair.2)
```

Expose membership:

```lean
@[simp] theorem mem_squarePrimePairs
    {n p q : ℕ} :
    (p,q) ∈ squarePrimePairs n ↔
      Nat.Prime p ∧ p ≤ n ∧
      Nat.Prime q ∧ q ≤ n ∧
      p < q
```

Equivalent association of conjunctions is acceptable.

The ordering is only canonicalization; mathematically the pair is unordered.

## 2. Global pair-overlap count

Define:

```lean
noncomputable def squarePrimePairOverlapCount (n : ℕ) : ℕ :=
  ∑ pair ∈ squarePrimePairs n,
    (squarePrimePairOverlapOffsets n pair.1 pair.2).card
```

This counts `(offset, unordered prime pair)` incidences.

It is not the number of offsets having overlap; one offset supported by three primes contributes three prime pairs.

## 3. Local unordered support-pair count

Expose the local number of unordered pairs inside one support set.

Preferred lightweight form:

```lean
def squareOffsetPrimePairMultiplicity (n r : ℕ) : ℕ :=
  Nat.choose (squareOffsetPrimeSupport n r).card 2
```

If a Finset of local pairs is materially easier for double counting, define it as well / instead:

```text
pairs (p,q) from squareOffsetPrimeSupport n r with p < q
```

but avoid creating duplicate public representations unless useful.

Prove the elementary local inequality:

```lean
theorem primeSupport_sub_one_le_pairMultiplicity
    {n r : ℕ} :
    (squareOffsetPrimeSupport n r).card - 1 ≤
      squareOffsetPrimePairMultiplicity n r
```

A generic Nat lemma

```text
k - 1 ≤ Nat.choose k 2
```

may be introduced privately or in the narrowest appropriate scope if Mathlib does not already provide it.

Do not make this about valuations or prime powers.

## 4. Exact pair-overlap double count

Prove that the global pair ledger equals the sum of local pair multiplicities:

```lean
theorem squarePrimePairOverlapCount_eq_sum_local_pairMultiplicity
    (n : ℕ) :
    squarePrimePairOverlapCount n =
      ∑ r ∈ squareOffsets n,
        squareOffsetPrimePairMultiplicity n r
```

Equivalent orientation is acceptable.

The intended proof is a finite transpose of the indicator relation:

```text
(p,q) is an old-prime pair
and r is in the p/q overlap
```

iff

```text
r is a square offset
and p,q are two distinct members of squareOffsetPrimeSupport n r.
```

Do not use inclusion-exclusion as a black box. This is only a double-counting identity.

If the exact `Nat.choose` rewriting becomes the only obstruction, it is acceptable to first prove equality with a local `Finset (ℕ × ℕ)` pair set and derive the `Nat.choose` statement separately.

## 5. Overlap excess is bounded by pair overlap

Using the local inequality and the exact double count, prove:

```lean
theorem squareCoverOverlapExcess_le_squarePrimePairOverlapCount
    (n : ℕ) :
    squareCoverOverlapExcess n ≤ squarePrimePairOverlapCount n
```

This theorem does **not** require full cover because the truncated local excess

```text
support.card - 1
```

is zero for support cardinality `0` and `1`.

Keep this theorem global if the proof allows it.

## 6. Full-cover second-order budget inequality

Combine PRIM-L008 with the previous bound:

```lean
theorem baseline_add_carry_le_two_mul_add_pairOverlapCount_of_fullyCovered
    {n : ℕ}
    (hfull : SquareOffsetsFullyCovered n) :
    squareCoverBaselineIncidence n + squareAnchorCarryCount n ≤
      2 * n + squarePrimePairOverlapCount n
```

This is the main semantic theorem of PRIM-L009.

It says that any hypothetical complete cover must possess enough pairwise repeated coverage to pay for the incidence surplus beyond one hit per offset.

It is a necessary condition, not a contradiction.

## 7. Exact pair-overlap arithmetic form

Using existing declarations only:

```text
squarePrimePairOverlapOffsets_eq_squareWaveOffsets_product
card_squarePrimePairOverlapOffsets_eq_div_sub_div
card_squareWaveOffsets_eq_div_add_carry
```

rewrite the pair ledger as either of the following exact forms.

Preferred baseline+carry form:

```lean
theorem squarePrimePairOverlapCount_eq_sum_product_div_add_carry
    (n : ℕ) :
    squarePrimePairOverlapCount n =
      ∑ pair ∈ squarePrimePairs n,
        ((2 * n) / (pair.1 * pair.2)
          + squareWaveCarry n (pair.1 * pair.2))
```

Also acceptable is the endpoint quotient-difference form:

```text
Σ_{p<q≤n} [((n²+2n)/(pq)) - (n²/(pq))].
```

If both are thin, expose both; do not duplicate long proofs.

## 8. Full-cover arithmetic second-order necessary condition

If the previous rewrite is available cleanly, expose the direct arithmetic frontier:

```text
SquareOffsetsFullyCovered n
->
Baseline(n) + Carry(n)
≤ 2*n + Σ_{p<q≤n} (floor(2*n/(p*q)) + carry(n,p*q)).
```

A theorem using the named `squarePrimePairOverlapCount` on the right is already sufficient for acceptance; the fully expanded sum is strongly preferred if it is a short rewrite.

## 9. Near/far product split — strongly encouraged

The existing PRIM-L006 theorem already says:

```text
2*n < p*q -> pair overlap cardinality ≤ 1.
```

Define a partition of canonical prime pairs by product size, preferably:

```lean
squarePrimeNearPairs n :=
  (squarePrimePairs n).filter (fun pair => pair.1 * pair.2 ≤ 2*n)

squarePrimeFarPairs n :=
  (squarePrimePairs n).filter (fun pair => 2*n < pair.1 * pair.2)
```

Prove the obvious partition / sum split if it remains compact.

Then prove the far-pair contribution bound:

```text
Σ pair in squarePrimeFarPairs n,
  card(pair overlap)
≤ (squarePrimeFarPairs n).card.
```

This is the finite local meaning of product-wave sparsity:

```text
near pair: product period fits in the window, possibly repeated overlap
far pair: product period exceeds the window, at most one overlap seat
```

Do not estimate the number of near/far pairs analytically in this checkpoint.

The near/far split is strongly encouraged but may be deferred if the core unordered-pair double count is already a substantial Lean task.

---

# Interpretation to preserve in docstrings

State clearly:

- `squarePrimePairOverlapCount` counts unordered distinct prime-pair incidences, not distinct offsets;
- an offset with support size `k` contributes `Nat.choose k 2` pair incidences;
- local overlap excess `k - 1` is therefore bounded by its pair multiplicity;
- under full cover, pair overlap must pay for every incidence beyond the mandatory one-per-offset budget;
- each prime pair is already known to be a single product-modulus square wave;
- pair overlap arithmetic therefore reduces to exact local occupancy for modulus `p*q`;
- this is second-order finite cover bookkeeping, not full inclusion-exclusion;
- support multiplicity remains squarefree prime-direction multiplicity, distinct from p-adic depth.

---

# Non-goals

Do **not** add in PRIM-L009:

- a proof of `SquareAnchoredSupportEscape`;
- a proof of Legendre's conjecture;
- an assertion that the second-order inequality is impossible;
- full inclusion-exclusion over all prime subsets;
- Möbius inversion;
- Mertens / PNT / prime harmonic asymptotics;
- estimates for the number of prime pairs;
- Jacobsthal-function machinery;
- quadratic reciprocity / quadratic-residue distribution;
- prime-power valuation / Depth theory;
- RH / CFBRC dependencies;
- numerical enumeration as the generic proof method.

Do not replace exact finite pair counts by probabilistic independence heuristics.

---

# Verification

Run:

```sh
lake build DkMath.NumberTheory.Legendre
lake build DkMath.NumberTheory.Primitive
lake build DkMath
git diff --check
```

Audit the touched Lean file for new occurrences of:

```text
sorry
admit
native_decide
axiom
```

Report unrelated pre-existing occurrences separately; do not broaden scope to repair them.

---

# Acceptance criteria

PRIM-L009 is complete when:

1. canonical unordered old-prime pairs are represented finitely;
2. total pair-overlap incidence is defined;
3. one offset with support cardinality `k` is connected to its unordered prime-pair multiplicity;
4. global pair-overlap count is exactly transposed to the sum of local pair multiplicities;
5. `squareCoverOverlapExcess ≤ squarePrimePairOverlapCount` is proved;
6. full cover implies the second-order budget inequality
   `Baseline + Carry ≤ 2*n + PairOverlapCount`;
7. pair-overlap count is rewritten through existing product-wave exact occupancy;
8. no contradiction / escape proof or analytic estimate is smuggled into the checkpoint;
9. requested builds and audits are clean.

Stop after PRIM-L009. Do not begin third-order inclusion-exclusion or an escape proof in this implementation pass.

---

# Review questions after PRIM-L009

After this checkpoint, compare the exact first- and second-order ledgers:

```text
first order:
  Σ_p local p-wave occupancy

second order:
  Σ_{p<q} local (p*q)-wave occupancy
```

Then inspect whether the square-anchor carries for `p`, `q`, and `p*q` exhibit additional compatibility constraints beyond generic covering systems.

In particular review these routes before choosing the next checkpoint:

```text
A. near/far pair split by p*q ≤ 2*n
B. carry compatibility between p, q, and p*q
C. higher squarefree intersections, only if second order reveals a real need
D. anchor-divisor / nondivisor prime partition
E. abandon incidence counting if the second-order ledger is structurally too weak
```

The purpose of PRIM-L009 is to decide whether second-order finite cover structure has genuine leverage before escalating further.
