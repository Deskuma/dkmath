# Codex Instruction — PRIM-L013 Coprime Quotient Lift / Packet Factorization

Branch: `wip/number-theory-primitive-structure-260822-v0`

Project: DkMath NumberTheory Primitive Structure

## Current verified state

PRIM-L012 is complete.

The Legendre application layer now has an exact coprime-packet decomposition of the square-offset window.

For `n > 0`:

```text
squareAnchorCoprimeOffsets n
  = base representatives r
    ∪ shifted representatives n+r
```

with exactly `Nat.totient n` base representatives and therefore `2 * Nat.totient n` coprime seats.

For every base representative `r`, the two nondivisor support sets

```text
squareOffsetAnchorNondivisorSupport n r
squareOffsetAnchorNondivisorSupport n (n+r)
```

are disjoint. Under `SquareOffsetsFullyCovered n`, both are nonempty, so the two seats require distinct old nondivisor prime directions.

The coprime-restricted incidence ledger is also available:

```text
squareAnchorCoprimeNondivisorIncidence n
```

with exact packet decomposition and the full-cover frontier

```text
2 * Nat.totient n
  ≤ squareAnchorCoprimeNondivisorIncidence n.
```

PRIM-L013 should not introduce another counting approximation. Instead, lift each nondivisor support incidence from a divisibility statement to its exact complementary-factor coordinate.

---

# Goal

For an old prime support incidence

```text
q ∣ n^2 + r
```

introduce the complementary quotient

```text
k = (n^2 + r) / q.
```

The important square-window facts are:

```text
q ≤ n
n^2 < n^2 + r
q * k = n^2 + r
```

so every actual square-window support factor has

```text
n < k.
```

For anchor-nondivisor primes, `q ∤ n`, hence `Nat.Coprime n q`. Because

```text
q*k = n^2+r ≡ r (mod n),
```

coprimality with the anchor transfers exactly:

```text
Nat.Coprime n r ↔ Nat.Coprime n k.
```

Thus every nondivisor incidence on a coprime square seat factors that seat as

```text
small old prime q ≤ n
×
large complementary factor k > n,
```

with both factors coprime to the anchor `n`.

For a full-cover packet `(r,n+r)`, PRIM-L012 already supplies distinct primes `p ≠ q`. PRIM-L013 should expose the corresponding large cofactors `a,b` and the exact packet equation

```text
p*a + n = q*b
```

(up to equivalent orientation), since

```text
p*a = n^2+r
q*b = n^2+n+r.
```

This is a structural factorization checkpoint. Do not try to derive a contradiction from the packet equation.

---

# Preferred location

Continue in:

```text
DkMath/NumberTheory/Legendre.lean
```

Do not refactor/move the existing PRIM-L001–L012 declarations in this pass.

---

# Required reconnaissance

Inspect the current Lean / Mathlib API around:

```text
Nat.mul_div_cancel'
Nat.div_mul_cancel
Nat.Coprime
Nat.Coprime.mul_right
Nat.Coprime.mul_left
Nat.coprime_add_self_right
Nat.coprime_add_mul_left
Nat.coprime_add_mul_right
Finset.image
Finset.card_image_iff
Finset.sum_image
```

The exact names are search hints only.

Prefer standard coprimality lemmas. Do not create a new gcd framework.

---

# Required implementation surface

Names are preferred, not mandatory. Report final names.

## 1. Complementary quotient coordinate

Define:

```lean
def squareOffsetSupportQuotient (n q r : ℕ) : ℕ :=
  (n ^ 2 + r) / q
```

Expose the exact factor reconstruction:

```lean
theorem mul_squareOffsetSupportQuotient_eq
    {n q r : ℕ}
    (hdiv : q ∣ n ^ 2 + r) :
    q * squareOffsetSupportQuotient n q r = n ^ 2 + r
```

Equivalent multiplication orientation is acceptable.

This is only a quotient coordinate attached to a known divisor; do not give it semantics when `q` is not a divisor.

## 2. Old support factor has a large complementary factor

Prove a generic square-window statement, preferably:

```lean
theorem anchor_lt_squareOffsetSupportQuotient
    {n q r : ℕ}
    (hr : SquareOffset n r)
    (hqle : q ≤ n)
    (hdiv : q ∣ n ^ 2 + r) :
    n < squareOffsetSupportQuotient n q r
```

If a positive-`q` hypothesis is required by the available division API, include it. For the intended prime specialization it is automatic.

Then provide a thin support wrapper:

```text
q ∈ squareOffsetAnchorNondivisorSupport n r
→ n < squareOffsetSupportQuotient n q r
```

when `r` is a square offset.

The proof should be order arithmetic from the exact factor equation. Do not invoke prime-gap results.

## 3. Coprimality transfer through the quotient

Prove the reusable arithmetic bridge. A prime-specialized statement is sufficient:

```lean
theorem coprime_anchor_squareOffsetSupportQuotient_iff
    {n q r : ℕ}
    (hq : Nat.Prime q)
    (hqn : ¬ q ∣ n)
    (hdiv : q ∣ n ^ 2 + r) :
    Nat.Coprime n (squareOffsetSupportQuotient n q r) ↔
      Nat.Coprime n r
```

Equivalent orientation is acceptable.

A more general theorem assuming `Nat.Coprime n q` is welcome if it is genuinely cleaner, but do not over-generalize at the cost of complexity.

The intended proof route is:

```text
q ∤ n and q prime
→ Coprime n q

q * quotient = n^2+r
Coprime n (n^2+r) ↔ Coprime n r
Coprime n (q*quotient) ↔ Coprime n q ∧ Coprime n quotient
```

Do not use an analytic or residue-distribution argument.

## 4. Coprime wave seats for one nondivisor prime

Define the actual coprime seats hit by one old nondivisor wave:

```lean
noncomputable def squareAnchorCoprimeWaveOffsets (n q : ℕ) : Finset ℕ := by
  classical
  exact (squareAnchorCoprimeOffsets n).filter
    (fun r => SquareOffsetForbiddenBy n q r)
```

Expose exact membership.

For `q ∈ squareAnchorNondivisorPrimes n`, every member has quotient `> n` and quotient coprime to `n`.

## 5. Finite quotient image

Define the complementary-factor image of those coprime wave seats:

```lean
noncomputable def squareAnchorCoprimeSupportQuotients (n q : ℕ) : Finset ℕ :=
  (squareAnchorCoprimeWaveOffsets n q).image
    (fun r => squareOffsetSupportQuotient n q r)
```

Prove the quotient map is injective on an actual positive prime wave, hence:

```lean
theorem card_squareAnchorCoprimeSupportQuotients
    {n q : ℕ}
    (hq : q ∈ squareAnchorNondivisorPrimes n) :
    (squareAnchorCoprimeSupportQuotients n q).card =
      (squareAnchorCoprimeWaveOffsets n q).card
```

An equivalent theorem using `Finset.card_image_iff` / `Finset.card_image_of_injective` is acceptable.

Also expose quotient-image membership strongly enough to recover:

```text
n < k
Nat.Coprime n k
q*k = n^2+r
for some coprime square offset r.
```

Do not claim the quotient is prime.

## 6. Transpose the restricted incidence through one-prime coprime waves

PRIM-L012 intentionally stopped before the optional transpose. Add it now:

```lean
theorem squareAnchorCoprimeNondivisorIncidence_eq_sum_coprimeWave_cards
    (n : ℕ) :
    squareAnchorCoprimeNondivisorIncidence n =
      ∑ q ∈ squareAnchorNondivisorPrimes n,
        (squareAnchorCoprimeWaveOffsets n q).card
```

Then rewrite through quotient images:

```lean
theorem squareAnchorCoprimeNondivisorIncidence_eq_sum_quotient_cards
    (n : ℕ) :
    squareAnchorCoprimeNondivisorIncidence n =
      ∑ q ∈ squareAnchorNondivisorPrimes n,
        (squareAnchorCoprimeSupportQuotients n q).card
```

If the second theorem needs `0 < n`, add that hypothesis. For each `q` in the nondivisor prime set, positivity is already available.

This is an exact finite double count / coordinate change, not a new inequality.

## 7. Packet factorization witness under full cover

Using the existing theorem

```text
exists_distinct_anchorNondivisor_cover_pair_of_fullyCovered
```

construct complementary factors for both seats.

Preferred theorem shape:

```lean
theorem exists_distinct_prime_large_cofactor_packet_of_fullyCovered
    {n r : ℕ}
    (hn : 0 < n)
    (hr : r ∈ squareAnchorCoprimeBaseOffsets n)
    (hfull : SquareOffsetsFullyCovered n) :
    ∃ p q a b,
      p ≠ q ∧
      p ∈ squareAnchorNondivisorPrimes n ∧
      q ∈ squareAnchorNondivisorPrimes n ∧
      n < a ∧ n < b ∧
      Nat.Coprime n a ∧ Nat.Coprime n b ∧
      p * a = n ^ 2 + r ∧
      q * b = n ^ 2 + (n + r)
```

Equivalent conjunction ordering is acceptable.

Strongly preferred thin corollary:

```text
p*a + n = q*b
```

for the produced packet data, either included in the witness theorem or exposed separately.

This is the main semantic theorem of PRIM-L013.

## 8. Optional: distinct cofactors in a packet

If cheap, prove that the two complementary factors in the full-cover packet witness cannot be equal.

The reason is that both are `> n` while their products differ by exactly `n` and the small prime factors are distinct.

Do not spend substantial effort on this optional refinement.

## 9. Optional: quotient interval bounds

If thin, expose from

```text
n^2 < q*k ≤ n^2+2*n
```

an exact quotient-window predicate or upper/lower bound. The lower bound `n < k` is required; additional upper bounds are optional.

Do not introduce real-valued estimates.

---

# Interpretation to preserve in docstrings

State clearly:

- PRIM-L012 separated the coprime window into two-seat packets and forced distinct nondivisor support directions under full cover;
- PRIM-L013 attaches the complementary factor `k = (n^2+r)/q` to each such incidence;
- because the old support prime satisfies `q ≤ n` while the anchored point exceeds `n^2`, the complementary factor is strictly larger than the anchor;
- for `q ∤ n`, coprimality with `n` transfers from the offset to the complementary factor;
- the quotient image is a coordinate change for existing finite incidences, not a claim that the quotient is prime or primitive;
- a fully covered coprime packet therefore yields two distinct small old primes and two large anchor-coprime cofactors whose products differ by exactly `n`;
- no contradiction is claimed in this checkpoint.

---

# Non-goals

Do **not** add in PRIM-L013:

- a proof of `SquareAnchoredSupportEscape`;
- a proof of Legendre's conjecture;
- a claim that the complementary quotient is prime;
- a contradiction from `p*a + n = q*b`;
- Hall's theorem / matching machinery;
- third-order inclusion-exclusion;
- Mertens / PNT / prime-density estimates;
- prime-power valuation / p-adic depth;
- factorization uniqueness beyond what is actually proved;
- RH / CFBRC dependencies;
- category theory.

Do not enumerate fixed values of `n` as the generic proof method.

---

# Verification

Run:

```sh
lake build DkMath.NumberTheory.Legendre
lake build DkMath.NumberTheory.Primitive
lake build DkMath
git diff --check
```

Audit touched Lean files for new occurrences of:

```text
sorry
admit
native_decide
axiom
```

Report unrelated pre-existing occurrences separately; do not broaden scope to repair them.

---

# Acceptance criteria

PRIM-L013 is complete when:

1. each known support divisor has an explicit complementary quotient coordinate;
2. the factor equation `q*k = n^2+r` is exact;
3. every old support factor in the square window has complementary factor `k > n`;
4. for anchor-nondivisor prime support, coprimality with `n` transfers exactly from offset to quotient;
5. one-prime coprime wave seats and their quotient image are represented finitely;
6. the quotient image preserves cardinality for a nondivisor prime wave;
7. coprime-restricted nondivisor incidence is transposed exactly into the quotient-coordinate ledger;
8. full cover of one coprime packet yields two distinct small nondivisor primes and two large anchor-coprime cofactors with the two exact product equations;
9. preferably the packet product difference `p*a + n = q*b` is exposed;
10. no matching theorem, contradiction, or Legendre proof is smuggled into this checkpoint;
11. requested builds and audits are clean.

Stop after PRIM-L013. Do not attempt to solve the resulting packet factorization equation in this implementation pass.

---

# Review questions after PRIM-L013

The next review should decide whether the new quotient coordinates reveal real rigidity beyond incidence counting.

In particular inspect:

```text
A. packet equation p*a + n = q*b with p,q ≤ n < a,b
B. all four factors p,q,a,b coprime to n except that p,q are additionally prime
C. whether quotient coordinates collide across different packet representatives
D. whether the quotient lift naturally forms a finite bipartite/matching graph
E. whether this is the right point to reconnect to Primitive Origin / first-occurrence structure
```

Do not escalate to matching or higher-order counting unless PRIM-L013 exposes a concrete invariant worth preserving.
