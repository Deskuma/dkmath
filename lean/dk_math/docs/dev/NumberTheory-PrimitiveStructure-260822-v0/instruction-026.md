# Codex Instruction — PRIM-L019 Packet Cross-Pair / Two-Seat Coupling Ledger

Branch: `wip/number-theory-primitive-structure-260822-v0`

Project: DkMath NumberTheory Primitive Structure

## Current verified state

PRIM-L018 is complete.

The coprime square window is already represented as `Nat.totient n` canonical packets

```text
(r, n + r)
```

with `r ∈ squareAnchorCoprimeBaseOffsets n`, and the two nondivisor support sets are disjoint:

```text
Disjoint
  (squareOffsetAnchorNondivisorSupport n r)
  (squareOffsetAnchorNondivisorSupport n (n + r)).
```

Under full cover, both seats have nonempty nondivisor support and therefore admit distinct prime witnesses.

PRIM-L018 also localized the seatwise obstruction ledgers to the same coprime/nondivisor domain:

```text
squareAnchorCoprimePrimeSquareDepthBudget n
squareAnchorCoprimePrimePairOverlapCount n
```

with exact local transposes.

The current pair ledger is still **within one seat**.  It records two old directions simultaneously supporting the same anchored point.  It does not record the compulsory relationship between the two different seats of one packet.

This checkpoint adds that missing packet-level coordinate.

Do not add third-order inclusion-exclusion or attempt a contradiction.

---

# Goal

For a packet `(r, n+r)`, define the ordered cross-incidences

```text
p supports the left seat r
q supports the right seat n+r.
```

The roles are ordered: `(p,q)` and `(q,p)` are different packet assignments.

Because both primes are anchor-nondivisors, the same prime cannot serve both seats.  Thus every cross-incidence automatically has `p ≠ q`.

For one packet with left support size `a` and right support size `b`, the number of ordered cross-prime assignments is exactly

```text
a * b.
```

Under full cover both supports are nonempty, so every packet contributes at least one cross-incidence.  Hence obtain the new packet frontier

```text
Nat.totient n ≤ squareAnchorPacketCrossPairCount n.
```

Then localize each fixed ordered pair `(p,q)` by its product modulus.  Two packet representatives hit by the same ordered cross-pair differ by a multiple of `p*q`; therefore when

```text
n < p*q
```

the ordered pair can serve at most one canonical packet.

This is a two-seat coupling ledger.  It is not the same as PRIM-L018's within-seat pair-overlap ledger.

---

# Preferred location

Continue in:

```text
DkMath/NumberTheory/Legendre.lean
```

Do not move existing declarations during this checkpoint.

---

# Required implementation surface

Names below are preferred, not mandatory.  Report final declaration names.

## 1. Ordered cross-prime domain

Define the ordered distinct anchor-nondivisor prime pairs:

```lean
noncomputable def squareAnchorNondivisorOrderedPrimePairs
    (n : ℕ) : Finset (ℕ × ℕ) := by
  classical
  exact ((squareAnchorNondivisorPrimes n).product
    (squareAnchorNondivisorPrimes n)).filter
      (fun pair => pair.1 ≠ pair.2)
```

Expose membership:

```lean
@[simp] theorem mem_squareAnchorNondivisorOrderedPrimePairs
    {n p q : ℕ} :
    (p,q) ∈ squareAnchorNondivisorOrderedPrimePairs n ↔
      Nat.Prime p ∧ p ≤ n ∧ ¬ p ∣ n ∧
      Nat.Prime q ∧ q ≤ n ∧ ¬ q ∣ n ∧
      p ≠ q
```

Do **not** canonicalize by `p < q`; left/right packet roles are ordered.

## 2. Fixed ordered cross-pair packet hits

Define the base representatives whose left seat is supported by `p` and shifted right seat by `q`:

```lean
noncomputable def squareAnchorPacketCrossOffsets
    (n p q : ℕ) : Finset ℕ := by
  classical
  exact (squareAnchorCoprimeBaseOffsets n).filter
    (fun r =>
      SquareOffsetForbiddenBy n p r ∧
      SquareOffsetForbiddenBy n q (n + r))
```

Expose exact membership.

The Finset is over canonical packet representatives, not over all `2*n` seats.

## 3. Same-prime exclusion across a packet

Expose / reuse the PRIM-L012 separation theorem in the packet-cross vocabulary.

A useful direct theorem is:

```lean
theorem not_mem_packetCross_same_prime
    {n p r : ℕ}
    (hp : p ∈ squareAnchorNondivisorPrimes n) :
    ¬ (SquareOffsetForbiddenBy n p r ∧
       SquareOffsetForbiddenBy n p (n+r))
```

This should be a thin reuse of

```text
not_both_squareOffsetForbiddenBy_of_not_dvd_anchor
```

not a second proof.

If the ordered pair domain already enforces `p ≠ q`, this theorem is still useful as semantic documentation.

## 4. Packet cross-pair ledger

Define:

```lean
noncomputable def squareAnchorPacketCrossPairCount (n : ℕ) : ℕ :=
  ∑ pair ∈ squareAnchorNondivisorOrderedPrimePairs n,
    (squareAnchorPacketCrossOffsets n pair.1 pair.2).card
```

This counts

```text
(packet representative r, left prime p, right prime q)
```

incidences.

It is not the number of packets and not the within-seat pair-overlap count.

## 5. Exact local product double count

Prove the central transpose:

```lean
theorem squareAnchorPacketCrossPairCount_eq_sum_support_card_mul
    (n : ℕ) :
    squareAnchorPacketCrossPairCount n =
      ∑ r ∈ squareAnchorCoprimeBaseOffsets n,
        (squareOffsetAnchorNondivisorSupport n r).card *
        (squareOffsetAnchorNondivisorSupport n (n+r)).card
```

Reason:

```text
for fixed packet r,
choose one left support prime and one right support prime.
```

The support disjointness from PRIM-L012 means the ordered-domain condition `p ≠ q` is automatic for actual packet incidences.

Prefer a finite sum transpose / product-cardinality proof.  Do not introduce a witness choice function.

## 6. Full-cover packet frontier

Under full cover, both support sets of every canonical packet are nonempty.  Therefore each local product is at least one.

Prove:

```lean
theorem totient_le_packetCrossPairCount_of_fullyCovered
    {n : ℕ}
    (hn : 0 < n)
    (hfull : SquareOffsetsFullyCovered n) :
    Nat.totient n ≤ squareAnchorPacketCrossPairCount n
```

Prefer deriving the left side from

```text
card_squareAnchorCoprimeBaseOffsets = Nat.totient n.
```

This theorem is a necessary condition only.

## 7. Cross-pair factorization package

For a cross hit `(r,p,q)`, expose the quotient coordinates from PRIM-L013 without assuming full cover:

```text
p*a = n^2 + r
q*b = n^2 + (n+r)
p*a + n = q*b
n < a
n < b
Coprime n a
Coprime n b
```

under the natural hypotheses that `(p,q)` is in the ordered nondivisor pair domain and `r` is in the cross-offset set.

Preferred theorem shape may existentially return `a,b`, or simply instantiate

```text
squareOffsetSupportQuotient n p r
squareOffsetSupportQuotient n q (n+r).
```

This should reuse existing quotient lemmas.  It is a coordinate package, not a Diophantine contradiction.

## 8. Product-period separation for a fixed cross pair

Prove the elementary periodic rigidity:

if `r` and `s` are both packet-cross hits for distinct primes `p,q`, then the difference is divisible by both `p` and `q`, hence by `p*q`.

A convenient theorem may state, for `r ≤ s`:

```text
p*q ∣ s-r
```

or an equivalent congruence theorem.

Use primality/distinctness to combine divisibility.  Do not invoke analytic estimates.

From this derive the important sparsity theorem:

```lean
theorem card_squareAnchorPacketCrossOffsets_le_one_of_anchor_lt_product
    {n p q : ℕ}
    (hpq : (p,q) ∈ squareAnchorNondivisorOrderedPrimePairs n)
    (hfar : n < p*q) :
    (squareAnchorPacketCrossOffsets n p q).card ≤ 1
```

The threshold here is **`n`**, not `2*n`, because cross offsets live in the base representative window `1..n`.

## 9. Near/far ordered cross-pair split

Define, preferably:

```lean
squareAnchorPacketNearCrossPairs n :=
  (squareAnchorNondivisorOrderedPrimePairs n).filter
    (fun pair => pair.1 * pair.2 ≤ n)

squareAnchorPacketFarCrossPairs n :=
  (squareAnchorNondivisorOrderedPrimePairs n).filter
    (fun pair => n < pair.1 * pair.2)
```

Prove partition/disjointness and the exact ledger split if compact.

Then prove the far contribution bound:

```text
Σ pair in farCrossPairs,
  card(squareAnchorPacketCrossOffsets ...)
≤ card(farCrossPairs).
```

Do not estimate the number of near/far prime pairs analytically.

This section is strongly preferred because it is the direct packet analogue of PRIM-L010, with the sharper window threshold `n`.

## 10. Within-seat / cross-seat pair decomposition — strongly preferred if thin

For one packet write

```text
A = left nondivisor support
B = right nondivisor support.
```

PRIM-L012 gives `Disjoint A B`.  Hence the unordered prime pairs in `A ∪ B` split into:

```text
within-left pairs
+ within-right pairs
+ cross pairs.
```

At the cardinality level:

```text
choose (A.card + B.card) 2
  = choose A.card 2 + choose B.card 2 + A.card * B.card.
```

If Mathlib arithmetic makes this cheap, expose a packet theorem and optionally sum it over `squareAnchorCoprimeBaseOffsets n`.

This gives a conceptual bridge:

```text
PRIM-L018 pair ledger = within-seat interactions
PRIM-L019 cross ledger = between-seat interactions
```

Do not build third-order subsets.

---

# Interpretation to preserve in docstrings

State clearly:

- canonical packet representatives are `r` with seats `(r,n+r)`;
- ordered prime pairs encode left/right roles;
- the same anchor-nondivisor prime cannot cover both seats of one packet;
- one packet contributes exactly `leftSupport.card * rightSupport.card` cross incidences;
- full cover therefore forces at least one cross incidence per packet;
- fixed cross-pair hits are periodic at product modulus `p*q`;
- when `p*q > n`, that ordered cross pair can hit at most one canonical packet;
- this is a packet-coupling constraint, distinct from within-seat pair overlap;
- no prime-density, probabilistic independence, matching theorem, or Legendre proof is used.

---

# Non-goals

Do **not** add in PRIM-L019:

- a proof that the packet cross frontier is impossible;
- a proof of `SquareAnchoredSupportEscape`;
- a proof of Legendre's conjecture;
- third-order/higher inclusion-exclusion;
- Hall/matching machinery;
- analytic estimates for prime counts or harmonic sums;
- Möbius inversion;
- p-adic valuation sums;
- PrimitiveBeam/Zsigmondy first-occurrence claims;
- RH / CFBRC dependencies;
- numerical enumeration as the generic proof method.

If an exact CRT residue formula for the cross phase is immediately available and thin, it may be added, but it is **not required** for acceptance.  Do not let CRT API work dominate the checkpoint.

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

PRIM-L019 is complete when:

1. ordered distinct nondivisor prime pairs are represented finitely;
2. fixed `(left prime,right prime)` packet-hit sets are defined;
3. the global packet cross ledger is defined;
4. the ledger has the exact local transpose `Σ_r leftCard * rightCard`;
5. full cover implies `Nat.totient n ≤ packetCrossPairCount`;
6. cross hits expose the existing quotient/factor equation `p*a+n=q*b`;
7. a fixed ordered pair with `p*q > n` hits at most one canonical packet;
8. near/far cross-pair localization is implemented if compact;
9. no contradiction, matching, higher-order inclusion-exclusion, or analytic estimate is introduced.

Stop after PRIM-L019.

---

# Review questions after PRIM-L019

After implementation, compare three exact packet-level quantities:

```text
within-left pair multiplicity
within-right pair multiplicity
cross left/right multiplicity
```

and inspect whether product-period sparsity at threshold `n` creates genuine leverage beyond the seatwise PRIM-L018 frontier.

Then choose among:

```text
A. cross-pair near/far arithmetic refinement if genuinely restrictive;
B. quotient equation rigidity for repeated ordered pair assignments;
C. canonical/minimal support assignment to remove pair multiplicity overcount;
D. packet graph / matching only if the finite neighborhood structure now justifies it;
E. declare second-order counting saturated and pivot to a different invariant.
```

Do not automatically escalate to third-order intersections.