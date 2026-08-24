# Codex Instruction — PRIM-L016 Simple Support / Fresh Quotient Direction

Branch: `wip/number-theory-primitive-structure-260822-v0`

Project: DkMath NumberTheory Primitive Structure

## Current verified state

PRIM-L015 is complete.

For a coprime square offset `r` and a selected old nondivisor support prime `p`, let

```text
k = squareOffsetSupportQuotient n p r
  = (n^2 + r) / p.
```

The current API now proves:

```text
p * k = n^2 + r
n < k
Nat.Coprime n k
```

and it describes all old nondivisor prime directions remaining in `k`.

For every old nondivisor prime `q ≠ p`:

```text
q ∈ quotient support ↔ q ∈ original offset support.
```

Equivalently, after erasing the selected direction:

```text
quotientSupport.erase p = offsetSupport.erase p.
```

For the selected direction itself:

```text
p ∈ quotient support ↔ p^2 ∣ n^2 + r.
```

Finally PRIM-L015 proves the exact Direction/Depth dichotomy:

```text
¬ Nat.Prime k
↔
  p ∣ k
  ∨ ∃ q, q ≠ p ∧ q ∈ squareOffsetAnchorNondivisorSupport n r.
```

Thus quotient compositeness has exactly two old-world explanations:

```text
selected direction persists in depth
or
another old prime direction persists.
```

PRIM-L016 should formalize the complementary positive case.

---

# Goal

Show that an incidence whose original old-prime support is exactly the selected direction `p`, with no second `p`-factor, produces a prime complementary quotient above the anchor.

Then bridge that prime quotient back to the reusable Primitive Structure vocabulary:

```text
old selected direction p ≤ n
        ↓ divide once
large prime quotient k > n
        ↓
fresh prime direction relative to primeScalesUpTo n
```

The desired result is an exact criterion, not merely a one-way sufficient condition.

This checkpoint is the first explicit return from the Legendre localization layer to the generic finite-prime `FreshPrimeDirection` / `SupportDisjointFrom` semantics.

Do not attempt to prove that every covered offset satisfies the simple-support/depth-one hypothesis.

---

# Preferred locations

Primary implementation:

```text
DkMath/NumberTheory/Legendre.lean
```

If a tiny theorem of the form

```text
Nat.Prime k -> n < k -> SupportDisjointFrom (primeScalesUpTo n) k
```

or

```text
Nat.Prime k -> n < k -> FreshPrimeDirection (primeScalesUpTo n) k k
```

is genuinely generic and absent from the current Primitive API, it may instead be added to:

```text
DkMath/NumberTheory/Primitive/FinitePrimeWorld.lean
```

and consumed from `Legendre.lean`.

Prefer the generic owner only if the proof is thin and clearly reusable. Do not refactor existing declarations.

---

# Required reconnaissance

Before coding, inspect the current declarations around:

```text
FreshPrimeDirection
SupportDisjointFrom
primeScalesUpTo
mem_primeScalesUpTo
supportDisjointFrom_primeScalesUpTo_iff
selectedPrime_mem_quotientSupport_iff_square_dvd
not_prime_quotient_iff_self_depth_or_distinct_support
mem_squareOffsetAnchorNondivisorSupport
```

Also inspect Mathlib lemmas around:

```text
Nat.dvd_prime
Nat.Prime.ne_one
Finset.eq_singleton_iff_unique_mem
Finset.erase_eq_empty_iff
Finset.subset_singleton_iff
```

Exact names are search hints only.

Prefer deriving primality from the already-proved PRIM-L015 dichotomy. Do not re-run the SquareBody composite-divisor proof.

---

# Required implementation surface

Names below are preferred, not mandatory. Report final declaration names.

## 1. No distinct support iff singleton selected support

For a selected incidence `hp : p ∈ squareOffsetAnchorNondivisorSupport n r`, expose the finite-set equivalence between absence of another old direction and singleton support.

Preferred shape:

```lean
theorem no_distinct_anchorNondivisorSupport_iff_eq_singleton
    {n p r : ℕ}
    (hp : p ∈ squareOffsetAnchorNondivisorSupport n r) :
    (¬ ∃ q,
        q ≠ p ∧ q ∈ squareOffsetAnchorNondivisorSupport n r) ↔
      squareOffsetAnchorNondivisorSupport n r = {p}
```

Equivalent use of `erase p = ∅` is acceptable and may be cleaner:

```text
support.erase p = ∅.
```

If both forms are thin, expose the singleton form publicly because it is the clearest semantic statement.

## 2. Depth-one selected direction

Expose the negated selected-depth equivalence using PRIM-L015:

```lean
theorem selectedPrime_not_dvd_quotient_iff_not_square_dvd
    {n p r : ℕ}
    (hp : p ∈ squareOffsetAnchorNondivisorSupport n r) :
    ¬ p ∣ squareOffsetSupportQuotient n p r ↔
      ¬ p ^ 2 ∣ n ^ 2 + r
```

This should be a thin negation of:

```text
selectedPrime_mem_quotientSupport_iff_square_dvd
```

or of the underlying divisibility statement.

Do not introduce general p-adic valuation machinery in this checkpoint.

## 3. Exact prime-quotient criterion

For a positive anchor, coprime square seat, and selected support prime, prove the main theorem:

```lean
theorem prime_squareOffsetSupportQuotient_iff_singleton_support_and_depth_one
    {n p r : ℕ}
    (hn : 0 < n)
    (hr : r ∈ squareAnchorCoprimeOffsets n)
    (hp : p ∈ squareOffsetAnchorNondivisorSupport n r) :
    Nat.Prime (squareOffsetSupportQuotient n p r) ↔
      squareOffsetAnchorNondivisorSupport n r = {p} ∧
      ¬ p ^ 2 ∣ n ^ 2 + r
```

Equivalent ordering of the two right-hand conditions is acceptable.

The intended proof should primarily negate the PRIM-L015 exact dichotomy:

```text
¬ Prime quotient
↔ self depth ∨ distinct support.
```

Then rewrite:

```text
not self depth ↔ not p^2-divisibility
not distinct support ↔ singleton support.
```

This theorem is the main acceptance target.

## 4. One-way convenient constructor

Add a thin theorem that consumes the simple-support hypotheses directly:

```lean
theorem prime_squareOffsetSupportQuotient_of_singleton_support_of_not_square_dvd
    {n p r : ℕ}
    (hn : 0 < n)
    (hr : r ∈ squareAnchorCoprimeOffsets n)
    (hp : p ∈ squareOffsetAnchorNondivisorSupport n r)
    (hsingle : squareOffsetAnchorNondivisorSupport n r = {p})
    (hdepth : ¬ p ^ 2 ∣ n ^ 2 + r) :
    Nat.Prime (squareOffsetSupportQuotient n p r)
```

This should be a direct wrapper around section 3.

## 5. Prime quotient lies outside the old prime world

For the same incidence, use the existing quotient lower bound to prove:

```lean
theorem squareOffsetSupportQuotient_not_mem_primeScalesUpTo
    {n p r : ℕ}
    (hr : SquareOffset n r)
    (hp : p ∈ squareOffsetAnchorNondivisorSupport n r) :
    squareOffsetSupportQuotient n p r ∉ primeScalesUpTo n
```

The proof should use:

```text
n < quotient
```

and `mem_primeScalesUpTo`.

This theorem does not need quotient primality merely to prove non-membership.

## 6. Generic fresh-direction bridge

Once quotient primality is known, package the result in Primitive Structure vocabulary.

Preferred theorem:

```lean
theorem freshPrimeDirection_squareOffsetSupportQuotient_of_singleton_support_of_depth_one
    {n p r : ℕ}
    (hn : 0 < n)
    (hr : r ∈ squareAnchorCoprimeOffsets n)
    (hp : p ∈ squareOffsetAnchorNondivisorSupport n r)
    (hsingle : squareOffsetAnchorNondivisorSupport n r = {p})
    (hdepth : ¬ p ^ 2 ∣ n ^ 2 + r) :
    FreshPrimeDirection
      (primeScalesUpTo n)
      (squareOffsetSupportQuotient n p r)
      (squareOffsetSupportQuotient n p r)
```

The witness prime is the quotient itself:

```text
Prime k
k ∣ k
k ∉ primeScalesUpTo n.
```

If there is already a generic theorem for `prime + outside S -> FreshPrimeDirection`, reuse it.

## 7. Support-disjointness of the prime quotient

Also expose the stronger all-old-directions-absent statement:

```lean
theorem supportDisjointFrom_squareOffsetSupportQuotient_of_singleton_support_of_depth_one
    {n p r : ℕ}
    (hn : 0 < n)
    (hr : r ∈ squareAnchorCoprimeOffsets n)
    (hp : p ∈ squareOffsetAnchorNondivisorSupport n r)
    (hsingle : squareOffsetAnchorNondivisorSupport n r = {p})
    (hdepth : ¬ p ^ 2 ∣ n ^ 2 + r) :
    SupportDisjointFrom
      (primeScalesUpTo n)
      (squareOffsetSupportQuotient n p r)
```

Because the quotient is prime and greater than `n`, every prime divisor of it is itself and therefore outside the old world.

If a generic reusable helper belongs in `FinitePrimeWorld.lean`, add it there and keep this theorem as a thin Legendre wrapper.

## 8. Exact old-prime × fresh-prime factorization package

Expose the arithmetic interpretation of the simple incidence:

```lean
theorem simple_support_depth_one_factorization
    {n p r : ℕ}
    (hn : 0 < n)
    (hr : r ∈ squareAnchorCoprimeOffsets n)
    (hp : p ∈ squareOffsetAnchorNondivisorSupport n r)
    (hsingle : squareOffsetAnchorNondivisorSupport n r = {p})
    (hdepth : ¬ p ^ 2 ∣ n ^ 2 + r) :
    let k := squareOffsetSupportQuotient n p r
    Nat.Prime p ∧ p ≤ n ∧ ¬ p ∣ n ∧
    Nat.Prime k ∧ n < k ∧ Nat.Coprime n k ∧
    p * k = n ^ 2 + r
```

Equivalent theorem shape without `let` is acceptable.

This theorem should mostly collect already-proved facts and the new prime criterion.

Do not claim `k` is a Zsigmondy primitive prime or PrimitiveBeam origin witness. Here `fresh` means only outside the finite prime world `primeScalesUpTo n`.

## 9. Fresh-or-obstructed trichotomy

Strongly preferred if thin: package PRIM-L015 and the new positive case into a single total classification for every selected coprime incidence:

```lean
theorem quotient_prime_or_self_depth_or_distinct_support
    {n p r : ℕ}
    (hn : 0 < n)
    (hr : r ∈ squareAnchorCoprimeOffsets n)
    (hp : p ∈ squareOffsetAnchorNondivisorSupport n r) :
    Nat.Prime (squareOffsetSupportQuotient n p r) ∨
      p ^ 2 ∣ n ^ 2 + r ∨
      ∃ q,
        q ≠ p ∧ q ∈ squareOffsetAnchorNondivisorSupport n r
```

This is a finite structural classification only.

Do not attempt to prove that the first branch must occur.

---

# Optional packet wrapper

If extremely thin, under full cover and a packet representative `r`, assume chosen left/right support witnesses each satisfy singleton support and depth one. Then package the two resulting large fresh prime quotients.

At `4 ≤ n`, the existing global quotient injectivity may also show those two quotients are distinct.

This packet wrapper is optional and must not become a matching/counting project.

---

# Interpretation to preserve in docstrings

State clearly:

- PRIM-L015 classified quotient compositeness by old Direction/Depth obstructions;
- PRIM-L016 identifies the exact complementary case;
- singleton support means exactly one distinct old prime direction divides the anchored point;
- depth one here means only `p^2 ∤ n^2+r`, not a general valuation API;
- after removing that one old direction once, the remaining quotient is prime and lies above the anchor;
- this prime is therefore fresh relative to the finite old world `primeScalesUpTo n`;
- `FreshPrimeDirection` here is finite-world freshness, not `PrimitivePrimeFactorOfDiffPow` / Zsigmondy origin;
- no assertion is made that every covered offset is simple-support/depth-one;
- no Legendre proof or contradiction follows from this checkpoint alone.

---

# Non-goals

Do **not** add in PRIM-L016:

- a proof that every coprime offset has singleton support;
- a proof that every selected support prime has depth one;
- a proof that every quotient is prime;
- a proof of `SquareAnchoredSupportEscape`;
- a proof of Legendre's conjecture;
- infinite descent;
- matching/Hall theory;
- global counting estimates for simple incidences;
- Zsigmondy / PrimitiveBeam origin claims;
- p-adic valuation-depth machinery beyond the one-step `p^2` criterion;
- Mertens/PNT/asymptotic density;
- RH/CFBRC dependencies;
- numerical enumeration as the generic proof method.

---

# Verification

Run:

```sh
lake build DkMath.NumberTheory.Legendre
lake build DkMath.NumberTheory.Primitive
lake build DkMath
git diff --check
```

If `FinitePrimeWorld.lean` is touched, also verify its direct module build.

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

PRIM-L016 is complete when:

1. absence of distinct old support is identified with singleton selected support;
2. selected depth-one is connected to `¬ p^2 ∣ n^2+r`;
3. quotient primality has an exact iff with singleton support + depth one;
4. the quotient is proved outside `primeScalesUpTo n`;
5. the simple quotient is packaged as a `FreshPrimeDirection` relative to the old world;
6. support-disjointness of that prime quotient is exposed;
7. the anchored point is packaged as one old nondivisor prime times one large fresh prime;
8. the checkpoint does not assert that the simple case always occurs;
9. no PrimitiveBeam/Zsigmondy origin or Legendre proof is smuggled in;
10. requested builds and audits are clean.

Stop after PRIM-L016.

---

# Review questions after PRIM-L016

After this checkpoint, classify coprime covered offsets into:

```text
SIMPLE
  singleton old direction
  + depth one
  -> large fresh prime quotient

OBSTRUCTED
  selected depth persists
  or another old direction persists
```

Then inspect which route has actual leverage:

```text
A. count / localize SIMPLE versus OBSTRUCTED incidences;
B. use the pair packet separation to force many distinct SIMPLE fresh quotients;
C. turn repeated Direction/Depth obstruction into a finite factor graph;
D. connect only the genuinely new fresh quotient direction to a Primitive Origin API;
E. stop incidence escalation if neither branch gives a strict capacity obstruction.
```

Do not choose among these before seeing the implemented PRIM-L016 theorem surface.
