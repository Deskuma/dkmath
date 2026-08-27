# Codex Instruction — PRIM-L014 Quotient Collision Rigidity / Global Injectivity

Branch: `wip/number-theory-primitive-structure-260822-v0`

Project: DkMath NumberTheory Primitive Structure

## Current verified state

PRIM-L013 is complete.

The Legendre application layer now attaches to every coprime nondivisor support incidence

```text
q ∣ n^2 + r
```

its complementary factor

```text
k = squareOffsetSupportQuotient n q r = (n^2 + r) / q.
```

For such an incidence the current API proves:

```text
q * k = n^2 + r
q ≤ n
n < k
Nat.Coprime n k
```

and the quotient image of one fixed prime wave has the same cardinality as that wave.

The restricted coprime incidence ledger is already transposed to quotient-image cardinalities:

```text
squareAnchorCoprimeNondivisorIncidence n
  = ∑ q ∈ squareAnchorNondivisorPrimes n,
      (squareAnchorCoprimeSupportQuotients n q).card.
```

Under full cover PRIM-L012 gives

```text
2 * Nat.totient n
  ≤ squareAnchorCoprimeNondivisorIncidence n.
```

PRIM-L013 also gives, for each fully covered coprime packet `(r, n+r)`, distinct small primes `p ≠ q`, large anchor-coprime cofactors `a,b > n`, and

```text
p * a = n^2 + r
q * b = n^2 + (n+r)
p * a + n = q * b.
```

The next question is whether the quotient coordinate can collide between different support incidences.

---

# Goal

Prove that quotient collisions are extraordinarily rigid and disappear completely once `n ≥ 4`.

Suppose two coprime nondivisor support incidences have the same quotient `k`:

```text
p * k = n^2 + r
q * k = n^2 + s.
```

Then

```text
|p-q| * k = |r-s|.
```

Both offsets lie in `1..2*n`, hence

```text
|r-s| < 2*n.
```

But every support quotient satisfies `n < k`.

Therefore:

1. if `|p-q| ≥ 2`, equality is impossible;
2. if distinct primes have `|p-q| = 1`, they must be `2` and `3`;
3. in that exceptional case the smaller factor is `2`, so

```text
n^2 < 2*k < 4*n,
```

forcing `n < 4`.

Hence for `4 ≤ n` the quotient map is injective on **all** coprime nondivisor support incidences, even across different prime waves.

This is the main target of PRIM-L014.

Do not turn this into a Legendre proof in this checkpoint.

---

# Preferred location

Continue in:

```text
DkMath/NumberTheory/Legendre.lean
```

Do not refactor or move the existing L011–L013 declarations in the same pass.

The file is large, but this checkpoint depends tightly on the current local quotient API. A later cleanup may split the analysis once the theorem surface stabilizes.

---

# Required reconnaissance

Before coding, inspect the current Lean 4.32 / Mathlib API around:

```text
Nat.Prime.eq_two_or_odd
Nat.Prime.two_le
Nat.Prime.ne_zero
Nat.Prime.not_even_iff
Nat.even_iff
Nat.Odd
Nat.absDiff
Nat.absDiff_eq
Nat.mul_lt_mul
Finset.product
Finset.filter
Finset.card_image_iff
Finset.sum_comm
```

The names above are search hints only.

In particular, find the cleanest existing route for the elementary prime-gap fact:

```text
Nat.Prime p
Nat.Prime q
p ≠ q
|p-q| < 2
→ {p,q} = {2,3}
```

or an equivalent ordered form:

```text
p < q
Nat.Prime p
Nat.Prime q
q - p < 2
→ p = 2 ∧ q = 3.
```

Do not introduce general prime-gap theory. A short parity argument is enough if Mathlib has no direct lemma.

---

# Required implementation surface

Names below are preferred, not mandatory. Report final declaration names.

## 1. Finite global coprime-support incidence set

Expose the actual finite incidence domain used by the restricted ledger.

Preferred representation:

```lean
noncomputable def squareAnchorCoprimeSupportIncidences
    (n : ℕ) : Finset (ℕ × ℕ) := by
  classical
  exact ((squareAnchorNondivisorPrimes n).product
    (squareAnchorCoprimeOffsets n)).filter
      (fun qr => SquareOffsetForbiddenBy n qr.1 qr.2)
```

The pair is `(q,r)` = `(old nondivisor prime, coprime square offset)`.

Expose exact membership:

```lean
@[simp] theorem mem_squareAnchorCoprimeSupportIncidences
    {n q r : ℕ} :
    (q,r) ∈ squareAnchorCoprimeSupportIncidences n ↔
      q ∈ squareAnchorNondivisorPrimes n ∧
      r ∈ squareAnchorCoprimeOffsets n ∧
      SquareOffsetForbiddenBy n q r
```

An expanded primality/bound/divisibility form may be added if thin, but do not duplicate existing support semantics unnecessarily.

## 2. Incidence-set cardinality equals the existing restricted ledger

Prove:

```lean
theorem card_squareAnchorCoprimeSupportIncidences
    (n : ℕ) :
    (squareAnchorCoprimeSupportIncidences n).card =
      squareAnchorCoprimeNondivisorIncidence n
```

Use finite double counting / filter-card transpose. Do not re-prove any number theory.

This gives one concrete finite domain on which to study the quotient map.

## 3. Global quotient projection

Define the quotient attached to an incidence pair, preferably:

```lean
def squareAnchorIncidenceQuotient
    (n : ℕ) (qr : ℕ × ℕ) : ℕ :=
  squareOffsetSupportQuotient n qr.1 qr.2
```

and the finite global image:

```lean
noncomputable def squareAnchorCoprimeGlobalQuotients (n : ℕ) : Finset ℕ :=
  (squareAnchorCoprimeSupportIncidences n).image
    (squareAnchorIncidenceQuotient n)
```

Expose membership if useful.

Do not claim these quotients are prime or primitive.

## 4. Generic same-prime quotient collision is trivial

Prove or reuse the thin fact:

```text
same q + same quotient
→ same r.
```

This already follows from

```text
q * quotient = n^2 + r.
```

It may remain a private helper if only needed by the global injectivity theorem.

## 5. Distinct-prime quotient collision forces a tiny anchor

This is the core arithmetic lemma.

Preferred theorem shape:

```lean
theorem anchor_lt_four_of_distinct_prime_quotient_collision
    {n p q r s : ℕ}
    (hp : (p,r) ∈ squareAnchorCoprimeSupportIncidences n)
    (hq : (q,s) ∈ squareAnchorCoprimeSupportIncidences n)
    (hpq : p ≠ q)
    (hquot : squareOffsetSupportQuotient n p r =
      squareOffsetSupportQuotient n q s) :
    n < 4
```

Equivalent theorem factoring out the incidence-set membership assumptions is acceptable.

Intended proof skeleton:

```text
k := common quotient
p*k = n^2+r
q*k = n^2+s
n < k
1 ≤ r,s ≤ 2*n
```

Order `p,q` without loss of generality.

If `q-p ≥ 2`, then

```text
2*k ≤ (q-p)*k = s-r < 2*n
```

contradicting `n < k`.

Hence `q-p = 1`. For distinct primes this forces `p=2`, `q=3`.
Then

```text
k = s-r < 2*n
n^2 < 2*k < 4*n
```

and therefore `n < 4`.

Keep all endpoint inequalities exact. The square window is `1 ≤ r,s ≤ 2*n`, so for distinct offsets the absolute difference is **strictly** less than `2*n`.

Do not use analytic prime-gap results.

## 6. Global quotient injectivity for `n ≥ 4`

Prove:

```lean
theorem squareAnchorIncidenceQuotient_injective_of_four_le
    {n : ℕ}
    (hn : 4 ≤ n) :
    Set.InjOn (squareAnchorIncidenceQuotient n)
      (squareAnchorCoprimeSupportIncidences n)
```

or, if easier for Finset cardinality APIs, the direct elementwise form:

```lean
theorem squareAnchorIncidenceQuotient_eq_imp_eq_of_four_le
    {n : ℕ} (hn : 4 ≤ n)
    {x y : ℕ × ℕ}
    (hx : x ∈ squareAnchorCoprimeSupportIncidences n)
    (hy : y ∈ squareAnchorCoprimeSupportIncidences n)
    (hxy : squareAnchorIncidenceQuotient n x =
      squareAnchorIncidenceQuotient n y) :
    x = y
```

This theorem must handle both cases:

```text
same prime -> same offset
distinct primes -> impossible because n ≥ 4.
```

This is the main semantic result of the checkpoint.

## 7. Global quotient cardinality preservation for `n ≥ 4`

Use injectivity to prove:

```lean
theorem card_squareAnchorCoprimeGlobalQuotients_of_four_le
    {n : ℕ}
    (hn : 4 ≤ n) :
    (squareAnchorCoprimeGlobalQuotients n).card =
      squareAnchorCoprimeNondivisorIncidence n
```

This should compose:

```text
card image = card incidence set
card incidence set = restricted incidence ledger.
```

The theorem says every coprime support incidence receives a globally unique quotient coordinate once `n ≥ 4`.

## 8. Quotient image properties

Prove a thin global property theorem:

```lean
theorem squareAnchorCoprimeGlobalQuotient_properties
    {n k : ℕ}
    (hk : k ∈ squareAnchorCoprimeGlobalQuotients n) :
    n < k ∧ Nat.Coprime n k
```

If useful and cheap, also include an upper-range consequence from `q ≥ 2` and the square-window bound, e.g. a theorem of the form

```text
2*k ≤ n^2 + 2*n
```

for every global quotient.

The lower/coprime properties are required; the upper bound is optional.

## 9. Full-cover distinct-quotient frontier

Combine the PRIM-L012 full-cover lower bound with global quotient cardinality preservation:

```lean
theorem two_mul_totient_le_card_globalQuotients_of_fullyCovered
    {n : ℕ}
    (hn : 4 ≤ n)
    (hfull : SquareOffsetsFullyCovered n) :
    2 * Nat.totient n ≤
      (squareAnchorCoprimeGlobalQuotients n).card
```

Interpretation:

```text
full cover
→ at least 2*φ(n) coprime-support incidences
→ for n ≥ 4 all of those incidences have distinct large anchor-coprime quotient coordinates.
```

This is a structural frontier only.

## 10. Optional: collision classification below `n = 4`

If very cheap after the main theorem, expose a theorem saying any nontrivial quotient collision must come from the prime pair `2,3` (up to orientation) and `n < 4`.

Do not enumerate all anchors `n=1,2,3` unless that falls out trivially. Numerical Legendre verification is not part of this checkpoint.

---

# Interpretation to preserve in docstrings

State clearly:

- the quotient is a complementary-factor coordinate attached to an existing support incidence;
- one fixed prime wave was already injective in PRIM-L013;
- PRIM-L014 proves the much stronger cross-prime injectivity for `n ≥ 4`;
- the proof uses only the short offset window, the lower bound `k > n`, and elementary rigidity of distinct primes at distance one;
- global quotient cardinality therefore equals coprime nondivisor incidence cardinality for `n ≥ 4`;
- quotient values are large and coprime to the anchor, but are not asserted prime, primitive, or fresh;
- no matching theorem, density estimate, or Legendre proof is claimed.

This is a **collision-rigidity** checkpoint, not a counting contradiction.

---

# Non-goals

Do **not** add in PRIM-L014:

- a proof of `SquareAnchoredSupportEscape`;
- a proof of Legendre's conjecture;
- analytic prime-gap estimates;
- PNT / Mertens / prime-density arguments;
- Hall matching machinery;
- PrimitiveBeam / Zsigmondy origin claims for the quotient;
- quotient primality claims;
- third-order inclusion-exclusion;
- RH / CFBRC dependencies;
- broad refactoring of `Legendre.lean`.

Do not turn the elementary `2,3` exceptional-prime argument into a general prime-gap abstraction.

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

PRIM-L014 is complete when:

1. the finite global coprime-support incidence domain is exposed;
2. its cardinality is identified with the existing restricted incidence ledger;
3. a global quotient image is defined;
4. distinct-prime quotient collision is proved to force `n < 4`;
5. for `4 ≤ n`, the quotient map is injective on all coprime-support incidences;
6. global quotient-image cardinality equals restricted incidence cardinality for `4 ≤ n`;
7. global quotient values are proved larger than `n` and coprime to `n`;
8. under full cover and `4 ≤ n`, at least `2 * Nat.totient n` distinct global quotient values are forced;
9. no quotient primality / primitive-origin claim or Legendre proof is smuggled into the checkpoint;
10. requested builds and audits are clean.

Stop after PRIM-L014. Do not begin a contradiction proof or Hall matching pass in the same implementation.

---

# Review questions after PRIM-L014

If the global quotient map is indeed injective for `n ≥ 4`, the next review should decide whether that rigidity can be converted into one of the following stronger structures:

```text
A. packet quotient graph:
   each coprime packet contributes two globally distinct large cofactors

B. quotient residue transport:
   q*k ≡ r (mod n), with q and k both units modulo n

C. finite quotient-range capacity:
   compare the forced 2*φ(n) distinct quotients with exact coprime capacity
   of the allowed quotient interval

D. Primitive Origin bridge:
   only if an existing theorem genuinely recognizes one of these large
   cofactors as a first-occurrence / fresh direction

E. stop the quotient route if global injectivity still gives no leverage
```

Do not assume in advance that injectivity proves enough. The next checkpoint must be chosen from the actual Lean surface.