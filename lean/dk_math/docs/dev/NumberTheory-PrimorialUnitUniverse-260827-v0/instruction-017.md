# PUU-L017 — Local Prime Sign Dichotomy / Square-Phase Factorization

## Goal

PUU-L016 introduced `SameSquareAnchorPhase S a b` and proved that one global
square phase determines the full finite-basis reservation pattern at every
fixed offset.  PUU-L017 should now expose the **local prime-coordinate content**
of that phase relation.

For a prime modulus `p`, equality of squares has the classical two-sign form

```text
a^2 ≡ b^2 (mod p)
  ↔ a ≡ b (mod p) or a ≡ -b (mod p).
```

This checkpoint should formalize that local dichotomy and prove that every
global square-anchor phase supplies one such local sign choice at every basis
prime.

Do **not** yet synthesize arbitrary mixed sign assignments by CRT.  That is the
next checkpoint.

## Module

Preferred new module:

```text
DkMath/NumberTheory/PrimorialUniverse/SquareAnchorPrimeSign.lean
```

Import:

```lean
import DkMath.NumberTheory.PrimorialUniverse.SquareAnchorPhase
```

`Mathlib.Tactic` / `ZMod` support may be added if useful.  Do not import the
Legendre consumer layer.

Export the module through `DkMath.NumberTheory.PrimorialUniverse`.

## 1. Local sign predicate

Introduce a small public predicate expressing the two local square roots.
A `ZMod` formulation is preferred because it avoids natural-number subtraction:

```lean
def SameSquarePrimeSign (p a b : ℕ) : Prop :=
  ((a : ZMod p) = (b : ZMod p)) ∨
    ((a : ZMod p) = -(b : ZMod p))
```

Equivalent naming or a `Nat.ModEq` formulation is acceptable if the API is
cleaner.  The semantic content must be exactly `+` or `-` modulo `p`.

Important: do **not** force the two branches to be disjoint.  At `p = 2`, the
`+` and `-` branches can coincide.  This overlap is mathematically real and
should remain visible.

Provide simple symmetry if useful:

```text
SameSquarePrimeSign p a b ↔ SameSquarePrimeSign p b a
```

but do not overbuild an equivalence-relation API.

## 2. Prime local square iff sign dichotomy

For prime `p`, prove the exact local theorem, e.g.

```lean
theorem square_mod_prime_eq_iff_sameSquarePrimeSign
    {p a b : ℕ}
    (hp : Nat.Prime p) :
    ((a : ZMod p) ^ 2 = (b : ZMod p) ^ 2) ↔
      SameSquarePrimeSign p a b
```

or an equivalent theorem phrased with `% p` / `Nat.ModEq`.

Preferred proof idea in `ZMod p`:

```text
a^2 = b^2
→ (a-b)(a+b)=0
→ a-b=0 or a+b=0
→ a=b or a=-b
```

using that `ZMod p` is a field / domain for prime `p`.

The reverse direction is immediate by substitution.

This is the mathematical kernel of PUU-L017.

## 3. Global phase descends to every basis prime

Let

```text
M = finitePrimeBasisProduct S.
```

For `hS : IsFinitePrimeBasis S`, `hpS : p ∈ S`, and

```text
hab : SameSquareAnchorPhase S a b
```

prove that the square congruence descends from modulus `M` to modulus `p`, and
then apply the local theorem:

```lean
theorem sameSquareAnchorPhase_implies_primeSign
    {S : Finset ℕ}
    (hS : IsFinitePrimeBasis S)
    {a b p : ℕ}
    (hab : SameSquareAnchorPhase S a b)
    (hpS : p ∈ S) :
    SameSquarePrimeSign p a b
```

Equivalent argument ordering is fine.

Useful facts already available:

- `p ∣ finitePrimeBasisProduct S` for `p ∈ S`;
- `SameSquareAnchorPhase` is equality of `a^2 % M` and `b^2 % M`.

Use a direct congruence descent / `Nat.ModEq` theorem if convenient.  Do not
reprove the finite product machinery.

## 4. Basis-wide local sign profile

Package the previous theorem into a basis-wide predicate if it helps later CRT
work, for example:

```lean
def SameSquarePrimeSignProfile
    (S : Finset ℕ) (a b : ℕ) : Prop :=
  ∀ p ∈ S, SameSquarePrimeSign p a b
```

Then prove:

```lean
theorem sameSquareAnchorPhase_implies_primeSignProfile
    (hS : IsFinitePrimeBasis S)
    (hab : SameSquareAnchorPhase S a b) :
    SameSquarePrimeSignProfile S a b
```

Do **not** prove the converse by full CRT in this checkpoint unless it is truly
one short theorem.  The required A+ result is the global-to-local
factorization.

If a converse falls out cheaply from an existing Mathlib CRT/congruence lemma,
it may be included as an explicitly marked strengthening, but it must not turn
PUU-L017 into a CRT engineering checkpoint.

## 5. Period translation = all-plus profile

For every basis prime, translating the anchor by a whole wheel period should
land in the `+` branch.

Prove a theorem with the meaning:

```text
b = n + k*M
→ for every p ∈ S,
   n ≡ b (mod p).
```

For example:

```lean
theorem period_translation_primeSign_plus
    {S : Finset ℕ}
    (hS : IsFinitePrimeBasis S)
    (n k : ℕ)
    {p : ℕ} (hpS : p ∈ S) :
    ((n : ZMod p) =
      ((n + k * finitePrimeBasisProduct S : ℕ) : ZMod p))
```

Exact coercion spelling may vary.

This theorem should make explicit that PUU-L016 period symmetry corresponds to
an **all-plus** local sign profile.

## 6. Reflection = all-minus profile

For `n ≤ M`, reflection

```text
b = M - n
```

should satisfy, at every basis prime,

```text
b ≡ -n (mod p).
```

Prove a theorem with this meaning, e.g.

```lean
theorem reflection_primeSign_minus
    {S : Finset ℕ}
    (hS : IsFinitePrimeBasis S)
    {n p : ℕ}
    (hn : n ≤ finitePrimeBasisProduct S)
    (hpS : p ∈ S) :
    (((finitePrimeBasisProduct S - n : ℕ) : ZMod p) =
      -(n : ZMod p))
```

or the opposite equality orientation.

Then optionally expose the corresponding `SameSquarePrimeSign` corollary.

This identifies the two PUU-L016 generators:

```text
period translation  → all +
reflection          → all -
```

At `p = 2`, `+` and `-` may coincide; do not claim sign uniqueness.

## 7. Visible regressions

Use the `{2,3}`, `M=6` wheel.

Recommended checks:

```text
1 ↔ 7  : period translation, plus at p=2 and p=3
1 ↔ 5  : reflection, minus at p=2 and p=3
```

For `1 ↔ 5`, modulo `3` this visibly reads `5 ≡ -1`; modulo `2`, plus and minus
coincide.

The regression should go through the general public theorems where practical.

## Outcome A+ rubric

PUU-L017 is A+ if it establishes:

1. a local `±` sign predicate modulo one prime;
2. prime-local square equality iff `+` or `-` sign;
3. global `SameSquareAnchorPhase` descends to the local sign predicate for
   every `p ∈ S`;
4. a basis-wide sign-profile packaging or equivalent theorem;
5. period translation identified as all-plus;
6. reflection identified as all-minus;
7. correct treatment of `p = 2` sign overlap;
8. visible `{2,3}` regression;
9. provider-only facade export and semantic report.

## STOP

Do **not** implement in PUU-L017:

- arbitrary mixed-sign CRT synthesis;
- a bijection between sign assignments and square-phase fibers;
- phase-fiber cardinality such as `2^k`;
- special counting of odd-prime subsets;
- escape existence or `escapingSquareOffsets`;
- Legendre consumer imports;
- Jacobsthal/max-gap bounds;
- PowerSwap;
- GN/CosmicFormula;
- PNT/RH.

The next checkpoint PUU-L018 should ask whether a chosen compatible family of
local signs can be synthesized into a global anchor modulo the product period,
and should handle the `p=2` degeneracy explicitly rather than pretending every
prime contributes two distinct signs.

## Report

Create:

```text
lean/dk_math/docs/dev/NumberTheory-PrimorialUnitUniverse-260827-v0/
  primorial-unit-universe-local-prime-sign-decomposition-260827.md
```

The report should emphasize:

- this is a provider-side factorization of square phase;
- local sign existence is proved, local sign uniqueness is **not** claimed;
- `p=2` is the canonical overlap case;
- CRT synthesis / mixed-sign realizability is intentionally deferred.
