# PUU-L018 — Mixed Prime-Sign CRT Synthesis / Global Square-Phase Reconstruction

## Goal

PUU-L017 proved the provider-side descent

```text
global square-anchor phase
  -> local +/- sign at every basis prime.
```

PUU-L018 closes the converse and then proves realizability of arbitrary mixed
local sign choices by CRT.

The checkpoint has two layers:

1. **local-to-global factorization** for an already given pair of anchors
   `a,b`;
2. **mixed-sign synthesis**: given a base anchor `a` and a sign assignment on
   the finite prime basis, construct a representative `b < M(S)` realizing
   those local signs.

This remains provider-side.  Do not import `DkMath.NumberTheory.Legendre`.

## Preferred module

```text
DkMath/NumberTheory/PrimorialUniverse/SquareAnchorPrimeSignCRT.lean
```

Import at least:

```lean
import DkMath.NumberTheory.PrimorialUniverse.SquareAnchorPrimeSign
```

Use Mathlib CRT / `Nat.ModEq` APIs as convenient.  In particular,
`Nat.modeq_and_modeq_iff_modeq_mul` is a natural route for the finite-basis
induction.

Export the module through `DkMath.NumberTheory.PrimorialUniverse`.

## 1. Converse: local sign profile implies global square phase

Prove the converse of PUU-L017:

```lean
theorem primeSignProfile_implies_sameSquareAnchorPhase
    {S : Finset ℕ}
    (hS : IsFinitePrimeBasis S)
    {a b : ℕ}
    (hprofile : SameSquarePrimeSignProfile S a b) :
    SameSquareAnchorPhase S a b
```

Suggested mathematical proof:

- for every `p ∈ S`, `SameSquarePrimeSign p a b` gives
  `a^2 ≡ b^2 [MOD p]` via
  `square_mod_prime_eq_iff_sameSquarePrimeSign`;
- combine congruences over the finite product using distinct-prime coprimality;
- conclude equality modulo `finitePrimeBasisProduct S`.

A `Finset` induction using pairwise coprimality and
`Nat.modeq_and_modeq_iff_modeq_mul` is preferred if clean.

Handle the empty basis correctly: product `1`, vacuous profile, global phase
trivial modulo `1`.

## 2. Exact global/local factorization theorem

Package PUU-L017 and the converse as:

```lean
theorem sameSquareAnchorPhase_iff_primeSignProfile
    {S : Finset ℕ}
    (hS : IsFinitePrimeBasis S)
    {a b : ℕ} :
    SameSquareAnchorPhase S a b ↔
      SameSquarePrimeSignProfile S a b
```

This is the main structural theorem of the first half of PUU-L018.

Meaning:

```text
same square phase modulo product of basis primes
  <->
for every basis prime p, anchors differ by a local +/- sign modulo p.
```

Do **not** interpret the sign as unique.

## 3. Explicit sign assignment

Introduce a small provider-side representation of a chosen local sign profile.
A simple shape is preferred, for example:

```lean
def RealizesPrimeSignChoice
    (S : Finset ℕ) (sigma : ℕ → Bool) (a b : ℕ) : Prop :=
  ∀ p ∈ S,
    if sigma p then
      ((b : ZMod p) = (a : ZMod p))
    else
      ((b : ZMod p) = -(a : ZMod p))
```

Equivalent polarity/orientation is fine.  Keep the type lightweight; do not
build a large dependent sign structure unless Lean requires it.

Provide the obvious bridge:

```text
RealizesPrimeSignChoice S sigma a b
  -> SameSquarePrimeSignProfile S a b
```

under `IsFinitePrimeBasis S` if needed.

## 4. Mixed-sign CRT synthesis

For any finite prime basis, base anchor, and sign assignment, construct a
representative in one global period:

```lean
theorem exists_anchor_realizing_primeSignChoice
    {S : Finset ℕ}
    (hS : IsFinitePrimeBasis S)
    (sigma : ℕ → Bool)
    (a : ℕ) :
    ∃ b : ℕ,
      b < finitePrimeBasisProduct S ∨ finitePrimeBasisProduct S = 1 ∧ b = 0 ∧
      RealizesPrimeSignChoice S sigma a b
```

The exact theorem shape above may be adjusted to avoid awkward precedence and
to handle the empty basis cleanly.  A preferred semantic shape is:

```text
∃ b < M, RealizesPrimeSignChoice ...
```

for nonempty `S`, plus a separate empty-basis theorem/regression if that is
cleaner.

An even cleaner public API is acceptable:

```lean
theorem exists_anchor_lt_period_realizing_primeSignChoice
    {S : Finset ℕ}
    (hS : IsFinitePrimeBasis S)
    (hSne : S.Nonempty)
    (sigma : ℕ → Bool)
    (a : ℕ) :
    ∃ b < finitePrimeBasisProduct S,
      RealizesPrimeSignChoice S sigma a b
```

and then treat `S = ∅` separately.

Use CRT over the pairwise-coprime prime moduli.  A `Finset` induction is fine:

```text
old synthesized residue modulo M_T
+ new target residue modulo fresh prime p
-> CRT residue modulo p * M_T.
```

Do not make a specific Mathlib CRT constructor part of the semantic API.

## 5. Synthesized anchor lies in the same square phase

From the realization theorem and the exact factorization theorem, provide:

```lean
theorem exists_sameSquareAnchorPhase_realizing_primeSignChoice ... :
  ∃ b < finitePrimeBasisProduct S,
    RealizesPrimeSignChoice S sigma a b ∧
    SameSquareAnchorPhase S a b
```

for nonempty basis, or an equivalent clean theorem shape.

This theorem is the central CRT-synthesis result:

```text
arbitrary mixed local +/- choices
        ↓ CRT
one global anchor residue b
        ↓
same square-anchor phase as a.
```

## 6. Degeneracy boundary

Do not prove uniqueness or injectivity of sign assignments.

Important reasons:

- modulo `2`, `+a` and `-a` always coincide;
- for any odd basis prime `p` with `p ∣ a`, `+a` and `-a` also coincide modulo
  `p`.

Therefore different Boolean sign assignments may synthesize the same global
anchor residue.

The correct PUU-L018 result is **existence / realizability**, not a bijection.

## 7. Visible mixed-sign regression

Use the `{2,3,5}` basis (`M = 30`) and base anchor `a = 1`.

A useful explicit mixed-sign example is:

```text
b = 19
19 ≡  1 (mod 2)
19 ≡  1 (mod 3)
19 ≡ -1 (mod 5)
19^2 ≡ 1^2 (mod 30)
```

Thus `1` and `19` have the same square-anchor phase even though the local sign
profile is genuinely mixed across the odd primes.

Another valid visible witness is `b = 11` with minus at `3` and plus at `5`.
One mixed-sign regression is enough for A+.

Prefer to derive the same-phase conclusion through the public factorization /
synthesis theorems rather than only `norm_num` on squares modulo `30`.

## Outcome A+ rubric

PUU-L018 is A+ if it establishes:

1. `SameSquarePrimeSignProfile -> SameSquareAnchorPhase`;
2. exact iff between global phase and basis-wide local sign profile;
3. an explicit lightweight chosen-sign predicate;
4. arbitrary mixed sign choice is CRT-realizable in one global period;
5. the synthesized residue is in the same square-anchor phase;
6. empty-basis handling is mathematically correct;
7. no sign uniqueness / injectivity claim;
8. a visible `{2,3,5}`, `M=30` mixed-sign regression;
9. provider facade export and report.

## STOP

Do **not** implement in PUU-L018:

- phase-fiber cardinality;
- a bijection between sign assignments and phase-fiber elements;
- `2^k` counting;
- odd-prime subset counting;
- coprime-anchor fiber cardinality;
- escape existence;
- `escapingSquareOffsets`;
- Legendre imports or reductions;
- Jacobsthal/max-gap bounds;
- PowerSwap;
- GN/CosmicFormula;
- PNT/RH.

The natural next checkpoint, if PUU-L018 closes cleanly, is to determine when
sign assignments are distinct.  Under a coprime-anchor hypothesis, all odd
basis primes give distinct `+/-` roots while prime `2` remains degenerate,
suggesting the later fiber count

```text
2 ^ ((S.erase 2).card)
```

when `2 ∈ S`, or equivalently one binary degree of freedom per odd basis prime.
That counting theorem belongs to PUU-L019, not this checkpoint.

## Report

Create:

```text
lean/dk_math/docs/dev/NumberTheory-PrimorialUnitUniverse-260827-v0/
  primorial-unit-universe-mixed-prime-sign-crt-synthesis-260827.md
```

The report must distinguish:

- local factorization of an already given phase pair;
- CRT synthesis of an arbitrary chosen sign assignment;
- existence from uniqueness;
- `p=2` / zero-residue sign degeneracy;
- no Legendre or escape claim.
