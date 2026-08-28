# PUU-L019 — Coprime Square-Phase Fiber / Odd-Prime Sign Cardinality

## Goal

PUU-L018 proved that every local Boolean sign assignment is realizable by some anchor below the finite prime-basis period, but deliberately did not claim uniqueness.  This checkpoint identifies the exact situation in which the local signs become independent coordinates: the **base anchor is coprime to the finite prime-basis period**.

For such an anchor, every odd basis prime contributes two genuinely distinct choices `+a` and `-a`; the prime `2` contributes only one because the two signs coincide modulo `2`.

The target is the exact finite cardinality

```text
|square phase fiber of a modulo M(S)| = 2 ^ |S.erase 2|
```

under

```text
IsFinitePrimeBasis S
Nat.Coprime a (finitePrimeBasisProduct S)
```

This is provider-side square-phase geometry only.  Do not import the Legendre consumer layer.

## Preferred module

```text
DkMath/NumberTheory/PrimorialUniverse/SquareAnchorPhaseFiber.lean
```

Import:

```lean
import DkMath.NumberTheory.PrimorialUniverse.SquareAnchorPrimeSignCRT
```

Export it through `DkMath.NumberTheory.PrimorialUniverse`.

## 1. One-period square-phase fiber

Define the finite fiber of anchors in one period, preferably:

```lean
def squareAnchorPhaseFiber (S : Finset ℕ) (a : ℕ) : Finset ℕ :=
  (Finset.range (finitePrimeBasisProduct S)).filter
    (fun b => SameSquareAnchorPhase S a b)
```

Provide the exact membership theorem:

```lean
@[simp] theorem mem_squareAnchorPhaseFiber ... :
  b ∈ squareAnchorPhaseFiber S a ↔
    b < finitePrimeBasisProduct S ∧
    SameSquareAnchorPhase S a b
```

The empty basis must remain valid: `M = 1`, so the fiber consists of the unique residue `0`.

## 2. Coprime base anchor excludes zero local coordinates

Under

```lean
hcop : Nat.Coprime a (finitePrimeBasisProduct S)
```

prove a reusable local fact for every `p ∈ S`:

```text
p ∤ a
```

or equivalently

```text
(a : ZMod p) ≠ 0.
```

Use the existing theorem that every basis prime divides `finitePrimeBasisProduct S`.

This theorem is the reason the two square roots are distinct at every odd basis prime.

## 3. Odd-prime sign exclusivity

For `p ∈ S`, `p ≠ 2`, and coprime base anchor, prove that the plus and minus descriptions cannot both hold.

A suitable public theorem shape is:

```lean
theorem primeSign_plus_ne_minus_of_coprime_anchor
    {S : Finset ℕ} (hS : IsFinitePrimeBasis S)
    {a p : ℕ}
    (hcop : Nat.Coprime a (finitePrimeBasisProduct S))
    (hpS : p ∈ S)
    (hp2 : p ≠ 2) :
    (a : ZMod p) ≠ -(a : ZMod p)
```

Equivalent formulations are fine.

The proof may use either:

- `a = -a → 2*a = 0`, then primality / `p ≠ 2` / `p ∤ a`; or
- field cancellation in `ZMod p`.

Do not claim sign exclusivity at `p = 2`.

## 4. Canonical odd-prime sign signature

Package the actual minus coordinates of a fiber element.  A Finset signature is preferred:

```lean
noncomputable def squareAnchorMinusPrimeSet
    (S : Finset ℕ) (a b : ℕ) : Finset ℕ :=
  (S.erase 2).filter
    (fun p => ((b : ZMod p) = -(a : ZMod p)))
```

Provide membership in the expected form:

```text
p ∈ squareAnchorMinusPrimeSet S a b
↔ p ∈ S ∧ p ≠ 2 ∧ b = -a in ZMod p
```

Exact syntactic shape may follow Lean convenience.

For a fiber member `b`, PUU-L017 gives `+` or `-` at each basis prime.  Under the coprime-anchor hypothesis and `p ≠ 2`, sign exclusivity makes this signature canonical.

## 5. Signature determines a fiber representative

Prove that within one period and the same square phase, equal odd-prime minus signatures force equal anchors:

```lean
theorem squareAnchorPhaseFiber_eq_of_minusPrimeSet_eq
    {S : Finset ℕ} (hS : IsFinitePrimeBasis S)
    {a b c : ℕ}
    (hcop : Nat.Coprime a (finitePrimeBasisProduct S))
    (hb : b ∈ squareAnchorPhaseFiber S a)
    (hc : c ∈ squareAnchorPhaseFiber S a)
    (hsig : squareAnchorMinusPrimeSet S a b =
      squareAnchorMinusPrimeSet S a c) :
    b = c
```

Intended proof structure:

1. for every odd `p ∈ S`, equal signatures plus local sign dichotomy force `b = c` in `ZMod p`;
2. for `p = 2`, any two elements in the same square phase have the same residue because `+` and `-` coincide there;
3. combine all local congruences modulo the prime product;
4. use `b < M` and `c < M` to turn congruence modulo `M` into equality.

Equivalent proof organization is fine.

## 6. Every subset of odd basis primes is realized

For any

```lean
T ⊆ S.erase 2
```

construct a sign choice where exactly the primes in `T` receive the minus sign, then invoke PUU-L018 CRT synthesis.

For example:

```lean
sigma p := decide (p ∉ T)
```

or an equivalent Boolean convention.

Prove existence of `b` with:

```text
b ∈ squareAnchorPhaseFiber S a
squareAnchorMinusPrimeSet S a b = T
```

under the coprime-anchor hypothesis.

The equality of signatures requires odd-prime sign exclusivity: a `+` coordinate must not accidentally also satisfy the `-` predicate.

A suitable theorem shape is:

```lean
theorem exists_phaseFiber_anchor_with_minusPrimeSet
    {S : Finset ℕ} (hS : IsFinitePrimeBasis S)
    {a : ℕ}
    (hcop : Nat.Coprime a (finitePrimeBasisProduct S))
    {T : Finset ℕ}
    (hT : T ⊆ S.erase 2) :
    ∃ b,
      b ∈ squareAnchorPhaseFiber S a ∧
      squareAnchorMinusPrimeSet S a b = T
```

## 7. Exact cardinality theorem — main target

Use Sections 5 and 6 to identify the phase fiber with the powerset of the odd-prime basis `S.erase 2`.

An explicit `Equiv` is welcome if it is clean, but is not required.  `Finset.card_bij`, injections/surjections, or another finite-cardinality route is acceptable.

Required public theorem:

```lean
theorem squareAnchorPhaseFiber_card_of_coprime_anchor
    {S : Finset ℕ}
    (hS : IsFinitePrimeBasis S)
    {a : ℕ}
    (hcop : Nat.Coprime a (finitePrimeBasisProduct S)) :
    (squareAnchorPhaseFiber S a).card =
      2 ^ (S.erase 2).card
```

This must include the degenerate cases correctly:

```text
S = ∅       -> card = 1
S = {2}     -> card = 1
2 ∉ S       -> card = 2 ^ S.card
```

Do not replace the exact `S.erase 2` formula by an informal `2^(k-1)` unless the required membership assumptions are explicit.

## 8. Optional corollaries

If short and stable, useful corollaries are:

```text
2 ∉ S -> fiber.card = 2 ^ S.card
```

and, under `2 ∈ S`,

```text
fiber.card = 2 ^ (S.card - 1)
```

These are optional.  The canonical theorem remains the `S.erase 2` formula.

It is also useful, but optional, to prove that every member of a coprime-anchor phase fiber is itself coprime to the period.

## 9. Visible regressions

Required visible regression for the `30`-wheel:

```text
S = {2,3,5}
M = 30
base anchor a = 1
phase fiber = {1,11,19,29}
card = 4 = 2^2
```

The exact Finset equality is preferred if Lean remains simple; otherwise prove membership of the four residues plus the cardinality theorem.

Also useful:

```text
S = {2,3}
M = 6
fiber of 1 = {1,5}
card = 2
```

At least one regression should flow through the general cardinality theorem rather than isolated `decide` only.

## Outcome A+ rubric

PUU-L019 is A+ if it establishes:

1. one-period square-phase fiber + membership theorem;
2. coprime base anchor excludes zero local coordinates;
3. odd-prime `+/-` exclusivity, with no false uniqueness at `p=2`;
4. canonical odd-prime minus-sign signature;
5. equal signatures imply equal fiber representatives;
6. every subset of `S.erase 2` is realized by a fiber representative;
7. exact cardinality `2 ^ (S.erase 2).card`;
8. visible `M=30`, base `1`, cardinal `4` regression;
9. provider facade export and semantic report.

## STOP

Do not introduce in this checkpoint:

- arbitrary-anchor fiber cardinality without the coprime hypothesis;
- multiplicities for primes dividing the anchor;
- higher prime powers;
- Legendre / `escapingSquareOffsets` / square-shell escape conclusions;
- Jacobsthal or max-gap bounds;
- PowerSwap;
- GN/CosmicFormula;
- PNT/RH.

The next structural question after PUU-L019 is how the phase-fiber cardinality changes when a fresh prime is inserted into the basis, and how that doubling interacts with the wheel projection tower.  That should be a later checkpoint, not folded into this one.

## Report

Create:

```text
lean/dk_math/docs/dev/NumberTheory-PrimorialUnitUniverse-260827-v0/
  primorial-unit-universe-coprime-square-phase-fiber-cardinality-260827.md
```

The report must distinguish:

- local sign **realizability** from PUU-L018;
- local sign **distinctness** under the coprime-anchor hypothesis;
- the special degeneration at prime `2`;
- exact fiber cardinality versus any later escape/existence application.
