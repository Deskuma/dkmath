# PUU-L020 — Fresh-Prime Square-Phase Fiber Cover / Doubling Law

## Goal

PUU-L019 proved that a coprime square-anchor phase fiber has cardinality

```text
2 ^ (S.erase 2).card.
```

PUU-L020 should upgrade that global count to a **nested finite-cover theorem**
under a fresh-prime extension.  The important statement is not merely that the
cardinality doubles: for a fresh odd prime `q`, every old phase-fiber anchor
should have exactly two enlarged phase-fiber anchors above it, corresponding
to the two local signs modulo `q`.

This is provider-side finite congruence geometry only.  Do not import the
Legendre consumer layer.

## Module

Preferred new module:

```text
DkMath/NumberTheory/PrimorialUniverse/SquareAnchorPhaseFiberProjection.lean
```

Import:

```lean
import DkMath.NumberTheory.PrimorialUniverse.SquareAnchorPhaseFiber
```

Export through `DkMath.NumberTheory.PrimorialUniverse`.

## 1. Projection of an enlarged phase fiber

Reuse the existing old-period projection

```lean
primeBasisWheelProjection S x = x % finitePrimeBasisProduct S
```

rather than introducing a second modulo map.

Prove that a member of the enlarged phase fiber projects to a member of the old
phase fiber.  A theorem shape such as the following is preferred:

```lean
theorem enlargedPhaseFiber_projects_to_old
    {S : Finset ℕ}
    (hS : IsFinitePrimeBasis S)
    {q a x : ℕ}
    (hq : Nat.Prime q)
    (hqS : q ∉ S)
    (hx : x ∈ squareAnchorPhaseFiber (insert q S) a) :
    primeBasisWheelProjection S x ∈ squareAnchorPhaseFiber S a
```

Equivalent hypotheses / orientation are acceptable.

This theorem does not require an escape or Legendre hypothesis.

## 2. Projection fiber

Package the enlarged phase-fiber anchors lying above one old representative,
for example:

```lean
noncomputable def squareAnchorPhaseProjectionFiber
    (S : Finset ℕ) (q a b : ℕ) : Finset ℕ :=
  (squareAnchorPhaseFiber (insert q S) a).filter
    (fun x => primeBasisWheelProjection S x = b)
```

Provide the exact membership theorem.

Interpretation:

```text
squareAnchorPhaseFiber (insert q S) a
                ↓ mod M(S)
squareAnchorPhaseFiber S a
```

## 3. Fresh-prime CRT lift above a fixed old anchor

Assume:

```text
hS   : IsFinitePrimeBasis S
hq   : Nat.Prime q
hqS  : q ∉ S
hcop : Nat.Coprime a (finitePrimeBasisProduct (insert q S))
hb   : b ∈ squareAnchorPhaseFiber S a
```

Use CRT with the two local conditions

```text
x ≡ b   (mod M(S))
x ≡ +a  (mod q)
```

and

```text
x ≡ b   (mod M(S))
x ≡ -a  (mod q)
```

to construct representatives below

```text
finitePrimeBasisProduct (insert q S) = q * M(S).
```

For `q ≠ 2`, prove the two representatives are distinct.  The coprime-anchor
hypothesis implies `q ∤ a`; therefore `+a ≠ -a` in `ZMod q` for an odd prime.

Do not identify the two CRT representatives by an implementation-specific
closed formula; keep the theorem semantic.

## 4. Exact two-sheet fiber for a fresh odd prime

Main local theorem:

```lean
theorem card_squareAnchorPhaseProjectionFiber_fresh_odd
    {S : Finset ℕ}
    (hS : IsFinitePrimeBasis S)
    {q a b : ℕ}
    (hq : Nat.Prime q)
    (hqS : q ∉ S)
    (hq2 : q ≠ 2)
    (hcop : Nat.Coprime a (finitePrimeBasisProduct (insert q S)))
    (hb : b ∈ squareAnchorPhaseFiber S a) :
    (squareAnchorPhaseProjectionFiber S q a b).card = 2
```

Equivalent theorem packaging is fine, including an explicit two-element
Finset equality if that is cleaner.

The converse classification must be exact: every enlarged phase-fiber anchor
above `b` is one of the two CRT sign lifts.  Do not prove only `≥ 2`.

## 5. Surjectivity and doubling law

Corollary: for fresh odd `q`, projection from the enlarged phase fiber onto the
old phase fiber is surjective.

Then prove the global cardinality recurrence:

```lean
theorem squareAnchorPhaseFiber_card_insert_fresh_odd
    {S : Finset ℕ}
    (hS : IsFinitePrimeBasis S)
    {q a : ℕ}
    (hq : Nat.Prime q)
    (hqS : q ∉ S)
    (hq2 : q ≠ 2)
    (hcop : Nat.Coprime a (finitePrimeBasisProduct (insert q S))) :
    (squareAnchorPhaseFiber (insert q S) a).card =
      2 * (squareAnchorPhaseFiber S a).card
```

Prefer deriving this from the exact projection-fiber structure if convenient.
Using PUU-L019's cardinality formula as a cross-check or short corollary is
also acceptable, but the **two-sheet local fiber theorem is the primary new
content**.

## 6. The prime `2` degeneracy

Do not force a false two-sheet theorem at `q = 2`.

At minimum prove the cardinality branch:

```text
fresh q = 2  -> no new sign degree
```

for a coprime anchor, i.e. insertion of `2` leaves the phase-fiber cardinality
unchanged.

A stronger exact one-sheet projection-fiber theorem for `q = 2` is welcome if
short and stable, but it is not required for A+.

The combined growth law should be described as:

```text
fresh q = 2    : ×1
fresh odd q    : ×2
```

## 7. Visible regressions

Use the base anchor `a = 1`.

Preferred tower:

```text
S = {2,3}, M = 6
fiber = {1,5}

insert q = 5
M' = 30
fiber = {1,11,19,29}
```

Under projection modulo `6`, verify the two fibers:

```text
1 <- {1,19}
5 <- {11,29}
```

Each has cardinality `2`.

This is the phase-fiber analogue of PUU-L009's nested wheel projection, but do
not conflate the two fiber sizes:

```text
wheel survivor fresh-q fiber : q - 1
square-phase fresh odd-q fiber: 2
```

## Outcome A+ rubric

PUU-L020 is A+ if it establishes:

1. enlarged phase-fiber projection lands in the old phase fiber;
2. a public projection-fiber Finset + membership theorem;
3. fresh odd-prime CRT `+/-` lifts above every old fiber anchor;
4. exact local projection-fiber cardinality `2` for fresh odd `q` under the
   coprime-anchor hypothesis;
5. projection surjectivity;
6. global fresh-odd-prime doubling law;
7. explicit `q = 2` no-new-sign-degree boundary at least at cardinality level;
8. `6 -> 30` regression with the two two-element projection fibers;
9. provider facade export and semantic report.

## STOP

Do **not** introduce in PUU-L020:

- Legendre imports or escape-existence claims;
- arbitrary-anchor phase-fiber cardinality;
- prime-power moduli;
- wheel-gap / Jacobsthal bounds;
- a comparison theorem claiming the `q-1` survivor replication and `2`
  phase replication force an escape;
- PowerSwap, GN/CosmicFormula, PNT, or RH.

The next mathematical question after L020 is whether the two independent
fresh-prime growth laws

```text
survivor wheel: ×(q-1)
phase fiber   : ×2
```

can be related through the moving square-shell reservation pattern without
reintroducing the anti-relabeling frontier detected in PUU-L015.

## Report

Create:

```text
lean/dk_math/docs/dev/NumberTheory-PrimorialUnitUniverse-260827-v0/
  primorial-unit-universe-fresh-prime-square-phase-fiber-cover-260828.md
```

The report must distinguish clearly between:

- the exact two-sheet local projection structure for fresh odd primes;
- the degenerate fresh prime `2` branch;
- the global cardinality doubling corollary;
- and the fact that none of these results by themselves imply square-shell
  escape existence.
