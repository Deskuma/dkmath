# PUU-L018 — Mixed Prime-Sign CRT Synthesis

## Scope

PUU-L017 extracted a local `+`/`-` sign at each basis prime from a global
square-anchor phase.  PUU-L018 proves the converse and realizes arbitrary
chosen local signs by finite CRT.  The implementation is
`DkMath/NumberTheory/PrimorialUniverse/SquareAnchorPrimeSignCRT.lean`,
exported by `DkMath.NumberTheory.PrimorialUniverse`.

The module remains provider-side and does not import the Legendre consumer
layer.

## Local-to-global factorization

The theorem

```lean
primeSignProfile_implies_sameSquareAnchorPhase
```

combines the square congruence at each prime in a finite basis using
pairwise-prime coprimality and `Nat.modEq_and_modEq_iff_modEq_mul`.  The empty
basis is handled explicitly: its product is `1`, so equality modulo the
product is automatic.

Together with PUU-L017, this gives the exact factorization:

```lean
sameSquareAnchorPhase_iff_primeSignProfile
```

That is,

```text
equal square phase modulo the basis product
  <->
local +/- square-root sign at every basis prime.
```

The signs are existence data, not unique labels.

## Chosen sign assignments

The lightweight predicate

```lean
RealizesPrimeSignChoice S sigma a b
```

uses `sigma : ℕ → Bool`: `true` selects `b = a` modulo a basis prime and
`false` selects `b = -a`.  The theorem
`realizesPrimeSignChoice_implies_primeSignProfile` converts a chosen profile
to the unsigned `SameSquarePrimeSignProfile` vocabulary.

## CRT synthesis

The theorem

```lean
exists_anchor_lt_period_realizing_primeSignChoice
```

constructs `b` with

```text
b < finitePrimeBasisProduct S
```

and the requested local sign choice.  The proof is a Finset induction.  At an
inserted prime it combines the new residue with the recursively synthesized
residue using `Nat.chineseRemainder`; the bound is supplied by
`Nat.chineseRemainder_lt_mul`.  The empty basis returns `b = 0 < 1` and the
choice condition is vacuous.

The central combined theorem is

```lean
exists_sameSquareAnchorPhase_realizing_primeSignChoice
```

which shows that the synthesized representative is in the same square phase
as the base anchor.  This is an existence / realizability result, not a
bijection.

## Degeneracy boundary

No sign uniqueness or injectivity is claimed.  In particular, modulo `2`,
`+a` and `-a` coincide; the same can happen modulo an odd prime when the
anchor is zero modulo that prime.  Different Boolean assignments may therefore
produce the same global representative.

## Visible mixed-sign regression

`mixedPrimeSign_two_three_five_regression` uses the basis `{2, 3, 5}` with
period `30`, base anchor `1`, and the assignment `(+,+,-)`.  It verifies the
concrete representative `b = 19 < 30`, so that

```text
19 ≡  1 (mod 2)
19 ≡  1 (mod 3)
19 ≡ -1 (mod 5).
```

The same-phase conclusion is derived through the public local-to-global
factorization theorem rather than by treating the square congruence as an
isolated regression fact.

## Boundary and next checkpoint

This checkpoint does not implement phase-fiber cardinality, a bijection with
sign assignments, `2^k` counting, odd-prime subset counting, coprime-anchor
fiber counts, escape existence, `escapingSquareOffsets`, Legendre reductions,
gap bounds, PowerSwap, GN/CosmicFormula, PNT, or RH.

The next structural question is when different sign assignments are distinct.
Under a coprime-anchor hypothesis, odd primes should contribute distinct signs,
while `p = 2` remains degenerate; that counting problem belongs to PUU-L019.

## Verification

The focused build succeeded:

```text
lake build DkMath.NumberTheory.PrimorialUniverse.SquareAnchorPrimeSignCRT
```
