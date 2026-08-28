# PUU-L017 — Local Prime Sign Decomposition

## Scope

PUU-L016 introduced the provider-side square-anchor phase relation.  This
checkpoint extracts its local prime-coordinate content without importing the
Legendre consumer layer.  The implementation is
`DkMath/NumberTheory/PrimorialUniverse/SquareAnchorPrimeSign.lean`, exported by
`DkMath.NumberTheory.PrimorialUniverse`.

The module is intentionally local: it does not synthesize arbitrary mixed
sign assignments by CRT, count phase fibers, or assert any escape existence.

## Local sign dichotomy

The public predicate

```lean
def SameSquarePrimeSign (p a b : ℕ) : Prop :=
  ((a : ZMod p) = (b : ZMod p)) ∨
    ((a : ZMod p) = -(b : ZMod p))
```

records the two local square-root signs.  The theorem

```lean
square_mod_prime_eq_iff_sameSquarePrimeSign
```

proves, for `Nat.Prime p`,

```text
a^2 = b^2 in ZMod p
  ↔ a = b in ZMod p or a = -b in ZMod p.
```

The proof factors the difference of squares in the field `ZMod p`.  The
predicate is symmetric, but no sign uniqueness is claimed.

## Global phase to local signs

For a finite prime basis `S`, the theorem

```lean
sameSquareAnchorPhase_implies_primeSign
```

descends equality of square-anchor residues modulo
`finitePrimeBasisProduct S` to equality of square residues modulo every
`p ∈ S`, and then applies the local prime dichotomy.  The packaged theorem

```lean
sameSquareAnchorPhase_implies_primeSignProfile
```

provides the corresponding basis-wide predicate
`SameSquarePrimeSignProfile`.

This is a provider-side factorization theorem: one global phase determines a
local `+` or `-` choice at each basis prime.  It does not claim that every
choice of local signs is globally realizable.

## Period and reflection generators

The theorem `period_translation_primeSign_plus` makes the PUU-L016 period
translation explicit: if `b = n + k*M`, then `n` and `b` are equal in `ZMod p`
for every basis prime `p`.  Thus period translation is the all-plus profile.

The theorem `reflection_primeSign_minus` proves that for `n ≤ M`,

```text
M - n = -n in ZMod p
```

for every basis prime `p`.  The corollary
`reflection_sameSquarePrimeSign` identifies reflection with the all-minus
profile.  No sign uniqueness is inferred from either theorem.

At `p = 2`, plus and minus can coincide.  This is retained explicitly by
`sameSquarePrimeSign_two_overlap_regression`; it is not treated as a proof
artifact.

## Visible `{2, 3}`, `M = 6` regressions

The module records:

* `period_translation_primeSign_two_three_regression`: `1 ↔ 7` is plus modulo
  both `2` and `3`;
* `reflection_primeSign_two_three_regression`: `1 ↔ 5` is minus modulo both
  `2` and `3`;
* `sameSquarePrimeSign_two_overlap_regression`: modulo `2`, the same pair also
  satisfies both the plus and minus descriptions.

The regressions use the public period/reflection theorems rather than isolated
modular computations.

## Boundary and next checkpoint

PUU-L017 does not implement CRT synthesis, mixed-sign realizability, a
bijection with phase fibers, `2^k` counting, odd-prime subset counting,
escape existence, `escapingSquareOffsets`, Legendre imports, gap bounds,
PowerSwap, GN/CosmicFormula, PNT, or RH.

The result is an independent provider-side local factorization, not a
Legendre provider.  PUU-L018 must handle whether compatible mixed local signs
can be synthesized globally, including the degeneracy at `p = 2`.

## Verification

The focused build succeeded:

```text
lake build DkMath.NumberTheory.PrimorialUniverse.SquareAnchorPrimeSign
```
