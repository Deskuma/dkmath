# Provenance

## A. Mathematical source

The following is transcribed only from existing repository records, principally
`docs/BookOfMagic/0001_三重魔核と一意性解除.md`:

```text
Author or account name: Levent Alpöge (@__alpoge__)
Title or post description: X post announcing the explicit map
Publication date: Not yet fixed in repository records
Exact URL: https://x.com/__alpoge__/status/2079028340955197566
Date accessed: Not yet fixed in repository records
```

The repository note says “2026-07-20 頃” (approximately 2026-07-20), but that
is not an exact publication date and is therefore not promoted into the field
above. No historical-priority claim is made beyond this available record.

## B. DkMath formal verification

DkMath independently formalizes the polynomial definitions, the three explicit
evaluations, the formal partial derivatives, the `3 × 3` determinant, the
rational-to-complex coefficient transport, the determinant-one output
normalization, and the noninjectivity and no-left-inverse consequences. These
proofs are checked by Lean 4 + Mathlib.

The formal verification establishes the stated algebraic formulas; it does not
certify authorship, publication status, priority, or external review.

## C. Interpretation added by DkMath

`UniqueGap`, `GapCrystal`, `forgetGap`, and `GNFiniteDifference` are DkMath
interpretation layers and are not attributed to the mathematical source claim.
Likewise, scaling the first output coordinate by `-1/2` is a presentation
normalization used by DkMath to obtain determinant `1`.
