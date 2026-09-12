# CGE-001 report

## Scope

Implemented the fixed-even-fiber certification endpoint from
`instruction-001.md`.  The implementation does not provide a survivor and
does not assert Strong Goldbach.

## Files

- Added `DkMath/NumberTheory/Goldbach/CrossGapEscape.lean`.
- Added `DkMathTest/NumberTheory/GoldbachCrossGapEscapeAudit.lean`.
- Updated `DkMath/NumberTheory/Goldbach.lean` to export the new module.

## Production theorems

- `crossLeft_le_even_target_of_fiber`
- `crossRight_le_even_target_of_fiber`
- `crossGap_not_prime_pair_iff_obstructed`
- `crossGapSurvives_iff_prime_pair`
- `goldbachPairAt_of_crossGapSurvives`

`CrossGapEvenFiberAt` retains `(d₁, x₁, u₁, d₂, x₂, u₂)`, requires
`pairedBig = 2*n`, and records `2 ≤ crossLeft` and `2 ≤ crossRight`.
These hypotheses yield both endpoint upper bounds through the CGE-000
conservation theorem.

`CrossGapProperObstructed` excludes endpoint equality with the divisor, so a
prime endpoint is not falsely classified as obstructed.  Under the exact
fixed-even-fiber hypotheses,
`crossGap_not_prime_pair_iff_obstructed` establishes failure of the prime pair
iff existence of a member of `goldbachSmallPrimes n` obstructing one endpoint.

`crossGapSurvives_iff_prime_pair` then obtains the exact certification bridge
without placing `Nat.Prime` in the survivor predicate.  Finally,
`goldbachPairAt_of_crossGapSurvives` returns the two Cross-Gap endpoints as a
local `GoldbachPairAt n` witness.  No survivor-existence provider is proved.

No off-diagonal primitive/ABC corollary was added; the diagonal case remains
explicitly allowed.

## Regression and firewall checks

The audit proves `25 + 27 = 52` with `Nat.Coprime 25 27` while both endpoints
are not prime, and proves `3 + 3 = 6` with non-coprime prime endpoints.  It
also replays the full-coordinate configuration
`(d₁,x₁,u₁,d₂,x₂,u₂) = (1,2,1,1,2,1)`, whose outputs are `3` and `3`, on the
even fiber `2*3`, including the survivor and one-hole bridge.

## Verification

Focused build command:

```text
lake build DkMath.NumberTheory.Goldbach DkMathTest.NumberTheory.GoldbachCrossGapEscapeAudit
```

The focused build and audit `#print axioms` checks passed.  The axiom output
contains no `sorryAx` and no newly introduced axiom.

The public facade was also checked with:

```text
lake build DkMath
```

It completed successfully (9843 jobs).  The forbidden-construct grep over the added
implementation and audit files found no `sorry`, `admit`, `native_decide`,
`unsafe`, or new `axiom` declaration.

## Outcome

**Outcome A — EXACT CROSS-GAP CERTIFICATION BRIDGE.**

The exact finite obstruction-to-prime-pair endpoint and the one-hole
`GoldbachPairAt` bridge are production theorems.  This is certification-side
progress only; the next required ingredient is a nontrivial provider proving
that every relevant fixed even fiber has at least one Cross-Gap survivor.
