# GCNB-003R implementation report

## Result

Outcome A — the public cyclotomic linear-factor Norm = GN theorem is now
unconditional in the base parameter `u`.

The canonical public API is:

```lean
cyclotomicLinearFactor_norm_eq_GN_ratCast hζ
cyclotomicLinearFactor_norm_eq_GN hζ
```

The previous nonzero-base results remain available as compatibility lemmas:

```lean
cyclotomicLinearFactor_norm_eq_GN_ratCast_of_ne_zero hζ hu0
cyclotomicLinearFactor_norm_eq_GN_of_ne_zero hζ hu0
```

The carrier is unchanged and still represents

```text
(x + u) - ζ * u
```

in the ring of integers. The exported integer identity is

```text
Algebra.norm ℤ carrier = ((GN p x u : Nat) : Int).
```

## `u = 0` boundary

The new canonical theorem splits on `u = 0`.

For the zero-base branch, the carrier reduces to the natural-number scalar
`x`. The field norm is computed by `Algebra.norm_algebraMap` and the prime
cyclotomic field rank
`Module.finrank ℚ K = p - 1`. Independently, the `u = 0` GN value is proved
from `GTail_one_eq_sum`: all terms except the `p - 1` term vanish, and the
remaining coefficient is `Nat.choose p p = 1`. The field result is then
transported to the integer norm with `Algebra.coe_norm_int`.

The nonzero-base branch delegates to the previously established
ratio/evaluation bridge. No ratio is used in the zero-base branch.

## Scope boundary

The implementation remains prime-only and uses the neutral CFBRC/cyclotomic
and Mathlib NumberField APIs. It does not add ideals, valuations,
principalization, TraceOne, FLT packets, Kummer imports, or any composite-degree
cyclotomic identification.

No `sorry`, `admit`, `sorryAx`, new axiom, or `unsafe` proof construct was
introduced.

## Regression coverage

`DkMathTest/CFBRC/CyclotomicNorm.lean` checks:

- the canonical integer Norm theorem for `CyclotomicField p ℚ` at `p = 3, 5, 7`
  with `u = 1`;
- the same theorem at `p = 3, 5, 7` with `x = 1, u = 0`;
- the optional `(x, u) = (0, 0)` boundary at `p = 3`;
- the existing root-product, shell, GN, and GTail boundary identities;
- `#print axioms` for the canonical Norm and root-product APIs.

## Validation

The following validation commands were run:

```text
lake build DkMath.CFBRC.CyclotomicNorm
lake build DkMathTest.CFBRC.CyclotomicNorm
lake build DkMath.CFBRC
lake build DkMath
git diff --check
git diff --no-index --check /dev/null DkMathTest/CFBRC/CyclotomicNorm.lean  # exit 1: differences present, no whitespace error
git diff --no-index --check /dev/null docs/dev/GTail-Cyclotomic-Norm-Bridge-260922-v0/report-001.md  # exit 1: differences present, no whitespace error
```

The forbidden-token scan over the changed Lean proof files found no forbidden
proof construct. The two `git diff --no-index --check` commands return the
normal nonzero status because the compared paths differ from `/dev/null`; they
emit no whitespace error.
The full-project build still reports the pre-existing
`DkMath/NumberTheory/ZsigmondyCyclotomicResearch.lean:147` `sorry` warning;
that research file is outside this checkpoint.
