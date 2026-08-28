# PUU-L035 Fresh-Prime Positive First-Hit Persistence / Deletion-Delay Law

## Scope

This checkpoint remains provider-side finite reservation arithmetic.  It studies
the positive first-hit coordinate under insertion of a fresh prime and does
not introduce `SquareCell`, `SquareOffset`, a `2*n` shell width, Legendre
consumers, Jacobsthal machinery, quantitative delay bounds, or analytic
claims.

## Reservation classification

The new module
`DkMath.NumberTheory.PrimorialUniverse.SquareAnchorOffsetFreshPrimeFirstHitTransport`
exports:

- `reservedByPrimeBasis_insert_fresh_iff`, which splits enlarged reservation
  into old reservation or fresh-prime divisibility;
- `reservedByPrimeBasis_mono_insert`;
- `not_reserved_insert_fresh_iff_of_not_reserved_old`;
- `isFinitePrimeBasis_insert_fresh`.

The first-hit proofs use the old search interval `1 ≤ t ≤ M` and the enlarged
interval `1 ≤ t ≤ q*M` separately.  The periods are related only through the
product identity for fresh insertion.

## First-hit transport

The following public results were added:

```text
H⁺_S(n) ≤ H⁺_(insert q S)(n)

H⁺_(insert q S)(n) = H⁺_S(n)
  ↔ ¬ q ∣ (n² + H⁺_S(n))

q ∣ (n² + H⁺_S(n))
  → H⁺_S(n) < H⁺_(insert q S)(n)
```

The converse strict-delay equivalence is also exposed.  The persistence proof
uses the raw square-shell reservation equivalence, while monotonicity uses the
fact that every old-reserved smaller positive offset remains reserved after
insertion.

The successor-pair coordinate is monotone pointwise, and its finite radius is
monotone across the enlarged period `M → q*M`.  No claim is made that the
pair-radius gain itself is monotone.

## Required `30 → 210` regression

For `S = {2,3,5}`, `M = 30`, and fresh `q = 7`:

| case | result |
|---|---|
| `n=1`, old basis | `H⁺_30(1) = 6` and `1²+6 = 7` is divisible by `7` |
| `n=1`, enlarged basis | `H⁺_210(1) = 10`, showing strict deletion delay |
| `n=11`, old basis | `H⁺_30(11) = 6` and `11²+6 = 127` is not divisible by `7` |
| `n=11`, enlarged basis | `H⁺_210(11) = 6`, showing persistence |
| pair radius | `PairRadius({2,3,5}) = 5`, `PairRadius({2,3,5,7}) = 7` |
| pair witness | at `n=1`, enlarged `H⁺(1)=10`, `H⁺(2)=7`, hence pair value `7` |

The projection witnesses `11² mod 30 = 1` and `12² mod 30 = 24` are included
in the exported regression theorem.

## Verdict

**Outcome A — FRESH-PRIME DELETION-DELAY LAW FOUND.**

Basis growth does not move an old first hit arbitrarily: it preserves that hit
unless the newly inserted prime deletes the exact raw seat, and deletion then
forces a strict forward delay.  This is provider information beyond the
single-basis first-hit statistics and is not a universal quantitative bound.

## Validation

The target module was validated with:

```text
lake build DkMath.NumberTheory.PrimorialUniverse.SquareAnchorOffsetFreshPrimeFirstHitTransport
```

The facade import and docstring were updated in
`DkMath.NumberTheory.PrimorialUniverse`.
