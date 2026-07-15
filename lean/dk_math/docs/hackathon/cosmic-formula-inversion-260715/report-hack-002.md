# Report — Checkpoint hack-002

## Status

```text
COMPLETED
```

## Session Metadata

```text
Checkpoint: hack-002
Session class: IMPLEMENTATION
Model: GPT-5 Codex
End: 2026/07/15 07:49 JST
```

## Primary Goal

Implement the minimal natural-number facade for finite-set prime escape: a
fresh-prime-factor predicate, supplied-divisor exclusion, and an existence
corollary.

## Files Changed

Checkpoint implementation files:

- `DkMath/Hackathon/FinitePrimeEscape.lean`
- `docs/hackathon/cosmic-formula-inversion-260715/report-hack-002.md`

Implementation-confirmed correction:

- `docs/hackathon/cosmic-formula-inversion-260715/EXISTING_DKMATH_MAP.md`

The map correction changes the ring-only unqualified `dvd_add_right` audit
entry to the actual Nat declaration `Nat.dvd_add_iff_right`, including its
correct implication orientation.

The pre-existing `hack-001` map and report changes remained in the working
tree and were not reverted.

## Definition Added

```lean
def FreshPrimeFactor (S : Finset ℕ) (n q : ℕ) : Prop :=
  Nat.Prime q ∧ q ∣ n ∧ q ∉ S
```

This predicate means exactly that `q` is a prime divisor of `n` outside the
finite reference set `S`.

## Theorems Added

```lean
theorem prime_dvd_product_add_coprime_not_mem
    {S : Finset ℕ} {u q : ℕ}
    (hcop : Nat.Coprime (∏ p ∈ S, p) u)
    (hqPrime : Nat.Prime q)
    (hqDiv : q ∣ (∏ p ∈ S, p) + u) :
    q ∉ S
```

```lean
theorem exists_fresh_prime_factor
    {S : Finset ℕ} {u : ℕ}
    (hcop : Nat.Coprime (∏ p ∈ S, p) u)
    (hboundary : 1 < (∏ p ∈ S, p) + u) :
    ∃ q, FreshPrimeFactor S ((∏ p ∈ S, p) + u) q
```

The requested names and binder shapes were retained.

## Imports

The implementation uses narrow imports:

```lean
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Data.Nat.Prime.Basic
```

No unfinished DkMath sample or prohibited primitive-factor, Petal, Zsigmondy,
KUS, Units, CosmicCompletion, or Demo module is imported.

## Exact Mathlib Declarations Reused

- `Finset.dvd_prod_of_mem (f) (ha : a ∈ s) :
  f a ∣ ∏ i ∈ s, f i`
- `Nat.dvd_add_iff_right (h : k ∣ m) :
  k ∣ n ↔ k ∣ m + n`
- `Nat.dvd_gcd : k ∣ m → k ∣ n → k ∣ Nat.gcd m n`
- `Nat.Coprime`, definitionally supplying `Nat.gcd m n = 1`
- `Nat.Prime.not_dvd_one : Nat.Prime q → ¬ q ∣ 1`
- `Nat.ne_one_iff_exists_prime_dvd :
  n ≠ 1 ↔ ∃ p, Nat.Prime p ∧ p ∣ n`
- `Nat.ne_of_gt : 1 < n → n ≠ 1`

## Actual Proof Route

For the kernel theorem, assume `q ∈ S`. Product membership gives
`q ∣ ∏ p ∈ S, p`. The reverse direction of `Nat.dvd_add_iff_right` removes
that known addend from the boundary divisibility and yields `q ∣ u`.
`Nat.dvd_gcd` then makes `q` divide the gcd. Coprimality rewrites the gcd to
`1`, contradicting `Nat.Prime.not_dvd_one`.

For existence, `hboundary` gives boundary `≠ 1`.
`Nat.ne_one_iff_exists_prime_dvd` supplies `q`, its primality, and its boundary
divisibility. The kernel theorem supplies `q ∉ S`, completing
`FreshPrimeFactor`.

The proof remains entirely in `ℕ`; no subtraction or integer bridge is used.

## Assumption Audit

The theorem surface contains only the required assumptions:

- `Nat.Coprime (∏ p ∈ S, p) u` for exclusion;
- `Nat.Prime q` and boundary divisibility for a supplied witness;
- `1 < (∏ p ∈ S, p) + u` only for prime-divisor existence.

It does not assume:

- every member of `S` is prime;
- `S.Nonempty`;
- `0 < u`;
- `0 < ∏ p ∈ S, p`.

These assumptions are mathematically unnecessary for this exact facade.

## Verification

Focused build:

```text
$ lake build DkMath.Hackathon.FinitePrimeEscape
✔ [726/726] Built DkMath.Hackathon.FinitePrimeEscape
Build completed successfully (726 jobs).
```

The first build exposed the exact orientation of
`Nat.dvd_add_iff_right`: the proof needed `.mpr`, not `.mp`. After correcting
that elaboration issue, the focused build passed.

No-sorry check:

```text
rg -n "\bsorry\b|\badmit\b|\baxiom\b" \
  DkMath/Hackathon/FinitePrimeEscape.lean
```

Result: no matches.

Repository checks:

```text
git diff --check
```

Result: passed with no output.

`git status --short` was inspected. The only new checkpoint changes are the
permitted source, report, and implementation-confirmed map correction; the
accepted `hack-001` documentation changes were already present.

## Mathematical Meaning

A prime factor of the completed boundary cannot be one of the numbers already
multiplied into `P` when `P` is coprime to the offset. If the boundary is
greater than one, at least one such fresh prime factor exists.

## Meaning Boundary

The result proves finite-set freshness only. It does not assert:

- sequence-relative primitive-divisor status;
- uniqueness of the fresh prime factor;
- that every outside prime divides the boundary;
- infinitude of primes;
- any Cosmic Formula, projection, DkReal, or geometric statement.

## First Genuine Obstruction

```text
none
```

The initial `.mp`/`.mpr` mismatch was a local API-orientation repair, not a
mathematical obstruction.

## Next Permitted Action

```text
Wise Wolf review of checkpoint hack-002.
```

## Stop Confirmation

```text
The checkpoint stopped after the finite-prime facade and report.
No Cosmic Formula implementation was begun.
No demo, projection, DkReal, visualization, or hack-003 work was begun.
```
