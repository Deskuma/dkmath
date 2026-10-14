# Codex instruction-012 — generic prime-power primitive-divisor obstruction

Branch: `research/FLT7-Mod42-AllocationSieve-261013-v0`
Review: `review-011.md` (gate 011 Outcome A accepted)
Implementer: GPT-6.1 Sol (light)

## Mission

Gate 011 proved an infinite exact-sieve-excluded family
`M=2*13^(6+4*k)` using **two different inputs**:

1. A structural result: prime-power ownership plus the
   full-sieve's *actual* quotient coprimality and size guard
   forces an eligible allocation divisor to be 1 or 2.
2. Numerical residue results: the complementary prime power
   is 1 modulo 42 and 4 modulo 5, excluding the respective
   chosen exact receiver branches.

**Separate the structural argument from the specific prime 13.**
Do not merely rename the existing 13 theorem and do not start
a new unrestricted modular search.

## Gate A — generic prime-power divisor restriction

Read actual source and Mathlib first. Proposed export:

```lean
theorem eligible_primitive_divisor_two_prime_pow
    {p n r : ℕ} (hp : Nat.Prime p)
    (hmem : r ∈ (2 * p ^ n).divisors)
    (hcop : Nat.Coprime r ((2 * p ^ n) / r))
    (hsize : 7 ^ 3 * r ^ 7 < 2 * p ^ n) :
    r = 1 ∨ r = 2
```

Use the real chosen divisor, quotient `t=(2*p^n)/r`,
and exact factor identity. Either:

- `p∤r`, whence coprimality with `p^n` and Euclid
  give `r∣2`; or
- `p∣r`, whence the actual `hcop` makes `p∤t`,
  Euclid gives `t∣2`, and then
  `2*p^n=r*t≤2*r≤343*r^7`, contradicting
  `343*r^7<2*p^n`.

This argument should be independent of a global bound
on `p`, `n` or `M`. If `n=0` is valid, keep it.
Do not discard the coprimality guard or replace membership
by a hypothetical factorization without provenance.

You may reuse source from the existing
`eligible_primitive_divisor_two_thirteen_pow`, but do
not change the earlier verified theorem without necessity.

## Gate B — generic *residue-conditional* exact exclusion

Suggested main export:

```lean
theorem sixthPowerSieved_two_prime_pow_excluded
    {p n : ℕ} (hp : Nat.Prime p)
    (h42 : Nat.ModEq 42 (p ^ n) 1)
    (h5 : Nat.ModEq 5 (p ^ n) 4) :
    ¬ SixthPowerSievedNestedCondition (2 * p ^ n)
```

Given an alleged exact full-sieve witness, apply the
generic lemma using **its** `hmem/hcop/hsize`.
Use `nestedAllocation_excluded_of_mod_fortyTwo`
with explicit divisor guard for r=1; use
`nestedAllocation_excluded_of_mod_five_square` for r=2,
normalizing `(2*p^n)/2=p^n`.

The residue assumptions must remain **conditions**,
not be falsely asserted for all primes and exponents.
This theorem should genuinely cover multiple possible
prime bases and powers without an upper bound, while
making no claim that source packets have those cores.

## Regression and independent example

- Specialize the generic theorem at `p=13,
  `n=6+4*k` using the residue theorems or their proof
  from gate 011. Show that this reproduces its old
  unbounded family; do not duplicate all prior proof code.
- Independently check `p=223, n=2` in Lean:
  `Nat.Prime 223`, `223^2≡1 (mod 42)`,
  `223^2≡4 (mod 5)`, `M=2*223^2=99458`.
  This gives a new fixed-core no-exact-sieve example
  via the generic theorem.
- If useful, also check the **eligible** divisor r=2
  at M=99458: membership, actual quotient coprimality
  and `343*2^7<99458`. This ensures the example is not
  merely a vacuous size case. Do not infer any
  exact receiver witness or an independent sixth-power
  sieve witness from eligibility alone.

A small test countermodel to dropping `hcop` can
simply reuse gate 011's `r=13, n=10` result.
No need to reproduce another huge finite enumeration.

## Compare real mathematical strength

Explain whether the proposed generic result follows
from **structural prime-power allocation** plus
**already-proved modular/centered image exclusions**,
rather than restating an exact receiver premise.

Identify what remains unresolved for composite s with
several **distinct** prime bases: primitivity can assign
whole prime powers to different sides, so the eligible
divisor set may include factors other than 1 and 2.
Do not assume the prime-power classification applies
to such s.

Do not claim the generic statement excludes *all* M
or any actual FLT7 source packet, or proves FLT7.
The missing same-packet carrier-to-chart link from
gate 005 remains open.

## Verification, records and stop

Reuse:
- `SevenRamifiedFusionThirteenPowerPrimitiveExclusion`;
- `SevenRamifiedFusionSixthPowerAllocationSieve`;
- `SevenRamifiedFusionModFortyTwoAllocationSieve`;
- `SevenRamifiedFusionGeneralGapModFiveImage`;
- relevant Mathlib prime/coprime/Euclid lemmas.

Codex chooses the minimal new source module, actual
imports, proof tactics and focused validation procedure.
No broad refactoring or gratuitous new framework.

For every new production export, run `#print axioms`
and record actual build/test exit status; reject
`sorryAx`, new axioms, `sorry`, `admit` or unsafe
substitutes.

Write `findings-012.md`, `report-012.md` and
`evidence/012-verification-summary.md` only with
compact relevant evidence and explicit provenance.
`logs/` is disposable.

**Codex implements, tests and reports only. Do NOT
git stage/add, commit, push, create a branch,
open a PR or merge. Stop after gate 012.**

Outcome A: kernel-checked generic primitive-divisor theorem,
residue-conditional exact exclusion, and a distinct
prime-base regression.
Outcome B: a narrower correct theorem or a precise
missing hypothesis with proof evidence.
Outcome C: a false target or rigorously diagnosed blocker.
