# Codex instruction-016 — seventh-power permutation primes and the centered sextic's nonzero image

Branch: `research/FLT7-Mod42-AllocationSieve-261013-v0`
Reviewer: `review-015.md` (Outcome A accepted)
Implementer: GPT-6.1 Sol (light)

## Mathematical question

Gate 015 verified that a prime power `p^n`,
with coefficient c≤343 and n>0, lies entirely on
the complementary side of any eligible primitive
allocation. Gate 013's *mod-13* nonvanishing then
excluded the whole exact sieve for c*13^n.

Why exactly does the centered sextic not vanish
modulo 13? The likely structural mechanism is
**injectivity of the seventh-power map on a finite field**.
Determine a valid generic theorem without demanding
a false claim for all primes.

## Gate A — a genuine ring identity, no modular guess

For the actual polynomial

```text
F(D,q) = 7*q^6 + 35*D^2*q^4 + 21*D^4*q^2 + D^6
```

the formal difference-of-powers identity is

```text
(q+D)^7 - (q-D)^7 = 2*D*F(D,q).
```

Over `ℤ` or any commutative ring this follows from
`ring` after unfolding the actual `centeredSevenSextic`
and casting to the target ring.

Do **not** use natural subtraction `q-D` as though
it were ring subtraction. Use `ℤ`/`ZMod ℓ` or
a generic commutative ring.

Prove the identity as a reusable lemma or use it
locally to establish the following candidate
nonvanishing theorem.

## Gate B — permutation-prime nonvanishing

Proposed precise natural-number API:

```lean
theorem centeredSevenSextic_not_dvd_of_seven_power_permutation
    {ℓ D q : ℕ}
    (hp : Nat.Prime ℓ)
    (hodd : ℓ ≠ 2)
    (hcop : Nat.Coprime 7 (ℓ - 1))
    (hD : ¬ ℓ ∣ D) :
    ¬ ℓ ∣ centeredSevenSextic D q
```

This is **not yet Lean checked**.

At the level of `ZMod ℓ`, prove or reuse:
if the prime ℓ has `gcd(7,ℓ−1)=1`,
then `x↦x^7` is injective on the full field,
including zero. In a finite field, its nonzero
multiplicative group has order ℓ−1. Use a
Mathlib injectivity/permutation theorem, a
finite-group argument or Bezout exponents.
Then:

- assume `F(D,q)=0` mod ℓ, `D≠0`;
- the difference identity gives equal seventh powers
  of `q+D` and `q−D`;
- injectivity yields `q+D=q−D`;
- hence `2D=0`, impossible because ℓ is odd
  and `D≠0`.

Do not divide by a possibly zero `D`, and do
not claim the nonvanishing theorem follows from
`ring` alone.

If Mathlib lacks the exact general injectivity lemma,
prefer a small mathematically correct helper rather
than silently postulating it. An independently
checked version for one new prime (e.g. ℓ=11) can
be Outcome B if the generic group argument is
a substantial unresolved dependency.

## Gate C — FLT7 exact receiver support transport

For the actual centered gap
`D=7^27*r^49` and target `448*s^49`,
a suitable explicit prime-support consumer is:

```lean
theorem nestedAllocation_excluded_of_permutation_prime_support
    {ℓ M r : ℕ}
    (hp : Nat.Prime ℓ)
    (hodd : ℓ ≠ 2)
    (hnot7 : ℓ ≠ 7)
    (hcop : Nat.Coprime 7 (ℓ - 1))
    (hr : ¬ ℓ ∣ r)
    (hs : ℓ ∣ M / r) :
    ¬ (NestedGNAllocationCondition M r ∨
       NestedRHSAllocationCondition M r)
```

The modulus must not divide the fixed `7^27`
factor: hence retain `ℓ≠7` when converting
`ℓ∤r` into `ℓ∤D`. Keep oddness `ℓ≠2`.
The given `ℓ|s` ensures the target is zero
modulo ℓ. Use the **existing**
`nestedAllocation_iff_centered` and preserve
the exact chosen r and s=M/r.
Do not change receiver definitions or assume
an exact endpoint exists.

If a different factoring makes the proof
cleaner, adapt the API while retaining every
real mathematical premise.

## Gate D — concrete regressions and sharp counterexample

Check kernel-verified examples:

1. `ℓ=13`: specialize the generic theorem to
   recover gate-013 nonvanishing, preferably
   without editing the previous production file.
2. `ℓ=11`: `Nat.Prime 11`, `11≠2,7` and
   `gcd(7,10)=1`. Show for any D,q with
   `11∤D`, the centered sextic is nonzero
   modulo 11. At r=1,s=11 or another
   simple supported chosen divisor, exclude
   the exact receiver. If the generic consumer
   is proved, an optional all-c≤343,n>0
   full-sieve exclusion at M=c*11^n can
   be derived by reusing gate-015's
   `eligible_smallCoefficient_prime_in_complement`.
3. `ℓ=29`: **the unrestricted version is false**.
   Independent BigInt exact-residue precheck:
   `F(1,5)≡0 (mod29)`. Here
   `29≡1 (mod7)` and
   `Nat.Coprime 7 (29−1)` fails.
   Fix a concrete Lean counterexample in DkMathTest
   to show why the permutation premise matters.
4. `ℓ=2`: `F(1,1)=64` is even, so the
   oddness condition matters in this identity proof.

Prior prechecks are **not** Lean proofs. Check
the actual polynomial and these numerals in Lean
before recording them as verification.

## Optional general family / limits

Only *if* Gates A–C succeed, it is useful to
derive the conditional all-coefficient prime-power
schema

```lean
theorem sixthPowerSieved_smallCoefficient_permutation_prime_excluded
    {c ℓ n : ℕ}
    (hp : Nat.Prime ℓ) (hodd : ℓ ≠ 2)
    (hnot7 : ℓ ≠ 7)
    (hcop : Nat.Coprime 7 (ℓ - 1))
    (hc : c ≤ 7 ^ 3) (hn : 0 < n) :
    ¬ SixthPowerSievedNestedCondition (c * ℓ ^ n)
```

Use actual full-sieve hmem/hcop/hsize, the
gate-015 coefficient support bridge, and the
same-r exact receiver consumer. Don't make
this optional corollary a prerequisite for
a correct, verified core polynomial result.

This generic criterion is a **sufficient**
image obstruction for a class of primes, not
a proof that every prime satisfies it.
Do not claim the boundary ℓ≡1(mod7) is
always an exact receiver witness merely
because modular zeros exist.

## Scientific stopping line

All such exclusions concern **abstract**
`SixthPowerSievedNestedCondition` on special
M. They neither show which M are actual
`internalDepthFourSeventhCore` of real
`RamifiedSignedRootRoutingPacket`, nor
construct an exact endpoint, nor prove FLT7.
The missing same-packet carrier/real-pair/chart
bridge from gate 005 remains an independent
research frontier.

After this gate, recommend whether to prioritize
that source-side bridge instead of generating
further modular sieve families. Do not start
gate 017.

## Verification and deliverables

Read source/index first:
- `SevenRamifiedFusionCenteredPolynomial`,
  `CenteredThirteenSupport` and `SmallCoefficientPrimeSupport`;
- `SevenRamifiedFusionSixthPowerAllocationSieve`
  and its actual witness fields;
- relevant Mathlib finite-field, ZMod,
  power-injective and coprimality APIs.

Minimal production code and DkMathTest checks,
focused Lean build and explicit `#print axioms`
for every exported declaration. No `sorryAx`,
new axioms, `sorry`, `admit` or unsafe proof
substitutes. Keep exact provenance (precheck
versus kernel proof) and build/test exit statuses.

Write `findings-016.md`, `report-016.md`,
and a compact `evidence/016-verification-summary.md`
when material checks were performed. `logs/`
temporary/ignored; no raw transcript archive.

**Codex implements, verifies and reports only.
No Git add/stage/commit/push, branch creation,
PR or merge. Stop after 016 and return for review.**

Outcome A: general algebraic/permutation-prime
nonvanishing and exact receiver consumer,
with distinct ℓ=11 and failure-case tests.
Outcome B: narrower Lean-checked structural
lemma and precise missing bridge.
Outcome C: a falsified proposal or documented
obstruction, with honest partial results.
