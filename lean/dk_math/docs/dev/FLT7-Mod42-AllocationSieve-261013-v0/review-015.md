# Review 015 — Outcome A accepted; from mod-13 to seventh-power permutation primes

Date: 2026-10-14
Research branch: `research/FLT7-Mod42-AllocationSieve-261013-v0`
Reviewed implementation: `bdb3932e9ebdad2f97c24a282a863536a8ba14c5`

## Review decision

**ACCEPTED — Outcome A.** Reviewed the actual published production
`DkMath/FLT/Seven/SevenRamifiedFusionSmallCoefficientPrimeSupport.lean`,
its DkMathTest module, `findings-015.md`, `report-015.md` and
`evidence/015-verification-summary.md`.

Production added precisely these three facts:

1. `eligible_primitive_divisor_smallCoefficient_prime_not_dvd`.
   For any prime p, c≤7^3, actual divisor membership, coprimality
   with `(c*p^n)/r`, and the strict `7^3*r^7<c*p^n` condition,
   `p∤r` holds for **all n**, including zero.
2. `eligible_smallCoefficient_prime_in_complement`.
   If n>0 under those same guards, `p|((c*p^n)/r)` as well.
3. `sixthPowerSieved_smallCoefficient_thirteen_pow_excluded`.
   For all c≤343 and n>0 the **entire exact full sieve** is false
   at `M=c*13^n`, by the already-checked mod-13 centered-image
   theorem using the actual same r and complementary quotient.

The proof is stronger than merely `r|c` from gate 014.
It rejects the entire `p|r` branch via Euclid and
`M=r*t≤c*r≤343*r≤343*r^7<M`, then uses actual
factorization for the complementary support. It does
**not** assume `Coprime c p`. This matters for c=13,
which has a nonvacuously eligible r=1 example in DkMathTest.

Regression at c=3,n=12 simultaneously has a cheap
r=3 allocation and an independent sixth-power sieve
candidate, but **no exact full-sieve allocation**.
The coefficient-divisibility-only countermodel is
correctly distinguished from an actual eligible
allocation counterexample. Tests cover c=0,1,3,13,343;
the n=0 complementary-support theorem is not claimed.

The implementer reported successful focused Lake build and
final test (exit 0), with only
`[propext, Classical.choice, Quot.sound]`
among axioms for all three exports and three audited tests.
No `sorryAx` was reported. Reviewer read source/evidence,
but **did not independently run Lean**.

## Scientific boundary

The theorem concerns abstract core values `c*13^n`,
not actual realization by
`RamifiedSignedRootRoutingPacket`. There is no theorem
that all source cores have such a factorization and
c≤343. The gate-005 source/real-pair/endpoint bridge
remains missing. No unconditional FLT7 proof follows.

## New structural observation: why mod 13 works

The actual sextic satisfies a polynomial identity
over any commutative ring:

```text
2*D*F(D,q) = (q+D)^7 - (q-D)^7,
F(D,q)=7*q^6+35*D^2*q^4+21*D^4*q^2+D^6.
```

If ℓ is an **odd prime** and the seventh-power map
on `ZMod ℓ` is injective, then
`ℓ∤D` and `F(D,q)≡0 (mod ℓ)` would imply
`(q+D)^7=(q-D)^7`, hence `q+D=q-D`,
so `2D=0`, a contradiction.

The seventh-power map on the nonzero field elements
is a permutation precisely when
`gcd(7,ℓ-1)=1`. With ℓ odd this is a
candidate general criterion for universal
nonvanishing of the centered sextic at ℓ-unit D.
The proof should be carried out in Lean; the ring
identity and finite-field power-injectivity are
not yet checked as repository theorems.

This suggests replacing the specific modulus 13 by
a structurally described **class of primes**.
For a chosen exact allocation, take
`D=7^27*r^49` and `s=M/r`.
If ℓ is prime, odd, ℓ≠7,
`Nat.Coprime 7 (ℓ-1)`,
`ℓ∤r` and `ℓ|s`, then ℓ∤D and
the exact centered scalar equation should be impossible.

In combination with gate 015's prime-side avoidance
for small coefficients, a future general corollary
may exclude `c*ℓ^n` (c≤343,n>0) for
each such ℓ. This is **not yet a Lean theorem**.

## Explicit arithmetic diagnostics — only exact integer prechecks

A separate JavaScript BigInt evaluation, not a formal
proof, verified:

- ℓ=11, D=1 has **no zero** of F(D,q)
  for q in all 11 residue classes.
- ℓ=13 likewise has no zero, consistent with gate 013.
- ℓ=29, D=1 has zeros:
  `F(1,5)≡0 (mod29)`, among other q.
  Here `29≡1 (mod7)` and
  `gcd(7,28)=7`, so the injectivity criterion fails.
- ℓ=2 is excluded from the generic argument:
  `F(1,1)=64` is even, and 2 cannot be cancelled
  from `2D*F`.

The p=29 and p=2 cases prevent careless claims that
every prime modulus has unit-gap nonvanishing.
They are **tests of a candidate criterion**, not
an assertion that the criterion is necessary in
every general algebraic context.

## Gate 016: separate algebra from FLT7 carrier provenance

Authorize `instruction-016.md` to verify the
seventh-power difference identity, prove (or localize
a missing Mathlib lemma for) the odd-prime
permutation criterion, and transport to the exact
receiver with support hypotheses. A concrete
modulus 11 regression is desirable. A small-
coefficient whole-core result for ℓ=11 is optional
and conditional on a verified generic no-image
theorem, not a precondition for acceptance.

**No new source-packet realization, arbitrary-M
receiver-emptiness, or FLT7 conclusion.**
After this gate, reassess whether future research
should return to the gate-005 same-packet source bridge
instead of indefinitely broadening arithmetic filters.

Codex handles implementation, focused build,
tests, axiom audit, findings/report/evidence only.
**No Git stage/commit/push, branch creation,
PR or merge.** Wise Wolf publishes reviewed
instructions; user retains integration decisions.
`logs/` disposable, `evidence/` compact with
proof provenance.
