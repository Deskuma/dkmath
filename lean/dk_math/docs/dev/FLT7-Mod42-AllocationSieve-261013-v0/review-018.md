# Review 018 — source valuation readout accepted; no independent core restriction

Date: 2026-10-14
Research branch: `research/FLT7-Mod42-AllocationSieve-261013-v0`
Reviewed implementation HEAD: `2ce78718834bd0453ddc43152fad9bb8a7331508`

## Decision

**Outcome A — formalization accepted. Strategic outcome: no independent source-core obstruction obtained.** The precise distinction matters: this gate proved useful same-packet statements but did not close the source/frontier.

Reviewed actual committed source
`DkMath/FLT/Seven/SevenRamifiedFusionSourcePrimeValuationLedger.lean`,
the matching DkMathTest, `findings-018.md`, `report-018.md`,
`source-valuation-frontier-018.md`, and
`evidence/018-verification-summary.md`.

Three exported source-indexed declarations:

1. `internalDepthFour_source_outerRoots_coprime p`:
   source-only `Nat.Coprime V C`, using the existing
   `vertical_coprime_compensation_residual` and
   `compensationCore_eq`, **not** assuming new coprimality.
2. `internalDepthFour_source_prime_valuation_balance p hℓ hdiv`:
   for prime ℓ dividing the **actual** core M,
   extract the actual positive complementary N;
   `Coprime M N`, `M*N=V*C`, `ℓ∤N` and
   `padicValNat ℓ M = padicValNat ℓ V + padicValNat ℓ C`.
   Nonzero factors are supplied for valuation additivity.
3. `internalDepthFour_source_prime_exclusive_valuation p hℓ hdiv`:
   source `Coprime V C` makes the entire ℓ multiplicity
   belong to one factor V or C, with the other ℓ-free.

The test's `M=4,N=1,V=C=2` arithmetic countermodel
correctly shows that a product identity plus
`Coprime M N` alone does **not** establish
`Coprime V C`; the countermodel is not a
`RamifiedSignedRootRoutingPacket`.
The test also compares `Nat.factorization`, positivity,
support and zero conventions.

Codex-reported focused build exited 0 (9087 jobs)
and final DkMathTest exited 0; an initial calibration
and an initial test failed for alias/API issues, then
were corrected. Each production export and the
countermodel has only
`[propext, Classical.choice, Quot.sound]`,
no `sorryAx`. Reviewer inspected real source and
evidence but **did not independently rerun Lean**.

## What changed, what did not

This is a useful source-provenance-preserving
readout of existing facts. The valuation equation
does not restrict the set of possible primes,
bound a residual coefficient by 343, or identify a
new natural center, chart divisor or endpoint.

The exclusive ownership adds the **existing independent
source coprimality** `Coprime V C`; it cannot be
deduced from the two-line scalar ledger alone.
But no new independent mathematical restriction on
M was obtained beyond the already established source
facts. Gate-017's missing constructive
same-packet source→primitive additive endpoint
remains missing.

The next gate must not promote the ownership
bookkeeping itself into a claim of FLT7 progress
or keep adding tautological re-expression APIs.

## Proposed falsifiability test for the scalar-only ledger

An independent **arithmetic planning** example is:

```text
M=29^2=841, N=1, V=841, C=1.
M*N=V*C.
Coprime M N and Coprime V C.
7∤M, 7∤N; all factors positive.
```

Only prime 29 divides M; it is **not** a
seventh-power permutation prime since
`gcd(7,29-1)=7`. The gate-016 small-coefficient
conditional sieve cannot be invoked for this M
using a good prime divisor. This does **not**
assert an exact receiver for 841 or a packet
with this core. It only shows that the *displayed
scalar ledger constraints* themselves do not force
the prime support condition needed by gate 016.
A Lean kernel-checked scalar model can make this
separation explicit at low cost.

What remains mathematically relevant is a possible
**independent constraint** coming from actual
quadratic coordinates, canonical split,
signed real cubic norm identities, valuation
depth, or phase/orientation data: something
which cannot be freely satisfied by the above
scalar numbers and which would genuinely
restrict actual M.

Source checked in prior gates includes:
`innerRoot_coordinates_isCoprime`,
`inner_secondCoordinate_product_eq`,
`signedRootGap_seventhPower_eq`,
`sourceDifference_eq_normalizedAxis_pow_six_mul_pow_seven`,
`internalDepthFourCarrier_eq_seven_pow_four_mul_core_pow`
and `realPair...` load/gcd facts. These
are meaningful constraints on distinct source objects;
the ledger test must **not** pretend to model them.

## Gate 019 authorization

Authorize `instruction-019.md` as a narrow
**source-intrinsic constraint discrimination audit**,
not another ledger restatement and not a new
modulus sieve.

The task is to check the scalar separation example,
then inspect **actual** independent source
coordinate/norm constraints for a warranted
new implication about the actual core M.
Prefer one precisely stated candidate and
an honest negative result to an inflated theorem.
No new endpoint existence or core factorization
may be assumed.

If no independent restriction is found, explicitly
recommend a strategic pause and reframe the
research rather than automatically assigning
another sequence of small gates.

Codex implements/checks/reports only:
**no Git stage/add/commit/push, branch, PR or merge**.
