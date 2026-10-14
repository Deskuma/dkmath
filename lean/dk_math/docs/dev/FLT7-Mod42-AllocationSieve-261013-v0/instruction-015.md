# Codex instruction-015 — avoid the power prime in every eligible small-coefficient allocation

Branch: `research/FLT7-Mod42-AllocationSieve-261013-v0`
Based on `review-014.md` (Outcome A accepted)
Implementer: GPT-6.1 Sol (light)

## One structural goal

Gate 014 proved r∣c for eligible primitive allocations
of M=c*p^n, p prime and c≤343. Read its actual proof:
the entire p∣r branch is contradictory under the
coarse size guard and quotient coprimality.

Strengthen this to an **explicit prime-base avoidance**
theorem and combine it with the gate-013 mod13 centered
image obstruction. The intended advance is from
M=3*13^n to **all M=c*13^n with c≤343 and n>0**.

This proposal is NOT yet Lean-verified. Check exact
definitions/theorems and revise if a claimed premise
or inference is insufficient.

## Required source inspection

- `SevenRamifiedFusionSmallCoefficientPrimePowerOwnership`:
  `eligible_primitive_divisor_smallCoefficient_prime_pow`.
  Reuse or factor its p∣r contradiction; do not
  unnecessarily refactor previously verified code.
- `SevenRamifiedFusionCenteredThirteenSupport`:
  `nestedAllocation_excluded_of_thirteen_support`.
- `SevenRamifiedFusionSixthPowerAllocationSieve`:
  exact `SixthPowerSievedNestedCondition` and its
  real membership, quotient coprimality, size, GN/RHS fields.
- Existing Mathlib `Nat.Prime.dvd_mul`,
  `Nat.Coprime`, power divisibility and quotient
  identities.
- `SevenRamifiedFusionDepthFourReconstructionAudit`
  and `internalDepthFourReconstruction_iff_sixth_power_sieved`
  only for a thin *optional* conditional source corollary.

Check theorem index and real declarations for
duplicates before new code.

## Gate A — rule out p on the chosen divisor side

Suggested theorem API, preserve the actual hypotheses:

```lean
theorem eligible_primitive_divisor_smallCoefficient_prime_not_dvd
    {c p n r : ℕ}
    (hp : Nat.Prime p) (hc : c ≤ 7 ^ 3)
    (hmem : r ∈ (c * p ^ n).divisors)
    (hcop : Nat.Coprime r ((c * p ^ n) / r))
    (hsize : 7 ^ 3 * r ^ 7 < c * p ^ n) :
    ¬ p ∣ r
```

The proof in gate 014 already shows why p∣r is
impossible: let t=(c*p^n)/r; coprimality
forces p∤t, Euclid forces t∣c,
and membership yields c*p^n=r*t.
Since c≤343, t≤343, so
c*p^n≤343*r≤343*r^7,
contradicting the strict guard.

Pay attention to c=0, n=0, r=0 edge cases.
An inconsistent eligibility premise can discharge a
branch, but do not add unnecessary positivity axioms.
The coefficient 343 bound is a visible hypothesis,
not a conclusion for arbitrary c.

**Important:** gate 014's conclusion `r∣c` alone
does not prove p∤r when p∣c.
Obtain p∤r from the actual discarded branch,
not from unwarranted relative primality of c and p.

## Gate B — the power prime lives in the actual complement

Under n>0, the factor identity makes p divide M.
Combined with Gate A and the prime divisibility law,
`p∣(M/r)` follows.

Possible bridge API:

```lean
theorem eligible_smallCoefficient_prime_in_complement
    {c p n r : ℕ}
    (hp : Nat.Prime p) (hc : c ≤ 7 ^ 3) (hn : 0 < n)
    (hmem : r ∈ (c * p ^ n).divisors)
    (hcop : Nat.Coprime r ((c * p ^ n) / r))
    (hsize : 7 ^ 3 * r ^ 7 < c * p ^ n) :
    ¬ p ∣ r ∧ p ∣ (c * p ^ n) / r
```

Use the **same** allocation r and actual quotient.
The conclusion is meaningful even when p∣c;
do not require `Nat.Coprime c p`. A unit
complement or r=0 cannot be assumed.

If it is cleaner, Gate B can be a single theorem
and Gate A private. Prefer smallest helpful public API.

## Gate C — broad mod13 exact full-sieve exclusion

The main proposed theorem is

```lean
theorem sixthPowerSieved_smallCoefficient_thirteen_pow_excluded
    {c n : ℕ} (hc : c ≤ 7 ^ 3) (hn : 0 < n) :
    ¬ SixthPowerSievedNestedCondition (c * 13 ^ n)
```

Assume a full-sieve witness, extract its actual
hmem/hcop/hsize and the same-r exact GN/RHS
disjunction. With p=13, use Gate B to get
`13∤r` and `13∣(c*13^n)/r`.
Then invoke the previously **kernel-checked**
`nestedAllocation_excluded_of_thirteen_support`
to reject both exact receiver branches.

This should not need mod42, a list of divisors of c,
specific c≡1 mod anything, an upper bound on n,
or a literal sixth-power witness.

Check genuinely different coefficients:
`c=1`, `c=3` (recover gate 014),
`c=13` (prime divides the coefficient!),
`c=343` (boundary), at positive exponents.
A c=0 case can be tested as a vacuous consequence
of impossible size, not a source-packet witness.

Optionally prove the n=0 corollary by a separate
trivial size contradiction for c≤343, and then an
all-n version. Do not assert p∣quotient at n=0
without independent support.

## Gate D — nontrivial mathematical contrast

- Recover the earlier `3*13^12` full-sieve exclusion
  without a special case-by-case r1/r3 proof.
- Import gate 013 test evidence only into **test**
  code if checking cheap/sixth-power passage at
  c=3,n=12. Do not assume uniform cheap passage
  for all c,n, and never import DkMathTest into production.
- Show that the new broad result really covers
  coefficients divisible by 13 (e.g. c=13)
  despite `r∣c` not alone guaranteeing p∤r.
- Record the reason a bound c≤343 is sufficient,
  and distinguish that fact from optimality.
  Gate 014 checked a countermodel after dropping
  the bound altogether; no maximality theorem
  is claimed.

If an intermediate theorem is false, provide
a concrete counterexample and correct the route
instead of making assumptions stronger just to
close the goal.

## Scope and boundaries

This would prove an entire infinite **two-parameter**
class of abstract cores c*13^n (bounded c,
unbounded n) has no exact full-sieve receiver.
It does not establish that any such value occurs as
an actual `internalDepthFourSeventhCore p`,
nor that every possible core has a 13 factor
with quotient ≤343. The source/chart gap from
gate 005 remains open; no unconditional FLT7
claim is permitted.

Acceptance:
- A: kernel-checked prime-side avoidance and
  actual-complement support, followed by full
  exact-sieve exclusion for all c≤343,n>0;
- B: a narrower proven theorem with first gap
  identified;
- C: a falsified proposal or documented blocker.

## Deliverables / verification / stop

Implement minimal new production module(s),
focused DkMathTest checks and `#print axioms`
for new exports. No `sorryAx`, new axioms,
`sorry`, `admit` or unsafe proof substitutes.
Codex decides imports, proof tactics and build method.

Write `findings-015.md` and `report-015.md`,
plus concise `evidence/015-verification-summary.md`
with precise build exit statuses and provenance
if relevant. `logs/` is disposable, not an archive.

**Codex handles exploration, implementation, checks and
reports ONLY: do not stage/add/commit/push,
create a branch, open PR or merge.
Stop after gate 015 for review.**
