# Codex instruction-014 — small-coefficient prime-power ownership and infinite 3*13^n exclusion

Research branch: `research/FLT7-Mod42-AllocationSieve-261013-v0`
Review: `review-013.md` (Outcome A accepted)
Implementer: GPT-6.1 Sol (light)

## Objective

Gate 013 established a universal mod13 centered sextic nonvanishing
and showed that the **chosen allocation** `r=3` at
`M=3*13^12` survives the old cheap/sixth-power checks but
fails the exact receiver.

Now combine this new prime-support obstruction with the
**existing primitive allocation coprimality and coarse size**
to see whether every eligible r can be excluded for an
**unbounded family** of cores `M=3*13^n`.

The intended advance is structural, not another large numeric
example or a new arbitrary modulus.

## Existing declarations and proof provenance to read first

Inspect exact statements, scopes, imports and duplicate indices:

- `SevenRamifiedFusionSixthPowerAllocationSieve`:
  actual `SixthPowerSievedNestedCondition` fields,
  including `r∈M.divisors`,
  `Nat.Coprime r (M/r)`, `343*r^7<M`
  and the exact GN/RHS disjunction.
- `SevenRamifiedFusionPrimePowerPrimitiveExclusion`:
  `eligible_primitive_divisor_two_prime_pow` and
  Euclid/quotient factoring technique. This **c=2**
  theorem is not in itself the general coefficient theorem.
- `SevenRamifiedFusionCenteredThirteenSupport`:
  `nestedAllocation_excluded_of_thirteen_support`
  with the same selected r and quotient.
- `SevenRamifiedFusionModFortyTwoAllocationSieve`:
  `nestedAllocation_excluded_of_mod_fortyTwo`,
  requiring explicit `r∣M`.
- `SevenRamifiedFusionCenteredPolynomial` only if a
  precise existing import or scalar transport requires it.

Do not modify verified prior Lean files or import DkMathTest
into production merely to obtain a regression.

## Gate A — small-coefficient prime-power divisor ownership

Proposed generic theorem (check truth and Lean signature):

```lean
theorem eligible_primitive_divisor_smallCoefficient_prime_pow
    {c p n r : ℕ}
    (hp : Nat.Prime p) (hc : c ≤ 7 ^ 3)
    (hmem : r ∈ (c * p ^ n).divisors)
    (hcop : Nat.Coprime r ((c * p ^ n) / r))
    (hsize : 7 ^ 3 * r ^ 7 < c * p ^ n) :
    r ∣ c
```

The key mathematical mechanism:

1. Let M=c*p^n and t=M/r with the **actual quotient**.
   Extract r>0, r∣M and r*t=M from membership.
2. If p∤r, use primality/coprimality and Euclid
   on r∣c*p^n to derive r∣c.
3. If p∣r, actual `Nat.Coprime r t` implies p∤t.
   Then Euclid on t∣c*p^n gives t∣c, so
   t≤c≤343 (using c>0 if necessary and deriving it
   from the real eligibility, not adding unnecessary premises).
   Thus M=r*t≤343*r≤343*r^7,
   contradicting the strict size guard.
4. Conclude r∣c for every eligible allocation.
   No fixed global upper bound on n or M.

The possible edge case c=0 or n=0 should be
handled **honestly**; if the displayed target is true
as written, keep it, otherwise report the narrowest
genuine extra premise. A condition c≤343 is essential
to this particular inequality proof and must remain visible.

Optional small diagnostic: if c is allowed to
grow beyond 343, explain why this proof no longer
applies. Do not infer a converse or an exact endpoint
from a failed bound.

## Gate B — exclude all exact eligible allocations of 3*13^n

Proposed theorem:

```lean
theorem sixthPowerSieved_three_thirteen_pow_excluded
    {n : ℕ} (hn : 0 < n) :
    ¬ SixthPowerSievedNestedCondition (3 * 13 ^ n)
```

From an alleged full-sieve witness at M=3*13^n:

- Apply Gate A with c=3 and p=13, using
  **the witness's actual hmem/hcop/hsize**.
- From r∣3 and primality of 3, get r=1 or r=3.
- r=1: M/1=3*13^n is divisible by3, hence
  cannot be 1 modulo42. Invoke the prior
  divisor-guarded mod42 exact receiver exclusion
  with membership-derived r∣M.
  This is true for all n, without parity or
  a particular exponent class.
- r=3: M/3=13^n; hn>0 gives 13∣13^n,
  and 13∤3. Invoke the gate-013
  `nestedAllocation_excluded_of_thirteen_support`.
  Do not assert this divisor is eligible for
  every n; it is a branch conditional on a
  supposed witness.
- Both GN and RHS exact branches must be
  handled by the already-proved same-r consumers.
  No new receiver definitions or endpoint assumptions.

The restriction n>0 is deliberate: for n=0 the
support obstruction at r=3 has no 13 in the quotient.
Do not simply generalize this same proof to n=0.
A separate n=0 size-vacuous corollary is optional
but not needed for the unbounded family.

## Gate C — demonstrate the actual infinite family

State or at least test:

```lean
∀ k : ℕ,
  ¬ SixthPowerSievedNestedCondition (3 * 13 ^ (k + 1))
```

Derive this from Gate B; prove the map
`k ↦ 3 * 13^(k+1)` is injective or
strictly monotone to establish **infinitely many
distinct abstract cores**.

Also regress the exact gate-013 target
`n=12, M=3*13^12`; verify the case follows
from the new whole-core theorem. Keep the
**fixed-divisor cheap + sixth-power passage**
from gate 013 in its existing test:
it need not hold at all exponents n.
If useful, test a few natural small exponents;
do not replace the universal theorem with a
finite enumeration.

## Research boundaries

A successful gate provides an infinite abstract
full-sieve exclusion family. It does NOT prove:

- every arithmetic core M is excluded;
- the existence/nonexistence of any actual
  `RamifiedSignedRootRoutingPacket` at M=3*13^n;
- the source–real-pair–chart bridge missing at gate 005;
- unconditional FLT7.

Do not conflate primality of 13, the coprimality
of selected divisor and its quotient, and the
support condition `13∤r, 13∣M/r`. Each arises from
specific hypotheses; keep their provenance.

Do not divert into classifying arbitrary-prime
modular image nonvanishing, new modulus hunts or
rewriting previous production modules.

## Acceptance, evidence, stopping rule

Outcome A: genuine generic small-coefficient
primitive ownership lemma, all-index exact full-sieve
exclusion for positive n, and verified infinity
certificate.
Outcome B: narrower correct result or localized
missing theorem with precise report.
Outcome C: false proposal or other demonstrated
obstruction without hidden assumptions.

Choose local imports/proof tactics/build strategy freely.
Run focused Lean build/tests and `#print axioms` on
new public results. Report exact exit status and
unexpected axioms. No `sorryAx`, `sorry`,
`admit`, fresh axioms or unsafe proof substitutes.

Produce `findings-014.md`, `report-014.md` and
compact `evidence/014-verification-summary.md`
with clear proof/test provenance. `logs/` remains
temporary and ignored.

**Codex implements, tests and reports ONLY. Do not
git add/stage/commit/push, create branches or PRs,
or merge. Stop after gate 014 for review.**
