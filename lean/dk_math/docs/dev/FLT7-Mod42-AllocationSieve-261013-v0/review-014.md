# Review 014 — Outcome A accepted; prime-side exclusion hidden in the ownership proof

Date: 2026-10-14
Research branch: `research/FLT7-Mod42-AllocationSieve-261013-v0`
Reviewed implementation: `a53b67fa74b6a631ee4cc3564639fa5c511f67b5`

## Verdict

**ACCEPTED — Outcome A.** Reviewed the actual committed
`DkMath/FLT/Seven/SevenRamifiedFusionSmallCoefficientPrimePowerOwnership.lean`,
its test module, `findings-014.md`, `report-014.md` and
`evidence/014-verification-summary.md`.

The four public declarations are:

1. `eligible_primitive_divisor_smallCoefficient_prime_pow`:
   for prime p, c≤343, actual r∈(c*p^n).divisors,
   coprimality with the **actual** complementary quotient,
   and 343*r^7<c*p^n, proves r∣c without a global
   bound on n or M.
2. `sixthPowerSieved_three_thirteen_pow_excluded`:
   for all n>0, full exact-sieve nonexistence at
   M=3*13^n.
3. `threeThirteenPowerCore_injective`:
   k↦3*13^(k+1) is injective.
4. `sixthPowerSieved_three_thirteen_power_family_excluded`:
   all k have no exact full-sieve allocation at that
   distinct infinite family of abstract cores.

The proof uses genuine selected-r provenance. When p∤r,
Euclid yields r∣c. When p∣r, actual quotient coprimality
yields t∣c, and t≤c≤343 together with
M=r*t and r≤r^7 contradicts the strict size guard.
The c=0 and n=0 cases do not require hidden positivity
assumptions. A Lean countermodel at c=21953,p=2,n=1,r=2
confirms that simply removing c≤343 makes the
proposed ownership statement false.

The specific 3*13^n full-sieve result classifies
r∣3, eliminates r=1 by the divisor-aware mod42
necessary congruence and r=3 using the previously
proved mod13 centered-image obstruction. It never
assumes that an r=3 exact endpoint actually exists.

Codex-reported focused build and tests returned zero,
and all four production exports and the countermodel
show only [propext, Classical.choice, Quot.sound],
no sorryAx. Reviewer inspected source and compact
evidence but **did not independently rerun Lean**.

These are exact full-sieve exclusions on abstract M,
not statements that actual FLT7 packets have any of
these core values. The gate-005 source/chart bridge
remains open and unconditional FLT7 is not proved.

## A sharper result visible in the proof, not yet exported

The generic ownership theorem's **p∣r branch is already
shown impossible**. Its return type records only r∣c,
but its proof actually establishes a stronger local
statement: any eligible allocation of M=c*p^n with
prime p and c≤343 must satisfy `p∤r`.

This matters because the actual factor identity
`r*(M/r)=c*p^n` implies, when n>0, `p∣M`.
Since p is prime and p∤r, one obtains
`p∣M/r`, **even if p divides c**.
Thus the coefficient need **not** be coprime to p.
Only the actual coprimality of r and its quotient,
the coarse bound, and c≤343 are used.

Specializing p=13 and invoking the gate-013
`nestedAllocation_excluded_of_thirteen_support`
now suggests a strictly broader (NOT yet Lean-proved)
theorem:

```lean
theorem sixthPowerSieved_smallCoefficient_thirteen_pow_excluded
    {c n : ℕ} (hc : c ≤ 7 ^ 3) (hn : 0 < n) :
    ¬ SixthPowerSievedNestedCondition (c * 13 ^ n)
```

All actual selected eligible r should have 13∤r
and 13∣(M/r), so the **single mod13 image consumer**
would exclude both GN/RHS branches, without mod42,
any fixed c, or another divisor enumeration.
This appears to strictly subsume the gate-014
c=3 result, and includes coefficients divisible
by 13 as well as coefficients coprime to 13.

For n=0 the support argument does not apply, but
all M=c≤343 should be size-vacuously excluded
because 343*r^7≥343≥M for any positive divisor r.
A possible all-n version is an optional corollary,
not a hidden assumption; prove separately if pursued.

A second optional source-side corollary, for any
given p:RamifiedSignedRootRoutingPacket whose actual
core is c*13^n, would remain a *conditional*
reconstruction exclusion via the existing
reconstruction/sieve iff. It would not show
that such p exists or exclude packets with other
cores.

## Gate 015 / proof boundaries

Authorize `instruction-015.md` as a bounded structural
follow-up: first prove **prime-base avoidance** under
the genuine membership, coprimality and size guards;
then deduce `13∣M/r` from factorization for n>0;
finally prove exact full-sieve absence for every
c≤343 at M=c*13^n.

Do not misinterpret r∣c alone as proving p∤r
when p∣c; prove avoidance independently.
Do not introduce a source-packet existence premise,
invent an arbitrary-prime mod13 nonvanishing theorem,
or infer full FLT7 closure.

Codex handles implementation, focused build, tests,
axiom audit, findings/report/evidence only. **No git
add/stage/commit/push, branch creation, PR or merge**.
The user controls integration. Logs stay disposable;
evidence stays compact and provenance-labelled.
