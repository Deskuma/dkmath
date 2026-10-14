# Codex instruction-010 — parametric mixed obstruction, not another single-core check

Branch: `research/FLT7-Mod42-AllocationSieve-261013-v0`
Review: `review-009.md` (Outcome A accepted)
Implementer: GPT-6.1 Sol (light)

## Research goal

Gate 009 proved all-divisor exact exclusion for one particular
composite core by combining **two independent obstructions**:
mod-42 necessary residue failure and mod-five centered
integer-image failure.

Test whether this is a **parameter theorem** rather than
an accident of a particular numeral.

Let `M=2*s`. A promising family of **pure arithmetic**
hypotheses is:

```text
s ≡ 1 (mod 42)
s ≡ 4 (mod 5)
2*s < 7^3*5^7
```

The conjectural conclusion is
`¬ SixthPowerSievedNestedCondition (2*s)`.
These conditions contain no endpoint witness, exact residual
equation or assumption of receiver emptiness.

This is a proposed implication awaiting kernel verification.
If a premise is missing, report the precise counterexample or
minimal correction rather than inventing a source relation.
You may improve theorem factoring and weaken unnecessary
hypotheses if mathematically justified.

## Main proposed Lean theorem

```lean
theorem sixthPowerSieved_two_times_complement_excluded
    {s : ℕ}
    (hs42 : Nat.ModEq 42 s 1)
    (hs5 : Nat.ModEq 5 s 4)
    (hbound : 2 * s < 7 ^ 3 * 5 ^ 7) :
    ¬ SixthPowerSievedNestedCondition (2 * s)
```

Names are indicative. This theorem should re-use the existing
`nestedAllocation_excluded_of_mod_fortyTwo` and
`nestedAllocation_excluded_of_mod_five_square`, as well as
the existing `SixthPowerSievedNestedCondition`.

**Do not import DkMathTest from production** and do not
re-prove the centered polynomial's mod-five image analysis.

## Argument to audit and formalize

Given an alleged full-sieve witness `r` at `M=2*s`:

1. `r∈(2*s).divisors` implies `0<r` and `r∣2*s`.
2. `343*r^7<2*s<343*5^7` forces `r<5`.
3. `s≡1 (mod 42)` implies `s` is odd and `3∤s`.
   Therefore `3∤2*s` and `4∤2*s`.
   The remaining eligible divisor is `r=1` or `r=2`.
   Do not assume a factorization of all s or an arbitrary
   choice of r; derive this from the specific guards.
4. `r=1`: `(2*s)/1≡2 (mod 42)`, hence not 1.
   Supply `1∣2*s` or the actual membership-derived
   divisibility guard and invoke the existing mod-42 receiver
   exclusion.
5. `r=2`: `(2*s)/2=s≡4=2² (mod 5)`,
   `5∤2`, so use the existing **same-divisor**
   centered-image mod-five receiver exclusion.

The GN/RHS split comes from the exact nested sieve's branch
and must be preserved. Do not infer that the cheap predicate
itself is false.

A separate reusable eligibility helper can be introduced if
it exposes a genuine arithmetic mechanism and avoids a
duplicated proof, but it is not necessary to add an additional
framework or a global sieve redefinition.

## Uniform bounded progression — meaningful regression

Set

```text
s_k = 589 + 210*k
M_k = 2*s_k = 1178 + 420*k.
```

Check the endpoint and prove for **every** `k:ℕ`
with `k≤63799` that

```lean
¬ SixthPowerSievedNestedCondition (2 * (589 + 210 * k))
```

because:

- `s_k≡1 (mod 42)`, `s_k≡4 (mod 5)`;
- `2*s_k≤26796758<26796875=343*5^7`;
- `M_{22982}=9653618`, so this genuinely
  generalizes the already-proved gate-009 example;
- `k↦2*(589+210*k)` is injective,
  therefore the bounded interval has **63800 distinct**
  cores, not merely a rephrasing of one number.

The exact endpoint of the range should be confirmed
in Lean. Distinguish **finite bounded family** from
unbounded/infinite: nothing in this gate shows that
the same simple proof applies for `k≥63800`,
since the upper bound can admit additional divisors.

Optional: if useful without significant complexity,
show a concrete member (e.g. k=22982) still has a
cheap allocation despite the full-sieve exclusion,
reusing existing gate-008/009 theorems. **Do not claim
the cheap filter passes at r=2 for all k.**

## What would count as real progress

A successful theorem covers *many free core values* by a
transparent arithmetic mechanism rather than by testing
each huge literal value separately. This does not assert
that any of these values arises from an actual
`RamifiedSignedRootRoutingPacket`, nor does it
exclude all FLT7 counterexamples.

If there is a different **strictly more general**
divisor-cover formulation requiring only number-theoretic
facts and no exact endpoint predicate in the certificate,
you may formulate it as a small helper. However,
avoid building a large generic API or proving only a
tautological restatement of a premise
`∀ r, ¬ exactReceiver M r`. The bounded parametric
case must remain a substantial checked consequence.

## Existing declarations to reuse

- `DkMath.FLT.Seven.SevenRamifiedFusionSixthPowerAllocationSieve`:
  exact predicate and eligible allocation guards;
- `SevenRamifiedFusionModFortyTwoAllocationSieve`:
  divisor-aware modulo-42 exclusion;
- `SevenRamifiedFusionGeneralGapModFiveImage`:
  same-chosen-r exact image exclusion;
- `SevenRamifiedFusionCompositeCore9653618`:
  fixed-core previously checked case, for comparison;
- `SevenRamifiedFusionModFortyTwoCheapAllocation`
  only if a cheap-vs-exact diagnostic is useful.

Use current theorem source and index to avoid duplicate APIs.
Minimal new production code and tests. No broad refactoring,
no additional residue modulus, no source-packet construction
and no unconditional FLT7 claim.

## Verification, evidence and stop

Run appropriate focused Lean checks in the actual local
environment and inspect `#print axioms` for every new
production export. No `sorry`, `admit`, hidden assumptions,
`sorryAx`, fresh axioms or unsafe proof substitutes.

Record:
- `findings-010.md`: theorem inventory, mathematical proof,
  finite-range bound and failures/limits;
- `report-010.md`: Outcome A/B/C, exact exported theorem
  signatures, tests, axiom audit, genuine mathematical
  generalization and proposed next question;
- `evidence/010-verification-summary.md` if compact
  decisive verification records are produced.

`logs/` remains transient, no raw log archiving.
Codex chooses implementation, imports and build strategy.

**Codex implements, tests and reports only: do not stage,
commit, push, create branches, PRs or merge. Stop here and
return results for review; do not start gate 011.**

Outcome A: parameter theorem and the whole bounded progression
are Lean checked without unproved source assumptions.
Outcome B: a narrower correct lemma and precisely localized
missing condition.
Outcome C: false candidate / proof obstacle reported without
manufactured hypotheses.
