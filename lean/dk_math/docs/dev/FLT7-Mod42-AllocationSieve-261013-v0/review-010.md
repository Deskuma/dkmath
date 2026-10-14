# Review 010 — Outcome A accepted; prime-power allocation frontier

Date: 2026-10-13
Branch: `research/FLT7-Mod42-AllocationSieve-261013-v0`
Reviewed implementation: `9742f80ec94d55d64143d7af1e4a80a4095ee7c1`

## Verdict

**ACCEPTED — Outcome A.** Inspected production
`SevenRamifiedFusionParametricMixedExclusion.lean`, matching DkMathTest,
`report-010.md`, `findings-010.md`, and
`evidence/010-verification-summary.md` on GitHub.

The production module exports exactly two theorems:

- `sixthPowerSieved_two_times_complement_excluded`:
  for a free parameter `s`, conditions `s≡1 (mod 42)`,
  `s≡4 (mod 5)` and `2*s<343*5^7` imply
  `¬ SixthPowerSievedNestedCondition (2*s)`.
- `sixthPowerSieved_bounded_mixed_family_excluded`:
  for every `k≤63799`, `M=2*(589+210*k)`
  has no exact eligible allocation.

The proof keeps the actual selected `r` from the full sieve.
Divisor membership and the strict coarse size bound force
`r<5`; congruence-derived nondivisibility excludes `r=3,4`;
previously proved mod-42 and general-gap mod-5 exact receiver
exclusions handle `r=1,2`. No unproved endpoint constraint
or source-packet assumption is introduced.

Tests verify the size window iff `k≤63799`, the upper
endpoint `M=26796758`, failure of that *specific* bound at
`k=63800`, `M_22982=9653618`, injectivity and 63,800
distinct image cores using a cardinality theorem, not brute force.

Focused build/test success and axioms
`[propext, Classical.choice, Quot.sound]` with no `sorryAx`
are **Codex-reported**. The reviewer inspected source and
compact evidence but did not independently rerun Lean.

This is a **bounded** parametric exclusion. It is not an
absolute limit on excluded cores. It does not show that any
of these cores comes from an actual FLT7 source packet or
close FLT7.

## Next mathematical frontier: primitivity, not another fixed cutoff

Gate 010 uses a *global numeric bound* to force `r∈{1,2}`.
But the original full-sieve definition also supplies
`Nat.Coprime r (M/r)`. This primitivity constraint was not
needed in the gate-010 divisor classification and may
remove the fixed upper bound for special core structures.

Consider the family (proposed, not yet Lean proved):

```text
n_k = 6+4*k
s_k = 13^n_k
M_k = 2*s_k
```

For every k, `13²≡1 (mod 42)` yields `s_k≡1 (mod42)`;
`13⁴≡1 (mod5)` and `13⁶≡4 (mod5)` yield
`s_k≡4 (mod5)`. These identities still require a general
Lean proof for this family.

**Proposed primitive divisor argument.** Take an eligible
`r∣M=2*13^n`, set `t=M/r`, and retain
`Nat.Coprime r t`, `r*t=M`, `343*r^7<M`.

- If `13∤r`, then r is coprime with `13^n`;
  Euclid's lemma and `r∣2*13^n` give `r∣2`,
  so `r=1∨r=2`.
- If `13∣r`, primitivity implies `13∤t`.
  Then t is coprime with `13^n`, and `t∣2*13^n`
  implies `t∣2`, hence `t≤2`.
  But `M=r*t≤2*r` contradicts `343*r^7<M`
  for positive r.

Thus **all eligible r should be 1 or 2 without a global
upper bound**. The existing mod-42 obstruction excludes r=1,
and the general-gap mod-5 image obstruction excludes r=2.
A successful proof would give the genuinely unbounded family

```text
∀ k : ℕ, ¬ SixthPowerSievedNestedCondition (2*13^(6+4*k)).
```

This remains a **proposed Lean target**, not yet established.
It neither constructs a real source packet nor proves FLT7.

Independent small-index integer checks (k=0 through 4) yield
primitive divisors `{1,2,13^n,2*13^n}` and only 1,2
satisfy the size guard; finite testing is not the proof.
For k=0, this family recovers `2*13^6=9653618`.

## Gate authorization / roles

Authorize `instruction-011.md`, narrowly focused on the
prime-power primitive-divisor lemma and unbounded exclusion
if the lemma is valid. Accept a narrower correct result and a
precise diagnosis if an assumption or proof bridge is missing.

Codex implements, tests and reports **only**. No Git
staging/commit/push, branch creation, PR or merge.
Wise Wolf publishes reviewed instructions and reviews.
`logs/` stays disposable, `evidence/` stays compact and
provenance-labeled. Stop after gate 011.
