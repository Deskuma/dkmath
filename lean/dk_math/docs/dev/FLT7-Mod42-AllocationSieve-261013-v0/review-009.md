# Review 009 — Outcome A accepted; promote a mixed obstruction to a parameter theorem

Date: 2026-10-13
Branch: `research/FLT7-Mod42-AllocationSieve-261013-v0`
Reviewed implementation: `69e73e3a40b2dc2caaa4eb55b94f49fcbf848a19`

## Verdict

**ACCEPTED — Outcome A.** Reviewed:

- `DkMath/FLT/Seven/SevenRamifiedFusionCompositeCore9653618.lean`;
- `DkMathTest/FLT/Seven/SevenRamifiedFusionCompositeCore9653618.lean`;
- `findings-009.md`, `report-009.md`, and
  `evidence/009-verification-summary.md`.

Exactly three production declarations are added:

1. `eligible_divisor_9653618_eq_one_or_two`;
2. `sixthPowerSievedNestedCondition_9653618_excluded`;
3. `RamifiedSignedRootRoutingPacket.QuotientPrimeSupport.no_reconstruction_of_core_eq_9653618`.

The eligibility proof **retains divisor membership and the coarse
size guard**. From `343*r^7<9653618` it gets `r<5`;
`r∣9653618` removes `r=3,4`, positivity removes zero.
It then handles the actual same chosen divisor:

- `r=1`: `M/1 ≢ 1 (mod 42)` and `r∣M`;
  use `nestedAllocation_excluded_of_mod_fortyTwo`.
- `r=2`: `5∤2` and `M/2≡2² (mod 5)`;
  use `nestedAllocation_excluded_of_mod_five_square`.

This correctly establishes
`¬ SixthPowerSievedNestedCondition 9653618`.
A test simultaneously proves
`HasModFortyTwoCheapAllocation 9653618`, by the
same `r=2` from gate 008, so passing necessary arithmetic
guards is not confused with exact endpoint existence.

The conditional source consequence invokes the existing
`internalDepthFourReconstruction_iff_sixth_power_sieved`
and does not construct a source packet or prove FLT7.

The implementer reports focused build and test exit 0; each
`#print axioms` lists only
`[propext, Classical.choice, Quot.sound]`, no `sorryAx`.
Reviewer read the published source and compact evidence;
**no independent Lean build rerun** was performed.

## Beyond one core: a genuine parametric possibility

There is a natural way to *generalize the arithmetic reason* for
009 without postulating anything about exact endpoints.

Consider `M=2*s`, where:

```text
s ≡ 1 (mod 42)
s ≡ 4 (mod 5)
2*s < 343*5^7 = 26796875.
```

These assumptions appear sufficient to prove, by the same
eligible-divisor analysis,
`¬ SixthPowerSievedNestedCondition (2*s)`:

- If `343*r^7<2*s<343*5^7`, then `r<5`.
- Since `s≡1 (mod 42)`, it is odd and not divisible by
  three. Hence `r=3` or `r=4` cannot divide `2*s`.
- At `r=1`, the complement is `2*s≡2 (mod 42)`,
  so the exact receiver is excluded by the existing mod-42
  necessary condition with its divisor guard.
- At `r=2`, the complement is `s≡4=2² (mod 5)`
  and `5∤2`, so the existing mod-five integer-image
  theorem excludes the exact receiver.

This is a **reviewer-side arithmetic proposal**, not yet a
Lean-verified general theorem. Unlike a tautological packaging
of `∀r, ¬ exactReceiver`, it uses only explicit number-theoretic
restrictions on a free parameter s.

A concrete progression is

```text
s_k = 589+210*k
M_k = 2*(589+210*k) = 1178+420*k
0 ≤ k ≤ 63799.
```

The endpoint k=63799 gives M=26796758, below
26796875; k=63800 is already outside this particular
size-bound proof. Thus this proposed theorem would exclude
**63800 distinct cores**, a finite bounded family, not
an unbounded family. The old core
`9653618 = 1178 + 420*22982` lies in that interval.

These numerical identities were checked with exact integer
arithmetic for planning only. No blanket theorem about the
full progression beyond the stated bound is being asserted.
Alternative generalizations remain open; do not bind the
research to a single formula if the executor identifies a
strictly cleaner hypothesis set.

## Next gate and proof boundary

Authorize `instruction-010.md` to test this parametric
mixed-obstruction theorem and (if valid) its bounded arithmetic
progression. Reuse the existing mod-42, mod-five, centered
and full-sieve APIs; do not create a fake source packet, guess
a relation to actual carrier coordinates, or derive unconditional
FLT7. Keep the free parameter and finite bound visible.

Codex performs research implementation, verification and reports
only: **no Git staging/commit/push, branches, PR or merges**.
Wise Wolf publishes review/instruction documents; the user
controls branch integration. `logs/` remains disposable;
`evidence/` small, provenance-labelled.
