# Codex instruction-009 — complete exact allocation exclusion at one composite core

Branch: `research/FLT7-Mod42-AllocationSieve-261013-v0`
Review: `review-008.md` (gate 008 Outcome A accepted)
Implementer: GPT-6.1 Sol (light)

## One goal

Gates 002 and 008 establish **different** receiver obstructions:

- mod-42 necessary residue failure excludes some allocations;
- a divisor-dependent centered-sextic **mod-five no-image**
  obstruction excludes other exact allocations.

For the **single core** `M=9653618=2*13^6`, show that
**every** eligible divisor is eliminated by one of these two
already-checked results.

This is a finite all-divisor **synthesis** of prior theorems,
not a request to discover another prime, modify source packets,
or prove global FLT7.

## Exact current source to inspect

Use source-index and actual Lean declarations, not guesses:

- `SevenRamifiedFusionSixthPowerAllocationSieve.lean`:
  `SixthPowerSievedNestedCondition`, including
  `r∈M.divisors`, `343*r^7 < M`, and the branch predicates;
- `SevenRamifiedFusionModFortyTwoAllocationSieve.lean`:
  `nestedAllocation_excluded_of_mod_fortyTwo` with
  **explicit `r∣M`**;
- `SevenRamifiedFusionGeneralGapModFiveImage.lean`:
  `nestedAllocation_excluded_of_mod_five_square` for
  **the same chosen `r`**;
- `SevenRamifiedFusionModFortyTwoCheapAllocation.lean`:
  the cheap-filter definition;
- `SevenRamifiedFusionDepthFourReconstructionAudit.lean` and
  `internalDepthFourReconstruction_iff_sixth_power_sieved`:
  conditional source consumer only if useful.

Do not import a DkMathTest module into production.
The gate-008 named r=2 regression is useful verification,
but production proofs must use production theorems directly.

## Proposed formal targets

Start by proving or reusing a small finite-divisor lemma:

```lean
theorem eligible_divisor_9653618_eq_one_or_two {r : ℕ}
    (hmem : r ∈ (9653618 : ℕ).divisors)
    (hsize : 7^3 * r^7 < 9653618) :
    r = 1 ∨ r = 2
```

The shape may vary if a direct proof is shorter.
Do not drop `hmem` or `hsize`.

Mathematical argument:

- membership yields `0<r` and `r∣9653618`;
- `r≥5` contradicts the size guard because
  `343*5^7=26796875 > 9653618`;
- for `r=3` or `4`, divisibility into 9653618 fails;
- the only remaining natural divisors satisfying both
  constraints are `r=1` or `r=2`.

Then a public no-receiver result:

```lean
theorem sixthPowerSievedNestedCondition_9653618_excluded :
    ¬ SixthPowerSievedNestedCondition 9653618
```

Under `r=1`:
- `9653618 mod 42 = 2`, not 1;
- `1∣9653618` must be available;
- invoke existing `nestedAllocation_excluded_of_mod_fortyTwo`
  to reject both exact GN/RHS branches.

Under `r=2`:
- `¬5∣2`;
- `9653618/2=4826809≡4=2² (mod 5)`;
- invoke existing `nestedAllocation_excluded_of_mod_five_square`.

The same `r` selected in the full sieve must be retained
throughout, and both GN/RHS disjuncts handled correctly.
A `SixthPowerAllocationSieve` witness or a cheap pass is
**not** an exact receiver witness.

Optional thin conditional source corollary:

```lean
theorem no_reconstruction_of_core_eq_9653618
    (p : RamifiedSignedRootRoutingPacket)
    (hcore : internalDepthFourSeventhCore p = 9653618) :
    ¬ InternalDepthFourCounterexampleReconstructionObligation p
```

Reuse `internalDepthFourReconstruction_iff_sixth_power_sieved`.
This does not assert that any packet with this core exists.

## Required mathematical contrast

Include focused Lean tests confirming, without silently
changing the chosen `r`, that:

1. `ModFortyTwoCheapAllocation 9653618 2` **holds**
   (reuse gate-008 test evidence or re-prove from source);
2. `SixthPowerAllocationSieve 2 (9653618/2)` **holds**;
3. the `r=2` exact GN/RHS receiver is false by mod-five image;
4. the `r=1` exact GN/RHS receiver is false by mod-42;
5. no **other eligible divisor** survives membership + size;
6. the full exact sieve is false.

Do not accidentally claim
`¬ HasModFortyTwoCheapAllocation 9653618`;
it is false because `r=2` passes the cheap filter.

No blanket claim about other `M`, all `r=2` allocations,
actual FLT7 source packet existence, or unconditional FLT7.

## Scope / acceptance

Outcome A: explicit all-divisor finite exhaustion and resulting
full-sieve exclusion are kernel-checked, with no new assumptions.
Outcome B: exact partial result with the first missing implication.
Outcome C: a falsified proposed claim or rigorously identified blocker.

Minimal new production theorem(s) and tests are enough.
Search for existing identical results before creating modules.
Codex chooses implementation tactics, imports, local build
and resource strategy.

Any new export must pass focused Lean verification with actual
`#print axioms`. Reject `sorryAx`, new axioms and placeholders;
report all tests accurately.

Write `findings-009.md`, `report-009.md`, and when decisive
`evidence/009-verification-summary.md` (compact, with provenance).
Keep `logs/` transient; do not archive giant transcripts.

**Codex only implements, verifies and reports. Do NOT stage,
commit, push, create branches, open PRs or merge.**
After reporting, stop and await review; do not start gate 010.
