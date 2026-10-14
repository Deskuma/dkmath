# Review 008 — Outcome A accepted; finite all-divisor synthesis at M=9653618

Date: 2026-10-13
Research branch: `research/FLT7-Mod42-AllocationSieve-261013-v0`
Reviewed implementation: `099f94348f6d6ec3d00122d1c1786da83fd89301`

## Decision

**ACCEPTED — Outcome A.** Reviewed the published Lean production module
`DkMath/FLT/Seven/SevenRamifiedFusionGeneralGapModFiveImage.lean`,
its DkMathTest module, `findings-008.md`, `report-008.md`, and
`evidence/008-verification-summary.md`.

Exactly two production theorems have been added:

- `centeredSevenSextic_generalGap_no_image_mod_five`:
  `¬ 5 ∣ r` and `Nat.ModEq 5 s (r^2)` force the **actual**
  center sextic `F(7^27*r^49,q)` not to equal `448*s^49`
  for any natural `q`.
- `nestedAllocation_excluded_of_mod_five_square`:
  transports that no-image obstruction to the existing GN/RHS exact
  receivers for the **same selected divisor `r`** and `s=M/r`.

The scalar no-image proof transports arbitrary natural inputs to
`ZMod 5` and checks all relevant residue classes. The endpoint
theorem reuses `nestedAllocation_iff_centered` and does not
redefine a receiver or manufacture a natural endpoint. The
`5∤r` hypothesis must be preserved. A zero-gap test shows
that simply dropping it makes the **generic natural** no-image
assertion false; that test is not a positive legitimate allocation.

The test theorem
`DkMathTest.FLT.Seven.allocationTwo_modFive_regression`
proves at `M=9653618, r=2, s=13^6=4826809` that
the **same allocation** passes both
`ModFortyTwoCheapAllocation` and
`SixthPowerAllocationSieve`, but its GN/RHS exact receiver
is absent. The existing perfect-sixth sufficient obstruction
requires `9*r²≤t`; its threshold fails for `r=2,t=13`
(`36≤13` is false), so this is not just a relabeled
application of that theorem.

The reported focused build and final test exited 0.
Two public theorem axiom audits and the named regression
listed only `[propext, Classical.choice, Quot.sound]`;
no `sorryAx`. Reviewer inspected the published Lean
code and reported evidence; **no independent Lean build
was run**.

## Scope of the result

- The no-image and receiver exclusions are **pointwise in `r`**.
- The finite modular allowed-`s` table only asserts modular
  compatibility, not actual integer endpoint existence.
- No theorem here eliminates all possible `r` at
  `M=9653618`; no packet with that core is constructed.
- No global FLT7 impossibility or descent follows.

## Next concrete synthesis — arithmetic precheck, not yet Lean

The integer `M=9653618=2*13^6` has
`M mod 42=2`. Existing
`nestedAllocation_excluded_of_mod_fortyTwo` with
`r=1` and `1∣M` thus forbids the **r=1** exact receiver.

To exclude **all** allocations at this one `M`, use
the existing exact sieve's coarse condition:

```text
r ∈ M.divisors
343*r^7 < M.
```

For `r≥5`, `343*r^7 ≥ 343*5^7 = 26796875 > 9653618`,
so any eligible `r` lies in `{1,2,3,4}`.
Among these, `3∤9653618` and `4∤9653618`;
hence only `r=1` or `r=2` remain.

- `r=1`: the **existing mod-42** necessary condition excludes it.
- `r=2`: the **new mod-5 sextic image** excludes it.

These arithmetic facts have been independently checked with
Python exact integers but **the all-divisor synthesis has not yet
been formally proved in Lean**. Do not report
`¬ SixthPowerSievedNestedCondition 9653618` as an
established theorem until kernel checked.

If successful, the source consequence
`internalDepthFourSeventhCore p=9653618 →
¬ InternalDepthFourCounterexampleReconstructionObligation p`
will be conditional on the given core, exactly like
the 554 and 589 corollaries, not a claim that a real
packet with that core exists.

This is a controlled joining of independently established
**necessary residue** and **exact image** obstructions for
different divisors. A one-core theorem does not by itself
generalize to any class of cores.

## Gate 009 authorization

Proceed with `instruction-009.md`, limited to the complete
eligible-divisor exclusion at `M=9653618`, the fixed-core
full-sieve statement, and an optional thin conditional source
consumer. Do not turn it into a search over arbitrary moduli
or an asserted global FLT7 result.

Codex handles implementation, verification and local reports only:
**no staging, commits, pushes, branch creation, PRs or merges**.
Wise Wolf publishes reviewed documents/instructions to the
research branch; user controls integration. Raw `logs/` are
disposable, `evidence/` compact and provenance marked.
