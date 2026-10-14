# Review 004 — Outcome A accepted; source-coupling phase opened

Date: 2026-10-13
Branch: `research/FLT7-Mod42-AllocationSieve-261013-v0`
Reviewed implementation: `dc8040ea7a0e52f793cc3ee5fcdf5aa2a8c6e2c0`

## Verdict

**ACCEPTED — Outcome A.** Source, named tests, `report-004.md`,
`findings-004.md` and the compact `evidence/004-verification-summary.md`
were inspected.

The six public theorems in
`DkMath.FLT.Seven.SevenRamifiedFusionModFortyTwoCheapBoundaryAudit`
are:

- `no_mod42Cheap_at_554`;
- `mod42Cheap_family`;
- `mod42Cheap_family_has`;
- `mod42Cheap_family_sixthPower`;
- `mod42Cheap_survivors_unbounded`;
- `RamifiedSignedRootRoutingPacket.QuotientPrimeSupport.no_reconstruction_of_core_eq_554`.

The 554 theorem quantifies **all divisor allocations**, unlike gate 003's
fixed `r=1` example. Its proof combines the coarse bound
`343*r^7<554` with positivity to force `r=1`, then contradicts
the required mod-42 residue.

The progressions `M=631+42*k`, `r=1` satisfy the endpoint-free filter
for every natural `k`. The separate
`SixthPowerAllocationSieve 1 (M/1)` is true modulo one, and an explicit
unboundedness theorem shows that these are not merely finite samples.
The code does **not** construct a Fermat equation, a source packet or
an actual reconstructed endpoint.

The Codex-provided focused build/test report gives exit code 0.
Five exports report only `[propext, Classical.choice, Quot.sound]`;
the sixth-power family reports only `[propext]`.
No `sorryAx` appears in the reported audit. This reviewer inspected
the published Lean code and evidence but **did not rerun Lean**.

## What is established — and not

**Established:** the present cheap arithmetic conditions can exclude
some entire values of `M`, but cannot by themselves exclude all
positive `M`, because they have an explicitly proved unbounded
family of satisfying values.

**Not established:** any surviving `M` equals
`internalDepthFourSeventhCore p` for an actual
`RamifiedSignedRootRoutingPacket p`; nor does it produce an exact
`NestedGNAllocationCondition` or `NestedRHSAllocationCondition`.
The conditional core-554 corollary does not assert that any such
packet with core 554 exists.

**Not established:** impossibility of all future modular refinements.
Only the currently implemented cheap conditions were tested.

## Next frontier: coupling the same source to the same allocation

Existing APIs already provide **source-specific** information:

- `internalDepthFourSeventhCore`,
  `internalDepthFourSeventhCore_pos`,
  `internalDepthFourSeventhCore_not_seven_dvd` in
  `SevenRamifiedFusionNestedReconstruction.lean`;
- `internalDepthFourReconstruction_iff_sixth_power_sieved` and
  `internalDepthFourAllocation_prime_support` in
  `SevenRamifiedFusionSixthPowerAllocationSieve.lean`;
- the actual norm packet's complementary root ledger
  `M*N = verticalGapRoot*compensationRoot`, plus coprimality and
  seven-unit information;
- `internalDepthFourReconstruction_iff_centered` and
  `CenteredNestedAllocationCandidate` in
  `SevenRamifiedFusionCenteredPolynomial.lean`;
- conditional centered-gap obstruction in
  `SevenRamifiedFusionCenteredGnomonGap.lean`.

Important limitation: `internalDepthFourAllocation_prime_support`
requires a prime `q` dividing the **selected** divisor `r`.
When `r=1`, no such prime exists: prime-support routing alone does
not eliminate the cheap survivors' fixed-divisor scenario.

The next useful task is to determine what additional **same-packet,
same-allocation** constraint links the original carrier or norm ledger
to the would-be centered integer chart or endpoint; and whether it is
independent of the exact residual equation rather than a renamed
equivalent existence obligation.

An explicit, sharply scoped **negative audit** is a valid result if
the available source data do not provide the missing link.

## Roles and evidence

- Codex only explores/implements, validates and reports locally.
  **No Git staging, commits, pushes, branch creation, PRs or merges.**
- Wise Wolf publishes reviewed research instructions and review documents
  to this branch; user controls integration decisions.
- `logs/` stays disposable; durable `evidence/` stays small,
  provenance-labelled and materially relevant.

## Decision

Authorize `instruction-005.md`, a **bounded source–allocation–chart
compatibility audit**. Do not turn it into another iteration of
cheap residue filters or restate the known reconstruction equivalence.
