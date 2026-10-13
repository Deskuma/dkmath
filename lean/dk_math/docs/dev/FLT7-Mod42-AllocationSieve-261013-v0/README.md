# FLT7 Mod-42 Allocation Sieve — 2026-10-13

Branch: **research/FLT7-Mod42-AllocationSieve-261013-v0**  
Base: **develop** (branch forked 2026-10-13).  
Status: **Gates 001–004 and 006–009 ACCEPTED (Outcome A); gate 005 ACCEPTED (Outcome B); gate 010 AUTHORIZED, parametric mixed-obstruction proof pending**.

## Question

Can the existing nested FLT7 allocation receiver be narrowed by a new
**necessary** congruence on its complementary factor `s = M / r`?

Under a *legitimate nested allocation* (in particular, `r ∣ M`), the
expected result is

```text
NestedGNAllocationCondition M r OR NestedRHSAllocationCondition M r
  + r | M
  -> M / r ≡ 1 (mod 6)
  + existing M / r ≡ 1 (mod 7)
  -> M / r ≡ 1 (mod 42).
```

Do not infer existence of a new counterexample, global impossibility, or
unconditional FLT7 from this necessary condition.

## Arithmetic starting point

For natural numbers `x,y`, write the homogeneous seventh-degree factors

```text
S7(x,y) = sum_{j=0}^6 x^(6-j) y^j
A7(x,y) = sum_{j=0}^6 (-1)^j x^(6-j) y^j.
```

The candidate neutral fact is that `Nat.Coprime x y` implies
`S7(x,y) ≡ A7(x,y) ≡ 1 (mod 6)`.  For the GN branch, the
two coprime endpoints are `D+u, u`, with
`D = 7^27 * r^49`; this endpoint coprimality must be derived from
`Nat.Coprime u (7*M)` **and `r ∣ M`**.
For the alternating branch they are `u, D-u`; the existing
receiver already assumes `Nat.Coprime u D`.

Both exact residual equations equate their residual to `7*s^49`.
Because `7 ≡ 1 (mod 6)` and `s^49 ≡ s (mod 6)`, their
primitive residue constraint yields `s ≡ 1 (mod 6)`.
The existing `nestedAllocation_residue_sieve` yields
`s ≡ 1 (mod 7)`.  The moduli 6 and 7 are coprime.

**Important guard:** `NestedGNAllocationCondition M r` by itself
does not assume `r ∣ M`.  Do not prove or state its mod-6 result
without a sufficient additional hypothesis; this is the primary
soundness trap to check before writing Lean.

## Previously implemented APIs — do not recreate

- `DkMath.FLT.Seven.SevenRamifiedFusionAllocationThreshold`:
  `NestedGNAllocationCondition`, `NestedRHSAllocationCondition`.
- `DkMath.FLT.Seven.SevenRamifiedFusionAllocationResidueSieve`:
  `nestedGNResidual_residue_sieve`,
  `nestedAlternatingResidual_residue_sieve`,
  `nestedAllocation_residue_sieve` (mod 7).
- `DkMath.FLT.Seven.SevenRamifiedFusionSixthPowerAllocationSieve`:
  `SixthPowerAllocationSieve` and its existing mod-3 consequence
  under `3 ∣ r`; **this is not the new unconditional mod-6 bridge**.
- `DkMath.FLT.Seven.SevenRamifiedFusionSymmetricReconstruction`:
  the two exact nested receiver forms and their counterexample-chart
  equivalence.
- `DkMath.FLT.Seven.SevenRamifiedFusionDepthFourReconstructionAudit`:
  already identified reconstruction obligation.
- Existing GTail selection/factor/transport, seven-power and focusing
  theorems must not be rewritten as part of this small experiment.

## Provenance and trust levels

- Python exploratory file: `flt7_mod42_precheck.py` from the 2026-10-12
  local precheck; the script was re-executed on 2026-10-13.
  It checks all 24 coprime residue classes modulo 6, 152,231
  coprime positive integer pairs in [1,500]^2, and one **fixed**
  RHS parameter slice (`r=1`, `s=589`). These are not Lean proofs.
- GitHub `develop` source paths were inspected before branch creation.
- Kernel acceptance requires focused compilation and axiom audit.
  A source-index hit or a passing Python test is not such acceptance.

## Workspace conventions

- Completed gate 001: [instruction-001.md](instruction-001.md), [report-001.md](report-001.md), [review-001.md](review-001.md)
- Accepted gate 002: [instruction-002.md](instruction-002.md), [report-002.md](report-002.md), [review-002.md](review-002.md), [evidence](evidence/002-verification-summary.md)
- Accepted gate 003: [instruction-003.md](instruction-003.md), [report-003.md](report-003.md), [review-003.md](review-003.md), [evidence](evidence/003-verification-summary.md)
- Accepted gate 004: [instruction-004.md](instruction-004.md), [report-004.md](report-004.md), [review-004.md](review-004.md), [evidence](evidence/004-verification-summary.md)
- Accepted gate 005: [instruction-005.md](instruction-005.md), [source-coupling-map-005.md](source-coupling-map-005.md), [report-005.md](report-005.md), [review-005.md](review-005.md)
- Accepted gate 006: [instruction-006.md](instruction-006.md), [report-006.md](report-006.md), [review-006.md](review-006.md), [evidence](evidence/006-verification-summary.md)
- Accepted gate 007: [instruction-007.md](instruction-007.md), [report-007.md](report-007.md), [review-007.md](review-007.md), [evidence](evidence/007-verification-summary.md)
- Accepted gate 008: [instruction-008.md](instruction-008.md), [report-008.md](report-008.md), [review-008.md](review-008.md), [evidence](evidence/008-verification-summary.md)
- Accepted gate 009: [instruction-009.md](instruction-009.md), [report-009.md](report-009.md), [review-009.md](review-009.md), [evidence](evidence/009-verification-summary.md)
- Next gate: [instruction-010.md](instruction-010.md) — parameterize the combined mod42/mod5 obstruction across a bounded progression
- Evidence policy: [evidence/README.md](evidence/README.md)
- Progress / proof boundaries: [ROADMAP.md](ROADMAP.md)
- Working folder is `lean/dk_math`; keep edits narrowly scoped.
- The Codex implementer is GPT-6.1 Sol (light): keep steps small;
  supply exact theorem statements and validation evidence.
- After each instruction the reviewer checks results and decides
  whether to extend, repair, or stop the route.
- `logs/` stays transient and ignored; `evidence/` holds only compact necessary verification data.
- The implementation environment chooses its own build strategy; do not impose fixed local resource assumptions.
- **Codex implements, tests and reports only. It must not stage/commit/push/merge or create PRs. Wise Wolf publishes reviewed instructions and review notes to GitHub; the user controls integration.**

## Current research boundary

The mod-42 necessary condition, an endpoint-free cheap filter, and its
positive/negative calibration are completed and reviewed (gates 001–004).
An unbounded family of abstract cheap candidates survives, with
trivial sixth-power sieve at divisor one. This does **not** establish
actual packet cores or endpoint witnesses. Gate 005 asks what additional
same-packet carrier/norm/chart constraints can cut across that gap;
it permits a precise negative audit if no existing bridge suffices.

Gate 005 identified no new source-coupled restriction; an actual-packet bridge to the chosen chart remains unresolved. Gate 006 then **proved** an exact adjacent-image obstruction at the concrete cheap survivor M=589, including all eligible divisors at that fixed core. Gate 007 **proved** a separate uniform local-image obstruction modulo five, showing no exact divisor-one receiver for every M=631+210*k despite cheap and sixth-power screening survival. Gate 008 **proved** the divisor-dependent mod-five no-image theorem for all 5-unit r with s≡r² (mod 5), excluding an exact r=2 allocation at M=9653618 despite passing cheap and sixth-power filters. Gate 009 tests a concrete full-sieve synthesis: only r=1 or r=2 meet the positive-divisor and size guards at this M; existing mod42 excludes r=1, and the new mod5 image excludes r=2. Gate 009 **proved** full exact allocation exclusion at M=9653618 by combining mod42 at r=1 with mod5 at r=2. Gate 010 asks whether a direct parameter theorem extends that mixed mechanism to M=2*(589+210*k), 0≤k≤63799, a finite bounded class. No global FLT7 closure, all-core receiver emptiness, or strict descent follows.
