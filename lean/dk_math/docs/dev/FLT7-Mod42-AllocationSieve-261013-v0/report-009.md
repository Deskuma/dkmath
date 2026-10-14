# report-009 — complete exact allocation exclusion at 9653618

**Outcome A**: membership + coarse size の eligible divisors を全数排除し、full-sieve の不存在を Lean で証明。

## Public API

Module: `DkMath.FLT.Seven.SevenRamifiedFusionCompositeCore9653618`。

```lean
namespace DkMath.FLT.Seven

theorem eligible_divisor_9653618_eq_one_or_two {r : ℕ}
    (hmem : r ∈ (9653618 : ℕ).divisors)
    (hsize : 7 ^ 3 * r ^ 7 < 9653618) : r = 1 ∨ r = 2

theorem sixthPowerSievedNestedCondition_9653618_excluded :
    ¬ SixthPowerSievedNestedCondition 9653618

namespace RamifiedSignedRootRoutingPacket.QuotientPrimeSupport

theorem no_reconstruction_of_core_eq_9653618 (p : RamifiedSignedRootRoutingPacket)
    (hcore : internalDepthFourSeventhCore p = 9653618) :
    ¬ InternalDepthFourCounterexampleReconstructionObligation p
```

## Reason and source reuse

Membership gives positive r and r∣M. If r≥5, pow monotonicity gives r^7≥78125, contradicting `343*r^7<9653618`, since `343*5^7=26796875`. The finite cases below5 leave only1/2: zero is excluded by positivity, 3/4 do not divide M. No prime factorization of all divisors or hypothetical endpoint is required.

The full-sieve proof extracts its **same** r and exact GN/RHS disjunction. At1, `M/1 mod42=2`, and `Nat.dvd_of_mem_divisors hmem` supplies the explicit guard to `nestedAllocation_excluded_of_mod_fortyTwo`. At2, `5∤2` and `M/2≡2² mod5` supply `nestedAllocation_excluded_of_mod_five_square`. Both are existing production theorems. No receiver definition, coprimality or chart orientation is changed.

Conditional source consequence uses the existing `internalDepthFourReconstruction_iff_sixth_power_sieved` and supplied core equality. It does not construct a packet.

Production imports are only GeneralGapModFiveImage, ModFortyTwoAllocationSieve, SixthPowerAllocationSieve in the same Seven fusion family. **No DkMathTest import in production.** Test-only code reuses gate008's named regression for the r2 cheap and sixth-power facts.

## Contrast checked in Lean

- `ModFortyTwoCheapAllocation 9653618 2` and `SixthPowerAllocationSieve 2 (9653618/2)` hold, using the existing regression.
- r2 exact receiver is false by mod5, r1 exact receiver false by mod42.
- Every membership + size eligible divisor is1/2.
- `¬ SixthPowerSievedNestedCondition 9653618` holds.
- The test proves `HasModFortyTwoCheapAllocation 9653618 ∧ ¬ SixthPowerSievedNestedCondition 9653618` simultaneously; cheap passage is not an exact receiver witness.

All-divisor synthesis is for this single core and these eligible-divisor guards. No other core, all r2 allocations, actual packet existence or global FLT7 conclusion is asserted.

## Validation

2026-10-13; cwd `lean/dk_math`; Lean4.34.1 / Lake5.0.0-src+5045d00.

| Command | Exit | Result |
| --- | --- | --- |
| actual-source duplicate target search | 1 | no matches |
| `python3 dkmath_theorems.py --db .dkmath-theorems.sqlite3 build --root .` | 0 | 1,809 files / 29,283 declarations |
| `lake env lean DkMathTest/FLT/Seven/CompositeCoreCalibration.lean` (first) | 1 | `norm_num at hdiv ⊢` closed a contradiction before goal normalization |
| `lake build DkMath.FLT.Seven.SevenRamifiedFusionCompositeCore9653618 DkMathTest.FLT.Seven.SevenRamifiedFusionGeneralGapModFiveImage` | 0 | corrected production + reused test dependency; 9093 jobs |
| `lake env lean DkMathTest/FLT/Seven/SevenRamifiedFusionCompositeCore9653618.lean` | 0 | all applications / contrasts / audits; no warning/error |

The initial tactic failure (`No goals to be solved`) was repaired by normalizing the divisibility hypothesis first and sending remaining goals to simp. No mathematical target or hypothesis was weakened. Calibration duplication was moved into final production/test files. 9093 jobs include import dependencies, not changed module count.

Actual axiom audit:

```text
'DkMath.FLT.Seven.eligible_divisor_9653618_eq_one_or_two' depends on axioms: [propext, Classical.choice, Quot.sound]
'DkMath.FLT.Seven.sixthPowerSievedNestedCondition_9653618_excluded' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'DkMath.FLT.Seven.RamifiedSignedRootRoutingPacket.QuotientPrimeSupport.no_reconstruction_of_core_eq_9653618' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

All three exports use standard `[propext, Classical.choice, Quot.sound]` only. No sorryAx or fresh axioms.

## Artifacts and next question

Added under `lean/dk_math`:

- `DkMath/FLT/Seven/SevenRamifiedFusionCompositeCore9653618.lean` (three exports).
- `DkMathTest/FLT/Seven/SevenRamifiedFusionCompositeCore9653618.lean`.
- `docs/dev/FLT7-Mod42-AllocationSieve-261013-v0/findings-009.md`.
- Same directory `report-009.md` and `evidence/009-verification-summary.md`.

Existing Lean sources / receivers / README / ROADMAP were not edited. Evidence is compact and Codex-reported, not an independent reviewer rerun. Raw logs remain disposable and ignored.

Next research question (not implemented): for another single core, can the finite eligible-divisor set be exhausted by these same two existing obstructions? No gate010 work, blanket claim or new modulus is part of this checkpoint. No staging / commit / push / branch / PR / merge.
