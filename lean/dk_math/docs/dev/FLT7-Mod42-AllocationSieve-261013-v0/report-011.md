# report-011 — unbounded prime-power full-sieve exclusion

**Outcome A**: primitive divisor mechanism を任意 n（0を含む）で証明し、全kのfull-sieve排除とinjective core familyをLeanで検証。Global M upper boundなし。

## Production APIs

Module: `DkMath.FLT.Seven.SevenRamifiedFusionThirteenPowerPrimitiveExclusion`。

```lean
namespace DkMath.FLT.Seven

theorem eligible_primitive_divisor_two_thirteen_pow (n : ℕ) {r : ℕ}
    (hmem : r ∈ (2 * 13 ^ n).divisors)
    (hcop : Nat.Coprime r ((2 * 13 ^ n) / r))
    (hsize : 7 ^ 3 * r ^ 7 < 2 * 13 ^ n) : r = 1 ∨ r = 2

theorem sixthPowerSieved_thirteen_power_family_excluded (k : ℕ) :
    ¬ SixthPowerSievedNestedCondition (2 * 13 ^ (6 + 4 * k))
```

n=0 is valid without an added condition. The size/membership premises are already inconsistent at the smallest core; the same proof handles it without weakening the predicate.

## Real structural mechanism

Set M=2*13^n and **t=M/r from the actual selected allocation**. Membership gives r>0, r∣M and r*t=M.

If 13∤r, primality yields Nat.Coprime r 13, then Nat.Coprime r (13^n). Existing Euclid `Nat.Coprime.dvd_mul_right` cancels that factor from r∣2*13^n and yields r∣2. Existing `Nat.dvd_prime` gives r=1∨r=2.

If 13∣r, actual hcop implies13∤t, hence Nat.Coprime t (13^n). The exact product gives t∣M; Euclid gives t∣2 and t≤2. Therefore M≤2*r. But r≤r^7 and r>0 imply the existing coarse inequality343*r^7<M is impossible. This branch is rejected for every n, not by bounded enumeration of n or r.

This is the primitivity information missing from the earlier bounded-size mechanism. The proof retains membership, hcop and coarse bound; it does not assume the chosen r is arbitrary or identified with another source coordinate.

## All-index residues and exclusion

For n=6+4*k, `(13²)^(3+2*k)` gives 13^n≡1 mod42 from13²≡1. Multiplying13^6≡4 mod5 by `(13^4)^k≡1` gives13^n≡4 mod5. These are general ModEq proofs, not finite sample checks.

Given a full-sieve witness, the structural lemma consumes its actual hmem/hcop/hsize and returns r1/r2. At1, M≡2 mod42; actual membership supplies the divisor guard to existing `nestedAllocation_excluded_of_mod_fortyTwo`. At2, natural division cancellation yields M/2=13^n≡4=2² mod5; existing `nestedAllocation_excluded_of_mod_five_square` excludes both exact branches. The original exact disjunction and same r are preserved throughout.

Direct imports: existing GeneralGapModFiveImage, ModFortyTwoAllocationSieve, SixthPowerAllocationSieve. No DkMathTest import in production. Gate010's global bound is not used. Existing receiver definitions and stable proof modules are unchanged.

## Diagnostics / genuine infinite family

DkMathTest adds and checks:

- generic applications to both production exports;
- `thirteenPowerCore_injective`: Function.Injective (k↦2*13^(6+4*k)), using multiplicative cancellation, Nat.pow_right_injective and linear index arithmetic;
- k=0 core=9653618 and its new-family exclusion;
- k=1,2 exclusions at exponents10,14;
- `coprimality_guard_countermodel`: r13 is a divisor of2*13^10, satisfies343*13^7<2*13^10, but is neither1 nor2 and is not coprime to its complement.

Thus the guard cannot be discarded from the primitive-divisor statement. This model is an arithmetic allocation without the primitive premise, not an exact endpoint witness.

Injectivity on all natural indices supplies the required genuine infinity certificate; distinct indices give distinct abstract natural cores. No finite upper cutoff occurs in the family theorem.

Optional uniform cheap/sixth-power contrast was not implemented. In particular no uniform literal sixth-power witness is assumed for13^(6+4*k). The theorem negates the exact full-sieve regardless of such independent cheap witnesses.

## Source inventory and verification

2026-10-13, cwd `lean/dk_math`. Lean4.34.1 / Lake5.0.0-src+5045d00。

Target-name actual-source search: no existing match. Index refreshed:1,811 files /29,288 declarations, exit0. Actual Mathlib Euclid / power-injectivity types and existing gate010 structure were checked.

| Command | Exit | Result |
| --- | --- | --- |
| `lake env lean DkMathTest/FLT/Seven/ThirteenPrimitiveCalibration.lean` | 0 | primitive lemma / all-k exclusion, initial success |
| `lake build DkMath.FLT.Seven.SevenRamifiedFusionThirteenPowerPrimitiveExclusion` | 0 | `Build completed successfully (9091 jobs).` |
| `lake env lean DkMathTest/FLT/Seven/SevenRamifiedFusionThirteenPowerPrimitiveExclusion.lean` | 0 | all applications, injectivity, countermodel, regressions and audits; no warnings/errors |

No failed proof attempt, missing premise or new source assumption. Calibration duplication was promoted into final modules.9091jobs include imports, not changed-module count.

Actual public-production and named-test axiom audits:

```text
'DkMath.FLT.Seven.eligible_primitive_divisor_two_thirteen_pow' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'DkMath.FLT.Seven.sixthPowerSieved_thirteen_power_family_excluded' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'DkMathTest.FLT.Seven.thirteenPowerCore_injective' depends on axioms: [propext, Classical.choice, Quot.sound]
'DkMathTest.FLT.Seven.coprimality_guard_countermodel' depends on axioms: [propext, Classical.choice, Quot.sound]
```

All four audited declarations use standard `[propext, Classical.choice, Quot.sound]` only. No sorryAx / fresh axioms. Forbidden construct search has no matches (rg exit1).

## Mathematical boundary / next question

This excludes an unbounded collection of abstract prime-power cores. It does not construct actual RamifiedSignedRootRoutingPacket values, close the source–chart bridges of gate005, prove arbitrary-M receiver emptiness, or prove unconditional FLT7.

Next single question (not implemented): on the narrower k=3*j subfamily, can r2 be proved to pass both cheap and sixth-power filters uniformly while this exact full-sieve exclusion persists? That subfamily has a literal-sixth exponent6+12*j; a future diagnostic must still verify every other cheap field rather than infer a witness from this exclusion.

## Files and stopping point

Added under lean/dk_math:

- `DkMath/FLT/Seven/SevenRamifiedFusionThirteenPowerPrimitiveExclusion.lean` (two exports).
- `DkMathTest/FLT/Seven/SevenRamifiedFusionThirteenPowerPrimitiveExclusion.lean` (applications, two named diagnostics, four axiom audits).
- `docs/dev/FLT7-Mod42-AllocationSieve-261013-v0/findings-011.md`。
- Same directory `report-011.md`, `evidence/011-verification-summary.md`。

Existing sources/receivers/README/ROADMAP unchanged. Compact evidence is Codex-reported, not an independent reviewer rerun. Raw logs remain transient and ignored. No staging/commit/push/branch/PR/merge or later gate work.
