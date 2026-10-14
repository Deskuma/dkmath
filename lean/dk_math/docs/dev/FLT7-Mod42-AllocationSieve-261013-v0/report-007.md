# report-007 — uniform centered image obstruction modulo five

**Outcome A**: fixed-gap mod-five no-image theorem と、cheap / sixth-power を通るが divisor-one exact receiver が成立しない無界な族を Lean で検証。

## Exact public API

Module: `DkMath.FLT.Seven.SevenRamifiedFusionCenteredModFiveImage`。

```lean
namespace DkMath.FLT.Seven

theorem centeredSevenSextic_fixedGap_mod_five_image (q : ℕ) :
    Nat.ModEq 5 (centeredSevenSextic (7 ^ 27) q) 1 ∨
    Nat.ModEq 5 (centeredSevenSextic (7 ^ 27) q) 2 ∨
    Nat.ModEq 5 (centeredSevenSextic (7 ^ 27) q) 4

theorem centeredSevenSextic_fixedGap_no_image_mod_five {s : ℕ}
    (hs : Nat.ModEq 5 s 1) :
    ¬ ∃ q : ℕ, centeredSevenSextic (7 ^ 27) q = 448 * s ^ 49

theorem nestedAllocation_one_excluded_of_mod_five {M : ℕ}
    (hM5 : Nat.ModEq 5 M 1) :
    ¬ (NestedGNAllocationCondition M 1 ∨ NestedRHSAllocationCondition M 1)

theorem mod42Cheap_modFive_family (k : ℕ) :
    ModFortyTwoCheapAllocation (631 + 210 * k) 1 ∧
    SixthPowerAllocationSieve 1 ((631 + 210 * k) / 1) ∧
    ¬ (NestedGNAllocationCondition (631 + 210 * k) 1 ∨
      NestedRHSAllocationCondition (631 + 210 * k) 1)
```

Private helper `centeredTarget_mod_five (s : ℕ)` proves `Nat.ModEq 5 (448*s^49) (3*s)` for every natural s, including zero. Public exports are four; no receiver definitions changed.

## Actual polynomial and reuse

Direct imports: `SevenRamifiedFusionCenteredPolynomial` and `SevenRamifiedFusionModFortyTwoCheapBoundaryAudit`。

The actual polynomial is `7*q^6+35*D^2*q^4+21*D^4*q^2+D^6`. With D=7^27 its mod-five image is proved by casting this definition into ZMod 5 and reducing arbitrary q to q%5. The five remaining closed cases use `decide`, with no guessed cyclotomic identity or sampled universal claim.

The target helper uses the same arbitrary-input reduction for s%5. For s≡1, target≡3. The image theorem permits only 1,2,4, so modular equality, hence natural equality, is impossible. No literal sixth-power hypothesis is used.

`nestedAllocation_iff_centered` transports the actual exact receiver into a centered candidate. The necessary scalar equation is normalized using `Nat.div_one`, `one_pow`, `mul_one`, associative multiplication and `64*7=448`. Parity, orientation, positivity and coprimality are not altered; the stronger no-image condition forgets these extra guards only when deriving contradiction.

For every k, `631+210*k=631+42*(5*k)`. `mod42Cheap_family (5*k)` and `mod42Cheap_family_sixthPower (5*k)` supply both existing filters. A direct ModEq proof gives residue one modulo five, hence the new exact exclusion. Existing seventh-power / threshold / sixth-power APIs are reused rather than recreated.

## Tests and mathematical comparison

The focused DkMathTest module verifies all four exports by proof-level applications and also checks:

- D≡3 mod5.
- Actual image witnesses q=0,1,2 give residues 4,2,1. Together with the universal inclusion, the modular image is exactly {1,2,4}.
- Every family core is one mod5 and one mod42.
- Every family core satisfies `HasModFortyTwoCheapAllocation`, with witness r=1.
- The core map k↦631+210*k is injective.
- For every bound B, index k=B gives a larger core passing both cheap filters and failing the divisor-one exact receiver. This is an unbounded family, not a finite sample list.
- At 589, residue of the core is4, the target is2, and F(D,1) has the same target residue. This modular match is proved alongside the existing `centeredSevenSextic_589_no_image` from gate006.

Therefore this particular mod-five test does not prove the 589 no-image result. Its exact integer-image exclusion comes from the independent adjacent-value bracket. Conversely, the new mod-five obstruction handles the entire divisor-one progression without a large-numeral adjacent bracket for each core.

The current theorem is fixed D=7^27, hence fixed allocation r=1. It does not rule out other divisor allocations for arbitrary M or for every k. In particular `¬ HasModFortyTwoCheapAllocation (631+210*k)` would be false and is not asserted. `¬ SixthPowerSievedNestedCondition (631+210*k)` is not inferred from this pointwise exclusion. No bounded-window all-divisor corollary or FLT7 closure is added.

## Validation and attempt history

Date: 2026-10-13。cwd `lean/dk_math`。Lean 4.34.1 / Lake 5.0.0-src+5045d00。

| Command | Exit | Result |
| --- | --- | --- |
| `python3 dkmath_theorems.py --db .dkmath-theorems.sqlite3 build --root .` | 0 | 1,807 files / 29,276 declarations |
| index `search --name centeredSevenSextic --limit 40` | 0 | 13 existing declarations; no equivalent mod-five theorem |
| `lake env lean DkMathTest/FLT/Seven/CenteredModFiveCalibration.lean` (first) | 1 | Nat mod simp rules looped to maxRecDepth |
| same calibration (ZMod revision) | 0 | all public targets and private target helper accepted |
| `lake build DkMath.FLT.Seven.SevenRamifiedFusionCenteredModFiveImage` | 0 | `Build completed successfully (9092 jobs).` |
| `lake env lean DkMathTest/FLT/Seven/SevenRamifiedFusionCenteredModFiveImage.lean` | 0 | all tests / contrast / axiom audits, no warnings/errors |

The failed attempt was a tactic recursion issue; it was corrected by finite ZMod reduction without increasing recursion limits or adding hypotheses. The supplied Python discovery is research context, not a Lean premise. This gate formally checks the residue statements in Lean; it does not present an unexecuted Python rerun as evidence. 9092 jobs include import dependencies, not changed modules.

Actual axiom output:

```text
'DkMath.FLT.Seven.centeredSevenSextic_fixedGap_mod_five_image' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'DkMath.FLT.Seven.centeredSevenSextic_fixedGap_no_image_mod_five' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'DkMath.FLT.Seven.nestedAllocation_one_excluded_of_mod_five' depends on axioms: [propext, Classical.choice, Quot.sound]
'DkMath.FLT.Seven.mod42Cheap_modFive_family' depends on axioms: [propext, Classical.choice, Quot.sound]
```

All four exports use standard `[propext, Classical.choice, Quot.sound]` only; no sorryAx or new axioms. Forbidden construct scan of the new two Lean files has no matches (rg exit1).

## Artifacts and next question

Added under `lean/dk_math`:

- `DkMath/FLT/Seven/SevenRamifiedFusionCenteredModFiveImage.lean` (four exports, one private helper).
- `DkMathTest/FLT/Seven/SevenRamifiedFusionCenteredModFiveImage.lean`.
- `docs/dev/FLT7-Mod42-AllocationSieve-261013-v0/findings-007.md`.
- Same folder `report-007.md` and `evidence/007-verification-summary.md`.

Calibration duplication was removed after promotion. Existing modules, receivers, README and ROADMAP were left intact. Raw output stays in disposable logs; durable evidence is compact, Codex-reported, and source-attributed. No independent reviewer rerun is claimed.

Next question (not implemented): how does the mod-five image change with the actual divisor r, and which remaining divisor residue classes can escape this fixed-r obstruction? A future result must state its divisor/gap assumptions explicitly rather than promoting r=1 exclusion to all allocations.

gate007 stops here. No staging, commit, push, branch creation, PR or merge.
