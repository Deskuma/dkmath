# report-010 — parametric mixed full-sieve exclusion

**Outcome A**: 提案された三つの純算術仮定は十分。自由変数 s の混合排除定理と、k≤63799 の全 progression を Lean で証明。

## Exact exported API

Module: `DkMath.FLT.Seven.SevenRamifiedFusionParametricMixedExclusion`。

```lean
namespace DkMath.FLT.Seven

theorem sixthPowerSieved_two_times_complement_excluded {s : ℕ}
    (hs42 : Nat.ModEq 42 s 1) (hs5 : Nat.ModEq 5 s 4)
    (hbound : 2 * s < 7 ^ 3 * 5 ^ 7) :
    ¬ SixthPowerSievedNestedCondition (2 * s)

theorem sixthPowerSieved_bounded_mixed_family_excluded {k : ℕ}
    (hk : k ≤ 63799) :
    ¬ SixthPowerSievedNestedCondition (2 * (589 + 210 * k))
```

Direct imports: existing GeneralGapModFiveImage, ModFortyTwoAllocationSieve, SixthPowerAllocationSieve。production に DkMathTest import なし。追加の source relation、endpoint witness、receiver emptiness、positivity 仮定を置いていない。

## Mathematical audit

full-sieve の alleged witness の同じ r を最後まで保持する。membership は r>0 と r∣2s を与える。

`343*r^7<2s<343*5^7` と natural power monotonicity で r<5。hs42 を2/3へ縮小する。s≡1 mod3 なら 2s≡2 mod3、従って3∤2s。s≡1 mod2 なので odd。もし4∣2sなら s=2*k が従い parity と矛盾する。従って3/4はdivisorにならず、残るrは1/2。

r1: hs42 を2倍して2s≡2 mod42、よって `(2s)/1` は1と合同でない。actual membershipから `r∣M` を取り出して既存 `nestedAllocation_excluded_of_mod_fortyTwo` に渡す。

r2: natural division cancellation により `(2s)/2=s`。hs5 は exactly `s≡4=2² mod5`、5∤2。既存 `nestedAllocation_excluded_of_mod_five_square` を同じrで適用する。

exact GN/RHS disjunction は元full-sieveのbranch fieldから得る。sixth-power witnessやcheap passをexact receiverに変換してはいない。法5のpolynomial image analysis、source packet、global sieve API は作り直していない。

## Whole finite progression and tests

s_k=589+210*k は常に1 mod42、4 mod5。k≤63799なら `2*s_k≤26796758<26796875=343*5^7`。この算術を omega / exact numeral reduction で一般kに証明し、parameter theoremへ適用した。

Tests confirm:

- 各新exportのproof-level application。
- 全kに対し `2*(589+210*k)<343*5^7 ↔ k≤63799`。
- endpoint k=63799 の core=26796758、threshold=26796875。
- k=63800 ではこのstrict size criterionが偽。
- k=22982 の core=9653618 とそのnew-family exclusion。
- core map `k↦2*(589+210*k)` のinjectivity。
- `Finset.range 63800` のimageのcardinality=63800（既存 `Finset.card_image_of_injective` / card_range を再利用、巨大な63800ケース列挙ではない）。
- 既存 gate008/009 evidence をtestだけで再利用し、同じcore9653618でcheap existentialが真、full-sieveが偽であること。

したがって自由変数を使う算術 mechanism により63800個の異なるcoreを扱う。cheap r2が全kで通るとは主張しない。finite bounded familyであり、unbounded / infinite exclusionではない。

63,799は指定したsize criterionの最大indexであり、数学的に可能な全排除範囲の最大値と証明したわけではない。k≥63800のreceiver存在・非存在やactual packet existence、FLT7 closure は今回の結果に含まれない。

## Source inventory / verification

Date: 2026-10-13。cwd `lean/dk_math`。Lean4.34.1 / Lake5.0.0-src+5045d00。

actual gate009 production、両existing consumerとfull-sieve fieldsを確認。parameter theorem / progression名の実ソース検索は一致なし。Source index refresh: 1,810 files /29,286 declarations、exit0。

| Command | Exit | Result |
| --- | --- | --- |
| `lake env lean DkMathTest/FLT/Seven/ParametricMixedCalibration.lean` | 0 | parameter theorem / bounded family、初回成功 |
| `lake build DkMath.FLT.Seven.SevenRamifiedFusionParametricMixedExclusion` | 0 | `Build completed successfully (9091 jobs).` |
| `lake env lean DkMathTest/FLT/Seven/SevenRamifiedFusionParametricMixedExclusion.lean` | 0 | all applications, bound iff, endpoint, cardinality, comparisons, axioms; no warning/error |

失敗試行、missing premise、hidden assumptionなし。9091jobsはimport dependencies込み。校正の重複証明は最終ファイルに移した。

Actual axiom output:

```text
'DkMath.FLT.Seven.sixthPowerSieved_two_times_complement_excluded' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'DkMath.FLT.Seven.sixthPowerSieved_bounded_mixed_family_excluded' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

両exportは標準 `[propext, Classical.choice, Quot.sound]` のみ、sorryAx / fresh axiomsなし。禁止構文検索一致なし（rg exit1）。

## Deliverables and next question

追加（lean/dk_mathから）:

- `DkMath/FLT/Seven/SevenRamifiedFusionParametricMixedExclusion.lean`（二exports）。
- `DkMathTest/FLT/Seven/SevenRamifiedFusionParametricMixedExclusion.lean`。
- `docs/dev/FLT7-Mod42-AllocationSieve-261013-v0/findings-010.md`。
- 同folder `report-010.md`, `evidence/010-verification-summary.md`。

既存sources / receivers / README / ROADMAPを変更していない。Evidenceはcompact Codex-reported、独立reviewer rerunではない。raw outputはignoredなlogsに留める。

次の一問（未実装）: 同じ二つのresidue仮定の下で、boundを緩めても残るdivisorsを排除できるか。例えばs≡4 mod5は5のdivisibilityも制限するため、今回のboundを必要条件と取り違えず、別の明示的size windowとdivisor coverを調べる余地がある。今回その拡張は証明していない。

gate010で停止。Git staging / commit / push / branch / PR / merge、gate011 workなし。
