# report-008 — divisor-dependent centered image modulo five

**Outcome A**: 全自然数 r,s に対する unit-divisor no-image、same chosen r の exact receiver transport、r=2 の strict-screening regression を Lean で検証。

## Exact exported APIs

Module: `DkMath.FLT.Seven.SevenRamifiedFusionGeneralGapModFiveImage`。

```lean
namespace DkMath.FLT.Seven

theorem centeredSevenSextic_generalGap_no_image_mod_five {r s : ℕ}
    (hr5 : ¬ 5 ∣ r) (hs5 : Nat.ModEq 5 s (r ^ 2)) :
    ¬ ∃ q : ℕ, centeredSevenSextic (7 ^ 27 * r ^ 49) q = 448 * s ^ 49

theorem nestedAllocation_excluded_of_mod_five_square {M r : ℕ}
    (hr5 : ¬ 5 ∣ r) (hs5 : Nat.ModEq 5 (M / r) (r ^ 2)) :
    ¬ (NestedGNAllocationCondition M r ∨ NestedRHSAllocationCondition M r)
```

直接 import は既存 `SevenRamifiedFusionCenteredPolynomial` 一本。hypotheses は要求通り、追加 positivity / coprimality / `r ∣ M` は不要。これは scalar necessary equation を使う transport であり、legitimate divisor allocation のガードを削除した定義変更ではない。具体的 cheap allocation では divisor membership を検証している。

## Proof and residue table

actual definition `7*q^6+35*D^2*q^4+21*D^4*q^2+D^6` を ZMod5 に cast する。hs5 を cast して s=r² に置き換え、任意の r,q を r%5,q%5 に移す。25ケース中 r≡0 の5ケースは hr5 と矛盾し、残る20ケースは exact scalar equality の還元で矛盾する。`decide` を用いたカーネル還元であり、有限 samples をそのまま universal claim にしていない。

以下の image / allowed-s 表は最終 test の二つの finite statements で Lean 検証した。allowed は **modular equality** の存在であり、自然数の exact equation の存在ではない。

| r mod5 | D mod5 | F image mod5 | allowed s mod5 |
| --- | --- | --- | --- |
| 0 | 0 | {0,2,3} | {0,1,4} |
| 1 | 3 | {1,2,4} | {2,3,4} |
| 2 | 1 | {1,3,4} | {1,2,3} |
| 3 | 4 | {1,3,4} | {1,2,3} |
| 4 | 2 | {1,2,4} | {2,3,4} |

表は supplied Python discovery と一致するが、ここでの formal acceptance は Lean の actual polynomial に対する proof による。Python 出力を仮定として取り込んでいない。D / target の算術は universal cast reduction 本体でも扱われる。

既存 `nestedAllocation_iff_centered` で chosen M,r の exact receiver から candidate を取り出す。その必要 scalar field の `64*7` を448に正規化するだけ。parity / orientation / natural interval / positivity / coprimality は元 candidate に保持され、no-image はそれらの追加制約を持つ候補も排除する。

## Nontrivial divisor regression

Named test theorem `DkMathTest.FLT.Seven.allocationTwo_modFive_regression`:

```lean
ModFortyTwoCheapAllocation 9653618 2 ∧
SixthPowerAllocationSieve 2 (9653618 / 2) ∧
¬ (NestedGNAllocationCondition 9653618 2 ∨ NestedRHSAllocationCondition 9653618 2) ∧
¬ 9 * 2 ^ 2 ≤ (13 : ℕ)
```

Lean で `13^6=4826809`、`9653618=2*4826809` を確認。同じ r=2 について divisor membership / coprimality / coarse bound / GN-side strict threshold / mod42 を検証し、cheap condition の全 fields を証明した。sixth-power sieve は witness13 の literal equality から成立し、unit/mod-five premises を新 consumer に渡して両 exact branches を排除する。

旧 sufficient perfect-sixth condition の size premise は `36≤13` で偽。したがってその既存 theorem をこの witness に適用した結果ではない。この size premise 不成立から receiver 成立を導く converse は主張しない。

gate007 は D=7^27、r=1 に固定されていた。今回の r=2 は D=7^27*2^49 で、補完因子は mod5 で4（1ではない）。fixed-gap theorem の仮定を満たす別の問題と同一視できない。一般 theorem は r=1 の形も特殊化できるが、この r=2 の診断は genuinely different gap を扱う。

## Necessity of the unit premise and scope

テストは r=s=q=0 の exact zero-gap image を構成する。hs5 は成立するが hr5 は成立せず、unit premise を落とした universal natural no-image conjecture は偽。この zero-gap model は正の legitimate allocation の witness ではない。

r≡0 の表では s≡0 も modular image に入るので、正の5-multiple divisor にも今回の unit proof を無条件に適用できない。ただし modular matching 自体から natural exact receiver を構成したとは言わない。

結果は same fixed divisor r=2 の receiver 排除。`¬ SixthPowerSievedNestedCondition 9653618` や他の divisors の排除、actual packet existence、FLT7 closure は結論していない。既存 cheap / sixth-power filters はこの同じ allocation を通すことが formal regression で明示された。

## Validation

Date: 2026-10-13。cwd `lean/dk_math`。Lean4.34.1 / Lake5.0.0-src+5045d00。

| Command | Exit | Result |
| --- | --- | --- |
| initial actual-source target-name search | 1 | duplicate matchesなし |
| `lake env lean DkMathTest/FLT/Seven/GeneralGapModFiveCalibration.lean` | 0 | generic no-image / exact transport、初回成功 |
| `lake build DkMath.FLT.Seven.SevenRamifiedFusionGeneralGapModFiveImage` | 0 | `Build completed successfully (9088 jobs).` |
| `lake env lean DkMathTest/FLT/Seven/SevenRamifiedFusionGeneralGapModFiveImage.lean` | 0 | regression / finite image table / applications / audits成功 |
| same final test after allowed-s table addition | 0 | 全検証、warning/errorなし |
| `python3 dkmath_theorems.py --db .dkmath-theorems.sqlite3 build --root .` | 0 | 1,809 files / 29,283 declarations |
| refreshed index `search --name generalGap_no_image_mod_five --full` | 0 | new export の実際の statement を確認 |

既存 mod-five index 検索は古い snapshot だったため更新し直し、実ソース検索と合わせて確認した。Lean の失敗試行・false target・追加仮定なし。concrete r=2 の literal exponent343 の正規化 warning を避けるため test module に `exponentiation.threshold 400` を設定した。これは numeral elaboration setting であり、証明の仮定ではない。9088 jobs は import 依存鎖込み。

Actual axiom output:

```text
'DkMath.FLT.Seven.centeredSevenSextic_generalGap_no_image_mod_five' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'DkMath.FLT.Seven.nestedAllocation_excluded_of_mod_five_square' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'DkMathTest.FLT.Seven.allocationTwo_modFive_regression' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Production二定理と named regression は標準 `[propext, Classical.choice, Quot.sound]` のみ。sorryAx / fresh axiom なし。

## Records and next research question

追加（`lean/dk_math` から）:

- `DkMath/FLT/Seven/SevenRamifiedFusionGeneralGapModFiveImage.lean`（二exports）。
- `DkMathTest/FLT/Seven/SevenRamifiedFusionGeneralGapModFiveImage.lean`（一般適用、r=2 named regression、両 finite tables、unit premise の zero-gap countermodel、axiom audit）。
- `docs/dev/FLT7-Mod42-AllocationSieve-261013-v0/findings-008.md`。
- 同ディレクトリ `report-008.md`, `evidence/008-verification-summary.md`。

既存 receiver / production / README / ROADMAP は変更なし。校正の重複コードを最終モジュールに移した。証拠は Codex-reported の compact formal acceptance のみ、raw output は ignored な logs に保存。独立 reviewer rerun とは呼ばない。

次の一問（未実装）: 同じ core 9653618 の他の eligible divisors は、この divisor-dependent condition を満たすか。固定r=2 の排除から全-divisor claim へ移るには、残る divisor の検査と明示的な provenance が必要である。

gate008 で停止。Git staging / commit / push / branch / PR / merge は行っていない。
