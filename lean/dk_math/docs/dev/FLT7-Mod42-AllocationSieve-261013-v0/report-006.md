# report-006 — centered integer-image exclusion at M=589

**Outcome A**: actual centered polynomial の strict adjacent bracket、no-image、fixed allocation の exact GN/RHS 排除、full-sieve 排除、conditional reconstruction consequence を Lean で証明。

## Exact API

Production module: `DkMath.FLT.Seven.SevenRamifiedFusionCenteredImage589`。

```lean
namespace DkMath.FLT.Seven

theorem centeredSevenSextic_589_bracket :
    centeredSevenSextic (7 ^ 27) 52382010648825907313680 < 448 * 589 ^ 49 ∧
    448 * 589 ^ 49 < centeredSevenSextic (7 ^ 27) (52382010648825907313680 + 1)

theorem centeredSevenSextic_589_no_image :
    ¬ ∃ q : ℕ, centeredSevenSextic (7 ^ 27) q = 448 * 589 ^ 49

theorem nestedAllocation_589_one_excluded :
    ¬ (NestedGNAllocationCondition 589 1 ∨ NestedRHSAllocationCondition 589 1)

theorem sixthPowerSievedNestedCondition_589_excluded :
    ¬ SixthPowerSievedNestedCondition 589

namespace RamifiedSignedRootRoutingPacket.QuotientPrimeSupport

theorem no_reconstruction_of_core_eq_589 (p : RamifiedSignedRootRoutingPacket)
    (hcore : internalDepthFourSeventhCore p = 589) :
    ¬ InternalDepthFourCounterexampleReconstructionObligation p
```

Direct import は既存 `SevenRamifiedFusionCenteredGnomonGap` 一本。既存 centered / receiver 定義や証明は変更していない。対象名と bracket numeral の重複を DkMath / DkMathTest で検索し、既存 589 exclusion は見つからなかった。

## Python precheck — arithmetic experiment only

今回、Python arbitrary-precision integers で D=7^27、actual polynomial と target / adjacent input を再計算した。実行 exit 0。出力:

```text
Python precheck only: D matches; F(k)<T=True; T<F(k+1)=True
Positive gap decimal digits: 117 116
```

下側 / 上側の正の差は117 / 116桁。浮動小数点や interpolation は使わない。ただしこの出力は Lean proof ではない。実行コードと結果の compact excerpt は evidence に別 section として保存。

## Lean proof — independent kernel acceptance

`centeredSevenSextic_589_bracket` は両不等式の conjunction を `by decide` で actual Lean definition からカーネル還元する。Python の出力を仮定や axiom として取り込んでいない。literal sixth-power equality 仮定はない。

既存 `centeredSevenSextic_no_image_of_adjacent_bracket` に両 strict inequalities を渡す。この theorem は既存 strict monotonicity と整数 index の隣接性を用いるので、二点だけの数値検査から全 `q:ℕ` の no-image が従う。

既存 `nestedAllocation_iff_centered` で exact receiver を actual centered candidate に移す。その necessary scalar field を取り出し、`one_pow`、`Nat.div_one`、`←mul_assoc`、`64*7=448` で target を合わせる。元 candidate の parity / positivity / orientation / coprimality guards を変更していない。全自然数中心の no-image は、その追加 guards を持つ candidate も排除するため、scalar field だけで矛盾が出る。

full-sieve の任意の eligible divisor r は membership により正。`r≥2` なら `r^7≥128`、`343*r^7<589` と矛盾するので r=1。その exact branch を pointwise exclusion に渡す。sieve の存在量化全体を否定する。

最後に既存 `internalDepthFourReconstruction_iff_sixth_power_sieved` の `.mp` と supplied `hcore` を使って source consequence を得る。packet existence は構成していない。

## Focused validation

Date: 2026-10-13、cwd `lean/dk_math`。Lean 4.34.1 / Lake 5.0.0-src+5045d00。

| Command | Exit | Result |
| --- | --- | --- |
| `python3 docs/dev/FLT7-Mod42-AllocationSieve-261013-v0/logs/006-precheck.py` | 0 | Python-only strict bracket recheck |
| `lake env lean DkMathTest/FLT/Seven/Centered589Calibration.lean`（初回） | 1 | receiver scalar normalization の結合方向不足 |
| 同 calibration（修正後） | 0 | 全五宣言成功 |
| `lake build DkMath.FLT.Seven.SevenRamifiedFusionCenteredImage589 DkMathTest.FLT.Seven.SevenRamifiedFusionModFortyTwoCheapAllocation` | 0 | new production + reused test dependency、9093 jobs |
| `lake env lean DkMathTest/FLT/Seven/SevenRamifiedFusionCenteredImage589.lean` | 0 | 全 applications / cheap-versus-exact contrast / axiom audits、warning/error なし |

初回失敗は `64*(7*589^49)` と `448*589^49` の式変形であり数学的 counterexample ではない。bracket は初回から通った。明示的な associative rewrite と kernel-checked constant equality で修正。校正の重複証明は最終 production / tests に移した。9093 は import dependencies を含む job 数であり変更モジュール数ではない。

実際の全五 exports の公理監査:

```text
'DkMath.FLT.Seven.centeredSevenSextic_589_bracket' depends on axioms: [propext]
'DkMath.FLT.Seven.centeredSevenSextic_589_no_image' depends on axioms: [propext, Classical.choice, Quot.sound]
'DkMath.FLT.Seven.nestedAllocation_589_one_excluded' depends on axioms: [propext, Classical.choice, Quot.sound]
'DkMath.FLT.Seven.sixthPowerSievedNestedCondition_589_excluded' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'DkMath.FLT.Seven.RamifiedSignedRootRoutingPacket.QuotientPrimeSupport.no_reconstruction_of_core_eq_589' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

bracket は `propext` のみ。残る四定理は標準 `[propext, Classical.choice, Quot.sound]`。`sorryAx` / fresh axiom なし。禁止構文検索はヒットなし（rg exit 1）。`git diff --check` exit 0、logs ignored、staging empty。

## Checked meaning and limits

Lean test は既存 `candidate589_passes` を再利用し、`HasModFortyTwoCheapAllocation 589 ∧ ¬ SixthPowerSievedNestedCondition 589` を同時に証明する。cheap survivor と exact receiver の存在を区別した。`¬ HasModFortyTwoCheapAllocation 589` は主張していない。

これは固定 core 589 の exact-image obstruction。任意の M、631+42*k の無限 cheap family、global reconstruction failure や unconditional FLT7 へは一般化していない。前 gate の未証明 perfect-sixth source bridge を仮定せず、今回の route は成立した。

## Files / evidence / proposed next question

追加（`lean/dk_math` から）:

- `DkMath/FLT/Seven/SevenRamifiedFusionCenteredImage589.lean`（五定理）。
- `DkMathTest/FLT/Seven/SevenRamifiedFusionCenteredImage589.lean`（両 strict inequalities と各 theorem の一般適用、cheap survival / exact exclusion の同時成立、公理監査）。
- `docs/dev/FLT7-Mod42-AllocationSieve-261013-v0/findings-006.md`。
- 同ディレクトリ `report-006.md`。
- 同ディレクトリ `evidence/006-verification-summary.md`。

Python / failed / full output は ignored な logs に留める。durable evidence は Python precheck と Lean proof を別 section とし、Codex-reported の provenance、必要な commands / exit statuses、公理 excerpt、checked source SHA-256 のみを保存。

次の研究候補（未実装）: 別の一つの固定 core でも、既存 adjacent-bracket certificate を見つけて kernel acceptance まで移せるか。この certificate discovery と theorem acceptance を分離し、成功例を全 M の obstruction と取り違えない。今回は source-coupling audit を再開していない。

gate 006 で停止。Git staging / commit / push / branch / PR / merge は行っていない。
