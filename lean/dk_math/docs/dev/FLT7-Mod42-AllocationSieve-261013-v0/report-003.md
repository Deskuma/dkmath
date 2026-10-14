# report-003 — independent allocation prefilter and discrimination audit

**Outcome A** — endpoint-free filter、exact-to-cheap implication と reconstruction consumer、旧必要条件を通過する候補の追加排除を Lean で確認。

## Exact APIs

Production module: `DkMath.FLT.Seven.SevenRamifiedFusionModFortyTwoCheapAllocation`。

```lean
namespace DkMath.FLT.Seven

def ModFortyTwoCheapAllocation (M r : ℕ) : Prop :=
  r ∈ M.divisors ∧ Nat.Coprime r (M / r) ∧ 7 ^ 3 * r ^ 7 < M ∧
    Nat.ModEq 42 (M / r) 1 ∧
    (7 ^ 161 * r ^ 343 < M ^ 49 ∨
      (M ^ 49 < 7 ^ 161 * r ^ 343 ∧ 7 ^ 161 * r ^ 343 ≤ 64 * M ^ 49))

def HasModFortyTwoCheapAllocation (M : ℕ) : Prop :=
  ∃ r : ℕ, ModFortyTwoCheapAllocation M r

theorem sixthPowerSieved_implies_mod42Cheap (M : ℕ)
    (h : SixthPowerSievedNestedCondition M) :
    HasModFortyTwoCheapAllocation M

namespace RamifiedSignedRootRoutingPacket.QuotientPrimeSupport

theorem internalDepthFourReconstruction_implies_mod42Cheap
    (p : RamifiedSignedRootRoutingPacket)
    (h : InternalDepthFourCounterexampleReconstructionObligation p) :
    HasModFortyTwoCheapAllocation (internalDepthFourSeventhCore p)
```

定義には exact receiver、endpoint `u`、残余多項式等式、sixth-power existence sieve を含めない。固定した `M,r` の decidability も DkMathTest で `unfold; infer_instance` により確認。`Has...` の存在は算術候補の存在だけを意味し、endpoint witness ではない。

## Source reuse and proof

直接 imports:

- `DkMath.FLT.Seven.SevenRamifiedFusionModFortyTwoAllocationSieve`
- `DkMath.FLT.Seven.SevenRamifiedFusionSixthPowerAllocationSieve`

`SixthPowerSievedNestedCondition` の witness `r` をそのまま使う。divisor membership から `Nat.dvd_of_mem_divisors` で `r ∣ M` を得て、既存 `nestedAllocation_mod_fortyTwo` を exact branch に適用する。coprimality / coarse bound / branch threshold と RHS band は既存 fields を取り出すだけ。新しい positivity 仮定や receiver equation は追加しない。

reconstruction consumer は既存 `internalDepthFourReconstruction_iff_sixth_power_sieved` の `.mp` と第一定理を合成するだけで、追加仮定はない。DepthFourReconstructionAudit の既存 finite-chart statements を調べたが、今回の consumer に追加 import や新しい chart construction は不要。

Source index 再構築: 1,804 files / 29,261 declarations、終了コード0。`CheapAllocation` 名検索は0件。関連 production / Mathlib の対象名検索でも equivalent filter は見つからない。既存 branch selector や mod-42 transport を作り直していない。

## Arithmetic discrimination

DkMathTest の named theorem `candidate554_old_guards` は次をすべて確認する。

- `1 ∈ 554.divisors`、`Nat.Coprime 1 (554/1)`。
- `7^3 < 554`。
- `554 ≡ 1 (mod 7)`。
- `554^49 < 7^161 ≤ 64*554^49`（RHS の必要 size band）。
- `SixthPowerAllocationSieve 1 (554/1)`（既存 modulus-one theorem を再利用）。

`candidate554_rejected` は `¬ ModFortyTwoCheapAllocation 554 1`。したがって、旧数値ガードと trivial sixth-power sieve を満たしても、新 mod-42 数値 filter には落ちる具体例が得られた。テストでは旧ガードから新 filter が常に従うとの命題の否定も、この反例を使って固定した。

新 filter から旧**数値**ガードへの一般含意もテストした（mod 42 を mod 7 に縮小）。この一般含意と 554 の例で、数値ガードに対する追加 screening が確かめられる。ただし sixth-power sieve は新定義に含めないため、新 filter が任意の divisor でそれを含意するとは主張しない。

`candidate589_passes` は `ModFortyTwoCheapAllocation 589 1`、さらに `HasModFortyTwoCheapAllocation 589` も検証した。新 filter が全候補を排除するわけではない。589 の exact receiver や reconstruction witness の有無は、この結果からは分からない。

重要な区別: 554 のテストは `SixthPowerSievedNestedCondition 554` を真とするものではない。また固定 divisor `r=1` の排除だけから `¬ HasModFortyTwoCheapAllocation 554` を結論していない。新しい定理は reconstruction に対する必要条件であり、global witness absence / unconditional FLT7 / strict descent を示さない。

## Validation

2026-10-13、cwd `lean/dk_math`。Lean 4.34.1 / Lake 5.0.0-src+5045d00。

| Command | Exit | Result |
| --- | --- | --- |
| `python3 dkmath_theorems.py --db .dkmath-theorems.sqlite3 build --root .` | 0 | source index refreshed |
| index `search --name CheapAllocation --limit 20` | 0 | 0 hits |
| `lake env lean DkMathTest/FLT/Seven/ModFortyTwoCheapCalibration.lean` | 0 | two definitions / two implications / candidate comparisons accepted |
| `lake build DkMath.FLT.Seven.SevenRamifiedFusionModFortyTwoCheapAllocation` | 0 | `Build completed successfully (9089 jobs).` |
| `lake env lean DkMathTest/FLT/Seven/SevenRamifiedFusionModFortyTwoCheapAllocation.lean` | 0 | applications, decidability, discrimination, survivor and axiom audit accepted |

Calibration に literal `1^343` の自動評価 threshold warning（256）が出た。証明自体は成功。最終 test module に `exponentiation.threshold 400` を置いて warning を解消し、最終 test 出力は warning / error なし。失敗した証明試行や missing premise はない。9089 jobs は単一ターゲットの import 依存鎖を含み、変更モジュール数ではない。

付帯監査: `git diff --check` 終了コード0。新規5ファイルの whitespace / 検証ソース SHA-256 / 定義本文の禁止依存検査も終了コード0。禁止構文の `rg` 検索は終了コード1（一致なし）。`git diff --cached --name-only` は空で、`logs/` の ignore を確認。

実際の公理監査出力（production 二定理と named test 三定理）:

```text
'DkMath.FLT.Seven.sixthPowerSieved_implies_mod42Cheap' depends on axioms: [propext, Classical.choice, Quot.sound]
'DkMath.FLT.Seven.RamifiedSignedRootRoutingPacket.QuotientPrimeSupport.internalDepthFourReconstruction_implies_mod42Cheap' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'DkMathTest.FLT.Seven.candidate554_old_guards' depends on axioms: [propext, Classical.choice, Quot.sound]
'DkMathTest.FLT.Seven.candidate554_rejected' depends on axioms: [propext, Classical.choice, Quot.sound]
'DkMathTest.FLT.Seven.candidate589_passes' depends on axioms: [propext, Classical.choice, Quot.sound]
```

すべて標準 `[propext, Classical.choice, Quot.sound]` のみ。`sorryAx` なし。数値比較も Python 出力の転記ではなく Lean の証明。

## Files and durable evidence

追加ファイル（`lean/dk_math` から）:

- `DkMath/FLT/Seven/SevenRamifiedFusionModFortyTwoCheapAllocation.lean`（二定義、二定理）。
- `DkMathTest/FLT/Seven/SevenRamifiedFusionModFortyTwoCheapAllocation.lean`（比較・反例・一般適用・decidability・公理監査）。
- `docs/dev/FLT7-Mod42-AllocationSieve-261013-v0/findings-003.md`。
- 同ディレクトリ `report-003.md`。
- 同ディレクトリ `evidence/003-verification-summary.md`。

既存 Lean ソース / receiver / README / ROADMAP は変更していない。校正の重複証明は最終ファイルへ統合し、必要な検証を DkMathTest に残した。Raw transcripts は Git-ignored な `logs/` にのみ保存。durable evidence は Codex-reported と明記した小さな成功 / 公理出力・候補の意味・ソース SHA-256 に絞った。独立 reviewer rerun とは呼ばない。

## Next research proposal (not implemented)

レビュー後に、`M.divisors` 上の有限候補集合を定義し、固定 allocation の filter と存在 wrapper を有限列挙へ結ぶ API を検討できる。そこで候補削減数と生き残る divisor を区別して調べると、実際の screening 効果を測れる。sixth-power filter は別レイヤーに保ち、残存候補から endpoint witness を得る未解決問題を混同しない。

今回は指示書の最小数学実験で停止する。gate 004、Git add / commit / push、PR / merge は行わない。
