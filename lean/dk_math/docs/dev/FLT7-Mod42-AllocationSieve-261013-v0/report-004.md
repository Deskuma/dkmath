# report-004 — global rejection and infinite-survivor audit

**Outcome A**: core 554 の全 divisor 排除と、sixth-power condition を含めた cheap candidates の無界族を Lean で証明。

## API

Production module: `DkMath.FLT.Seven.SevenRamifiedFusionModFortyTwoCheapBoundaryAudit`。

```lean
namespace DkMath.FLT.Seven

theorem no_mod42Cheap_at_554 : ¬ HasModFortyTwoCheapAllocation 554

theorem mod42Cheap_family (k : ℕ) :
    ModFortyTwoCheapAllocation (631 + 42 * k) 1

theorem mod42Cheap_family_has (k : ℕ) :
    HasModFortyTwoCheapAllocation (631 + 42 * k)

theorem mod42Cheap_family_sixthPower (k : ℕ) :
    SixthPowerAllocationSieve 1 ((631 + 42 * k) / 1)

theorem mod42Cheap_survivors_unbounded (B : ℕ) :
    ∃ k : ℕ, B < 631 + 42 * k ∧
      ModFortyTwoCheapAllocation (631 + 42 * k) 1 ∧
      SixthPowerAllocationSieve 1 ((631 + 42 * k) / 1)

namespace RamifiedSignedRootRoutingPacket.QuotientPrimeSupport

theorem no_reconstruction_of_core_eq_554 (p : RamifiedSignedRootRoutingPacket)
    (hcore : internalDepthFourSeventhCore p = 554) :
    ¬ InternalDepthFourCounterexampleReconstructionObligation p
```

直接 import は既存 `SevenRamifiedFusionModFortyTwoCheapAllocation` のみ。既存 receiver / stable FLT7 proof / README / ROADMAP は変更していない。

## Mathematical reasoning and source reuse

554 の任意の cheap allocation divisor は `Nat.pos_of_mem_divisors` により正。`r≥2` なら `Nat.pow_le_pow_left` により `r^7≥128`、coarse guard は `343*r^7<554` なので矛盾する。従って `r=1`。`554/1` が mod 42 で1でないことを Lean の `decide` で確認して排除する。前 gate の fixed-divisor exclusion から、今回は全 divisor を量化した否定に進んだ。

family はすべて `M=631+42*k`、`r=1`。divisor membership、coprimality、`343<M`、mod 42 を証明する。GN-side の threshold は base integer inequality `7^161<631^49` を `decide` でチェックし、自然数冪の単調性で全 k に運ぶ。RHS band を使う族ではない。

`mod42Cheap_family_sixthPower` は既存 `sixthPowerAllocationSieve_mod_one` の適用のみ。`mod42Cheap_survivors_unbounded B` は index `k=B` を具体的に与え、任意の上界 B より大きい core が両条件を通過する。テストで `k↦631+42*k` の単射性も証明した。従って bounded samples ではなく、相異なる自然数 core の無限族である。

conditional reconstruction consumer は gate-003 の `internalDepthFourReconstruction_implies_mod42Cheap` と全 divisor 排除を合成するだけ。実際の packet に core=554 を持つものが存在するとは主張しない。既存 `internalDepthFourReconstruction_false_of_core_le_343` は554に適用できないが、他の source constraints が554を既に排除する可能性までは否定しない。

Source index build は 1,805 files / 29,265 declarations、exit 0。`search --name mod42Cheap --limit 20` は既存 gate-003 の二含意のみ。既存 predicates、mod-42 bridge、modulus-one sieve、threshold と DepthFourReconstructionAudit の statements を再確認した。新しい対象の重複定理は見つからない。

## Strength and limits

**Proved:** core 554 には cheap allocation がない。631+42*k は無限に多くの相異なる core を与え、cheap filter と divisor-one sixth-power sieve を通る。既存 test theorem を再利用し、589 が通過することも対比した。

**Not proved:** passing cores が実際の packet の core として現れること、GN / RHS の exact endpoint equation、一般の reconstruction failure、FLT7 closure。無限の cheap survivors は FLT7 counterexamples ではない。

現在の必要条件集合だけから全候補の不在は導けない。無界なモデルが今回構成され、同じ filter の反復適用ではそれを消せない。将来のすべての合同式強化が不可能だという一般定理を証明したわけでもない。候補数を任意の moduli で減らすだけでは無条件定理への根拠にならず、actual outer/inner carrier・整数 chart・endpoint を結ぶ **source-coupled constraints** が次の研究対象になる。

具体的には、実際の core / complementary factor / outer-root product の既存 exact ledger と prime-support transport が、chosen divisor と endpoint residual に課す追加条件を調べる。その条件を、抽象的な cheap survivor ではなく実際の packet に対して証明し、何が族から排除できるかを裁く。今回は追加 moduli・新 source predicate・その接続を実装していない。

## Validation and attempts

Date: 2026-10-13。cwd: `lean/dk_math`。Lean 4.34.1 / Lake 5.0.0-src+5045d00。

| Command | Exit | Result |
| --- | --- | --- |
| `lake env lean DkMathTest/FLT/Seven/ModFortyTwoBoundaryCalibration.lean`（初回） | 1 | `/1` 除去を `change` だけで行うと失敗 |
| 同 calibration（修正後） | 0 | `rw [Nat.div_one]` で成功 |
| `lake build DkMath.FLT.Seven.SevenRamifiedFusionModFortyTwoCheapBoundaryAudit DkMathTest.FLT.Seven.SevenRamifiedFusionModFortyTwoCheapAllocation` | 0 | focused module と再利用する既存 test dependency、9091 jobs |
| `lake env lean DkMathTest/FLT/Seven/SevenRamifiedFusionModFortyTwoCheapBoundaryAudit.lean`（初回） | 1 | injectivity example の lambda 未展開で omega 失敗 |
| 同 final test（修正後） | 0 | 全 applications / 554・589・631・673 / base inequality / injectivity / audit 成功、warning/error なし |

二つの失敗は戦術上の型/展開の問題。false mathematical target、missing premise、hidden hypothesis はない。最終 tests は一般の無界 theorem を適用する proof-level example も含む。9091 は依存鎖を含む job 数であり変更モジュール数ではない。

全六 exports の実際の公理監査:

```text
'DkMath.FLT.Seven.no_mod42Cheap_at_554' depends on axioms: [propext, Classical.choice, Quot.sound]
'DkMath.FLT.Seven.mod42Cheap_family' depends on axioms: [propext, Classical.choice, Quot.sound]
'DkMath.FLT.Seven.mod42Cheap_family_has' depends on axioms: [propext, Classical.choice, Quot.sound]
'DkMath.FLT.Seven.mod42Cheap_family_sixthPower' depends on axioms: [propext]
'DkMath.FLT.Seven.mod42Cheap_survivors_unbounded' depends on axioms: [propext, Classical.choice, Quot.sound]
'DkMath.FLT.Seven.RamifiedSignedRootRoutingPacket.QuotientPrimeSupport.no_reconstruction_of_core_eq_554' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

sixth-power family は `propext` のみ。他の五定理は標準 `[propext, Classical.choice, Quot.sound]`。`sorryAx` / fresh axiom なし。禁止構文検索はヒットなし（rg exit 1）。`git diff --check` exit 0、staging は空、logs は ignored。

## Files and evidence

追加（`lean/dk_math` から）:

- `DkMath/FLT/Seven/SevenRamifiedFusionModFortyTwoCheapBoundaryAudit.lean`（六定理）。
- `DkMathTest/FLT/Seven/SevenRamifiedFusionModFortyTwoCheapBoundaryAudit.lean`（一般適用、対比、無限族の単射性、公理監査）。
- `docs/dev/FLT7-Mod42-AllocationSieve-261013-v0/findings-004.md`。
- 同ディレクトリ `report-004.md`。
- 同ディレクトリ `evidence/004-verification-summary.md`。

校正の重複証明は最終ファイルへ移した。証拠は Codex-reported と明記し、compact success / axiom output と source SHA-256 のみ。独立 reviewer rerun とは呼ばない。Raw / failed transcripts は ignored な logs に留めた。

instruction-004 をここで終了する。Git staging / commit / push / branch / PR / merge は行っていない。
