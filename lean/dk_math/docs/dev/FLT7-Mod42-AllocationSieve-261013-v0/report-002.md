# report-002 — divisor-aware mod-42 allocation filter

**Outcome A** — 三つの要求 API を追加 positivity 仮定なしで実装し、focused build / tests / axiom audit 成功。

## 実装範囲と API

対象は instruction-002 / gate 002 の必要条件と exclusion consumer。
Production module は `DkMath.FLT.Seven.SevenRamifiedFusionModFortyTwoAllocationSieve`。

```lean
theorem nestedAllocation_mod_six {M r : ℕ}
    (hdiv : r ∣ M)
    (h : NestedGNAllocationCondition M r ∨ NestedRHSAllocationCondition M r) :
    Nat.ModEq 6 (M / r) 1

theorem nestedAllocation_mod_fortyTwo {M r : ℕ}
    (hdiv : r ∣ M)
    (h : NestedGNAllocationCondition M r ∨ NestedRHSAllocationCondition M r) :
    Nat.ModEq 42 (M / r) 1

theorem nestedAllocation_excluded_of_mod_fortyTwo {M r : ℕ}
    (hdiv : r ∣ M)
    (hbad : ¬ Nat.ModEq 42 (M / r) 1) :
    ¬ (NestedGNAllocationCondition M r ∨ NestedRHSAllocationCondition M r)
```

要求された divisor guard を三宣言すべてで保持した。追加の positivity 仮定なし。既存 receiver の定義・既存 FLT7 証明の変更なし。

## 再利用と数学的理由

直接 import は次の二つ。

- `DkMath.FLT.Seven.SevenRamifiedFusionModSixResidues`
- `DkMath.FLT.Seven.SevenRamifiedFusionAllocationResidueSieve`

`D = 7^27*r^49`, `s = M/r` とする。

GN branch では `Nat.Coprime u (7*M)` と `7 ∣ 7*M` から `Nat.Coprime u 7`、`r ∣ M ∣ 7*M` から `Nat.Coprime u r` を `of_dvd_right` で得る。`pow_right` と `mul_right` を用いて `Nat.Coprime u D`、対称化して `Nat.Coprime D u` を得る。既存 `GN_seven_mod_six_of_coprime` と exact residual equation により `7*s^49 ≡ 1 (mod 6)`。

RHS branch では `u<D` の弱化 `u≤D` と既存 `Nat.coprime_sub_self_right` で `Nat.Coprime u (D-u)` を得る。自然数の減算を保持し、既存 `alternatingCyclotomicSeven_mod_six_of_coprime` と exact residual equation で同じ合同式を得る。

private helper `fortyNinth_power_mod_six` は任意の自然数を mod 6 の剰余に移し、6ケースを `decide` でカーネル還元して `s^49 ≡ s (mod 6)` を証明する。単元条件なし、ゼロを含む。private helper `complementary_mod_six` は `7≡1 (mod 6)` との乗算と推移律で `s≡1 (mod 6)` を回収する。

既存 `nestedAllocation_residue_sieve` の `s≡1 (mod 7)` と、既存 Mathlib `Nat.modEq_and_modEq_iff_modEq_mul`（`Nat.Coprime 6 7`）により mod 42 に合成する。新しい CRT や conditional mod-3 filter は再実装していない。

## 検証内容と推論の境界

DkMathTest の検証モジュールに各 export の一般適用を配置した。power の具体例は 0,2,3,5 を含み、非単元を落とさない。CRT の一般適用と具体例 589、mod 7 は通るが mod 42 は落ちる 8 を検査する。

`M=1,r=2,u=2` は `Nat.Coprime u (7*M)` を満たすが、`r ∣ M` と `Nat.Coprime r u` を満たさず、さらに `Nat.Coprime D u` も成立しない。この反例が否定するのはガードなしの coprimality transport であり、receiver の全 residual equation が成立するとの主張ではない。unguarded receiver theorem 全体の反例とは呼ばない。

`M=8,r=1` の mod-42 失敗は新しい exclusion consumer で排除する。一方 `M=1,r=1` は divisor guard と mod-42 必要条件を満たすが、既存 GN threshold / alternating coarse bound により両 receiver を排除できる。これは必要条件が十分条件でないことの具体的な Lean 証拠となる。

数学的には RHS branch の mod-6 輸送自体に `r ∣ M` は不要だが、共通 API は GN branch に必要な guard を保持する。`M>0` や `r>0` を追加する必要はなかった。小さい surviving residue の排除は一般の receiver 空性を意味しない。589 の合同式通過も witness を与えない。

## gate 003 の提案（未実装・レビュー待ち）

wrapper を作る前に、既存 `SixthPowerSievedNestedCondition` の divisor membership から今回の guard が得られる consumer を検討する。追加の必要合同式を exact receiver を保ったまま前置できるが、新しい wrapper の価値はユーザー向け consumer の有無で判断する。reconstruction obligation の inhabitance、global empty receiver、無条件 FLT7、strict descent は証明していない。instruction-003 には進んでいない。

## 検証結果

2026-10-13、cwd は `lean/dk_math`。環境: Lean 4.34.1 / Lake 5.0.0-src+5045d00。

| Command | Exit | Result |
| --- | --- | --- |
| `lake env lean DkMathTest/FLT/Seven/ModFortyTwoCalibration.lean`（API type check） | 0 | coprimality / ModEq の実際の型を確認 |
| 同 calibration（proof 追加後） | 0 | power / recovery helpers と三 API が初回で成功 |
| `lake build DkMath.FLT.Seven.SevenRamifiedFusionModFortyTwoAllocationSieve` | 0 | `Build completed successfully (9087 jobs).` |
| `lake env lean DkMathTest/FLT/Seven/SevenRamifiedFusionModFortyTwoAllocationSieve.lean` | 0 | 全 examples と公理監査成功 |

focused build は一つの新規 production module とその import 依存鎖を検証した。9087 は job 数であり変更ファイル数ではない。校正の重複証明は production に移し、有益な検証は最終 DkMathTest モジュールに保存した。証明の失敗試行・追加仮定・Lean 検証の未解消制限はない。

実際の `#print axioms` 出力:

```text
'DkMath.FLT.Seven.nestedAllocation_mod_six' depends on axioms: [propext, Classical.choice, Quot.sound]
'DkMath.FLT.Seven.nestedAllocation_mod_fortyTwo' depends on axioms: [propext, Classical.choice, Quot.sound]
'DkMath.FLT.Seven.nestedAllocation_excluded_of_mod_fortyTwo' depends on axioms: [propext, Classical.choice, Quot.sound]
```

全 exports が `[propext, Classical.choice, Quot.sound]` のみ。`sorryAx` なし。新規二 Lean ファイルの禁止構文検索はヒットなし（`rg` 終了コード1は一致なし）。`git diff --check` は終了コード0。新規5ファイルへの `git diff --no-index --check /dev/null <file>` は差分ありの終了コード1、空白エラーの出力なし。全7ファイルをステージ後、`git diff --cached --check` も終了コード0。

## ファイル差分と証拠

`lean/dk_math` からの相対パス:

- 追加: `DkMath/FLT/Seven/SevenRamifiedFusionModFortyTwoAllocationSieve.lean`（3 exports、2 private helpers）。
- 追加: `DkMathTest/FLT/Seven/SevenRamifiedFusionModFortyTwoAllocationSieve.lean`（一般適用・反例・非十分性・power/CRT examples・3公理監査）。
- 追加: `docs/dev/FLT7-Mod42-AllocationSieve-261013-v0/findings-002.md`。
- 追加: 同ディレクトリ `report-002.md`。
- 追加: 同ディレクトリ `evidence/002-verification-summary.md`（Codex-reported、終了コード・最小の成功出力・公理出力・検証ソースの SHA-256）。
- 更新: 同ディレクトリ `README.md` / `ROADMAP.md` の gate-002 完了・レビュー待ち注記のみ。

既存 Lean ファイルと receiver は変更なし。`logs/` は Git-ignored を確認し、Git の対象に含めない。独立した reviewer による再実行とは呼ばない。指示書末尾に従い今回の狭い成果物をコミット対象とする。通常環境の `git add` は `.git/index.lock` が read-only のため終了コード128だったが、Git メタデータ書込みを許可された実行で同じ7ファイルだけをステージし終了コード0。`git diff --cached --name-only` で logs 不在を確認した。

instruction-002 をここで終了し、instruction-003 には進まない。
