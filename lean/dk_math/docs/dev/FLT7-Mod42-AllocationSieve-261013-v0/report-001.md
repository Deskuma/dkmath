# report-001 — primitive seventh residues modulo 6

**Outcome A** — 指定した二定理を、要求どおりの coprimality 仮定で Lean カーネル検証済み。

## 実装範囲

instruction-001 / gate 001 の二つの算術定理。allocation receiver の変更、mod 42、gate 002 は実装していない。

## 宣言と証明

Production module: `DkMath.FLT.Seven.SevenRamifiedFusionModSixResidues`。

```lean
theorem alternatingCyclotomicSeven_mod_six_of_coprime
    {x y : ℕ} (hxy : Nat.Coprime x y) :
    Nat.ModEq 6 (alternatingCyclotomicSeven x y) 1

theorem GN_seven_mod_six_of_coprime
    {D u : ℕ} (hDu : Nat.Coprime D u) :
    Nat.ModEq 6 (GN 7 D u) 1
```

互いに素の仮定から「2を共有しない」「3を共有しない」を private lemma で導く。mod 6 の36対のうち12対をこの仮定で排除し、24対で多項式の値を `decide` によりカーネル還元する。任意の自然数を剰余へ移す等式を証明しているため、有限の数値サンプルだけの検査ではない。

交代因子には既存の `alternatingCyclotomicSeven_intCast` を使い、自然数除算を整数多項式へ正当に移す。GN には既存の `GN_seven_eq_gap_mul_add_seven_mul_y_pow_six` を使う。GN の引数は gap `D` と unit `u` で、通常の同次因子の端点は `D+u,u`。`gcd(D+u,u)=gcd(D,u)` であり仮定は十分。今回の直接展開証明は端点への新しい API を必要としない。

直接 import は次の2本:

- `DkMath.FLT.Seven.SevenBaseTerminalRowZAlternatingPowerSplit`（自然交代因子と整数変換。GN 展開も依存関係から利用可能）
- `Mathlib.Data.ZMod.Basic`（剰余への cast と ModEq の変換）

既存 receiver モジュールや FLT7 closing theorem を追加 import していない。重複調査と既存宣言の確認は findings-001 に記録。

既存モジュールのソースは変更していない。focused build はこの単一ターゲットの import 依存鎖を再コンパイルする。ビルド対象に現れる依存モジュール数は今回の変更ファイル数ではない。

## 数学的観察と Lean examples

DkMathTest の検証モジュールに以下を残した。

- 二つの一般定理の proof-level 適用。
- `(0,1)` の交代因子、`(1,0)` の GN: 正の端点の仮定は不要。
- `(2,3)` の両因子: 個々の端点が mod 6 の単元である必要はない。
- `(2,2)` の両因子は residue 1 ではない。互いに素の仮定を無条件で削除する一般化は偽。
- `(5,5)` は互いに素ではないが、両因子とも residue 1。逆向きの「residue 1 → coprime」も偽。

数学的には全体の coprimality より「2と3を共有しない」という局所条件で証明が進む。しかし新しい公開 API は要求通り二つに留めた。残存候補があるため、この合同式は必要条件であり receiver の空性や FLT7 を示さない。

## 次の提案（gate 002、未実装）

GN branch では `r ∣ M` と `Nat.Coprime u (7*M)` から `Nat.Coprime (7^27*r^49) u` を証明する。RHS branch は既存の `u<D` と `Nat.Coprime u D` から `Nat.Coprime u (D-u)` を得る。それぞれ今回の定理と残余等式で `7*s^49 ≡ 1 (mod 6)` を得て、`s^49 ≡ s (mod 6)` により `s ≡ 1 (mod 6)`、既存 mod 7 と合わせ mod 42 とする。GN receiver に divisor guard がない点を維持する。

## 実行結果と公理監査

すべて nested Lake cwd `lean/dk_math` で実行。

| Command | Exit status | Result |
| --- | --- | --- |
| `python3 dkmath_theorems.py --db .dkmath-theorems.sqlite3 build --root .` | 0 | 1,802 files / 29,253 declarations |
| index `search --name nestedAllocation_residue_sieve --full` | 0 | 1 declaration、実ソース確認 |
| index `search --name alternatingCyclotomicSeven --limit 40` | 0 | 14 declarations、既存 mod 6 定理なし |
| `lake env lean DkMathTest/FLT/Seven/ModSixCalibration.lean`（初回） | 1 | 戦術失敗。反例ではない |
| 同 calibration（戦術修正後） | 0 | 二つの一般定理成功、production に移行 |
| `lake build -j 1 DkMath.FLT.Seven.SevenRamifiedFusionModSixResidues` | 1 | 現行 Lake は `-j` 非対応 |
| `lake build DkMath.FLT.Seven.SevenRamifiedFusionModSixResidues` | 0 | 単一ターゲットと依存鎖、9011 jobs、成功 |
| `lake env lean DkMathTest/FLT/Seven/SevenRamifiedFusionModSixResidues.lean` | 0 | 全 examples と公理監査成功 |
| `git diff --check` | 0 | 既存追跡ファイルの差分なし |
| `git diff --no-index --check /dev/null <new file>`（新規 Lean / findings / report の4ファイル） | 0 | 新規ファイルの空白検査も成功 |

`#print axioms` の実出力:

```text
'DkMath.FLT.Seven.alternatingCyclotomicSeven_mod_six_of_coprime' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'DkMath.FLT.Seven.GN_seven_mod_six_of_coprime' depends on axioms: [propext, Classical.choice, Quot.sound]
```

両定理とも `propext` / `Classical.choice` / `Quot.sound` のみ。`sorryAx` や追加の未検証公理なし。新規 Lean 二ファイルの禁止構文検索はヒットなし。環境は Lean 4.34.1 / Lake 5.0.0-src+5045d00。

## 追加ファイル一覧

既存ソースの編集はなく、以下を追加した（パスは `lean/dk_math` から）。

- `DkMath/FLT/Seven/SevenRamifiedFusionModSixResidues.lean`: 二つの公開定理と一つの private 補助定理。
- `DkMathTest/FLT/Seven/SevenRamifiedFusionModSixResidues.lean`: 一般適用、具体例、偽一般化の反例、公理監査。
- `docs/dev/FLT7-Mod42-AllocationSieve-261013-v0/findings-001.md`
- `docs/dev/FLT7-Mod42-AllocationSieve-261013-v0/report-001.md`
- 同ディレクトリ `logs/calibration-first.txt`: 初回エラー全文。
- `logs/calibration-fixed.txt`: 修正後の成功ログ（出力なし）。
- `logs/focused-build-command-error.txt`: `-j` の非対応エラー。
- `logs/focused-build.txt`: focused build 全出力。
- `logs/tests-and-axioms.txt`: examples と公理監査の全出力。

一時 calibration の重複証明は最終ファイルに統合した。README / ROADMAP の編集はない。instruction-001 をここで終了する。
