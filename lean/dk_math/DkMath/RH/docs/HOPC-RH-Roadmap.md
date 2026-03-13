# HOPC-RH Roadmap

`#HOPC-RH`（Holo Orthogonal Phase–Curvature method）の
Lean 実装ロードマップを 1 枚で管理するための文書。

## 目的

- RH の即時証明主張ではなく、観測器 API を段階的に整備する。
- prime-local contribution 言語で CFBRC と接続できる構成を維持する。
- `arg` の枝問題を避け、`phaseVel` / `phaseUnwrap` 中心で進める。

## 実装レイヤ

1. 位相ドリフト骨格
2. 単一素数因子 API
3. 曲率 API
4. 有限 Euler 積観測 API
5. HOPC 公開名（CFBRC 連携）API
6. docs / glossary / open problems

## フェーズと状態

### A. 用語・基礎定義

- 目標:
  - `phaseVel`, `driftFreeAt`, `phaseCurv` 等の基礎語彙を固定
- 状態: 完了
- 主ファイル:
  - `DkMath/RH/Defs.lean`
  - `DkMath/RH/Lemmas.lean`

### B. 単一素数因子解析

- 目標:
  - `w_p(t) = exp((σ+it)log p) - 1` の導関数・位相速度補題
- 状態: 完了
- 主ファイル:
  - `DkMath/RH/EulerZetaLemmas.lean`

### C. 曲率（2 次情報）

- 目標:
  - `phaseCurv` と停留・非退化停留 API
- 状態: 完了
- 主ファイル:
  - `DkMath/RH/Defs.lean`
  - `DkMath/RH/Lemmas.lean`
  - `DkMath/RH/EulerZetaLemmas.lean`

### D. 有限 Euler 積（積→和）

- 目標:
  - 有限積の位相速度を局所寄与有限和へ落とす
- 状態: 完了
- 主ファイル:
  - `DkMath/RH/EulerZeta.lean`
  - `DkMath/RH/Lemmas.lean`
  - `DkMath/RH/EulerZetaLemmas.lean`

### E. `eulerZetaFinite_onVertical` 本体接続

- 目標:
  - 本体側でも停留/非退化停留を有限寄与和で判定
- 状態: 完了
- 主ファイル:
  - `DkMath/RH/EulerZetaLemmas.lean`

### F. 明示和への正規化

- 目標:
  - `∑ (log p - phaseVel(w_p))` 形へ API を統一
- 状態: 完了
- 主ファイル:
  - `DkMath/RH/EulerZetaLemmas.lean`

### G. HOPC 公開名（CFBRC 導線）

- 目標:
  - `hopcPrimeLocalContribution`
  - `hopcPrimeContributionSum`
  - 停留判定 wrapper の公開
- 状態: 完了
- 主ファイル:
  - `DkMath/RH/EulerZeta.lean`
  - `DkMath/RH/EulerZetaLemmas.lean`

### H. 文書同期（Discussion / README）

- 目標:
  - 議論文書から実装 API へ直接ジャンプ可能にする
- 状態: 完了
- 主ファイル:
  - `DkMath/RH/README.md`
  - `DkMath/RH/docs/README.md`
  - `DkMath/RH/docs/RH-CFBRC-Discussion.md`

### I. 次段（未完）

- 目標候補:
  - `HOPC-RH-Glossary.md`（用語集, 作成済み）
  - `HOPC-RH-OpenProblems.md`（未解決タスク, 作成済み）
  - finite から infinite への接続条件整理（収束・非零・停留の整合）
- 状態: 進行中（OP-001 着手、OP-003 完了）

## 参照導線

- 方針本文: `HOPC-RH.txt`
- 用語集: `HOPC-RH-Glossary.md`
- 未解決タスク: `HOPC-RH-OpenProblems.md`
- CFBRC 連携議論: `RH-CFBRC-Discussion.md`
- 詳細解説: `README.md`
- 実装履歴: `RH_Implements_History.md`

## Next Sprint（短期実装順）

次スプリントは OP-001 を主軸として進める。

1. OP-001（finite→infinite 接続）を継続
   - 到達済み（RH-O1/O2/O3/O4/O5/O6/O7/O8/O9/O10/O11/O12/O13/O14/O15/O16/O17/O18/O19/O20/O21/O22）:
     - `HopcInfiniteLift.lean` を追加
     - `HasSum` 仮定から `hopcPrimeContributionSum` の atTop 極限へ接続
     - `Summable + tsum=0` 仮定から同極限へ接続
     - majorant 比較 (`|hopc| ≤ g`, `Summable g`) から `Summable` へ接続
     - `eventually stationary` から
       `eventually hopcPrimeContributionSum = 0` と
       `hopcPrimeContributionTsum = 0`（`Summable` 併用）へ接続
     - `C / p^σ`（`σ > 1`）型上界から `Summable` / majorant / atTop 極限を供給
     - `σ > 1` から `hPrime_ne` を自動供給する wrapper を追加
     - `BoundarySide` split 上界（divide/off-divide）から `hAbsLe` を合成し、
       `tsum=0` / atTop 極限へ接続
     - local-zero 仮定から `hAbs_dvd` / `hAbs_offdvd` を具体供給し、
       split bound 前提を簡約
     - off-dvd local-zero を record 化し、provider 版 wrapper へ統一
     - `BoundaryInsertLocalLiftProvider` から
       `BoundaryOffDvdLocalZeroProvider` への変換規則を追加
     - `BoundaryInsertLocalLiftProvider` を直接受ける
       `prime_rpow_bound/tsum/tendsto` 高位 wrapper を追加
     - off-dvd 側の `w_p ≠ 0` / factor0 を
       `BoundaryOffDvdFactorZeroProvider` として record 化
     - `BoundaryOffDvdFactorZeroProvider` を
       insert-provider 直結の高位 wrapper へ統合
     - `BoundaryOffDvdFactorZeroProvider` の標準構成器
       （split / nonzero+local-zero / insert-provider 経由）を追加
     - singleton `S={r}` で、
       insert-provider の `hsum_lift` から off-dvd local-zero を抽出する補題を追加
     - `BoundaryOffDvdLocalZeroOnSetProvider` を導入し、
       singleton 抽出結果を on-set provider として公開
     - 一般有限集合 `S` 版の 1点抽出補題
       （`S.erase r` 上 local-zero 仮定つき）を追加
     - 一般有限集合 `S` 版の on-set provider 構成器
       （witness + local-zero-on-erase 入力）を追加
     - RH-O15 の `hlocal_erase` を、
       factor0 + divisibility（erase / 全体 `S`）から内部生成する wrapper を追加
     - RH-O17 として、一般有限集合 `S` 抽出 wrapper 群の witness 入力から
       `p ∉ S` 条件を除去
     - RH-O18 として、on-set provider 構成器の witness 前提を
       `global witness` 版へ簡約し、
       `CFBRC` primitive-prime existence 直結 wrapper を追加
     - RH-O19 として、`BoundaryInsertLocalLiftProvider` 単体では
       witness existence を内包しないことを API で明確化し、
       `BoundaryGlobalWitnessProvider` /
       `BoundaryGlobalWitnessLocalZeroProvider` を導入
     - RH-O20 として、witness 分離 provider 前提の高位 API を
       命名統一（`..._of_globalWitnessProvider...`）し、
       `BoundaryDiffPowFactorZeroProvider` 導入で前提を record 化
     - RH-O21 として、旧 `..._global_witness...` 命名に
       `deprecated` 属性を付与し、移行先 wrapper を明示
     - RH-O22 として、`CFBRCBridge` 内部呼び出しを
       旧命名依存から新命名 / 非 legacy 経路へ移行し、
       旧命名 API の削除候補日を `2026-06-30` に固定
   - 次の焦点:
     - RH-O24: 未公開運用前提を確認し、外部依存監視タスクをクローズ
     - 旧命名 API 削除は `2026-06-30` を目安に公開計画と合わせて再判定
2. OP-004（曲率条件運用）を並行整理
   - `phaseCurv` 供給規約と wrapper 命名規約の整備
