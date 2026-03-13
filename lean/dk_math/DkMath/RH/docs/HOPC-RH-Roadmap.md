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
   - 到達済み（RH-O1/O2/O3/O4/O5/O6/O7）:
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
   - 次の焦点:
     - `hAbs_dvd` / `hAbs_offdvd` の具体評価補題（CFBRC provider 連携）を追加
     - split bound 仮定を `BoundaryInsertLocalLiftProvider` レベルへ持ち上げる設計を追加
2. OP-004（曲率条件運用）を並行整理
   - `phaseCurv` 供給規約と wrapper 命名規約の整備
