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
- 状態: 一部完了（Glossary/OpenProblems 完了）

## 参照導線

- 方針本文: `HOPC-RH.txt`
- 用語集: `HOPC-RH-Glossary.md`
- 未解決タスク: `HOPC-RH-OpenProblems.md`
- CFBRC 連携議論: `RH-CFBRC-Discussion.md`
- 詳細解説: `README.md`
- 実装履歴: `RH_Implements_History.md`

## Next Sprint（短期実装順）

次スプリントは OP-003 を継続しつつ、OP-001 の接続設計へ入る。

1. OP-003（CFBRC 連携の実定理）を継続
   - 到達済み:
     - singleton → small finite-set への持ち上げ（RH-N1/N2）
     - `BoundarySide` 統一高位 API（RH-N3）
     - README / Discussion / docs README の利用テンプレート同期（RH-N4/N5）
   - 次の焦点:
     - provider 層（実際の `hS_lift` / `hsum_lift` 供給）との直結補題
2. OP-001（finite→infinite 接続）へ着手
   - 目標: `hopcPrimeContributionSum` の極限接続条件（収束/極限交換）を整理
   - 具体: まずは条件列挙と補題インタフェース設計を先に固定する

理由:

- OP-003 の API 骨格は RH-N5 で一段落したため、
  次は供給層の実装と finite→infinite 接続を並行管理する段階に入ったため。
