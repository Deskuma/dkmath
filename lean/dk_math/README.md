# dk_math

presented by D. and Wise Wolf

## 概要

- dk_math は、Lean 4 用の数学ライブラリであり、
  特に動的調和数論（Dynamic Harmonic Number Theory, DHNT）に焦点を当てています。
- このライブラリは、単位と量の概念を導入し、数学的な定義や定理を形式化するためのツールを提供します。
- 現在の主軸は **FLT（フェルマーの最終定理）形式化** で、特に `d = 3` 周辺の複数アプローチを整備しています。
- Collatz・DHNT・宇宙式系は、FLT を支える周辺理論として継続開発中です。

## この README の役割

- このファイルは **Lean 実装の詳細入口**（モジュール一覧・ファイル導線・ビルド情報）を扱います。
- プロジェクト全体の進捗要約はルート [README.md](../../README.md) を参照してください。
- FLT 最新進捗の正本は [../../docs/PROJECT_STATUS.md](../../docs/PROJECT_STATUS.md) です。

## 最新ステータス（2026-03-08）

- 要点はルート [README.md](../../README.md) の「最新ステータス（2026-03-08）」に集約しています。
- 詳細分析は [../../docs/PROJECT_STATUS.md](../../docs/PROJECT_STATUS.md) を参照してください。

## カテゴリ

- 数学ライブラリ
  - DkMath
    - 基本定義とユーティリティ (Basic Definitions and Utilities)
    - 動的調和数論 (Dynamic Harmonic Number Theory, DHNT)
    - 宇宙式 (Cosmic Formula)
    - ポリオミノ (Polyomino)
    - 単位と量の理論 (Units and Quantities Theory)
    - FLT（フェルマーの最終定理）関連 (FLT-related)
    - Collatz予想関連 (Collatz-related)
    - ABC 予想関連 (ABC-related)
    - RH 関連 (RH-related)
    - KUS 関連 (KUS-related)
    - CFBRC 関連 (CFBRC-related)

## ファイル

- 動的調和数論 (DHNT) 主要ファイル一覧 (.lean):
  - Dynamic Harmonic Number Theory: [DHNT](./DkMath/DHNT.lean)
  - 宇宙式 [CosmicFormula](./DkMath/CosmicFormula.lean)
    - 定義群 [Defs](./DkMath/CosmicFormula/Defs.lean)
    - 基本版 [CosmicFormulaBasic](./DkMath/CosmicFormula/CosmicFormulaBasic.lean)
    - 線形代数版 [CosmicFormulaLinear](./DkMath/CosmicFormula/CosmicFormulaLinear.lean)
    - ジオメトリ（有限集合）版 [CosmicFormulaGeom](./DkMath/CosmicFormula/CosmicFormulaGeom.lean)
    - 次元版 [CosmicFormulaDim](./DkMath/CosmicFormula/CosmicFormulaDim.lean)
    - 二項定理版 [CosmicFormulaBinom](./DkMath/CosmicFormula/CosmicFormulaBinom.lean)
    - 指数版 [CosmicFormulaExp](./DkMath/CosmicFormula/CosmicFormulaExp.lean)
    - docs: (.md)
      - 宇宙式の基本説明 [CosmicFormula.md](./DkMath/CosmicFormula/docs/CosmicFormula.md)
      - 宇宙式の次元に関する定理 [CosmicFormulaCellDim.md](./DkMath/CosmicFormula/docs/CosmicFormulaCellDim.md)
  - トロミノ構造 [Tromino](./DkMath/Tromino.lean)
  - 宇宙式とトロミノ構造の接続定理 [CosmicFormulaTrominoLink](./DkMath/CosmicFormula/CosmicFormulaTrominoLink.lean)
- 基本定義とユーティリティ [Basic](./DkMath/Basic.lean)
- サンプル定理と例 [Samples](./DkMath/Samples.lean)
- 数学未解決問題（解決済み難問も含む）
  - フェルマーの最終定理（FLT）関連 [FLT](./DkMath/FLT.lean)
    - 実装ガイド [FLT/README.md](./DkMath/FLT/README.md)
    - prime-ge5 provider 本丸 [TriominoCosmicPrimeGe5](./DkMath/FLT/PrimeProvider/TriominoCosmicPrimeGe5.lean)
  - Collatz予想関連 [Collatz](./DkMath/Collatz/Collatz2K26.lean)
  - 宇宙式×FLT 接続 [TriominoFLT](./DkMath/CosmicFormula/TriominoFLT.lean)
  - ABC 予想系入口 [ABC](./DkMath/ABC.lean)
  - RH 系入口 [RH](./DkMath/RH.lean)
  - RH CFBRC 接続 [CFBRCBridge](./DkMath/RH/CFBRCBridge.lean)
  - KUS 系入口 [KUS](./DkMath/KUS.lean)
  - CFBRC Lean 入口 [CFBRC](./DkMath/CFBRC.lean)
  - Silver Ratio 入口 [SilverRatio](./DkMath/SilverRatio.lean)
  - UnitCycle 入口 [UnitCycle](./DkMath/UnitCycle.lean)
- 研究ノート（未整理のアイデアや証明のスケッチ）

## ビルド

- Lean 4 をインストール後、プロジェクトルートで `lake build` を実行してください。
- または `./lean-build.sh` を使用して、ビルドとドキュメント生成を一括で行うこともできます。（※現在は、ドキュメントは生成されません）

### Research ビルド

- 研究ビルド（未完成の定理やアイデアを含む）は `lake build DkMath.Research` または `./lean-build.sh DkMath.Research` で行います。
- これらは、本流からは外されています。補題・定理に sorry を含みます。
- ファイル名は `*Research.lean` で終わるものが対象です。
- 完成され次第、本流の `*.lean` ファイルに統合される予定です。

## ドキュメント

### 宇宙式の次元に関する定理

- [CosmicFormulaCellDimGuide](./DkMath/CosmicFormula/docs/CosmicFormulaCellDimGuide.md) に、宇宙式の次元に関する定理のガイドを掲載しています。

### CFBRC × GN × RH Bridge（概要）

- CFBRC は `cyclotomicPrimeCore` と `GN` を接続し、差冪・除法判定・valuation・原始素因子存在を扱う橋渡し層です。
- RH 側の [CFBRCBridge.lean](./DkMath/RH/CFBRCBridge.lean) は、その primitive-prime existence を `hopcPrimeContributionSum` と `stationaryAt` 判定へ接続します。
- 詳細は [DkMath/CFBRC/README.md](./DkMath/CFBRC/README.md) と [DkMath/RH/README.md](./DkMath/RH/README.md) を参照してください。

### Collatz ドキュメント（進捗）

- 実装報告: [IMPLEMENTATION_REPORT_20260130.md](./DkMath/Collatz/docs/IMPLEMENTATION_REPORT_20260130.md)
- 補助補題完成報告: [AUXILIARY_LEMMA_COMPLETION_20260130.md](./DkMath/Collatz/docs/AUXILIARY_LEMMA_COMPLETION_20260130.md)
- sorry 解消進捗: [SORRY_CLEANUP_PROGRESS_20260130.md](./DkMath/Collatz/docs/SORRY_CLEANUP_PROGRESS_20260130.md)

---

## 今後の展望

- **Slab 分解の API 整備**（命名・補題の粒度を固定し再利用性を上げる）
- **2D（トロミノ/図形）側とのリンク強化**（既存平面コードとの往復補題）
- **一般化宇宙式（他の形状、他の分割ルール）** への拡張
- `Nat` 以外（`ℤ`, `ℚ`, `ℝ`）への持ち上げと、解析的道具（生成関数など）との接続

---

## 引用・ライセンス

- MIT License
- 研究利用の場合は、該当する定理名・ファイル名を併記してください

---
