# RH Implements History

## RH 実装の記録

RH: Riemann Hypothesis を説明するための補題群の実装に関する記録

## 記録内容テンプレート（例）

### 日時: 2026/03/12 21:49: 概要見出し

1. 目的: RH の実装履歴の記録と要約
2. 内容:
   - RH の実装の概要と目的
   - 主要なファイル構成とその役割
   - 実装の目的と今後の展開
3. 結論: RH の実装は数式の構造解析と数値実験の基盤を提供するものであり、今後の展開が期待される。
4. 失敗事例: 特に大きな失敗はないが、数値実験の精度向上や複雑な性質の証明にはさらなる工夫が必要である。
5. 備考: 追加の詳細や数値実験の結果は、関連するドキュメントやノートブックに記録されている。
6. 次の課題: より高度な性質の証明や数値実験の拡充を行うこと。

---

## 実装履歴

※ここに上記テンプレートに沿った実装履歴を記録していく。

### 日時: 2026/03/12 21:12 JST: HOPC-RH × CFBRC 連携の事前調査（実装計画の準備）

1. 目的: RH 側の現状実装と HOPC-RH 方針を照合し、`CFBRC` 観測器との連携実装に向けた着手順を確定する。
2. 内容:
   - 参照資料を読解:
     - `RH/docs/RH-CFBRC-Discussion.md`
     - `RH/docs/HOPC-RH.txt`
     - `RH/docs/README.md`
   - RH 実装本体を確認:
     - `Defs.lean`: `vertical`, `torque`, `phaseVel`, `phaseUnwrap`, `driftFreeAt`
     - `EulerZeta.lean`: `w(p,σ,t)`, magnitude/phase 定義、`eulerZetaMag`
     - `EulerZetaConvergence.lean`: `σ>1` での `Multipliable` と正値
   - 健全性確認:
     - `lake build DkMath.RH` 成功
     - `DkMath/RH` 配下に `sorry` は検出されず（`rg` ベース確認）
   - 実装ギャップを特定:
     - HOPC-RH 優先度 B/C/D（単一因子位相速度・曲率・有限 Euler 積観測量）が未着手
     - CFBRC 連携の `prime-local contribution` 共通 API が未定義
3. 結論: RH 側は「位相骨格 + magnitude 収束」まで到達済みで、次段は
   `single-prime phase API -> finite Euler HOPC API -> CFBRC bridge` の順に進めるのが最短。
4. 失敗事例:
   - `rg "sorry"` はヒットなし時に終了コード 1 を返すため、確認時は「エラー」ではなく「未検出」として解釈が必要。
5. 備考:
   - HOPC-RH 文書の禁止事項（RH 証明主張・枝問題無視・誇張）を実装方針の制約として採用する。
6. 次の課題:
   - Phase RH-B1（単一素数因子位相 API）を開始:
     - `w_p` の導関数補題
     - `phaseVel` を `w_p` へ適用した明示式補題
     - `driftFreeAt` との接続補題
