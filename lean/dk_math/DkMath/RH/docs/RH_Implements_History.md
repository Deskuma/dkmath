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

### 日時: 2026/03/12 21:28 JST: Phase RH-B1 を実装（単一素数因子 `w_p` の位相 API）

1. 目的: HOPC-RH 優先度 B に沿って、単一素数因子
   `w_p(t) = exp((σ+it)log p) - 1` の位相観測を Lean 補題として直接使える形にする。
2. 内容:
   - 変更ファイル:
     - `DkMath/RH/EulerZetaLemmas.lean`
   - 依存追加:
     - `import DkMath.RH.Lemmas`（`driftFreeAt ↔ phaseVel=0` 再利用）
   - 追加補題:
     - `hasDerivAt_vertical_mul_log_p`
     - `hasDerivAt_eulerZeta_exp_s_log_p_sub_one`
     - `deriv_eulerZeta_exp_s_log_p_sub_one`
     - `phaseVel_eulerZeta_exp_s_log_p_sub_one_eq`
     - `driftFreeAt_eulerZeta_exp_s_log_p_sub_one_iff_phaseVel_eq_zero`
   - 数学的要点:
     - 連鎖律で `w_p'(t) = exp((σ+it)log p) * (i*log p)` を確立
     - `phaseVel f t = Im(f'(t)/f(t))` に `f = w_p` を代入して明示式化
     - `w_p(t) ≠ 0` 前提で停留条件 API（`driftFreeAt`）へ接続
   - 検証:
     - `lake build DkMath.RH.EulerZetaLemmas`
     - `lake build DkMath.RH`
     ともに成功。
3. 結論: HOPC-RH の「単一素数因子位相 API」が成立し、
   次段（曲率 API / 有限 Euler 積観測量）へ進むための最小核を確保できた。
4. 失敗事例:
   - 初回実装で `hasDerivAt_ofReal` 識別子が環境に存在せず失敗。
   - `((hasDerivAt_id (t : ℂ)).mul_const ...).comp_ofReal` へ置換して解消。
5. 備考:
   - 停留同値補題は `w_p(t) ≠ 0` を仮定した形で公開（枝問題回避方針と整合）。
6. 次の課題:
   - Phase RH-C1 として `phaseVel` の 2 次情報（曲率様量）を定義し、
     `w_p` に対する導関数補題を追加する。

### 日時: 2026/03/12 21:45 JST: Phase RH-C1 を実装（位相曲率 API と `w_p` 2次導関数）

1. 目的: HOPC-RH 優先度 C に沿って、位相の 2 次情報（曲率様量）を Lean 上で扱える形にする。
2. 内容:
   - 変更ファイル:
     - `DkMath/RH/Defs.lean`
     - `DkMath/RH/Lemmas.lean`
     - `DkMath/RH/EulerZetaLemmas.lean`
   - 新規定義（`Defs.lean`）:
     - `phaseCurv`
     - `stationaryAt`
     - `nondegenerateStationaryAt`
   - 追加補題（`Lemmas.lean`）:
     - `driftFreeAt_iff_stationaryAt`
     - `nondegenerateStationaryAt_iff_driftFreeAt_and_phaseCurv_ne_zero`
   - 追加補題（`EulerZetaLemmas.lean`）:
     - `hasDerivAt_deriv_eulerZeta_exp_s_log_p_sub_one`
     - `deriv_deriv_eulerZeta_exp_s_log_p_sub_one`
     - `stationaryAt_eulerZeta_exp_s_log_p_sub_one_iff_driftFreeAt`
     - `nondegenerateStationaryAt_eulerZeta_exp_s_log_p_sub_one_iff`
   - 数学的要点:
     - `w_p'(t)=exp((σ+it)log p)*(i log p)` をさらに微分し、
       `w_p''(t)=exp((σ+it)log p)*(i log p)^2` を補題化。
     - 停留・非退化停留を `driftFreeAt` と `phaseCurv` の言語へ統一。
   - 検証:
     - `lake build DkMath.RH.EulerZetaLemmas`
     - `lake build DkMath.RH`
     ともに成功。
3. 結論: RH-C1 の最小核（停留 + 曲率 + `w_p` 2次微分）が成立し、
   次段の有限 Euler 積観測量（RH-D1）へ進む準備が整った。
4. 失敗事例: 特になし（追加定義と補題は一括でビルド通過）。
5. 備考:
   - `phaseCurv` は `deriv (phaseVel f)` として導入し、枝問題に踏み込まない設計を維持。
6. 次の課題:
   - Phase RH-D1（有限 Euler 積版 HOPC 観測量）を実装し、
     prime-local contribution の和表示 API を追加する。

### 日時: 2026/03/12 22:03 JST: Phase RH-D1 を実装（有限 Euler 積観測量 API）

1. 目的: HOPC-RH 優先度 D に沿って、無限積へ上げる前段として
   有限 Euler 積と prime-local contribution の有限和 API を公開する。
2. 内容:
   - 変更ファイル:
     - `DkMath/RH/EulerZeta.lean`
     - `DkMath/RH/EulerZetaLemmas.lean`
   - 新規定義（`EulerZeta.lean`）:
     - `eulerZetaFinite`
     - `eulerZetaFinite_onVertical`
     - `eulerZetaMagFinite`
     - `eulerZetaPhaseVelLocal`
     - `eulerZetaPhaseVelFinite`
   - 追加補題（`EulerZetaLemmas.lean`）:
     - `eulerZetaFinite_empty`, `eulerZetaFinite_insert`
     - `eulerZetaMagFinite_empty`, `eulerZetaMagFinite_insert`
     - `eulerZetaPhaseVelFinite_empty`, `eulerZetaPhaseVelFinite_insert`
     - `eulerZetaPhaseVelLocal_eq_phaseVel_formula`
   - 役割:
     - 積（有限 Euler 積）と和（局所位相速度寄与）を明示的に分離し、
       HOPC 観測量を有限次元で組み立てる API を整備。
   - 検証:
     - `lake build DkMath.RH.EulerZetaLemmas`
     - `lake build DkMath.RH`
     ともに成功。
3. 結論: RH-D1 の最小核が成立し、
   `single-prime -> finite aggregation -> infinite product` の中段が実装された。
4. 失敗事例:
   - 初回で `Finset` 記法を `∏ p in S` / `∑ p in S` と書いて構文エラー。
   - Lean 記法 `∏ p ∈ S` / `∑ p ∈ S` に修正して解消。
5. 備考:
   - `eulerZetaPhaseVelFinite` は local 寄与の総和として定義のみ先行。
   - 次段で有限積の微分と和表示（log 微分）へ接続可能。
6. 次の課題:
   - Phase RH-D2 として、有限 Euler 積の位相速度が
     局所位相速度和へ落ちる補題（積→和）を追加する。
