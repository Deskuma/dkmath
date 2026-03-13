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

### 日時: 2026/03/12 22:22 JST: Phase RH-D2 を実装（有限積の位相速度 積→和）

1. 目的: RH-D1 で定義した有限観測量に対し、
   「有限積の位相速度 = 局所位相速度寄与の和」を Lean 補題として確立する。
2. 内容:
   - 変更ファイル:
     - `DkMath/RH/EulerZeta.lean`
     - `DkMath/RH/Lemmas.lean`
     - `DkMath/RH/EulerZetaLemmas.lean`
   - 新規定義（`EulerZeta.lean`）:
     - `eulerZetaExpSubOneFinite`（`w_p` の有限積）
   - 新規補題（`Lemmas.lean`）:
     - `phaseVel_mul`
       （`f(t), g(t) ≠ 0` 下で `phaseVel(f*g)=phaseVel f + phaseVel g`）
   - 新規補題（`EulerZetaLemmas.lean`）:
     - `eulerZetaExpSubOneFinite_empty`
     - `eulerZetaExpSubOneFinite_insert`
     - `differentiableAt_eulerZetaExpSubOneFinite`
     - `phaseVel_eulerZetaExpSubOneFinite_insert`
     - `phaseVel_eulerZetaExpSubOneFinite_eq_sum`
   - 数学的要点:
     - `phaseVel` の積法則を 1-step（insert）で適用し、
       `Finset` 帰納で有限積全体へ拡張。
     - 各因子の非零条件 `w_p(t) ≠ 0` を仮定して 0 除算を回避。
   - 検証:
     - `lake build DkMath.RH.EulerZetaLemmas`
     - `lake build DkMath.RH`
     ともに成功。
3. 結論: RH-D2 の主目的（積→和補題）が成立し、
   有限 Euler 積の位相観測を prime-local 和表示へ落とせる状態になった。
4. 失敗事例:
   - 初回実装で `DifferentiableAt.finset_prod` の関数形整合が崩れ、型不一致が発生。
   - 微分可能性補題を `Finset` 帰納で直接構成して解消。
5. 備考:
   - 今回の積→和は `w_p` 有限積に対する位相速度版。
   - 次段で `eulerZetaFinite`（因子本体）側への接続を追加可能。
6. 次の課題:
   - Phase RH-E1 として、`eulerZetaFinite` 側の位相速度接続
     （必要な非零条件を整理した上での積→和）を検討する。

### 日時: 2026/03/12 22:54 JST: Phase RH-E1 を実装（`eulerZetaFinite` 側の因子位相速度接続）

1. 目的: RH-D2 の `w_p` 有限積 API を一段進め、
   `1 / (exp((σ+it)log p) - 1)` 因子（`eulerZetaFinite` の構成因子）側で
   位相速度の局所寄与と有限和表示を扱えるようにする。
2. 内容:
   - 変更ファイル:
     - `DkMath/RH/EulerZeta.lean`
     - `DkMath/RH/Lemmas.lean`
     - `DkMath/RH/EulerZetaLemmas.lean`
   - 新規定義（`EulerZeta.lean`）:
     - `eulerZetaFactorVerticalExp`
     - `eulerZetaFactorVerticalExpFinite`
     - `eulerZetaFactorPhaseVelLocal`
     - `eulerZetaFactorPhaseVelFinite`
   - 新規補題（`Lemmas.lean`）:
     - `phaseVel_inv`
     - `phaseVel_div`
   - 新規補題（`EulerZetaLemmas.lean`）:
     - `eulerZetaFactorVerticalExpFinite_empty`
     - `eulerZetaFactorVerticalExpFinite_insert`
     - `eulerZetaFactorVerticalExp_ne_zero`
     - `phaseVel_exp_vertical_mul_log_p_eq_log`
     - `differentiableAt_eulerZetaFactorVerticalExp_of_ne`
     - `phaseVel_eulerZetaFactorVerticalExp_eq_log_sub_phaseVelLocal`
     - `differentiableAt_eulerZetaFactorVerticalExpFinite_of_ne`
     - `phaseVel_eulerZetaFactorVerticalExpFinite_eq_sum`
   - 数学的要点:
     - 逆数・商に対する `phaseVel` の加法則
       （`phaseVel(1/f) = - phaseVel(f)`, `phaseVel(f/g)=phaseVel(f)-phaseVel(g)`）を追加。
     - `exp((σ+it)log p)` の位相速度が `log p` であることを補題化し、
       `1/(exp(...) - 1)` 因子の局所寄与を `log p - phaseVelLocal` へ展開。
     - `Finset` 帰納で有限積の位相速度を局所寄与有限和に落とす補題を整備。
   - 検証:
     - `lake build DkMath.RH.Lemmas`
     - `lake build DkMath.RH.EulerZetaLemmas`
     - `lake build DkMath.RH`
     すべて成功。
3. 結論: RH-E1 の主目標を達成し、
   `eulerZetaFinite` 構成因子側でも「積→和」の位相観測 API を利用可能にした。
4. 失敗事例:
   - `phaseVel` の逆数補題で虚部の符号整理が不十分な状態があり、
     `field_simp` 後に `simp [neg_div, Complex.neg_im]` へ調整して解消。
   - `exp(...)` 因子の位相速度補題で `Complex.log` の実数化処理が崩れたため、
     非零性からの `Complex.log_ofReal_re` を明示して再構成した。
5. 備考:
   - 今回の補題群は `eulerZetaFinite` 本体（積の逆数形）への直接接続前段として設計。
   - 枝問題には踏み込まず、既存方針どおり `phaseVel` ベースで局所寄与を記述。
6. 次の課題:
   - RH-E2 として、`eulerZetaFinite` 本体の位相速度を
     `eulerZetaFactorPhaseVelFinite` と直結する補題を追加する。

### 日時: 2026/03/12 22:57 JST: Phase RH-E2 を実装（`eulerZetaFinite_onVertical` の積→和接続）

1. 目的: RH-E1 で整備した exp 形因子 API を `eulerZetaFinite_onVertical` 本体へ接続し、
   有限 Euler 積本体の位相速度を局所寄与和として直接利用できる形にする。
2. 内容:
   - 変更ファイル:
     - `DkMath/RH/EulerZetaLemmas.lean`
   - 追加補題:
     - `eulerZetaFactor_onVertical_eq_factorVerticalExp`
     - `eulerZetaFinite_onVertical_eq_factorVerticalExpFinite`
     - `phaseVel_eulerZetaFinite_onVertical_eq_factor_sum`
   - 数学的要点:
     - 素数 `p` に対し `eulerZetaFactor p (vertical σ t)` を
       `exp((σ+it)log p)/(exp((σ+it)log p)-1)` 形へ同一化。
     - 有限積レベルで同一化を `Finset.prod_congr` で持ち上げ。
     - RH-E1 の `phaseVel_eulerZetaFactorVerticalExpFinite_eq_sum` を再利用して
       `eulerZetaFinite_onVertical` 本体の位相速度和表示を導出。
   - 検証:
     - `lake build DkMath.RH.EulerZetaLemmas`
     - `lake build DkMath.RH`
     ともに成功。
3. 結論: `eulerZetaFinite_onVertical` 本体から
   局所寄与有限和 (`eulerZetaFactorPhaseVelFinite`) への橋渡しが完成し、
   RH-D/E 系の有限観測 API が本体側まで閉じた。
4. 失敗事例: なし（初回実装でビルド通過）。
5. 備考:
   - 非零条件は RH-E1 と同じく `w_p(t) ≠ 0` で統一。
   - 本補題は HOPC-RH の「有限 Euler 積観測器」の実運用入口として利用可能。
6. 次の課題:
   - RH-F1 として、`eulerZetaFinite_onVertical` の停留 (`driftFreeAt`) 条件と
     有限和 API の零化条件 (`= 0`) の同値補題を追加する。

### 日時: 2026/03/12 23:01 JST: Phase RH-F1 を実装（`driftFreeAt` と有限和零化の同値）

1. 目的: RH-E2 の位相速度和表示を `driftFreeAt` 判定へ接続し、
   停留条件を「有限局所寄与和 = 0」で直接扱える高位 API を追加する。
2. 内容:
   - 変更ファイル:
     - `DkMath/RH/EulerZetaLemmas.lean`
   - 追加補題:
     - `eulerZetaFinite_onVertical_ne_zero_of_ne`
     - `driftFreeAt_eulerZetaFinite_onVertical_iff_factor_sum_eq_zero`
   - 数学的要点:
     - 各 `p ∈ S` で `w_p(t) ≠ 0` を仮定し、有限積の非零性を `Finset.prod_ne_zero_iff` で導出。
     - 一般補題 `driftFreeAt_iff_phaseVel_eq_zero` と
       RH-E2 の `phaseVel_eulerZetaFinite_onVertical_eq_factor_sum` を合成して
       `driftFreeAt ↔ eulerZetaFactorPhaseVelFinite = 0` を確立。
   - 検証:
     - `lake build DkMath.RH.EulerZetaLemmas`
     - `lake build DkMath.RH`
     ともに成功。
3. 結論: `eulerZetaFinite_onVertical` の停留判定が
   finite Euler 観測量（局所寄与和）へ完全に還元され、HOPC-RH の可観測条件として利用可能になった。
4. 失敗事例: なし（初回実装でビルド通過）。
5. 備考:
   - 非零前提はこれまでと同様に `w_p(t) ≠ 0` で統一。
   - 枝問題を導入せず、既存の `phaseVel` 骨格内で停留条件を扱う設計を維持。
6. 次の課題:
   - RH-F2 として、`stationaryAt` / `nondegenerateStationaryAt` への写像補題を
     `eulerZetaFinite_onVertical` について追加する。

### 日時: 2026/03/12 23:11 JST: Phase RH-F2 を実装（停留・非退化停留の高位 API）

1. 目的: RH-F1 の `driftFreeAt ↔ finite-sum=0` を基盤に、
   `stationaryAt` と `nondegenerateStationaryAt` で同じ判定を使える高位補題を追加する。
2. 内容:
   - 変更ファイル:
     - `DkMath/RH/EulerZetaLemmas.lean`
   - 追加補題:
     - `stationaryAt_eulerZetaFinite_onVertical_iff_factor_sum_eq_zero`
     - `nondegenerateStationaryAt_eulerZetaFinite_onVertical_iff`
   - 数学的要点:
     - 一般補題 `driftFreeAt_iff_stationaryAt` と RH-F1 の同値補題を合成し、
       停留条件を局所寄与和の零化へ還元。
     - 一般補題
       `nondegenerateStationaryAt_iff_driftFreeAt_and_phaseCurv_ne_zero` を適用し、
       非退化停留を
       「局所寄与和 = 0 かつ `phaseCurv ≠ 0`」へ分解。
   - 検証:
     - `lake build DkMath.RH.EulerZetaLemmas`
     - `lake build DkMath.RH`
     ともに成功。
3. 結論: `eulerZetaFinite_onVertical` に対して
   停留/非退化停留の判定 API が有限局所寄与和ベースで統一され、
   HOPC-RH 観測器としての利用性が向上した。
4. 失敗事例: なし（初回実装でビルド通過）。
5. 備考:
   - 非零前提は引き続き `w_p(t) ≠ 0`（`p ∈ S`）で統一。
   - 曲率は既存定義 `phaseCurv` をそのまま利用し、追加の解析仮定は導入していない。
6. 次の課題:
   - RH-G1 として、`eulerZetaFactorPhaseVelFinite` の明示式
     （`∑_{p∈S} (log p - eulerZetaPhaseVelLocal p)`）を
     停留補題群へ接続する整理補題を追加する。

### 日時: 2026/03/12 23:21 JST: Phase RH-G1 を実装（明示和形への正規化）

1. 目的: RH-F 系の停留補題群で使っている
   `eulerZetaFactorPhaseVelFinite` を明示和形
   `∑_{p∈S}(log p - eulerZetaPhaseVelLocal p)` に統一し、
   観測量を直接読める形へ整理する。
2. 内容:
   - 変更ファイル:
     - `DkMath/RH/EulerZetaLemmas.lean`
   - 追加補題:
     - `eulerZetaFactorPhaseVelFinite_eq_sum_log_sub_phaseVelLocal`
     - `driftFreeAt_eulerZetaFinite_onVertical_iff_sum_log_sub_phaseVelLocal_eq_zero`
     - `stationaryAt_eulerZetaFinite_onVertical_iff_sum_log_sub_phaseVelLocal_eq_zero`
   - 数学的要点:
     - RH-E1 の局所式
       `phaseVel_eulerZetaFactorVerticalExp_eq_log_sub_phaseVelLocal`
       を `Finset.sum_congr` で有限和へ持ち上げ。
     - RH-F1/F2 の同値補題を上記明示和へ rewrite し、
       `driftFreeAt` / `stationaryAt` を同一の和零化条件に正規化。
   - 検証:
     - `lake build DkMath.RH.EulerZetaLemmas`
     - `lake build DkMath.RH`
     ともに成功。
3. 結論: 停留判定 API が「抽象和」から「明示和」へ正規化され、
   HOPC-RH の観測量解釈と downstream 利用（数値評価・比較）がしやすくなった。
4. 失敗事例: なし（初回実装でビルド通過）。
5. 備考:
   - 前提は一貫して `p ∈ S` での `w_p(t) ≠ 0` を使用。
   - 既存補題の再利用中心で、定義変更や互換性破壊はなし。
6. 次の課題:
   - RH-G2 として、`nondegenerateStationaryAt_eulerZetaFinite_onVertical_iff` も
     明示和形（`sum_log_sub = 0 ∧ phaseCurv ≠ 0`）へ揃える補題を追加する。

### 日時: 2026/03/12 23:52 JST: Phase RH-G2 を実装（非退化停留条件の明示和版）

1. 目的: RH-G1 で整えた明示和正規化を非退化停留条件にも拡張し、
   停留・非退化停留の API を同一表現で揃える。
2. 内容:
   - 変更ファイル:
     - `DkMath/RH/EulerZetaLemmas.lean`
   - 追加補題:
     - `nondegenerateStationaryAt_eulerZetaFinite_onVertical_iff_sum_log_sub_phaseVelLocal`
   - 数学的要点:
     - 既存の
       `nondegenerateStationaryAt_eulerZetaFinite_onVertical_iff`
       を基礎に、
       RH-G1 の `eulerZetaFactorPhaseVelFinite_eq_sum_log_sub_phaseVelLocal`
       で第一成分を rewrite。
     - これにより非退化停留条件を
       `sum_log_sub = 0 ∧ phaseCurv ≠ 0` の直読可能な形へ統一。
   - 検証:
     - `lake build DkMath.RH.EulerZetaLemmas`
     - `lake build DkMath.RH`
     ともに成功。
3. 結論: `eulerZetaFinite_onVertical` の
   `driftFreeAt` / `stationaryAt` / `nondegenerateStationaryAt` が
   すべて明示和ベースで整列し、観測器 API の一貫性が完成した。
4. 失敗事例: なし（初回実装でビルド通過）。
5. 備考:
   - 非零前提は従来どおり `p ∈ S` での `w_p(t) ≠ 0`。
   - 新規は整理補題のみで、既存証明・既存定義の互換性は維持。
6. 次の課題:
   - RH-H1 として、RH-CFBRC 連携資料に合わせて
     `EulerZetaLemmas` の公開補題群を「観測器インタフェース」として再整理し、
     `RH-CFBRC-Discussion.md` と同期する導線を追加する。

### 日時: 2026/03/13 00:01 JST: Phase RH-H1 を実装（HOPC 公開インタフェース整備）

1. 目的: RH-CFBRC 連携で直接利用する観測器 API を明示し、
   既存補題群を「HOPC 公開名」で参照できるように整理する。
2. 内容:
   - 変更ファイル:
     - `DkMath/RH/EulerZeta.lean`
     - `DkMath/RH/EulerZetaLemmas.lean`
   - 新規定義（`EulerZeta.lean`）:
     - `hopcPrimeLocalContribution`
     - `hopcPrimeContributionSum`
   - 追加補題（`EulerZetaLemmas.lean`）:
     - `hopcPrimeLocalContribution_eq_log_sub_phaseVelLocal`
     - `hopcPrimeContributionSum_eq_sum_log_sub_phaseVelLocal`
     - `eulerZetaFactorPhaseVelFinite_eq_hopcPrimeContributionSum`
     - `driftFreeAt_eulerZetaFinite_onVertical_iff_hopcPrimeContributionSum_eq_zero`
     - `stationaryAt_eulerZetaFinite_onVertical_iff_hopcPrimeContributionSum_eq_zero`
     - `nondegenerateStationaryAt_eulerZetaFinite_onVertical_iff_hopcPrimeContributionSum`
   - 数学的要点:
     - 明示和 `∑(log p - phaseVel(w_p))` を HOPC の公開観測量名へ束ねる。
     - 既存の停留/非退化停留同値補題を wrapper 化し、
       CFBRC 側から「寄与総和 = 0」言語で直結可能にする。
   - 検証:
     - `lake build DkMath.RH.EulerZetaLemmas`
     - `lake build DkMath.RH`
     ともに成功。
3. 結論: RH 側の観測器 API が HOPC 名で公開され、
   RH-CFBRC 連携に必要な「prime-local contribution language」の入口が整った。
4. 失敗事例:
   - `hopcPrimeContributionSum` 展開補題で `rfl` を欠落させ、`sum = sum` の未解決ゴールが発生。
   - `rfl` を補って解消し、再ビルドで通過。
5. 備考:
   - `RH/docs/README.md` は存在せず、同期対象は `HOPC-RH.txt` と `RH-CFBRC-Discussion.md` に限定。
   - 定義追加は薄い alias 層であり、既存 API 互換性は維持。
6. 次の課題:
   - RH-H2 として、`RH-CFBRC-Discussion.md` 側に
     新公開 API（`hopcPrimeContributionSum` 系）への参照断面を追加し、
     実装名と議論文書の往復導線を固定する。

### 日時: 2026/03/13 00:25 JST: RH 直下 README（表紙）を新規追加

1. 目的: `DkMath/RH` 直下に入口ページを作り、
   初見で「何が実装され、どこを読めばよいか」を即座に辿れるようにする。
2. 内容:
   - 変更ファイル:
     - `DkMath/RH/README.md`（新規）
   - 記載項目:
     - モジュールの目的（位相ドリフト骨格 / Euler 因子観測 / HOPC 公開 API）
     - ファイル構成（`Defs/Lemmas/Theorems/EulerZeta*`）
     - RH-H1 時点の主要公開 API
     - `docs`（`HOPC-RH.txt`, `RH-CFBRC-Discussion.md`, `RH_Implements_History.md`）への導線
     - import 例
3. 結論: RH 層に「表紙」が追加され、実装入口と議論文書の導線が統一された。
4. 失敗事例: なし（ドキュメント追加のみ）。
5. 備考:
   - 詳細解説は従来どおり `DkMath/RH/docs/README.md` を参照する構成。
   - 直下 README は短いナビゲーション用途に限定。
6. 次の課題:
   - RH-H2 として、`RH-CFBRC-Discussion.md` に
     `hopcPrimeContributionSum` 系 API 参照断面を追加し、
     文書側から実装へジャンプできる目次を整備する。

### 日時: 2026/03/13 00:27 JST: Phase RH-H2 を実装（Discussion 文書の API 導線固定）

1. 目的: `RH-CFBRC-Discussion.md` から実装 API へ直接辿れる参照断面を追加し、
   議論文書と Lean 実装名の往復導線を固定する。
2. 内容:
   - 変更ファイル:
     - `DkMath/RH/docs/RH-CFBRC-Discussion.md`
   - 追加断面:
     - `Implementation Bridge (RH-H1/H2)`
   - 記載項目:
     - HOPC 公開定義（`hopcPrimeLocalContribution`, `hopcPrimeContributionSum`）
     - 同一化補題（`eulerZetaFactorPhaseVelFinite_eq_hopcPrimeContributionSum`）
     - 停留/非退化停留同値補題
     - 推奨読み順（定義 → 同一化 → 判定補題）
3. 結論: RH-CFBRC 議論文書に実装ジャンプ導線が入り、
   CFBRC 側から RH 側 API を引く際の参照コストを削減できた。
4. 失敗事例: なし（ドキュメント追記のみ）。
5. 備考:
   - 内容は RH-H1 で公開済み API の整理であり、新しい数学命題は追加していない。
   - 実装本体（`.lean`）には変更なし。
6. 次の課題:
   - RH-I1 として、`DkMath/RH/docs/README.md` の「現状 API」節も
     HOPC 公開名に同期し、重複記述を避けた文書構成へ整える。

### 日時: 2026/03/13 00:29 JST: Phase RH-I1 を実装（docs README の API 同期）

1. 目的: `DkMath/RH/docs/README.md` を RH-H1/H2 の公開 API に同期し、
   直下 README との重複を減らした文書役割分担を明確化する。
2. 内容:
   - 変更ファイル:
     - `DkMath/RH/docs/README.md`
   - 変更点:
     - 更新日時を現行時刻へ更新。
     - 「詳細版である」旨と、入口/API は `DkMath/RH/README.md` を優先参照する旨を追記。
     - 新節 `現状 API（HOPC 公開名・RH-H2 時点）` を追加し、
       `hopcPrimeContributionSum` 系 API と停留判定補題を明示。
3. 結論: RH 文書群で
   「直下 README = 表紙/入口」「docs README = 詳細解説」
   の分担が固定され、API 名の参照揺れが解消した。
4. 失敗事例: なし（ドキュメント更新のみ）。
5. 備考:
   - `.lean` 実装への変更はなし。
   - `RH-CFBRC-Discussion.md` の `Implementation Bridge (RH-H1/H2)` と内容同期。
6. 次の課題:
   - RH-I2 として、`HOPC-RH.txt` の優先度 A/E に沿って
     `HOPC-RH-Roadmap.md`（1枚設計図）を新規作成する。

### 日時: 2026/03/13 00:32 JST: Phase RH-I2 を実装（HOPC-RH-Roadmap を新規作成）

1. 目的: `HOPC-RH.txt` の優先度 E に対応し、
   RH 実装の進捗と次段タスクを 1 枚で把握できる設計図を作る。
2. 内容:
   - 変更ファイル:
     - `DkMath/RH/docs/HOPC-RH-Roadmap.md`（新規）
     - `DkMath/RH/README.md`（ロードマップ導線追加）
     - `DkMath/RH/docs/README.md`（ロードマップ参照追記）
   - ロードマップ構成:
     - 目的
     - 実装レイヤ
     - フェーズ A〜I の状態（完了/未完）
     - 次段候補（Glossary / OpenProblems / finite→infinite 接続）
3. 結論: HOPC-RH の実装計画が文書化され、
   方針文書 (`HOPC-RH.txt`) と実装履歴 (`RH_Implements_History.md`) の中間導線が整った。
4. 失敗事例: なし（ドキュメント追加・更新のみ）。
5. 備考:
   - `.lean` 実装の変更はなし。
   - RH 直下 README と docs README の両方からロードマップへ到達可能。
6. 次の課題:
   - RH-I3 として、`HOPC-RH-Glossary.md` を新規作成し、
     `phaseVel`, `driftFreeAt`, `stationaryAt`, `hopcPrimeContributionSum` など
     現行公開語彙の定義域・依存関係を簡潔に整理する。

### 日時: 2026/03/13 00:58 JST: Phase RH-I3 を実装（HOPC-RH-Glossary を新規作成）

1. 目的: HOPC 公開語彙の参照点を 1 つにまとめ、
   `Defs/EulerZeta/EulerZetaLemmas` を横断する用語の意味と依存を短く確認できるようにする。
2. 内容:
   - 変更ファイル:
     - `DkMath/RH/docs/HOPC-RH-Glossary.md`（新規）
     - `DkMath/RH/docs/HOPC-RH-Roadmap.md`（Glossary 完了に更新）
     - `DkMath/RH/README.md`（Glossary 導線追加）
     - `DkMath/RH/docs/README.md`（Glossary 参照追記）
   - 用語集の対象:
     - Core: `vertical`, `torque`, `phaseVel`, `driftFreeAt`, `phaseCurv`,
       `stationaryAt`, `nondegenerateStationaryAt`
     - Euler/HOPC: `w_p`, `eulerZetaPhaseVelLocal`, `eulerZetaFactorPhaseVelFinite`,
       `hopcPrimeLocalContribution`, `hopcPrimeContributionSum`
     - 公開 wrapper: 停留/非退化停留の HOPC 判定補題
3. 結論: HOPC 用語の「定義場所・意味・依存」が固定され、
   実装参照時の往復（コード↔文書）のコストが下がった。
4. 失敗事例: なし（ドキュメント追加・更新のみ）。
5. 備考:
   - `.lean` 実装の変更はなし。
   - Roadmap の I フェーズは「一部完了（Glossary 完了）」へ更新。
6. 次の課題:
   - RH-I4 として、`HOPC-RH-OpenProblems.md` を新規作成し、
     finite→infinite 接続条件と CFBRC 連携の未完タスクを issue 形式で整理する。

### 日時: 2026/03/13 02:33 JST: Phase RH-I4 を実装（HOPC-RH-OpenProblems を新規作成）

1. 目的: HOPC-RH の未完タスクを issue 形式で固定し、
   次の実装フェーズを文書として管理可能にする。
2. 内容:
   - 変更ファイル:
     - `DkMath/RH/docs/HOPC-RH-OpenProblems.md`（新規）
     - `DkMath/RH/docs/HOPC-RH-Roadmap.md`（OpenProblems 作成済みへ更新）
     - `DkMath/RH/README.md`（OpenProblems 導線追加）
     - `DkMath/RH/docs/README.md`（OpenProblems 参照追記）
   - Open problems（抜粋）:
     - OP-001: finite→infinite（位相寄与和）接続
     - OP-002: 非零前提の管理 API
     - OP-003: CFBRC 連携の実定理
     - OP-004: 曲率条件の運用規約
     - OP-005: 文書同期の継続管理
3. 結論: HOPC-RH 文書セット（Roadmap/Glossary/OpenProblems）が揃い、
   実装課題を優先度付きで継続管理できる状態になった。
4. 失敗事例:
   - 初回で `HOPC-RH-Roadmap.md` のパス指定を誤り、パッチ適用に失敗。
   - 正しい `lean/dk_math/...` パスで再適用して解消。
5. 備考:
   - `.lean` 実装の変更はなし。
   - Roadmap の I フェーズは「Glossary/OpenProblems 完了」に更新。
6. 次の課題:
   - RH-J1 として、OP-002（非零前提の管理 API）から着手し、
     `w_p ≠ 0` 前提を束ねる finite-set wrapper 補題を
     `EulerZetaLemmas.lean` に追加する。

### 日時: 2026/03/13 02:36 JST: Phase RH-J1 を実装（非零前提 finite-set wrapper）

1. 目的: OP-002 に対応し、`∀ p ∈ S, w_p ≠ 0` 前提から
   有限積非零を都度再構成する重複を解消する。
2. 内容:
   - 変更ファイル:
     - `DkMath/RH/EulerZetaLemmas.lean`
   - 追加補題:
     - `eulerZetaExpSubOneFinite_ne_zero_of_ne`
     - `eulerZetaFactorVerticalExpFinite_ne_zero_of_ne`
   - 既存補題の置換:
     - `phaseVel_eulerZetaExpSubOneFinite_eq_sum`
     - `phaseVel_eulerZetaFactorVerticalExpFinite_eq_sum`
     - `eulerZetaFinite_onVertical_ne_zero_of_ne`
     で手書き `Finset.prod_ne_zero_iff` ブロックを wrapper 呼び出しへ差し替え。
3. 結論: 非零前提の管理が補題レベルで正規化され、
   以後の停留/位相速度補題で前提処理の再利用性が向上した。
4. 失敗事例: なし（初回実装でビルド通過）。
5. 備考:
   - 既存 API の外部シグネチャ変更はなし。
   - 変更は証明本体の重複削減と読みやすさ改善が中心。
6. 次の課題:
   - RH-J2 として、OP-003（CFBRC 連携の実定理）に着手し、
     `hopcPrimeContributionSum` 判定へ落とす最小 bridge 補題（1本）を設計する。

### 日時: 2026/03/13 02:47 JST: Phase RH-J2 を実装（CFBRC 連携の最小 bridge）

1. 目的: OP-003 の最小着手として、CFBRC 側 primitive-prime existence と
   RH 側 `hopcPrimeContributionSum` 判定を 1 本の補題で接続する。
2. 内容:
   - 変更ファイル:
     - `DkMath/RH/CFBRCBridge.lean`（新規）
     - `DkMath/RH.lean`（`import DkMath.RH.CFBRCBridge` 追加）
     - `DkMath/RH/README.md`（`CFBRCBridge.lean` 反映）
   - 新規補題:
     - `exists_stationaryAt_singleton_of_cfbRc_primitive_prime_bridge`
   - 補題の役割:
     - CFBRC の
       `exists_primitive_prime_factor_sub_pow_of_prime_exp_boundary_of_coprime`
       で得た素数を singleton 観測器へ載せ、
       翻訳仮定（`hwnz`, `hhopc0`）の下で RH 側 `stationaryAt` 存在へ落とす。
3. 結論: CFBRC→RH の「実定理」最小形が成立し、
   prime existence から HOPC 停留判定へ接続する具体的導線を提供できた。
4. 失敗事例:
   - 新規ファイル先頭コメントを module doc 形式にしたため import 位置エラーが発生。
   - 通常コメントへ修正して解消。
5. 備考:
   - 本 bridge は翻訳仮定つき（`hwnz`, `hhopc0`）の最小接続版。
   - CFBRC 本体へ依存するコードは `CFBRCBridge.lean` に隔離。
6. 次の課題:
   - RH-J3 として、RH-J2 の翻訳仮定を弱めるため
     singleton で再利用可能な `hS_ne` / `hopcPrimeContributionSum=0` 供給 wrapper を
     `EulerZetaLemmas.lean` 側に追加する。

### 日時: 2026/03/13 02:55 JST: Phase RH-J3 を実装（singleton wrapper と local 仮定版 bridge）

1. 目的: RH-J2 bridge の翻訳仮定を弱めるため、
   singleton 観測器で再利用可能な wrapper を RH 側へ追加する。
2. 内容:
   - 変更ファイル:
     - `DkMath/RH/EulerZetaLemmas.lean`
     - `DkMath/RH/CFBRCBridge.lean`
   - 追加補題（`EulerZetaLemmas.lean`）:
     - `eulerZeta_exp_s_log_p_sub_one_ne_zero_on_singleton`
     - `hopcPrimeContributionSum_singleton`
     - `stationaryAt_eulerZetaFinite_onVertical_singleton_of_hopcPrimeLocalContribution_eq_zero`
   - 追加補題（`CFBRCBridge.lean`）:
     - `exists_stationaryAt_singleton_of_cfbRc_primitive_prime_bridge_of_local`
       （`hopcPrimeContributionSum=0` ではなく `hopcPrimeLocalContribution=0` を仮定）
3. 結論: singleton での前提供給が補題化され、
   CFBRC→RH bridge に対する翻訳仮定を local 版へ弱化できた。
4. 失敗事例: なし（最終的に全ビルド通過）。
5. 備考:
   - 既存の RH-J2 補題は互換のため維持。
   - local 版 bridge は RH 側 wrapper を再利用して構成。
6. 次の課題:
   - RH-J4 として、RH-J2/J3 bridge の利用例を
     `RH/docs/RH-CFBRC-Discussion.md` に短いコード断面で追加し、
     仮定セット（global 版 / local 版）の使い分けを明記する。

### 日時: 2026/03/13 03:01 JST: Phase RH-J4 を実装（bridge 利用例の文書化）

1. 目的: RH-J2/J3 で追加した bridge の使い分けを明文化し、
   CFBRC 側ユーザーが仮定セット（global/local）を選びやすくする。
2. 内容:
   - 変更ファイル:
     - `DkMath/RH/docs/RH-CFBRC-Discussion.md`
   - 追加断面:
     - `Bridge Usage (RH-J2/J3)`
   - 記載項目:
     - global 仮定版 / local 仮定版の補題名
     - 使い分け指針
     - 最小 import
     - local 仮定版の短い利用イメージ（Lean 断面）
3. 結論: bridge 補題の実運用入口が文書上で可視化され、
   CFBRC→RH 連携の導入コストが低下した。
4. 失敗事例: なし（ドキュメント追記のみ）。
5. 備考:
   - 実装本体（`.lean`）への変更はなし。
   - コード断面は `provider` 側の仮定供給を `sorry` で示す説明用サンプル。
6. 次の課題:
   - RH-K1 として、`RH/README.md` にも RH-J2/J3 bridge の項目を追記し、
     実装トップ README から CFBRC 連携入口を直接辿れるようにする。

### 日時: 2026/03/13 03:03 JST: Phase RH-K1 を実装（トップ README の bridge 入口追加）

1. 目的: 実装トップ README から CFBRC 連携 bridge を直接参照できるようにし、
   RH-J2/J3 の入口を docs 依存なしで把握できるようにする。
2. 内容:
   - 変更ファイル:
     - `DkMath/RH/README.md`
   - 追記箇所:
     - `主要 API` 節に `CFBRC 連携 bridge（singleton）` を追加
   - 追加項目:
     - `exists_stationaryAt_singleton_of_cfbRc_primitive_prime_bridge`（global 仮定版）
     - `exists_stationaryAt_singleton_of_cfbRc_primitive_prime_bridge_of_local`（local 仮定版）
3. 結論: `DkMath/RH/README.md` 単体で
   HOPC API と CFBRC bridge の両方を把握できる構成になった。
4. 失敗事例: なし（ドキュメント追記のみ）。
5. 備考:
   - `.lean` 実装には変更なし。
   - 詳細な使い分けは `RH-CFBRC-Discussion.md` の `Bridge Usage (RH-J2/J3)` を参照。
6. 次の課題:
   - RH-K2 として、`DkMath/RH/docs/README.md` の現状 API 節にも
     bridge API を同期し、README 間の記載差分を解消する。

### 日時: 2026/03/13 03:04 JST: Phase RH-K2 を実装（docs README の bridge API 同期）

1. 目的: `DkMath/RH/README.md` と `DkMath/RH/docs/README.md` の
   API 記載差分を解消し、CFBRC bridge 入口を両 README で一致させる。
2. 内容:
   - 変更ファイル:
     - `DkMath/RH/docs/README.md`
   - 変更点:
     - 見出しを `RH-K2` 時点へ更新。
     - `現状 API` 節に
       `CFBRCBridge.lean` の 2 補題（global/local）を追記。
3. 結論: RH の 2 つの README 間で bridge API 表記が統一され、
   入口文書の整合性が取れた。
4. 失敗事例: なし（ドキュメント更新のみ）。
5. 備考:
   - `.lean` 実装への変更はなし。
   - bridge の使い分け詳細は引き続き `RH-CFBRC-Discussion.md` を参照。
6. 次の課題:
   - RH-L1 として、`DkMath/RH/README.md` の import 例に
     `DkMath.RH.CFBRCBridge` 利用例を追加し、
     CFBRC 連携の最小起動手順を明示する。

### 日時: 2026/03/13 03:05 JST: Phase RH-L1 を実装（README import 例の bridge 追加）

1. 目的: CFBRC 連携を使う最小起動手順をトップ README で明示し、
   `RH.CFBRCBridge` の導入を即座に再現できるようにする。
2. 内容:
   - 変更ファイル:
     - `DkMath/RH/README.md`
   - 追記項目:
     - `CFBRC 連携 bridge まで使う場合` セクション
     - `import DkMath.RH.CFBRCBridge`
     - `open DkMath.RH.EulerZeta`
3. 結論: README の import 例だけで
   RH 単体利用と CFBRC 連携利用の両方を起動できる構成になった。
4. 失敗事例: なし（ドキュメント追記のみ）。
5. 備考:
   - `.lean` 実装への変更はなし。
   - bridge の仮定セット詳細は `RH-CFBRC-Discussion.md` を参照。
6. 次の課題:
   - RH-L2 として、`DkMath/RH/docs/README.md` にも同等の import 例を追記し、
     README 間の利用手順を完全同期する。

### 日時: 2026/03/13 03:07 JST: Phase RH-L2 を実装（docs README の import 例同期）

1. 目的: `DkMath/RH/README.md` と `DkMath/RH/docs/README.md` の
   利用手順（import 例）を一致させ、導入時の分岐をなくす。
2. 内容:
   - 変更ファイル:
     - `DkMath/RH/docs/README.md`
   - 追加内容:
     - `利用例（import）` セクション
     - RH 側 API 最小例（`EulerZeta`, `EulerZetaLemmas`）
     - CFBRC 連携 bridge 例（`CFBRCBridge` + `open DkMath.RH.EulerZeta`）
3. 結論: RH の 2 README で import 手順が同期され、
   利用者はどちらを先に読んでも同じ起動方法に到達できる。
4. 失敗事例: なし（ドキュメント追記のみ）。
5. 備考:
   - `.lean` 実装への変更はなし。
   - bridge 仮定の詳細は引き続き `RH-CFBRC-Discussion.md` 側で説明。
6. 次の課題:
   - RH-M1 として、`DkMath/RH/docs/HOPC-RH-OpenProblems.md` の OP-005 に対応し、
     文書更新チェックリスト（README/Roadmap/Glossary/OpenProblems/Discussion/History）
     を追記する。

### 日時: 2026/03/13 03:09 JST: Phase RH-M1 を実装（OP-005 チェックリスト追加）

1. 目的: OP-005 の「文書同期ルール」を抽象記述から運用可能な手順へ落とし、
   更新漏れを定常的に減らす。
2. 内容:
   - 変更ファイル:
     - `DkMath/RH/docs/HOPC-RH-OpenProblems.md`
   - 追加内容:
     - `OP-005 チェックリスト v1（最小運用）`
     - 判定軸 5 項目（`.lean` 構成、公開 API、CFBRC bridge、Roadmap/OpenProblems 状態、History 記録）
3. 結論: 文書同期の更新順序が固定され、
   RH ドキュメント群の整合を保つ運用基準が明文化された。
4. 失敗事例: なし（ドキュメント追記のみ）。
5. 備考:
   - `.lean` 実装への変更はなし。
   - チェックリストは最小版であり、必要に応じて項目追加可能。
6. 次の課題:
   - RH-M2 として、`HOPC-RH-Roadmap.md` に
     OP-001/OP-003 の短期実装順（next sprint）を明記し、
     コード実装フェーズへ戻る優先線を固定する。

### 日時: 2026/03/13 03:10 JST: Phase RH-M2 を実装（Roadmap に next sprint を明記）

1. 目的: 文書整備フェーズから実装フェーズへ戻る優先線を固定し、
   OP-001/OP-003 の実行順を明確化する。
2. 内容:
   - 変更ファイル:
     - `DkMath/RH/docs/HOPC-RH-Roadmap.md`
   - 追加内容:
     - `Next Sprint（短期実装順）` セクション
     - 実装順:
       1. OP-003（CFBRC bridge 拡張）先行
       2. OP-001（finite→infinite 接続）後続
     - 先行理由（橋の具体化を先に進めることで観測量設計軸を固定）
3. 結論: 次スプリントの着手順が文書化され、
   実装計画の判断が都度ブレない状態になった。
4. 失敗事例: なし（ドキュメント追記のみ）。
5. 備考:
   - `.lean` 実装への変更はなし。
   - OP-002/OP-005 は継続運用とし、短期優先からは外した。
6. 次の課題:
   - RH-N1 として、OP-003 先行方針に沿い
     singleton bridge（J2/J3）を small finite-set へ一般化する
     API スケッチを `CFBRCBridge.lean` に追加する。

### 日時: 2026/03/13 03:13 JST: Phase RH-N1 を実装（small finite-set への API スケッチ）

1. 目的: OP-003 先行方針に沿い、singleton bridge から
   `insert p S` 形の small finite-set 観測器へ拡張する入口 API を用意する。
2. 内容:
   - 変更ファイル:
     - `DkMath/RH/CFBRCBridge.lean`
   - 追加補題:
     - `stationaryAt_insert_of_hopcPrimeContributionSum_eq_zero`
       （`insert p S` 上の非零前提 + 寄与総和ゼロから停留）
     - `exists_stationaryAt_insert_of_cfbRc_primitive_prime_bridge_of_local`
       （CFBRC primitive-prime existence と `hlift` 仮定を合成した
        small finite-set 版 bridge スケッチ）
3. 結論: CFBRC→RH bridge を singleton 専用から一段抽象化し、
   finite-set 拡張へ進むための最小 API 骨格を実装できた。
4. 失敗事例: なし（初回実装でビルド通過）。
5. 備考:
   - `hlift` は翻訳層の仮定を保持したスケッチ設計。
   - 既存 J2/J3 補題はそのまま残し、後方互換を維持。
6. 次の課題:
   - RH-N2 として、`hlift` の仮定を分解して
     `hS_ne` 供給部分と `hopcPrimeContributionSum=0` 供給部分を
     個別 wrapper 化し、small finite-set bridge の再利用性を上げる。

### 日時: 2026/03/13 03:20 JST: Phase RH-N2 を実装（`hlift` 分解版 bridge 追加）

1. 目的: RH-N1 の `hlift` 一括仮定を分解し、
   非零前提と寄与総和ゼロ前提を別々に再利用できる API へ整理する。
2. 内容:
   - 変更ファイル:
     - `DkMath/RH/CFBRCBridge.lean`
   - 追加補題:
     - `exists_stationaryAt_insert_of_cfbRc_primitive_prime_bridge_of_local_split`
       （`hS_lift` と `hsum_lift` を分離した small finite-set bridge）
   - 互換対応:
     - 既存 `exists_stationaryAt_insert_of_cfbRc_primitive_prime_bridge_of_local`
       は残し、従来の `hlift` 一括入力を受ける wrapper として維持。
3. 結論: small finite-set bridge の仮定設計が分離され、
   翻訳レイヤで `w_r ≠ 0` と `hopcPrimeContributionSum=0` を独立供給できる形になった。
4. 失敗事例:
   - 初回実装で wrapper から split 補題を先行参照し、
     `Unknown identifier` が発生。
   - wrapper 本体を直接証明へ戻して forward reference を解消。
5. 検証:
   - `lake build DkMath.RH.CFBRCBridge` 成功。
   - `lake build DkMath.RH` 成功。
6. 次の課題:
   - RH-N3 として、`BoundarySide` と対応づけた finite-set 向け高位 API
     （left/right 共通インターフェース）を検討し、
     CFBRC 側 boundary 正規化 wrapper と接続する。

### 日時: 2026/03/13 03:23 JST: Phase RH-N3 を実装（`BoundarySide` 高位 API 公開）

1. 目的: RH 側 bridge でも left/right 境界を統一的に扱えるよう、
   `BoundarySide` パラメータ付きの高位 API を追加する。
2. 内容:
   - 変更ファイル:
     - `DkMath/RH/CFBRCBridge.lean`
   - 追加補題:
     - `exists_stationaryAt_singleton_of_cfbRc_primitive_prime_boundary_bridge_of_local`
     - `exists_stationaryAt_insert_of_cfbRc_primitive_prime_boundary_bridge_of_local_split`
     - `exists_stationaryAt_insert_of_cfbRc_primitive_prime_boundary_bridge_of_local`
   - 設計:
     - `right` は既存 bridge へ直接委譲。
     - `left` は `(x,u)` を `(u,x)` に入れ替えて既存 bridge を再利用。
3. 結論: singleton と small finite-set の両方で、
   boundary 側の前提を 1 つの API 群で受けられるようになった。
4. 失敗事例:
   - 初回実装は `match side` 依存型引数の適用で型不一致が発生。
   - `cases side` による左右分岐 + 既存補題委譲へ変更して解消。
5. 検証:
   - `lake build DkMath.RH.CFBRCBridge` 成功。
   - `lake build DkMath.RH` 成功。
6. 次の課題:
   - RH-N4 として、`BoundarySide` 高位 API の利用例を
     `RH/docs/RH-CFBRC-Discussion.md` と `RH/README.md` に反映し、
     実利用時の仮定テンプレート（`hS_lift`/`hsum_lift`）を明示する。

### 日時: 2026/03/13 03:25 JST: Phase RH-N4 を実装（BoundarySide 利用テンプレート文書化）

1. 目的: RH-N3 で追加した `BoundarySide` 高位 API の利用導線を文書へ反映し、
   実装側の仮定テンプレートを利用者がそのまま再利用できる状態にする。
2. 内容:
   - 変更ファイル:
     - `DkMath/RH/README.md`
     - `DkMath/RH/docs/RH-CFBRC-Discussion.md`
   - 追記内容:
     - `README.md`
       - 主要 API を RH-N3 時点へ更新
       - `BoundarySide` 統一 bridge（singleton / insert / split）を列挙
       - `..._boundary_bridge_of_local_split` の最小利用テンプレートを追加
     - `RH-CFBRC-Discussion.md`
       - `Implementation Bridge (RH-N4: BoundarySide 高位 API)` セクションを追加
       - `hS_lift` / `hsum_lift` の分離前提を明示
       - split 版 bridge の最小テンプレートを追加
3. 結論: API 追加とドキュメントが同期され、
   `BoundarySide` + small finite-set bridge の利用入口が明文化された。
4. 失敗事例: なし（ドキュメント更新のみ）。
5. 備考:
   - `.lean` 実装への変更はなし。
   - テンプレートは `BoundarySide` 統一版の推奨入口（split 仮定）を採用。
6. 次の課題:
   - RH-N5 として、`DkMath/RH/docs/README.md` にも同等の
     `BoundarySide` 利用テンプレートを同期し、README 間の API 導線を統一する。

### 日時: 2026/03/13 03:26 JST: Phase RH-N5 を実装（docs README へ BoundarySide テンプレート同期）

1. 目的: `DkMath/RH/README.md` と `DkMath/RH/docs/README.md` の
   API 導線を一致させ、BoundarySide 高位 API の参照先を一意化する。
2. 内容:
   - 変更ファイル:
     - `DkMath/RH/docs/README.md`
   - 追記内容:
     - `現状 API` 見出しを RH-N5 時点へ更新
     - CFBRC bridge 一覧に RH-N1〜N3 の補題群を追加
     - `BoundarySide` + small finite-set（split 仮定）の最小テンプレートを追加
3. 結論: RH の 2 README で `BoundarySide` bridge の利用手順が同期され、
   実装側の仮定テンプレート参照が統一された。
4. 失敗事例: なし（ドキュメント更新のみ）。
5. 備考:
   - `.lean` 実装への変更はなし。
   - `RH-CFBRC-Discussion.md` 側の RH-N4 セクションと内容整合済み。
6. 次の課題:
   - RH-N6 として、`HOPC-RH-Roadmap.md` / `HOPC-RH-OpenProblems.md` の
     OP-003 状態を RH-N3/N5 到達点に合わせて更新する。

### 日時: 2026/03/13 11:30 JST: Phase RH-N6 を実装（Roadmap/OpenProblems の OP-003 状態更新）

1. 目的: RH-N3/N5 までの到達状況を計画文書へ反映し、
   OP-003 の進捗と残課題を明示して次段着手点を固定する。
2. 内容:
   - 変更ファイル:
     - `DkMath/RH/docs/HOPC-RH-Roadmap.md`
     - `DkMath/RH/docs/HOPC-RH-OpenProblems.md`
   - 更新内容:
     - `Roadmap`:
       - Next Sprint を「OP-003 継続 + OP-001 着手」へ更新
       - OP-003 の到達済み項目（N1〜N5）と次の焦点（provider 直結）を明記
     - `OpenProblems`:
       - OP-003 を「未実装」から「進行中」へ更新
       - 到達済み（singleton/small finite-set/BoundarySide/docs同期）を列挙
       - 残タスク（`hS_lift` / `hsum_lift` 供給、OP-001 再利用仮定化）を追加
3. 結論: OP-003 は API 骨格完成フェーズを通過し、
   次は provider 供給層と finite→infinite 接続を主軸に進める段階へ移行した。
4. 失敗事例: なし（ドキュメント更新のみ）。
5. 備考:
   - `.lean` 実装への変更はなし。
   - OP-003 の優先度は高のまま維持（継続）。
6. 次の課題:
   - RH-N7 として、provider 側の最小実装に向け
     `hS_lift` / `hsum_lift` を生成する抽象インターフェースを
     `CFBRCBridge.lean` 近傍へ設計する。

### 日時: 2026/03/13 11:34 JST: Phase RH-N7 を実装（`hS_lift` / `hsum_lift` provider interface）

1. 目的: small finite-set bridge で必要な split 仮定
   (`hS_lift` / `hsum_lift`) を provider 層から渡しやすくする。
2. 内容:
   - 変更ファイル:
     - `DkMath/RH/CFBRCBridge.lean`
   - 追加実装:
     - `BoundaryInsertLocalLiftProvider` 構造体
       （`BoundarySide` + `insert p S` 用の `hS_lift` / `hsum_lift` を束ねる record）
     - `exists_stationaryAt_insert_of_cfbRc_primitive_prime_boundary_bridge_of_provider`
       （provider record を受けて split bridge へ委譲する wrapper）
3. 結論: RH 側 bridge に provider 直結入口を追加でき、
   翻訳層は record 1 個で `BoundarySide` small finite-set 停留補題へ接続可能になった。
4. 失敗事例:
   - 初回 wrapper 実装で `match side, hpnd` 由来の依存型不一致が発生。
   - `cases side` 分岐へ変更して型差を解消。
5. 検証:
   - `lake build DkMath.RH.CFBRCBridge` 成功。
   - `lake build DkMath.RH` 成功。
6. 次の課題:
   - RH-N8 として、`BoundaryInsertLocalLiftProvider` を使う
     最小利用例を `RH/README.md` と `RH/docs/RH-CFBRC-Discussion.md` に追記し、
     provider 設計の導入導線を固定する。

### 日時: 2026/03/13 11:40 JST: Phase RH-N8 を実装（provider 利用例の文書導線化）

1. 目的: RH-N7 で追加した provider interface の利用入口を
   README / Discussion に明示し、split 仮定版との使い分けを固定する。
2. 内容:
   - 変更ファイル:
     - `DkMath/RH/README.md`
     - `DkMath/RH/docs/RH-CFBRC-Discussion.md`
   - 追記内容:
     - `README.md`
       - `BoundarySide` API 一覧へ
         `BoundaryInsertLocalLiftProvider` と
         `..._boundary_bridge_of_provider` を追加
       - provider record 版の最小テンプレートを追加
     - `RH-CFBRC-Discussion.md`
       - RH-N4 セクションの公開 API に provider 系を追加
       - `Implementation Bridge (RH-N8: Provider record 直結)` を新設
       - split 版と provider 版の使い分けを明示
3. 結論: provider 設計の導入導線が文書上で確立し、
   bridge 利用者は「関数2本」か「record 1個」かで入口を選べるようになった。
4. 失敗事例: なし（ドキュメント更新のみ）。
5. 備考:
   - `.lean` 実装への変更はなし。
   - RH-N7 の実装補題名とテンプレート記述の整合を確認済み。
6. 次の課題:
   - RH-N9 として、`DkMath/RH/docs/README.md` にも provider 版テンプレートを同期し、
     README 間で RH-N8 導線を統一する。

### 日時: 2026/03/13 11:49 JST: Phase RH-N9 を実装（docs README へ provider テンプレート同期）

1. 目的: RH-N8 で整備した provider 導線を
   `DkMath/RH/docs/README.md` にも同期し、README 間の参照体験を一致させる。
2. 内容:
   - 変更ファイル:
     - `DkMath/RH/docs/README.md`
   - 追記内容:
     - `現状 API` 見出しを RH-N9 時点へ更新
     - CFBRC bridge 一覧に
       `BoundaryInsertLocalLiftProvider` と
       `..._boundary_bridge_of_provider` を追加
     - provider record 版の最小テンプレートを追加
3. 結論: `RH/README.md` と `RH/docs/README.md` の
   provider 利用導線が同期され、split 版 / provider 版の両入口が一致した。
4. 失敗事例: なし（ドキュメント更新のみ）。
5. 備考:
   - `.lean` 実装への変更はなし。
   - RH-N8 の Discussion 記述との整合を維持。
6. 次の課題:
   - RH-N10 として、`HOPC-RH-OpenProblems.md` の OP-003 残タスクに
     provider 実装進捗（RH-N7〜N9）を反映し、
     次の実装対象（provider 実体供給補題）を明示する。

### 日時: 2026/03/13 11:51 JST: Phase RH-N10 を実装（OP-003 残タスクの provider 進捗反映）

1. 目的: OpenProblems 側の OP-003 記述を RH-N7〜N9 の進捗に合わせて更新し、
   「入口整備済み / 実体供給未完」の境界を明確化する。
2. 内容:
   - 変更ファイル:
     - `DkMath/RH/docs/HOPC-RH-OpenProblems.md`
   - 更新内容:
     - OP-003 の状態文言を RH-N1〜N9 到達へ更新
     - 到達済みに provider 入口（record + wrapper）を追加
     - 残タスクを provider 実体供給補題中心へ具体化
       （`hS_lift` / `hsum_lift` 構成と供給源整理）
3. 結論: OP-003 は「bridge API 導線整備」段を完了し、
   次の実装対象が provider 供給補題群であることを文書上で固定できた。
4. 失敗事例: なし（ドキュメント更新のみ）。
5. 備考:
   - `.lean` 実装への変更はなし。
   - OP-003 の優先度は高（継続）のまま維持。
6. 次の課題:
   - RH-N11 として、`CFBRCBridge.lean` に
     provider 供給補題の最小スケッチ（`hS_lift` 供給器の雛形）を追加し、
     実体供給層へ着手する。

### 日時: 2026/03/13 11:54 JST: Phase RH-N11 を実装（provider 供給補題の最小スケッチ）

1. 目的: RH-N10 で明確化した「provider 実体供給」へ着手するため、
   split/pair 仮定から provider record を構成する最小補題を実装する。
2. 内容:
   - 変更ファイル:
     - `DkMath/RH/CFBRCBridge.lean`
   - 追加実装:
     - `boundaryInsertLocalLiftProvider_of_split`
       （`hS_lift` / `hsum_lift` から `BoundaryInsertLocalLiftProvider` を構成）
     - `boundaryInsertLocalLiftProvider_of_pair`
       （既存 pair 形式 `hlift` から provider を構成）
3. 結論: provider record への「供給入口」が補題化され、
   以後は供給側が split 形式または pair 形式で証明を作っても
   provider API へ同一手順で接続できるようになった。
4. 失敗事例:
   - `boundaryInsertLocalLiftProvider_of_pair` の初回実装で
     `match side` 依存型不一致が発生。
   - `cases side` で right/left を固定して解消。
5. 検証:
   - `lake build DkMath.RH.CFBRCBridge` 成功。
   - `lake build DkMath.RH` 成功。
6. 次の課題:
   - RH-N12 として、provider 実体供給の最初の候補として
     nonzero 前提 (`hS_lift`) だけを組み立てる補題群を導入し、
     `hsum_lift` 側と段階分離した実装計画へ進む。

### 日時: 2026/03/13 11:59 JST: Phase RH-N12 を実装（`hS_lift` 段階供給補題の導入）

1. 目的: provider 供給実装を段階分離するため、
   `hS_lift` を「`S` 上非零 + witness 非零」から合成する補題群を導入する。
2. 内容:
   - 変更ファイル:
     - `DkMath/RH/CFBRCBridge.lean`
   - 追加実装:
     - `boundary_hS_lift_of_nonzero_on_S_and_witness`
       （`hS_nonzero` と `hwnz_witness` から `hS_lift` を構成）
     - `boundaryInsertLocalLiftProvider_of_nonzero_on_S_and_witness`
       （上記 `hS_lift` 合成 + 既存 `hsum_lift` で provider record を構成）
3. 結論: `hS_lift` 供給が独立補題として切り出され、
   今後は `hsum_lift` の供給研究を別ラインで進められる構造になった。
4. 失敗事例:
   - 初回実装で `match side` 依存型不一致と `insert` 分岐での同一視ミスが発生。
   - `cases side` 分岐固定 + `simpa [hr_eq]` による同一視へ修正して解消。
5. 検証:
   - `lake build DkMath.RH.CFBRCBridge` 成功。
   - `lake build DkMath.RH` 成功。
6. 次の課題:
   - RH-N13 として、`hsum_lift` 供給候補（local contribution 由来）の
     最小 wrapper 設計を追加し、
     provider 実体供給の両輪（nonzero/sum-zero）を揃える。

### 日時: 2026/03/13 12:02 JST: Phase RH-N13 を実装（`hsum_lift` 段階供給 wrapper）

1. 目的: RH-N12 で先行した `hS_lift` 供給に対応して、
   `hsum_lift` 側も local contribution 由来で段階供給できる補題を追加する。
2. 内容:
   - 変更ファイル:
     - `DkMath/RH/CFBRCBridge.lean`
   - 追加実装:
     - `boundary_hsum_lift_of_local_zero_on_S_and_witness`
       （`S` 上 local=0 + witness local=0 から `hopcPrimeContributionSum(insert p S)=0` を構成）
     - `boundaryInsertLocalLiftProvider_of_nonzero_and_local_zero_on_S_and_witness`
       （RH-N12 の `hS_lift` 供給と RH-N13 の `hsum_lift` 供給を統合した provider 構成）
3. 結論: provider 実体供給の両輪（nonzero/sum-zero）が揃い、
   `BoundaryInsertLocalLiftProvider` への段階供給導線が完結した。
4. 失敗事例:
   - 初回実装で `match side` 依存型不一致が発生。
   - `cases side` で分岐固定して `hS_lift` / `hsum_lift` を組み立てる形へ修正。
5. 検証:
   - `lake build DkMath.RH.CFBRCBridge` 成功。
   - `lake build DkMath.RH` 成功。
6. 次の課題:
   - RH-N14 として、RH README / Discussion に
     RH-N12/N13 の段階供給テンプレート（nonzero/local-zero から provider 生成）を追記し、
     provider 実体供給の利用例を公開導線へ反映する。

### 日時: 2026/03/13 12:16 JST: Phase RH-N14 を実装（段階供給テンプレートの公開導線反映）

1. 目的: RH-N12/N13 で追加した段階供給補題を
   README / Discussion の公開導線に反映し、利用入口を明確化する。
2. 内容:
   - 変更ファイル:
     - `DkMath/RH/README.md`
     - `DkMath/RH/docs/RH-CFBRC-Discussion.md`
   - 追記内容:
     - `README.md`
       - 主要 API 見出しを RH-N14 時点へ更新
       - 段階供給補題 4 本を API 一覧へ追加
       - nonzero/local-zero から provider を生成する最小テンプレートを追加
     - `RH-CFBRC-Discussion.md`
       - `Implementation Bridge (RH-N14: 段階供給から provider 生成)` を追加
       - RH-N12/N13 補題の役割整理と最小テンプレートを追記
3. 結論: provider 実体供給の実装導線が文書化され、
   split 版 / provider 版 / 段階供給版の 3 入口が利用者に明示された。
4. 失敗事例: なし（ドキュメント更新のみ）。
5. 備考:
   - `.lean` 実装への変更はなし（RH-N13 で完了済み）。
   - `docs/README.md` は次フェーズで同等テンプレート同期予定。
6. 次の課題:
   - RH-N15 として、`DkMath/RH/docs/README.md` にも RH-N14 の
     段階供給テンプレートを同期し、README 間の導線差分を解消する。

### 日時: 2026/03/13 12:18 JST: Phase RH-N15 を実装（docs README へ段階供給テンプレート同期）

1. 目的: RH-N14 で追加した段階供給導線を `DkMath/RH/docs/README.md` に同期し、
   README 間の API/テンプレート差分を解消する。
2. 内容:
   - 変更ファイル:
     - `DkMath/RH/docs/README.md`
   - 追記内容:
     - `現状 API` 見出しを RH-N15 時点へ更新
     - CFBRC bridge 一覧へ段階供給補題 4 本を追加
     - nonzero/local-zero から provider を構成する最小テンプレートを追加
3. 結論: `RH/README.md` と `RH/docs/README.md` の導線が揃い、
   split 版 / provider 版 / 段階供給版の 3 入口が両 README で一貫した。
4. 失敗事例: なし（ドキュメント更新のみ）。
5. 備考:
   - `.lean` 実装への変更はなし（RH-N13 までで完了）。
   - `RH-CFBRC-Discussion.md` の RH-N14 セクションと内容整合済み。
6. 次の課題:
   - RH-N16 として、`HOPC-RH-OpenProblems.md` の OP-003 到達済みに
     RH-N12〜N15（段階供給導線）を反映し、残タスクを provider 実供給補題へ再整理する。

### 日時: 2026/03/13 12:20 JST: Phase RH-N16 を実装（OP-003 到達済み/残タスクの再整理）

1. 目的: RH-N12〜N15 の到達点を OP-003 に反映し、
   「導線整備済み」と「実供給未完」の境界を最新状態へ更新する。
2. 内容:
   - 変更ファイル:
     - `DkMath/RH/docs/HOPC-RH-OpenProblems.md`
   - 更新内容:
     - OP-003 状態文言を RH-N1〜N15 到達へ更新
     - 到達済みに段階供給補題群（`hS_lift` / `hsum_lift` 系）を追加
     - 残タスクを provider 実供給補題へ具体化
       （`hS_nonzero`, `hS_local0`, `hlocal_witness` の実供給補題）
3. 結論: OP-003 は橋渡し API と段階供給導線を確保済みで、
   次段は供給源の実補題実装に集中すべき状態へ整理された。
4. 失敗事例: なし（ドキュメント更新のみ）。
5. 備考:
   - `.lean` 実装への変更はなし。
   - OP-003 優先度は高（継続）を維持。
6. 次の課題:
   - RH-N17 として、`hS_nonzero` を CFBRC 側条件から供給する
     最小補題（候補1本）を `CFBRCBridge.lean` に追加し、
     provider 実供給フェーズへ入る。

### 日時: 2026/03/13 12:23 JST: Phase RH-N17 を実装（`hS_nonzero` 実供給補題の追加）

1. 目的: OP-003 の実供給フェーズ着手として、
   CFBRC 側条件（boundary 除法 + gap 非除法）から `hS_nonzero` を導出する最小補題を実装する。
2. 内容:
   - 変更ファイル:
     - `DkMath/RH/CFBRCBridge.lean`
   - 追加実装:
     - `boundary_nonzero_on_S_of_boundary_dvd_and_gap`
       （`S` 上の boundary 除法/非除法条件から `S` 上非零を供給）
     - `boundaryInsertLocalLiftProvider_of_boundary_dvd_and_gap_and_local_zero`
       （上記 `hS_nonzero` と local-zero 条件を統合して provider を構成）
3. 結論: `hS_nonzero` の実供給入口が導入され、
   CFBRC 条件セットから provider 構成へ接続する最小ルートが成立した。
4. 失敗事例:
   - 初回実装で `match side` 依存型不一致が発生。
   - `cases side` で side 固定の組立てへ修正して解消。
5. 検証:
   - `lake build DkMath.RH.CFBRCBridge` 成功。
   - `lake build DkMath.RH` 成功。
6. 次の課題:
   - RH-N18 として、`docs/README.md` / `RH-CFBRC-Discussion.md` に
     RH-N17 の `boundary_dvd + gap` 供給テンプレートを追記し、
     実供給ルートを公開導線へ反映する。

### 日時: 2026/03/13 12:25 JST: Phase RH-N18 を実装（`boundary_dvd + gap` 導線の文書反映）

1. 目的: RH-N17 の実供給ルートを公開導線へ反映し、
   docs 側から provider 実供給テンプレートへ直接到達できるようにする。
2. 内容:
   - 変更ファイル:
     - `DkMath/RH/docs/README.md`
     - `DkMath/RH/docs/RH-CFBRC-Discussion.md`
   - 追記内容:
     - `docs/README.md`
       - API 見出しを RH-N18 時点へ更新
       - RH-N17 追加補題 2 本を API 一覧へ追加
       - `boundary_dvd + gap + local-zero` から provider 生成するテンプレートを追加
     - `RH-CFBRC-Discussion.md`
       - `Implementation Bridge (RH-N18: boundary_dvd + gap 直結供給)` セクションを追加
       - 同テンプレートを追記
3. 結論: RH-N17 の実供給ルートが docs 導線へ統合され、
   実利用者は `hS_dvd` / `hS_gap` から provider 生成まで一気通貫で参照可能になった。
4. 失敗事例: なし（ドキュメント更新のみ）。
5. 備考:
   - `.lean` 実装への変更はなし（RH-N17 で完了済み）。
   - `RH/README.md` への同等同期は次フェーズ候補。
6. 次の課題:
   - RH-N19 として、`RH/README.md` にも RH-N18 テンプレートを同期し、
     README 間の公開導線を完全一致させる。

### 日時: 2026/03/13 12:27 JST: Phase RH-N19 を実装（RH README へ RH-N18 導線同期）

1. 目的: RH-N18 で docs 側に追加した実供給導線を
   `DkMath/RH/README.md` に同期し、README 間の公開導線を一致させる。
2. 内容:
   - 変更ファイル:
     - `DkMath/RH/README.md`
   - 追記内容:
     - 主要 API 見出しを RH-N19 時点へ更新
     - RH-N17 追加補題 2 本を API 一覧へ追加
     - `boundary_dvd + gap + local-zero` から provider 生成するテンプレートを追加
3. 結論: `RH/README.md` と `RH/docs/README.md` の
   RH-N18 導線が同期され、公開導線の差分が解消された。
4. 失敗事例: なし（ドキュメント更新のみ）。
5. 備考:
   - `.lean` 実装への変更はなし。
   - Discussion 側 RH-N18 セクションとの整合を維持。
6. 次の課題:
   - RH-N20 として、`HOPC-RH-OpenProblems.md` の OP-003 到達済みに
     RH-N17〜N19（実供給導線）を反映し、残タスクをさらに具体化する。

### 日時: 2026/03/13 12:29 JST: Phase RH-N20 を実装（OP-003 到達済みと残タスクの更新）

1. 目的: RH-N17〜N19 の実供給導線を OP-003 へ反映し、残タスクを実装可能粒度へ再整理する。
2. 内容:
   - 変更ファイル:
     - `DkMath/RH/docs/HOPC-RH-OpenProblems.md`
   - 更新内容:
     - OP-003 の状態を「RH-N1〜N19 到達済み」へ更新
     - 到達済みに RH-N17 実供給導線（`boundary_nonzero_on_S_of_boundary_dvd_and_gap`、
       `boundaryInsertLocalLiftProvider_of_boundary_dvd_and_gap_and_local_zero`）を反映
     - 残タスクを provider 実供給補題（`hS_local0` / `hlocal_witness` / `hS_dvd` / `hS_gap` 接続）
       へ再整理
3. 結論: OP-003 は「導線整備済み・実供給拡張継続中」の境界が明確化され、
   次段を `hS_local0` 側自動供給の実装へ集中できる状態になった。
4. 失敗事例: なし（ドキュメント更新のみ）。
5. 備考:
   - `.lean` 実装への変更はなし。
6. 次の課題:
   - RH-N21 として、`hS_local0` を `boundary_dvd + gap + hlocal_witness` から
     自動供給する補題と、前提簡約版 provider wrapper を追加する。

### 日時: 2026/03/13 12:32 JST: Phase RH-N21 を実装（`hS_local0` 自動供給と前提簡約 wrapper）

1. 目的: OP-003 残タスクのうち `hS_local0` 供給を実装し、
   `boundary_dvd + gap` 系 provider 構成の前提を削減する。
2. 内容:
   - 変更ファイル:
     - `DkMath/RH/CFBRCBridge.lean`
     - `DkMath/RH/docs/README.md`
     - `DkMath/RH/README.md`
     - `DkMath/RH/docs/HOPC-RH-OpenProblems.md`
   - 追加実装（`CFBRCBridge.lean`）:
     - `boundary_local_zero_on_S_of_boundary_dvd_and_gap`
       （`hS_dvd` / `hS_gap` / `hlocal_witness` から `hS_local0` を供給）
     - `boundaryInsertLocalLiftProvider_of_boundary_dvd_and_gap`
       （`hS_local0` を自動生成して RH-N17 wrapper へ委譲）
   - 文書同期:
     - `RH/docs/README.md` と `RH/README.md` の API 見出しを RH-N21 へ更新
     - 新規 API 2 本を一覧へ追加
     - `boundary_dvd + gap` テンプレートを前提簡約版へ更新
     - OP-003 状態を RH-N1〜N21 へ更新し、残タスクから `hS_local0` 供給を除外
3. 結論: `boundary_dvd + gap` 系 provider 構成は
   `hS_local0` 手動供給不要の段階まで進み、OP-003 は `hlocal_witness` 実供給に主眼が移った。
4. 失敗事例:
   - `BoundarySide` 依存型の一致で 1 箇所型不一致が発生。
   - `cases side` で right/left を固定して解消。
5. 検証:
   - `lake build DkMath.RH.CFBRCBridge` 成功。
   - `lake build DkMath.RH` 成功。
6. 次の課題:
   - RH-N22 として、local contribution 側から `hlocal_witness` を供給する実補題を追加し、
     `boundary_dvd + gap` 系 wrapper の仮定をさらに削減する。
