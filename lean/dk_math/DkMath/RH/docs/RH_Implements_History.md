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
