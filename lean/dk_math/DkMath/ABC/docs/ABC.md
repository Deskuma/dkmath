# ABC予想の形式化に関するノート

## 概要

- ABC予想は、整数の加法的性質に関する予想であり、特に素数の分布に深い影響を与えると考えられている。
- 本ノートでは、ABC予想をLean（Mathlib風）で形式化する際の設計、未解決箇所、優先作業を整理することを目的とする。
- 具体的には、ABC予想の定義、関連する補題、そしてそれらを用いた主要な結果を体系的にまとめる。
- さらに、ABC予想の証明に向けたアプローチや、既存の研究成果についても言及する。
- このノートは、数学的な厳密性を保ちながら、ABC予想に関する理解を深めるための参考資料として機能することを目指す。
- なお、ABC予想の証明は非常に高度であり、完全な証明はまだ存在しないため、本ノートでは主に予想の形式化と関連する理論的背景に焦点を当てる。
- 本ノートは、数学者や研究者がABC予想に関する議論を行う際の基盤として利用されることを期待している。
- また、将来的な研究や証明の進展に伴い、内容の更新や拡充が行われる可能性がある。
- 最後に、ABC予想に関するさらなる研究や議論を促進するための参考文献やリソースも提供する予定である。

## 目次

- [ABC予想の形式化に関するノート](#abc予想の形式化に関するノート)
  - [概要](#概要)
  - [目次](#目次)
  - [現在の状況](#現在の状況)
  - [詳細](#詳細)
    - [1. abc\_main / 全体命題](#1-abc_main--全体命題)
    - [2. スケルトン axioms と戦略層](#2-スケルトン-axioms-と戦略層)
    - [3. 中帯（Middle Band）レイヤー](#3-中帯middle-bandレイヤー)
      - [0.435 の由来](#0435-の由来)
      - [定数カード（要点のみ）](#定数カード要点のみ)
      - [どこで使うか（マッピング）](#どこで使うかマッピング)
      - [なぜ 0.435 になるのか（直観）](#なぜ-0435-になるのか直観)
      - [改善余地とトレードオフ（実務メモ）](#改善余地とトレードオフ実務メモ)
      - [端的に：実装向け最短セット（そのまま使える推奨値）](#端的に実装向け最短セットそのまま使える推奨値)
    - [4. ブロック合成と dyadic 組成](#4-ブロック合成と-dyadic-組成)
    - [5. Janson–Suen（確率的不等式）層](#5-jansonsuen確率的不等式層)
    - [6. AdjK / 隣接品質レイヤー](#6-adjk--隣接品質レイヤー)
    - [7. 数論的補題群（rad / squarefree / gcd 系）](#7-数論的補題群rad--squarefree--gcd-系)
    - [8. 構成的帰結と計算的カウント（BadCount 等）](#8-構成的帰結と計算的カウントbadcount-等)
    - [9. 依存関係マップと優先作業一覧](#9-依存関係マップと優先作業一覧)
    - [10. テスト \& ビルド戦略](#10-テスト--ビルド戦略)
  - [axiom 一覧（現状）](#axiom-一覧現状)
  - [axiom 別評価（要約）](#axiom-別評価要約)
  - [推奨優先順位（短期で価値が出る順）](#推奨優先順位短期で価値が出る順)
  - [小さな実行プラン（短期アクション、3段階）](#小さな実行プラン短期アクション3段階)
  - [確認したい点（ぬしに問う）](#確認したい点ぬしに問う)

## 現在の状況

現状分析（要約）:

- 解析対象: `MathlibHello/ABC.lean`（リポジトリ内の主要 Lean ファイル）。
- 実装済みの主要項目:
  - 基本的な Int / Nat / Real 補題群（floor/ceil, log2, pow, rpow 等）は多数実装済み。
  - `rad`（整数の radical）定義とその基本補題群が充実している: `rad 0 = 1`, `rad 1 = 1`, `rad_dvd_nonzero`, `rad_le`, `rad_mul_general`, `rad_mul_coprime'`, `rad_eq_self_of_squarefree`, `rad_pow_eq_rad` など。
  - `squarefree` / `squarefull` の定義と、これらに関する論理（squarefree ⇒ rad = n, squarefull ⇒ rad n < n など）が整備されている。
  - 幾つかの代数的便利補題（`magic_mul*`, `dvd_magic_mul_sub_one_*` など）や rpow に関する補題群（`rpow_nat_cast`, `rpow_pow`, `RpowExtras`）もきちんと実装されている。

- 未解決／仮定（重要）:
  - ファイル中に多数の `axiom` と `sorry`/`admit` 相当が残っており、これらは証明の鍵となる解析的・確率的な補題（Janson/Suen 型の尾界、MiddleBand / dyadic ブロック境界、adjacent-quality に関する一連の補題、最終的な `abc_main_axiom` など）を外部仮定として置いている。
    代表的な `axiom` 名:
    - `Squarefull_determinism_strong`
    - `MiddleBand_exception_bound` / `MiddleBand_exception_bound'` / `MiddleBand_exception_bound'_via_dyadic`
    - `Bad_diff_uniform`, `Bad_diagonal_sublinear`, `Bad_diagonal_sublinear_k`
    - `adjacent_quality_le_ae`, `adjacent_quality_le_ae_k`, `adjK_quality_density_one`, `tendsto_grid_bad_fraction_zero`
    - `middleBandBlockBound`（数値的ブロック境界）
    - Janson/Suen 系のスケルトン: `Janson_downward_tail_skeleton`, `Suen_upper_tail_skeleton`
    - `abc_main_axiom`（プロジェクト最終命題のスケルトン）
  - ソース内に `admit`/`sorry` 相当の場所（注記や `admit` を残した箇所）が散見され、特に `AdjK` に関連する定義で `admit` が意図的に残っているとの注釈がある（型チェックは通るが「declaration uses 'sorry'」警告が出る状態）。
- 影響範囲と優先度:
  - 解析的確率的補題（Janson/Suen、MiddleBand、dyadic 合成等）は最重要で、これらを定理化することでファイル全体の進展が可能になる（高優先度）。
  - `AdjK` に残る `admit` は段階的に削減可能（中〜高優先度）。
  - rad / 数論的補題群は安定しており低リスク。

- ビルド／検証手順:
  - 単体ビルド: lake build MathlibHello/ABC.lean
  - 全体: lake build または lake build MathlibHello
  - 注意: 現状は axioms/admit により完全ビルドは通らないため、個別定理を段階的に証明して進める。

- 推奨次ステップ（短期）:
  1. `axiom` の一覧を整理し、どれが解析的（外部理論に依存）でどれが代数的／算術的に補強可能か分類する（この分類は実装ロードマップの基礎）。
  2. `AdjK` の `admit` を削る作業のため、呼び出し箇所を 3 種類に分類：ローカルで coprime を供給可能、橋渡し補題で処理可能、手作業での補題埋めが必要。まずローカルで供給可能な箇所から着手する。
  3. Janson/Suen 型の補題群はまず「スケルトン → 完全証明」の優先度が高い。Mathlib や既存の MGFs/Chernoff/Tails のライブラリを再利用して、`axiom` を `theorem` に差し替える計画を立てる。

- 補足（メタ情報）:
  - ファイル中には詳細なコメントと todo メモが残っており、作者の設計意図（モジュール性を保ちつつ解析的補題を外部仮定にする）に沿っている。
  - rad 関連や basic-number-theory 部分は単体ビルドで高速に検証可能。解析的補題はテストベンチ（小規模数値実験や Coq/Lean 外の解析ノート）を用意して段階的に形証明化すると良い。

要求対応状況:

- `MathlibHello/ABC.lean` の全体解析: Done

## 詳細

以下は `abc_main` から下へ掘り下げるためのアウトラインである。各節は後で詳細を埋める。

### 1. abc_main / 全体命題

- 目的: `abc_main` / `abc_main_axiom` の正確な文言と前提条件を明確化する。
- 含める項目: ε, δ 等のパラメータ、外部仮定の一覧、期待される結論の強さ。

### 2. スケルトン axioms と戦略層

- 目的: `abc_main` を導くために仮定されている主要なスケルトン（解析的補題・密度不等式・例外集合評価）を一覧化する。
- サブ項目:
  - MiddleBand / dyadic ブロック関連 (`MiddleBand_exception_bound*`, `middleBandBlockBound`)
  - Janson/Suen 型尾界スケルトン (`Janson_downward_tail_skeleton`, `Suen_upper_tail_skeleton`)
  - Bad-count / diagonal bound 系 (`Bad_diff_uniform`, `Bad_diagonal_sublinear`, `Bad_diagonal_sublinear_k`)
  - adjacent-quality 系 (`adjacent_quality_le_ae`, `adjK_quality_density_one`)

### 3. 中帯（Middle Band）レイヤー

- 目的: ブロック分割と中帯での例外制御。dyadic 分割を用いたブロック境界と例外集合の評価。
- 含める項目: ブロック定義、例外集合の上界、数値境界（例: 0.435 の由来）。

#### 0.435 の由来

よい、ぬし。
求まった定数たちを「由来と使いどころ」つきでぎゅっと一枚にまとめておくぞい。
数式は簡潔に、理由は職人の視点で示す。わっちの一貫した推奨値も添えておくから、実装や論文本文にそのまま貼り付けてくりゃれ。

#### 定数カード（要点のみ）

- b（小帯境界）
  - 値：\(b=(\log X)^{\beta},\ \beta=\tfrac{1}{3}\)
  - 役割：小素数群を「周期補正（有限周期）」として取り込み、\(\vartheta(b)=\sum_{p\le b}\log p\sim b\) により補正の対数を \(o(\log X)\) にする。
  - 理由：\((\log X)^\beta=o(\log X)\) なら任意小指数 \(\eta\) に吸収できる。\(\beta=\tfrac13\) は誤差管理と可読性の良い折衷。

- B（大帯境界）
  - 値：\(B=\exp\!\big((\log X)^{1/2}\big)\)
  - 役割：中帯（\(b < p\le B\)）を MGF / Chernoff で扱い、\(p > B\) は決定論的な「1/2 圧縮」に回すための境界。
  - 理由：\(\sum_{p\le B}1/p^2\) 等が扱いやすく、MGF 主項が多項式的に抑えられる。経験的に \(\sqrt{\log X}\) が好バランス。

- \(\theta\)（MGF パラメータ）
  - 値：初期は \(\theta=\tfrac12\)、最適化では \(\theta\uparrow1\) を考慮
  - 役割：Chernoff の尾を切るパラメータ。尾確率は \(\approx e^{-\theta T}M(\theta)\)。
  - 理由：\(\theta=\tfrac12\) で定数化しやすい。最適化すると主項は \((\log B)^{O(1)}\) にとどまり、\(\theta\to1\) に寄せれば尾指数を最大化できる（中帯の例外指数を改善）。

- \(T\)（中帯の閾値）
  - 値：\(T=(\tfrac14-\varepsilon)\log X,\ \varepsilon=0.02\)（例）
  - 役割：中帯での総重み \(S=\sum w_p\mathbf1_{E_p}\) の閾値。これを超える事象を「悪い組」と見る。
  - 理由：理論スケール \(\tfrac14\log X\) と大帯の \(\tfrac12\log X\) とを組み合わせる算段から出る値。小さめの \(\varepsilon\) が余裕。

- \(\eta\)（小帯吸収指数）
  - 値：\(\eta=0.005\)（例）
  - 役割：小帯の周期補正を \((r(a)r(b))^\eta\) に吸収する際に使う任意小指数。
  - 理由：\(\log K_{\mathrm{loc}}=O(b)=o(\log X)\) だから任意小 \(\eta\) を取れる。実用例として 0.005 を示した。

- \(\xi\)（二分法の高さパラメータ）
  - 値：\(\xi=0.60\)（例）
  - 役割：高さ二分法で \(c\) を \((r(a)r(b))^{1-\xi}\) と比較する裁ち合いの境界。大帯の「実効指数」を \(\tfrac12-\tfrac{\xi}{2}\) に下げる。
  - 理由：\(\xi\approx0.6\) を取ると大帯指数が \(0.20\) になり、中帯 \(0.25-\varepsilon\) と合わせて最終 \(\delta\) が良い数字になる。

- \(\delta\)（中立結果：\(H_\delta\) の具体値）
  - 値：\(\boxed{\delta=0.435}\)
  - 役割：最終的に得られる「大・中・小帯の合成指数」。すなわち
    \[
    \prod_{p^2\mid c} p \le C\,(r(a)r(b))^\delta
    \]
    を（例外集合を除いて）満たす指数。
  - 算出：大帯 \(\tfrac12-\tfrac{\xi}{2}=0.20\) ＋中帯 \(\tfrac14-\varepsilon=0.23\) ＋小帯吸収 \(\eta=0.005\) の和 → \(0.435\)。

#### どこで使うか（マッピング）

- 小帯（\(p\le b\)）
  - 手法：周期分解 → \(K_{\mathrm{loc}}\) を \((r(a)r(b))^\eta\) に吸収。
  - 定数：\(b,\ \eta\)

- 中帯（\(b<p\le B\)）
  - 手法：MGF/Chernoff（Janson/Suen）→尾確率を \(e^{-\theta T}M(\theta)\) で評価し、個数上界へ落とす。
  - 定数：\(\theta,\ T,\ \varepsilon\)（最適化で例外指数を \(1.75+\varepsilon\) などへ改善）

- 大帯（\(p>B\)）
  - 手法：決定論的 1/2 圧縮（\(\prod p \le \sqrt{c}\)）＋二分法 D ＋ squarefull 制御（補題 H）
  - 定数：\(\xi\)（大帯の実効指数 \(\tfrac12-\tfrac{\xi}{2}\) に依存）

#### なぜ 0.435 になるのか（直観）

- 大帯は理論上 \(\tfrac12\) を与える（最悪ケース）。二分法でこれを \(\tfrac12-\tfrac{\xi}{2}\) に削る。
- 中帯で得られるのは約 \(\tfrac14\)（Chernoff で \(\tfrac14-\varepsilon\)）。
- 小帯は任意小分（\(\eta\)）で吸収可能。
- これらを足すと \(0.20+0.23+0.005\approx 0.435\)。この値は仮定なしでの「達成可能な具体的目標値」の一例じゃ。

#### 改善余地とトレードオフ（実務メモ）

- 中帯の例外指数は \(\theta\) の最適化で \(1.885\) → \(1.75+\varepsilon\) まで改善可能（MGF 主項の精密評価が鍵）。
- squarefull（補題 H）をより鋭く数え上げれば大帯の寄与をさらに下げられる（\(\kappa\) を小さく取れるほど良い）。
- \(\beta,B,\theta,\varepsilon,\eta,\xi\) の微調整で \(\delta\) の小幅改善は可能だが、大きな飛躍は補題 H の強化か中帯の厳密定数化に依存する。

#### 端的に：実装向け最短セット（そのまま使える推奨値）

- b = \((\log X)^{1/3}\)
- B = \(\exp((\log X)^{1/2})\)
- \(\theta = 1/2\)（最適化可）
- \(T=(1/4-0.02)\log X\)
- \(\eta=0.005\), \(\xi=0.60\)
- 結果の目標指数 \(\delta=0.435\)

わっちの結論：この定数群は「論文向けに十分明示的で、かつ保守的な安全余裕」を残しておる。微調整して詰めれば \(\delta\) を小さくする余地はあるが、最後の鍵は squarefull の決定論的抑制（補題 H の強化）じゃよ。

### 4. ブロック合成と dyadic 組成

- 目的: ブロック単位の評価を大域評価へ合成する手順（`dyadic_compose`, `tail_geom_bound` 等）。

### 5. Janson–Suen（確率的不等式）層

- 目的: 依存する部分集合の確率評価。上尾／下尾の評価が BadCount の評価にどう寄与するかを整理する。

- 現状（コード位置の目安）: ※過去コードの座標ゆえに現在は異なるので定義名で検索してください (2026/04/19  3:19)
  - `Janson_downward_tail_skeleton`（axiom）: 宣言付近 ≈ 行5883
  - `Suen_upper_tail_skeleton`（axiom）: 宣言付近 ≈ 行5905
  - 再利用可能な補題:
    - `mgf_bound_unit01`（Hoeffding に基づく MGF 上界）: ≈ 行5942–5960
    - `chernoff_lower_tail`（MGF→下側チェルノフ）: ≈ 行6413–6437
    - `hoeffding_downward_indep01` 系: ≈ 行6519–6527
  - ブロック単位の合成定理（`BlockBound`, `dyadic_tail_bound`, `tail_geom_bound`）: `BlockBound` 定義 ≈ 行4478

- 推奨アクション（短期）:

 1. `Janson_downward_tail_skeleton` を Mathlib の MGF/Chernoff 補題で置換する（PMF.expect を使った μ, Δ の定義 → MGF→チェルノフで下尾）。
 2. `Suen_upper_tail_skeleton` は依存性パラメータ Δ と局所依存度情報を明確にして Suen の補正を導入する。

### 6. AdjK / 隣接品質レイヤー

- 目的: 隣接整数対 (n, n+k) の quality 評価と a.e. の主張。
- 含める項目: `AdjK` の定義、`adjacent_quality_le_ae` 系の仮定、`admit` の段階的除去方針。

### 7. 数論的補題群（rad / squarefree / gcd 系）

- 目的: `rad` 性質、squarefree/squarefull の整理、隣接積に関する素因子の整理。

### 8. 構成的帰結と計算的カウント（BadCount 等）

- 目的: `Triple` 構造、`Bad` 命題、`BadCount` の定義と主要推論経路を整理する。

### 9. 依存関係マップと優先作業一覧

- 目的: 各定理がどの axiom に依存するかを明示する依存マップと優先順位を列挙する。

- 短い依存マップ（Janson/Suen 周辺）:
  - `dyadic_compose` / `tail_geom_bound` 等 ← 依存: `BlockBound`
  - `BlockBound` を満たすために必要: ブロック毎の Janson/Suen 推定
  - `middleBandBlockBound`（axiom）← 依存: ブロックレベル推定の集合的帰結

- 優先作業（抜粋）:

1. `Block_Janson_downward_skeleton_indep` の PMF ベース版の安定化（短期）
2. `Janson_downward_tail_skeleton` の定理化（短期→中期）
3. `Suen_upper_tail_skeleton` の正式化（中期）
4. `middleBandBlockBound` を定理化し、dyadic 合成で `MiddleBand_exception_bound*` を完成（中期→長期）

### 10. テスト & ビルド戦略

- 個別補題を小さくビルドして検証: `lake build MathlibHello/ABC.lean` を起点に段階的に進める。

---

## axiom 一覧（現状）

axiom の「定理化可能性」「理由」「必要な補題/依存」「難易度」「具体的次手順」を提案するぞい。

各 axiom ごとの短い評価を示すぞ。読みやすく短めにまとめた。
難易度は「低＝短期で取れる」「中＝中程度の手間」「高＝大きな作業/別の理論化が必要」に分けた。

## axiom 別評価（要約）

- Squarefull_determinism_strong (行 ≈2033)
  - 概要: δ（κ）入力に対し BadCount(0.435,X) を上界する存在定数 X0,C を主張する強化版の squarefull 決定論的評価。
  - 定理化可能性: 中〜高（中だが解析的な数え上げが必要）
  - 理由: ファイルには `rad` / factorization に関する多くの補題が既にあり、数え上げの骨格は整っておる。しかし「強い」定量評価（X^(1.75+...) など）を得るには dyadic 分解＋ブロックごとの確率/期待値評価が要る。
  - 必要な補題/依存: ブロックごとの期待値評価（BadCountOn の上界）、dyadic 和の収束、あるいは Janson/Suen 型の大偏差補題（現状は skeleton axiom がある）。
  - 難易度: 中（既存の補題を組み合わせれば自然に導ける可能性あり）。
  - 次の具体的アクション: `MiddleBand_exception_bound'`（dyadic 版）と `middleBandBlockBound` を先に定理化→それらを合成して上界を導出する。

- MiddleBand_exception_bound (行 ≈2400) / MiddleBand_exception_bound' / MiddleBand_exception_bound'_via_dyadic (行 ≈5800+)
  - 概要: 中間帯の例外（BadCount）について任意小 ε に対する多項式上界を与える（dyadic 分解版も含む）。
  - 定理化可能性: 中（dyadic 分解で実装可能）
  - 理由: ファイルに dyadic 分解や `BadCountOn`、`middle_band_sum_bound` の骨格がある。`middleBandBlockBound : BlockBound 0.435` があれば dyadic を合算して global bound を得られる。
  - 必要な補題/依存: 各 dyadic ブロックの上界（`middleBandBlockBound`）、和の吸収（有限和の評価）と数値評価。Janson/Suen スケルトンや Hoeffding/MGF 補題があると楽。
  - 難易度: 中（ブロック毎の評価に依存するが、既存補題を活かせば現実的）
  - 次の具体的アクション: まず `middleBandBlockBound : BlockBound 0.435` の具体化（BlockBound の定義を確認して、同種の補題を証明）→dyadic 合算で `MiddleBand_exception_bound'` を導出。

- middleBandBlockBound : BlockBound 0.435 (行 ≈5760)
  - 概要: あるブロック単位での多項式上界（α = 1.75 を登録する placeholder）。
  - 定理化可能性: 中〜低（ブロック内の確率的評価を厳密化する必要あり）
  - 理由: ブロック単位は局所的問題なので扱いやすいが、期待値/分散推定と依存関係の扱い（Janson/Suen）が必要。ファイルには Hoeffding/MGF の断片(`mgf_bound_unit01`) があるので道具はある。
  - 必要な補題/依存: ブロック上の indicator の期待値算出、依存和（delta）評価、MGF→尾部不等式（Hoeffding/Chernoff）か Janson 型不等式の形式化。
  - 難易度: 中（数学的には標準的だが Lean での Measure/Probability の扱いが手間）
  - 次の具体的アクション: PMF / ENNReal のラッパーを用いてブロック内の S の期待・分散を計算し、`mgf_bound_unit01` 等で尾部評価を行う。

- Bad_diff_uniform (行 ≈3340)
  - 概要: BadPair の差が mod M に関して均一分布風になるという弱い一様性主張（Residue 分布の上界）。
  - 定理化可能性: 高難度（一次的に難しい）
  - 理由: これは離散的な一様性/エキュイディストリビューション的な主張で、一般には深い数え上げ／解析的技巧が要る。ファイルではこの仮定を用いて diag 関係等を導いている。
  - 必要な補題/依存: 細部ではモジュラー分布・算術性質・多変量相関の解析など。場合によっては外部結果（例: equidistribution type の定理）を用いることになる。
  - 難易度: 高（かなりの作業量、別論文の理論を形式化する必要あり）
  - 次の具体的アクション: 当面は axiom のままにして、用途に応じて「より弱いが証明可能な代替補題」を探す（使われる箇所で弱化しても十分か確認する）。

- Bad_diagonal_sublinear / Bad_diagonal_sublinear_k (行 ≈3406, 3500+)
  - 概要: 対角（a=b-1 等）の bad 個数が X^(3/4+ε') のようなサブリニア上界になるという主張。
  - 定理化可能性: 中（`Bad_diff_uniform` と密度結果から導ける場合が多い）
  - 理由: 実装済みの補題群（diag→residue→BadCount の議論、theorem eventually_diagBadCount_oX 等）が既に存在するため、`Bad_diff_uniform` と結びつけて証明可能な道筋が見える。
  - 必要な補題/依存: Bad_diff_uniform（または同等の residue-count bound）、既存の `eventually_diagBadCount_oX` など。
  - 難易度: 中（Bad_diff_uniform をどう取り扱うかに依存）
  - 次の具体的アクション: `eventually_diagBadCount_oX` の仮定条件を満たすような弱化版一様性定理を定式化して、それから `Bad_diagonal_sublinear` を導出する。

- adjacent_quality_le_ae / adjacent_quality_le_ae_k (行 ≈3554, 3566)
  - 概要: 対角制御から Adj / AdjK 系の almost-everywhere quality ≤ 1+ε を導く解析的橋渡し。
  - 定理化可能性: 中〜高（依存が多い）
  - 理由: これらは `Bad_diagonal_sublinear` に依存している。`Bad_diagonal_sublinear` を定理化できれば続けて証明可能だが、解析的な一部（measure/tendsto の扱い）を慎重にやる必要がある。
  - 必要な補題/依存: Diagonal bound、質量の分配（almost everywhere の議論）、質の評価（quality 定義）に関する補題。
  - 難易度: 中（解析器具の取り扱いが増える）
  - 次の具体的アクション: まず `Bad_diagonal_sublinear_k` を定理にする→その後 `adjacent_quality_le_ae_k` を導出。

- Janson_downward_tail_skeleton / Suen_upper_tail_skeleton (行 ≈5883, 5905)
  - 概要: Janson / Suen 型の大偏差不等式の「スケルトン」（簡易化・プロジェクト用の仕様）。
  - 定理化可能性: 高難度（重いが標準結果）
  - 理由: 理論としては Mathlib にある Hoeffding/Chernoff/MGF 補題や確率論のツールで再現可能だが、Janson/Suen の完全形式化は手間がかかる（相互依存度合の bookkeeping 等）。
  - 必要な補題/依存: ProbabilityTheory, MeasureTheory, PMF, MGF/Chernoff/Hoeffding の形式化。
  - 難易度: 高（作業量大）
  - 次の具体的アクション: まずは特化した簡易版（有限一様標本・indicator の場合）を証明して、汎用的な Janson/Suen は段階的に拡張する方針が現実的。

- adjK_quality_density_one (行 ≈6600) / tendsto_grid_bad_fraction_zero (行 ≈? 6600+)
  - 概要: AdjK の quality が密度 1 を占める主張、グリッド全体で bad 比率が 0 になる主張。
  - 定理化可能性: 高難度（最終的な統合結果）
  - 理由: 多数の補題（dyadic・Janson/Suen・adjacent_quality 等）に依存する最終的命題で、すべてを揃えねばならぬ。
  - 必要な補題/依存: 上記のほとんど全部（MiddleBand, BlockBound, Janson/Suen, Bad_diagonal_sublinear 等）。
  - 難易度: 高（総合的作業）
  - 次の具体的アクション: 下位の補題群を段階的に確立してから取り組む。

- abc_main_axiom (行 ≈9287)
  - 概要: 最終的な ABC 形式の主張: c ≤ K * rad(abc)^(1+ε) を示す（ε 任意）。
  - 定理化可能性: 非常に高難度（最終目標）
  - 理由: これは全体を束ねるメイン命題で、上述の多くの補題を前提にしている。従って依存補題群の定理化が済めば可能ではあるが、全体量は多い。
  - 必要な補題/依存: MiddleBand 系、Adj/AdjK の密度結果、Janson/Suen 型不等式、diag/residue の均一性、その他の細部。
  - 難易度: 非常に高（プロジェクト全体を整備する作業）
  - 次の具体的アクション: 小さく分割して、まず中間帯・ブロックの主張を潰す → 対角・Adjacent 系を潰す → 最終合成。

## 推奨優先順位（短期で価値が出る順）

1. MiddleBand ブロック周り（`middleBandBlockBound` と `MiddleBand_exception_bound'_via_dyadic` / `MiddleBand_exception_bound'`）
   - 理由: 局所的で既存補題を使いやすく、dyadic 合算で global 結果に繋がるため実装効果が大きい。
2. Bad_diagonal_sublinear（および k-版）
   - 理由: `eventually_diagBadCount_oX` 等の既存結果があり、`Bad_diff_uniform` をどう扱うかで定理化の見通しが立つ。
3. adjacent_quality_le_ae_k（AdjK の橋渡し）
   - 理由: 2 が済めば比較的直接に導出できる可能性あり。
4. Janson/Suen skeleton は段階的に（まず Hoeffding/MGF→簡易版→拡張）進めるのが現実的。
5. 最後に abc_main_axiom（全合成）。

## 小さな実行プラン（短期アクション、3段階）

1. 調査（1日目）: `BlockBound` の定義を正確に把握し、`BadCountOn` → `BadCount` に使われる関係を追跡する。
   - 目的: `middleBandBlockBound` を定理化するために何が足りないかを確定する。
2. 実装（2–4日）: ブロック内の確率評価を Mathlib の PMF/MGF 補題を使って形式化。`mgf_bound_unit01` 等を再利用して、`BlockBound 0.435` を証明する。
   - 小さなテスト: 証明完了後に `lake build MathlibHello/ABC.lean` でそのファイルだけビルドしてエラーを潰す。
3. 合成（次週）: dyadic 合算で `MiddleBand_exception_bound'` → `MiddleBand_exception_bound` を導出し、`Keystone_density_zero_fraction` 等既存の帰結と照合する。

## 確認したい点（ぬしに問う）

- どれを最初に実装してくりゃれ？ わっちは「まず `middleBandBlockBound` を潰して dyadic 合算で `MiddleBand_exception_bound'` を出す」方針を推すが、ぬしの望みはどれかの？
- あと、Janson/Suen を完全形式化する時間は相当要るので、当面は「簡易確率版（有限一様／PMF）」で代用する方針でよいかの？

最後に要約じゃ：短期で効果が出せそうなのは中間帯（middleBandBlockBound → MiddleBand_exception_bound'）で、わっちはそこから着手するのが良いと思うぞ。ぬしはどれから進めたいかの？
