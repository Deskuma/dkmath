# Observed Minimum Profile Works History

## 運用方針

- このファイルは `ObservedMinProfile` 系作業の履歴を時系列で積み上げる。
- 以後は**作業ごとに追記**し、過去記録は削除せず残す。
- 1 エントリは「目的 / 変更 / 検証 / 次アクション」を最小単位とする。

## 履歴

### 2026-03-17: 交換条件の最小形を追加（理論接続を強化）

- **目的**
  - 試算転記節を、観測メモだけでなく最小命題形へ接続して理論強度を上げる。

- **変更**
  - `ObservedMinProfile-ResearchNote.md` の `12` 節に
    - `12.4 交換条件の最小形（命題）` を追加。
    - 命題: `A = a^t ⇒ A^m = a^(tm)` を明記。
    - 試算表の分割比 `t` と次数倍率 `tm` の対応を代数核として接続。

- **検証**
  - 文書更新のみ（既存試算表と命題形の整合を確認）。

- **次アクション候補**
  - Lean 側で `Nat` 版の最小補題（同命題）を追加する。
  - 反転平衡節との橋渡しとして「粒度交換平衡」短注を追加する。

### 2026-03-17: 交換則試算を ResearchNote へ転記

- **目的**
  - 新実験「粗視化↔微視化交換・反転平衡」の結果を
    観測記録として研究ノートへ固定する。

- **変更**
  - `ObservedMinProfile-ResearchNote.md` に
    - `12. 粗視化↔微視化交換則（試算転記）` を追加。
    - `exchange_coarse_fine_examples.csv` の交換例表を転記。
    - `exchange_multiresolution_chain.csv` の多段鎖を転記。
    - `powerswap_continuous_samples.csv` の連続族試算を転記。
    - 「試算転記であり証明主張ではない」を明記。
  - 追記テンプレート節を `13.` に繰り下げ。

- **検証**
  - `python/LPS/DHNT/docs/` の各 CSV 内容を照合して転記。

- **次アクション候補**
  - 交換例の自動探索結果を同節へ追加（上限付き列挙）。
  - Lean 側に最小補題（`A=a^t -> A^m=a^(tm)`）を試験追加。

### 2026-03-17: 新実験「割り切り関係倍数の抽出」スクリプトを追加

- **目的**
  - 粗視化↔微視化交換（`A^m = a^n`）と反転平衡（`a^b = b^a`）の試算を
    CSV で再現可能にする。

- **変更**
  - `python/LPS/DHNT/experiment_exchange_balance.py` を新規追加。
    - 粗視化↔微視化交換例を `exchange_coarse_fine_examples.csv` として出力。
    - 多段粒度鎖を `exchange_multiresolution_chain.csv` として出力。
    - 連続族 PowerSwap 試算を `powerswap_continuous_samples.csv` として出力。
  - `python/LPS/DHNT/README.md` に実行手順を追記。

- **検証**
  - `python experiment_exchange_balance.py --t-list 0.5,2,3,4` を実行。
  - 3 種 CSV の生成と代表行を確認。
  - 実行後に `64` 行の不整合を修正し、再実行して整合確認。

- **次アクション候補**
  - 交換例 CSV を ResearchNote の「粗視化↔微視化交換条件」節へ転記。
  - `A=a^t` 成立例の自動探索モード（上限付き）を追加。

### 2026-03-17: 抽出スクリプトを追加（縮約ビュー再生成）

- **目的**
  - 既存 profile-map CSV から、研究ノート更新に必要な縮約ビューを再生成できるようにする。

- **変更**
  - `python/LPS/DHNT/extract_profile_views.py` を新規追加。
    - `profile_map_boundary_switches.csv` から `Δ` 付き境界表を生成。
    - `ΔBody` 初出表を生成。
    - `One/Two` 増殖タイムラインを生成。
  - `python/LPS/DHNT/README.md` に抽出スクリプトの実行手順を追記。

- **検証**
  - `python extract_profile_views.py --big-order 27,64,125,216,343,512,729` を実行。
  - 出力確認:
    - `profile_map_boundary_with_delta.csv`
    - `profile_map_delta_first_appearance.csv`
    - `profile_map_growth_timeline.csv`

- **次アクション候補**
  - 抽出 CSV から ResearchNote へ自動転記する小ツールを追加。
  - `d=2` 用の同型抽出パイプラインを整備。

### 2026-03-17: `m`–`ΔTwo` 対応小表と弱い仮説文を追加

- **目的**
  - 増殖段階タイムラインから、`ΔTwo` の変化をより直接に読める形へ圧縮する。

- **変更**
  - `ObservedMinProfile-ResearchNote.md` に
    - `11.12 m と ΔTwo の対応（簡易表）` を追加。
    - `m=4..9` について `Big, ΔTwo, 同段の新規 ΔBody` を記録。
    - 「全体として増勢」「大きい新規ΔBody と増加段の近接」
      という弱い仮説文を追記。

- **検証**
  - 既存 `11.11` と `11.10` の記録値から整合確認。

- **次アクション候補**
  - `ΔTwo` の段差系列を簡易可視化（折れ線）してノートへ添付。
  - `d=2` 側の同型表を追加し、`d=3` との増勢差を比較する。

### 2026-03-17: タイムラインに `ΔOne` / `ΔTwo` 列を追加

- **目的**
  - profile 島の個数推移を「個数」だけでなく「増加速度」で比較可能にする。

- **変更**
  - `ObservedMinProfile-ResearchNote.md` の `11.11` を更新。
    - 列を `One-candidate, ΔOne, Two-candidate, ΔTwo` へ拡張。
    - `ΔOne` は一貫して `+1`、`ΔTwo` は段階増加する観測メモを追記。

- **検証**
  - 既存 `profile_map_summary.csv` の系列差分に基づく文書更新。

- **次アクション候補**
  - `ΔTwo` 増加の経験則を `Big=m^3` と対応づけて要約する。
  - `d=2` 側にも同じ差分列付きタイムラインを追加する。

### 2026-03-17: 増殖段階タイムライン表を追加

- **目的**
  - `Big` 増加に対する profile 島増殖と境界初出を同時に読める管理表を作る。

- **変更**
  - `ObservedMinProfile-ResearchNote.md` に
    - `11.11 増殖段階タイムライン` を追加。
    - 列: `Big`, `One-candidate`, `Two-candidate`, `新規 ΔBody`, `備考`。
    - `profile_map_summary.csv` と `11.10` 初出表の統合結果を記録。

- **検証**
  - 既存集計値（summary + 初出）に基づく文書更新のみ。

- **次アクション候補**
  - タイムラインの `One/Twо` 増加率を追加（差分列）。
  - `d=2` 側にも同型タイムラインを作って比較する。

### 2026-03-17: `ΔBody` 初出表を追記（境界増殖の段階性）

- **目的**
  - 境界間隔の「出現順」を固定し、地形増殖を段階的に追えるようにする。

- **変更**
  - `ObservedMinProfile-ResearchNote.md` に
    - `11.10 ΔBody 初出表` を追加。
    - `Big = 27..729`（立方列）での
      - その Big での観測集合
      - 初出集合
      - 累積集合
      を併記。
    - 初出系列 `{1,6,11} → +10 → +34 → +27 → +2 → +44` を観測メモとして追記。

- **検証**
  - `python/LPS/DHNT/docs/profile_map_boundary_switches.csv` から機械集計して反映。

- **次アクション候補**
  - 初出系列と `Big=m^3` の対応を簡易回帰で可視化。
  - `d=2` でも同形式の初出表を作成し、次数比較を行う。

### 2026-03-17: 境界縮約表を 343/512/729 へ拡張し頻度表を追加

- **目的**
  - 境界間隔の比較対象を 64/125/216 から立方列全体へ拡張し、
    反復パターンを定量化する。

- **変更**
  - `ObservedMinProfile-ResearchNote.md` の `11.8` を拡張。
    - `Big = 343, 512, 729` の `ΔBody` / `Δresidual` 付き境界表を追加。
    - `Big = 27..729` に対する `ΔBody` 頻度表を追加。
    - 出現候補 `1, 2, 6, 10, 11, 27, 34, 44` を明示。

- **検証**
  - `python/LPS/DHNT/docs/profile_map_boundary_switches.csv` から機械集計。

- **次アクション候補**
  - `ΔBody` 頻度と `Big=m^3` の関係を簡易回帰/経験則として整理する。
  - `d=2` 側で同様の `Δ` 頻度表を作り次数比較を行う。

### 2026-03-17: 境界縮約表に間隔列（ΔBody, Δresidual）を追加

- **目的**
  - 切替境界を座標だけでなく、間隔比較まで行える形に拡張する。

- **変更**
  - `ObservedMinProfile-ResearchNote.md` の `11.8` を更新。
    - `Big = 64, 125, 216` の境界表へ `ΔBody`, `Δresidual` 列を追加。
    - `Δresidual = -ΔBody` の恒等関係を注記。
    - 繰り返し候補間隔（`1, 6, 10, 11, 27, 34`）を追跡対象として明記。

- **検証**
  - `python/LPS/DHNT/docs/profile_map_boundary_switches.csv` を基に差分値を算出。

- **次アクション候補**
  - `Big = 343, 512, 729` まで同じ間隔表を拡張。
  - `ΔBody` の頻度表を作って境界増殖則を仮説化する。

### 2026-03-17: 観測領域拡大の分析結果を研究ノートへ固定

- **目的**
  - `Big = 27..729`（立方列）まで拡大した観測結果を、
    研究ノートへ再利用可能な形で記録する。

- **変更**
  - `ObservedMinProfile-ResearchNote.md` に
    - 「11.9 観測領域の拡大（Big = m^3, m=3..9）」節を追加。
    - One/Two/other の集計表（7点）を追記。
    - One 側の `m+1` 増加、Two 側の増殖、
      ならびに「境界は一般 Type I でなく次数固定圧縮可否」
      という修正版結論を明記。

- **検証**
  - `python/LPS/DHNT/docs/profile_map_summary.csv` の数値を転記して確認。

- **次アクション候補**
  - 境界切替点の間隔（`ΔBody`, `Δresidual`）を集計して
    増殖則の候補を調べる。
  - `d=2` 側にも同じ summary 形式を作って次数横断比較へ進む。

### 2026-03-17: 観測領域拡大（立方 Big 列 m=3..9）

- **目的**
  - 次数を増やす前に `d=3` の観測地図を「点」から「面」へ拡大する。

- **変更**
  - `python/LPS/DHNT/experiment_profile_map.py` を拡張。
    - 複数 Big 一括走査（`--big-list`）
    - 立方列一括走査（`--cube-m-start/--cube-m-end`）
    - 集計 CSV（`--emit-summary`）
    - `profile != other` 集約 CSV（`--emit-non-other`）
    - 境界切替 CSV（`--emit-boundary`）
  - `python/LPS/DHNT/README.md` に一括実行手順と成果物を追記。

- **検証**
  - `python experiment_profile_map.py --cube-m-start 3 --cube-m-end 9 --emit-summary --emit-non-other --emit-boundary`
  - 生成物を確認:
    - `profile_map_big_27/64/125/216/343/512/729.csv`
    - `profile_map_summary.csv`
    - `profile_map_non_other.csv`
    - `profile_map_boundary_switches.csv`

- **次アクション候補**
  - `profile_map_summary.csv` の推移を `ResearchNote` に追記。
  - 境界切替 CSV から `ΔBody` / `Δresidual` の間隔統計を作る。

### 2026-03-17: 境界縮約表（One↔Two 切替点）を追加

- **目的**
  - 展開マップを圧縮し、profile 切替境界の座標だけを比較可能にする。

- **変更**
  - `ObservedMinProfile-ResearchNote.md` に
    - `11.8 境界縮約表` を追加。
    - `Big = 64, 125, 216` それぞれで、
      `profile != other` 行の隣接切替点（One↔Two）を一覧化。
    - 縮約規則（非 other 行を Body 昇順、隣接 profile 差分を境界）を明記。

- **検証**
  - `python/LPS/DHNT/docs/profile_map_big_64.csv`
  - `python/LPS/DHNT/docs/profile_map_big_125.csv`
  - `python/LPS/DHNT/docs/profile_map_big_216.csv`
  から機械抽出した切替点を反映。

- **次アクション候補**
  - 境界切替点の間隔（Body差, residual差）を定量化する。
  - `d = 2` 側でも同じ縮約規則で境界表を作る。

### 2026-03-17: fixed Big マップ展開（profile != other 抜粋表）

- **目的**
  - 「マップを広げる」方針に沿って、
    fixed Big ごとの profile 島の位置を直接読める形にする。

- **変更**
  - `ObservedMinProfile-ResearchNote.md` に
    - `11.7` 節を追加。
    - `Big = 64, 125, 216` の `profile != other` 行を展開表として追記。
    - `Body / residual / profile / cube2_repr / type_i` を同時表示し、
      島配置の横比較を可能化。

- **検証**
  - `python/LPS/DHNT/docs/profile_map_big_64.csv`
  - `python/LPS/DHNT/docs/profile_map_big_125.csv`
  - `python/LPS/DHNT/docs/profile_map_big_216.csv`
  から機械抽出した行を使用。

- **次アクション候補**
  - 各 Big で境界近傍（One↔Two切替点）を抽出した縮約表を追加。
  - `d = 2` 側にも同形式の展開表を作り、次数横断比較を行う。

### 2026-03-17: 仮説更新（Type I 一般から次数固定圧縮へ）

- **目的**
  - CSV 観測結果を反映し、`ObservedMinOne/Two` の境界仮説を
    実データ整合的な形へ更新する。

- **変更**
  - `ObservedMinProfile-ResearchNote.md` に
    - `Big = 64, 125, 216` の profile 集計表を追加。
    - `Type I` 粗分類の限界（`16`, `9` など）を明記。
    - 仮説を
      「一般 Type I 対応」から
      「次数 `d` 固定の single-`d`-power / two-`d`-power 圧縮対応」へ修正。

- **検証**
  - 既存 CSV（`profile_map_big_64/125/216.csv`）の集計に基づく文書更新。

- **次アクション候補**
  - `profile != other` 行の抜粋表を Big ごとにノートへ追加。
  - Lean 側で `single-cube` / `two-cube` の補助述語名を整備して対応を明確化。

### 2026-03-17: 実証データより分類記録を優先して追記

- **目的**
  - 新規実証を増やす前に、既存標本の Type 分類を記録として固定する。

- **変更**
  - `ObservedMinProfile-ResearchNote.md` に
    - 「現時点の分類記録（実証データ追加なし）」を追加。
    - residual `64, 27, 125, 91, 35, 65` について、
      `ObservedMin` と Type I（両整数表示）有無を対応表で整理。
    - `ObservedMinOne ↔ Type I あり`、`ObservedMinTwo ↔ Type I を持ちにくい`
      という作業仮説を「分類記録」として固定。

- **検証**
  - 文書更新のみ（Lean/Python コード変更なし）。

- **次アクション候補**
  - Type II/III/IV の補助分類表を追加する（存在証明を分離して記録）。
  - 分類表の各行に `BigFamilyExamples.lean` の対応定理名を併記する。

### 2026-03-17: 指数表示相 Type I–IV の実装計画を明記

- **目的**
  - `n = a^b` 表示の整数性/無理数性を軸に、
    residual 観測を段階的に実装できる計画へ落とす。

- **変更**
  - `ObservedMinProfile-ResearchNote.md` に
    - 「実装計画：指数表示相（Type I–IV）」節を追加。
    - Type I–IV の作業定義を固定。
    - ドキュメント→Lean補助定理→Python補助スクリプト→接続仮説の
      5段階タスクを明記。
    - 実験段階の完了条件（ラベル付与、対応表、Lean再利用性）を追記。

- **検証**
  - 文書更新のみ（Lean/Python コード変更なし）。

- **次アクション候補**
  - residual `64, 91, 35, 27, 65` の Type ラベル表を作成。
  - `BigFamilyExamples.lean` の既存補題名と Type 表の対応をノートに追記。

### 2026-03-17: DHNT 基本原理（指数座標と再配分）を固定

- **目的**
  - `n = e^k` 観点を中心に、DHNT の原理文を
    LPS 観測ノートへ接続可能な形で明文化する。

- **変更**
  - `ObservedMinProfile-ResearchNote.md` に
    - 「DHNT 基本原理（指数座標と再配分）」節を追加。
    - 指数座標化 (`n = e^k`, `k = log n`) と同一値再配分 (`n = e'^k' = a^b`) を整理。
    - `DHNT_SimpleDemo.py` の `ln(e^k)=k` を観測器の最小実装として位置づけ。
    - residual profile 分岐との接続を作業仮説として追記。

- **検証**
  - 文書更新のみ（Lean コード変更なし）。

- **次アクション候補**
  - DHNT docs 側（`DkMath/DHNT/docs`）にも同原理の短縮版を転記し、
    LPS ノートへの相互リンクを追加する。

### 2026-03-17: DHNT 観点（連続対称核と格子フィルター）を追記

- **目的**
  - PowerSwap 交点と residual profile 分岐を、
    DHNT 的な「連続対称核→離散格子観測」の地図として整理する。

- **変更**
  - `ObservedMinProfile-ResearchNote.md` に
    - 「DHNT 動的調和数論観点（連続対称核と格子フィルター）」節を追加。
    - 連続層（`e` 中心の対称核）、離散層（整数格子フィルター）、
      residual 層（Big 固定 profile 観測）の 3 層構造を明記。
    - 作業仮説として、PowerSwap 整数解と residual 分岐を
      同一対称核の別観測像として読む方針を追記。

- **検証**
  - 文書更新のみ（Lean コード変更なし）。

- **次アクション候補**
  - `Big = 64, 125, 216` の profile map と DHNT 3層地図の対応図を追記する。
  - 必要なら簡易図（1次元バー or 表）を docs 側で統一フォーマット化する。

### 2026-03-17: 極点（中心 e）観点の明文化

- **目的**
  - `a^b = b^a` の「ひっくり返り」を、偶然一致ではなく
    中心 `e` を軸にした双極2解構造として研究ノートに固定する。

- **変更**
  - `ObservedMinProfile-ResearchNote.md` の指数法則節に
    - 「中心 `e` と双極2解構造（PowerSwap center principle）」を追記。
    - `f(x) = log x / x` の山型（増加→最大 at `e`→減少）を明記。
    - `c < 1/e` で左右2解が現れる解釈と、`2^4 = 4^2` を離散標本として整理。

- **検証**
  - 文書更新のみ（Lean コード変更なし）。

- **次アクション候補**
  - profile map 側に「中心 `e` 由来の双極解釈」を注記し、
    境界表との対応関係を明示する。

### 2026-03-17: 指数法則観点の整理と指数圧縮表の追加

- **目的**
  - `ObservedMinOne/Two` 境界を「指数圧縮可能性」の観点で読み直し、
    交点模様の解釈軸を `ResearchNote` に固定する。

- **変更**
  - `ObservedMinProfile-ResearchNote.md` に
    - 「指数法則観点（指数圧縮と反転交点）」節を追加。
    - 圧縮法則 `(a^m)^n = a^(mn)`、反転交点 `a^b = b^a`、
      対数密度 `log a / a` の観測視点を整理。
    - `ObservedMinOne/Two` を「単一冪へ圧縮可/不可」の作業仮説として明記。
    - 立方3標本を跨いだ residual の指数圧縮表を追加。

- **検証**
  - 文書更新のみ（Lean コード変更なし）。

- **次アクション候補**
  - `Big = 64, 125, 216` について profile map の掃引表を拡張する。
  - 小スクリプトで residual 分類表を半自動生成し、ノート追記を効率化する。

### 2026-03-17: 交点地形（profile map）分析の追記

- **目的**
  - 「標本がある」状態から一歩進め、`ObservedMinOne ↔ ObservedMinTwo` の境界が
    どこに現れるかを研究ノートで読める形にする。

- **変更**
  - `ObservedMinProfile-ResearchNote.md` に
    - 「交点地形メモ（profile map）」節を追加。
    - 交点を 3 層（PowerSwap / same Big / profile 境界）で整理。
    - 固定 Big で `B ↦ label(Big - B)` として観測する枠組みを明記。
    - `Big = 216, d = 3` の境界表（Body, residual, profile）を追記。

- **検証**
  - 文書更新のみ（Lean コード変更なし）。

- **次アクション候補**
  - 同形式の境界表を `Big = 64`, `Big = 125` にも追加。
  - 必要なら小スクリプトで `Body` 掃引表を自動生成し、ノートへ転記。

### 2026-03-17: 現状分析の固定と生成テンプレ明文化

- **目的**
  - 現状分析の重要点を `ResearchNote` に固定し、次作業へ使える Lean 対応テンプレを明文化する。

- **変更**
  - `ObservedMinProfile-ResearchNote.md` に
    - 「現状分析（2026-03-17）」節を追記。
    - `d = 3` 独立 3 標本再現の重要性、`d = 2` 補足、強み・未確定点を整理。
    - 「生成テンプレ（Lean 定理名対応）」節を追加し、
      `candidate*` 系定理の最小構成手順を固定。

- **検証**
  - 文書更新のみ（Lean コード変更なし）。

- **次アクション候補**
  - テンプレに沿って `d = 3` の 4 標本目を追加する。
  - もしくは `d = 2` 側で 2 標本目を追加し、次数横断の再現性を厚くする。

### 2026-03-17: 初回作業履歴（現状までの概要）

- **目的**
  - LPS サンプル群で observed minimum profile 分岐の実験基盤を整備する。

- **変更**
  - `BigFamilyInt.lean` を `Samples/LPS` 配下に新設。
  - `BigFamilyExamples.lean` を新設し、観測標本を追加。
  - `ObservedMinOne/Two` を局所定義として導入（実験段階のため局所維持）。
  - 立方 `d = 3` で独立 3 標本を束ねる総括定理
    - `cube_observed_min_split_reproduced_three_samples`
    を追加。
  - `docs/ObservedMinProfile-ResearchNote.md` を新設し、
    事実確認と標本生成原理（短メモ）を整理。
  - `README.md` に `docs` ノートへの導線を追加。

- **検証**
  - `./lean-build.sh DkMath.Samples.LPS.BigFamilyExamples` 成功。
  - `./lean-build.sh DkMath.Samples` 成功。

- **次アクション候補**
  - 新規標本追加（`d = 3` 継続）または生成原理節の精密化。
  - 必要に応じて `ObservedMin` の共通 API 昇格を再評価。
