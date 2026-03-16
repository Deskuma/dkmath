# Observed Minimum Profile Works History

## 運用方針

- このファイルは `ObservedMinProfile` 系作業の履歴を時系列で積み上げる。
- 以後は**作業ごとに追記**し、過去記録は削除せず残す。
- 1 エントリは「目的 / 変更 / 検証 / 次アクション」を最小単位とする。

## 履歴

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
