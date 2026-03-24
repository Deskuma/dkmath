# Beam構造と因数分解 - Implements History

cid: 69c20351-9194-83a5-8a0d-6308a6e8c75c
branch: dev/flt-abc-260324-v0
head: 713f369

## 記録内容テンプレート（例）

### 日時: 2026/03/24 21:05 JST: タイトル

1. 目的:

2. 内容:
   - (内容/説明)

3. 結論:
4. 失敗事例:
5. 備考:
6. 次の課題:

## 実装履歴

### 日時: 2026/03/24 21:05 JST: 事前調査（Beam 資料読解・既存 API 棚卸し・現行ビルド確認）

1. 目的: `Beam構造と因数分解.md` の提案を、現在の DkMath ワークスペースでどこまで既存資産だけで受けられるかを具体化する。
2. 内容:
   - `DkMath/FLT/docs/Beam構造と因数分解.md` を読了し、特に後半の設計区間（`PrimitiveBeam` 提案、`body_not_perfect_pow` 接続、`no sorry` 優先順位）を抽出。
   - `DkMath/NumberTheory/ZsigmondyCyclotomic.lean` を確認し、原始素因子と Beam/GN 接続に直接使える既存定理を特定。
     - `exists_primitive_prime_factor_basic`
     - `prime_exp_not_dvd_diff_imp_primitive`
     - `pow_sub_pow_factor_cosmic_N`
     - `padicValNat_of_primitive_prime_factor_via_G`
   - `DkMath/NumberTheory/ZsigmondyCyclotomic.lean` の namespace が `DkMath.NumberTheory.GcdNext` であることを確認。
     - したがって新規 `PrimitiveBeam.lean` は、会話ログ雛形のように `GcdNext.lean` を import するより、`ZsigmondyCyclotomic.lean` を直接 import して上流 API を薄く束ねる方が依存方向として安全。
   - `DkMath/NumberTheory/GcdNext.lean` を確認し、mainline 側は「再利用基礎補題のみ保持」、一般 `d` の統合は `GcdNextResearch.lean` に退避済みであることを確認。
   - `DkMath/NumberTheory/GcdNextResearch.lean` を確認し、未完核が次の 2 箇所に残っていることを確認。
     - `body_not_perfect_pow` の中核となる `hpadic_bound` 部分
     - `padicValNat_upper_bound_layer_b_stub` の一般 `d > 3` 分岐
   - `lean/dk_math/INDEX.md` を確認し、`body_not_perfect_pow` と `padicValNat_general_upper_bound` が現在も 🚧 扱いであることを再確認。
   - `DkMath/FLT/Basic.lean` を確認し、一般指数の直接 Zsigmondy ルートは未接続で、現状は `n = 3` 分岐が本線であることを確認。
   - `lake build DkMath.NumberTheory.ZsigmondyCyclotomic DkMath.NumberTheory.GcdNext DkMath.NumberTheory.UniqueFactorizationGN` を実行し、mainline 関連モジュールのビルド成功を確認。
   - `git status --short --branch` を確認し、調査開始時点の作業ブランチが `dev/flt-abc-260324-v0` であり、`Beam構造と因数分解.md` は未追跡ファイルであることを確認。
3. 結論: 現在の mainline は「primitive prime の存在」「primitive 性」「差冪の GN 因数分解」「valuation の GN 帰着」まで揃っている。したがって最初の実装対象は、研究補題を閉じることではなく、これらを `primitive -> GN / Beam` という名前付き API に束ねる薄い中間層を追加することが最適。
4. 失敗事例:
   - なし（調査・棚卸しフェーズ）。
5. 備考:
   - `GcdNextResearch.lean` の `sorry` は研究隔離された 2 件に集中しており、mainline の薄い API 整備とは切り離して進められる。
   - `Beam構造と因数分解.md` 自体が現時点で未追跡なので、今回の履歴もまずは作業記録として同系統 docs に追加する。
6. 次の課題:
   - `DkMath/NumberTheory/PrimitiveBeam.lean` を新設し、まず divisibility レベルの `no sorry` API を成立させる。
   - 研究補題 (`body_not_perfect_pow`, `padicValNat_general_upper_bound`) は第 2 段階で新 API を利用する側へ整理する。

### 日時: 2026/03/24 21:05 JST: 実装計画確定（PrimitiveBeam 中間層を先行導入）

1. 目的: 現行ワークスペースの依存関係と未完箇所を踏まえて、`Beam構造と因数分解.md` を実装タスク列へ落とし込む。
2. 内容:
   - Phase A: `DkMath/NumberTheory/PrimitiveBeam.lean` を新設する。
     - import は `DkMath.NumberTheory.ZsigmondyCyclotomic` を主とし、`GcdNext.lean` への逆依存は作らない。
     - ここで固定する候補 API:
       - `PrimitivePrimeFactorOfDiffPow`
       - `exists_primitive_prime_factor_as_prop`
       - `primitive_prime_not_dvd_boundary`
       - `primitive_prime_dvd_GN`
       - `primitive_prime_dvd_GN_body`
       - `primitive_prime_in_beam_for_body_one`
     - この段階の完成条件は「primitive prime が boundary ではなく GN/Beam を割る」を `no sorry` で呼べることに置く。
   - Phase B: `DkMath/NumberTheory/PrimitiveBeamExamples.lean` を追加する。
     - `GN 5 1 1 = 31`
     - `GN 5 2 1 = 121`
     - `11 ∣ GN 5 2 1` かつ `¬ 11 ∣ 2`
     - 非約数次数の非整数 Beam 観測は theorem 化せず comment/example に留める。
   - Phase C: `DkMath/NumberTheory/GcdNextResearch.lean` へ新 API を接続する。
     - `body_not_perfect_pow` の前半で、既存の生補題列を直接並べる代わりに `primitive_prime_dvd_GN` を使う形へ整理する。
     - `padicValNat_general_upper_bound` 自体は現状スタブなので、まず statement と使用箇所の依存整理を優先する。
   - Phase D: `DkMath/FLT/Basic.lean` 側の一般指数ルートを整理する。
     - 直ちに一般 prime `d` の最終証明完成を狙わず、`PrimitiveBeam` API を使う接続点・コメント・将来 TODO を明示化する。
     - 現状の mainline 本線は `n = 3` なので、これを壊さずに一般指数ルートを「研究入口」として差し込む。
   - Phase E: ABC 側は初手では theorem 化しない。
     - `ABC/PrimitiveBeamBridge.lean` 新設は保留。
     - まず NumberTheory 側で primitive -> Beam API を安定化し、その後 comment / bridge へ展開する。
3. 結論: 実装の最短路は `PrimitiveBeam` を「Zsigmondy の成果物を Beam/GN の名前で再公開する中間 API 層」として先に立てること。研究課題そのものに直接突っ込むより、mainline で再利用可能な境界を先に作る方が現在のワークスペース構造に合う。
4. 失敗事例:
   - 会話ログ雛形どおりに `PrimitiveBeam.lean` から `GcdNext.lean` を import する案は、依存方向の観点では採らない方がよいと判断した。
5. 備考:
   - 既存 `ZsigmondyCyclotomic.lean` が `DkMath.NumberTheory.GcdNext` namespace で実装されているため、新ファイルでは namespace と import を意識的に分離する必要がある。
   - `UniqueFactorizationGN.lean` は wrapper 命名と valuation 比較 API を先行実装した前例として参照価値が高い。
6. 次の課題:
   - Phase A の最小実装として、まず `PrimitivePrimeFactorOfDiffPow` と `primitive_prime_dvd_GN` までを作る。
   - 続いて `PrimitiveBeamExamples.lean` を置き、整数 Beam に primitive prime が立つ具体例を固定する。

### 日時: 2026/03/24 21:31 JST: Phase A/B 実装（`PrimitiveBeam` 本体と具体例を追加）

1. 目的: 事前計画どおり、研究層へ踏み込む前に `primitive -> GN / Beam` の薄い mainline API と小例を固定する。
2. 内容:
   - 新規ファイル `DkMath/NumberTheory/PrimitiveBeam.lean` を追加。
   - namespace は `DkMath.NumberTheory.PrimitiveBeam` を採用しつつ、既存上流 API は `DkMath.NumberTheory.GcdNext` から再利用。
   - 実装した定義・補題:
     - `PrimitivePrimeFactorOfDiffPow`
     - `exists_primitive_prime_factor_as_prop`
     - `primitive_prime_not_dvd_boundary`
     - `primitive_prime_dvd_GN`
     - `primitive_prime_padic_eq_GN`
     - `primitive_prime_dvd_GN_body`
     - `primitive_prime_in_beam_for_body_one`
   - 証明方針はすべて既存定理の薄い再編成に限定。
     - existence / primitive 化:
       `exists_primitive_prime_factor_basic`,
       `prime_exp_not_dvd_diff_imp_primitive`
     - Beam への移送:
       `pow_sub_pow_factor_cosmic_N`
     - valuation 帰着:
       `padicValNat_factorization`
   - 新規ファイル `DkMath/NumberTheory/PrimitiveBeamExamples.lean` を追加。
   - 具体例として以下を固定。
     - `GN 5 1 1 = 31`
     - `GN 5 2 1 = 121`
     - `11 ∣ GN 5 2 1`
     - `¬ 11 ∣ 2`
   - `native_decide` は linter warning を出すため採用せず、例は `decide` で通す形へ調整。
   - `lake build DkMath.NumberTheory.PrimitiveBeam DkMath.NumberTheory.PrimitiveBeamExamples` を実行し、ビルド成功を確認。
3. 結論: `Beam構造と因数分解.md` で要求されていた最初の核
   「primitive prime は boundary ではなく GN / Beam 側へ移る」
   を mainline API として `no sorry` で固定できた。特に `primitive_prime_dvd_GN` と
   `primitive_prime_padic_eq_GN` が、今後 `GcdNextResearch` / `FLT.Basic` へ接続する入口になる。
4. 失敗事例:
   - 初版では `a^1 - b^1` から `a - b` への型簡約を `simpa` なしで通そうとして失敗。
   - `Nat.Prime.dvd_of_dvd_mul_left` を想定していたが、現行環境では未提供だったため
     `Nat.Prime.dvd_mul` の分岐で処理する形に修正。
   - 例ファイルで `native_decide` を使うと style warning が出たため `decide` に差し替えた。
5. 備考:
   - 今回は intentionally 研究補題
     `body_not_perfect_pow` / `padicValNat_general_upper_bound`
     にはまだ手を入れていない。
   - 先に thin wrapper を立てたことで、研究層の `sorry` へ依存せずに
     primitive → Beam の意味づけを mainline で共有できる状態になった。
6. 次の課題:
   - `GcdNextResearch.lean` の `body_not_perfect_pow` 前半を、新 API
     `primitive_prime_dvd_GN` / `primitive_prime_padic_eq_GN`
     へ差し替える。
   - `FLT.Basic.lean` では一般指数ルートの comment / TODO / statement を、
     新 API を前提に整理する。

### 日時: 2026/03/24 23:23 JST: `GcdNextResearch` 前半を `PrimitiveBeam` API へ差し替え、`FLT.Basic` の一般指数 TODO を整理

1. 目的: Phase A/B で追加した `PrimitiveBeam` を、研究層と FLT 応用層の接続点に反映する。
2. 内容:
   - `DkMath/NumberTheory/GcdNextResearch.lean` に `import DkMath.NumberTheory.PrimitiveBeam` を追加。
   - `body_not_perfect_pow` 前半の raw Zsigmondy 展開を削減し、以下へ差し替えた。
     - `PrimitiveBeam.exists_primitive_prime_factor_as_prop`
     - `PrimitiveBeam.primitive_prime_not_dvd_boundary`
     - `PrimitiveBeam.primitive_prime_dvd_GN`
     - `PrimitiveBeam.primitive_prime_padic_eq_GN`
   - これにより、従来この定理の前半にあった
     - `q ∣ a^d - b^d` の整数/自然数キャスト往復
     - `q ∣ x * Sd` から `q ∣ Sd` を抜く手作業
     を削除し、primitive -> GN / Beam への移送を wrapper 経由で表現する形へ整理した。
   - `body_not_perfect_pow` の層Bコメントも、新方針に合わせて更新。
     - まず primitive prime を proposition API で取る
     - `primitive_prime_dvd_GN` で GN 側へ送る
     - `primitive_prime_padic_eq_GN` で valuation も GN 側へ送る
   - `DkMath/FLT/Basic.lean` の一般指数ルートコメントを更新。
     - raw Zsigmondy 展開を書くのではなく、`PrimitiveBeam` -> `GcdNextResearch.body_not_perfect_pow` の橋へ寄せる方針を明記。
     - `n > 3` 分岐の TODO も、`PrimitiveBeam` API 名を明示した 3 段構成へ更新。
   - `lake build DkMath.NumberTheory.GcdNextResearch DkMath.FLT.Basic` を実行し、対象モジュールのビルド成功を確認。
3. 結論: `PrimitiveBeam` は standalone 追加に留まらず、`GcdNextResearch` と `FLT.Basic` の間で「一般指数ルートの入口 API」として機能し始めた。研究層の `sorry` 自体は残るが、primitive prime の取り回しは今後 wrapper ベースで統一できる。
4. 失敗事例:
   - 初回で `GcdNextResearch.lean` 側に `open DkMath.CosmicFormulaBinom` がなく、`GN` が unqualified で解決できなかった。
   - `open DkMath.CosmicFormulaBinom` を追加して解消。
5. 備考:
   - `GcdNextResearch.lean` と `FLT.Basic.lean` は引き続き `sorry` を含むが、今回の差分はそれらを増やしていない。
   - 今回のビルドでは `GcdNextResearch.lean` / `FLT.Basic.lean` 由来の既存 `sorry` warning は継続して出る。
6. 次の課題:
   - `body_not_perfect_pow` の `hpadic_bound` を、`PrimitiveBeam` から渡した GN 側 valuation 文脈で埋める。
   - 一般指数 `n > 3` の FLT ルートを、`body_not_perfect_pow` あるいは同等の provider へ明示的に委譲する。
