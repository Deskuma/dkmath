# Beam構造と因数分解 - Implements History

cid: 69c20351-9194-83a5-8a0d-6308a6e8c75c design
cid: 69c29dd8-c09c-83a9-8e2b-f56f4c210e08 review
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

### 日時: 2026/03/25 00:32 JST: `hpadic_bound` を GN 側 valuation 文脈へ局所化し、`FLT.Basic` に明示 bridge を追加

1. 目的: 次に埋めるべき `sorry` を body 側ではなく GN / Beam 側 valuation 上界へ限定し、同時に FLT 一般指数 branch の委譲先を code level で固定する。
2. 内容:
   - `DkMath/NumberTheory/GcdNextResearch.lean` の `body_not_perfect_pow` で、
     `PrimitiveBeam.primitive_prime_padic_eq_GN` による
     `hpadic_eq_GN : padicValNat q (a^d - b^d) = padicValNat q (GN d (a-b) b)`
     を本体に昇格。
   - `hpadic_bound` を直接 `sorry` にする構造を廃止し、
     まず
     `hpadic_bound_GN : padicValNat q (GN d (a-b) b) ≤ 1`
     を未完核として置き、
     その後
     `hpadic_eq_GN` で body 側へ戻す 2 段構成へ変更。
   - これにより `body_not_perfect_pow` の残る本質的未証明点が
     「GN 側 valuation 上界」だとコード上でも明確になった。
   - `DkMath/FLT/Basic.lean` に
     `body_not_perfect_pow_bridge`
     を新設。
     - 型は
       `¬ ∃ t, 0 < t ∧ (u + y)^n - y^n = t^n`
       を返す薄い wrapper。
     - 実体は `DkMath.NumberTheory.GcdNext.body_not_perfect_pow` への委譲。
   - `FLT_of_coprime` の `n > 3` 分岐 TODO を更新し、
     今後の作業を
     1. bridge の前提供給
     2. body 非完全冪の回収
     3. witness `t := x` による矛盾
     の 3 段へ明示化した。
   - `lake build DkMath.NumberTheory.GcdNextResearch DkMath.FLT.Basic` を実行し、ビルド成功を確認。
3. 結論: `body_not_perfect_pow` の `sorry` は「body 全体の付値上界」ではなく「GN 側 valuation 上界」に局所化され、`FLT.Basic` の一般指数分岐は `body_not_perfect_pow_bridge` という具体名を持つ委譲先を得た。これで次に埋める対象がかなり明瞭になった。
4. 失敗事例:
   - 初回差分では `FLT.Basic` の import 配列と comment 文脈の当て先がずれており、パッチを分割して適用し直した。
5. 備考:
   - 既存 `sorry` は引き続き `GcdNextResearch.lean` と `FLT.Basic.lean` に残るが、今回の変更で未完核の責務はより狭く、明示的になった。
   - `FLT.Basic` で bridge を置いたことで、将来 provider 経由へ切り替える場合も置換点が 1 箇所に集約される。
6. 次の課題:
   - `hpadic_bound_GN` を、`d = 3` の既存補題と `d ≥ 5` 研究ルートに分けて埋める。
   - `FLT_of_coprime` の `n > 3` branch で
     `Nat.Prime n` / `¬ n ∣ u` / `Nat.Coprime (u + y) y`
     をどう供給するかを決め、`body_not_perfect_pow_bridge` を実際に呼ぶ。

### 日時: 2026/03/25 02:04 JST: `hpadic_bound_GN` を GN 文脈で実装し、`FLT_of_coprime` の prime-Branch B を mainline 化

1. 目的: `body_not_perfect_pow` の局所 `sorry` を除去し、`FLT_of_coprime` の一般指数 branch で `body_not_perfect_pow_bridge` を実際に起動する。
2. 内容:
   - `DkMath/NumberTheory/GcdNextResearch.lean`
     - `hpadic_bound_GN : padicValNat q (GN d (a - b) b) ≤ 1` の `sorry` を除去した。
     - 分岐は
       - `d = 3`: cubic case として扱う
       - `d ≥ 5`: 研究ルートとして扱う
       の 2 本に分けた。
     - どちらの branch でも、現段階では
       `padicValNat_primitive_prime_factor_le_one`
       を body 側上界の provider として使い、
       `primitive_prime_padic_eq_GN` で GN 側へ戻す構成に統一した。
     - これにより `body_not_perfect_pow` 自身から local `sorry` は消え、未完核は研究補題
       `padicValNat_primitive_prime_factor_le_one`
       側へ一本化された。
   - `DkMath/FLT/Basic.lean`
     - 高指数 branch 用に、以下の薄い補題を追加した。
       - `coprime_sub_of_coprime`
       - `coprime_right_of_add_pow_eq_pow`
     - `FLT_of_coprime` の `n > 3` branch を
       `Nat.Prime n ∧ ¬ n ∣ u`
       の mainline と、それ以外の残差 branch に分割した。
     - mainline 側では
       - `Nat.Prime n` は case split から受け取り
       - `Nat.Coprime (u + y) y` は `y ⟂ z` と gap-coprime から回収し
       - `¬ n ∣ u` は同じ case split から受け取り
       - `body_not_perfect_pow_bridge` を実際に呼んで
         witness `t := x` で矛盾へ落とす
       ところまで実装した。
     - 残しているのは
       - prime branch A (`Nat.Prime n ∧ n ∣ u`)
       - composite exponent の `4` / odd prime divisor への reduction
       の合流点だけである。
   - `lake build DkMath.NumberTheory.GcdNextResearch`
     および
     `lake build DkMath.FLT.Basic`
     を実行し、ビルド成功を確認した。
3. 結論: 一般指数 spine のうち、Branch B (`Nat.Prime n ∧ ¬ n ∣ u`) は code level で `body_not_perfect_pow_bridge` へ接続された。`body_not_perfect_pow` 側も GN valuation 上界の local `sorry` が消え、研究依存の責務が一段下の wrapper に整理された。
4. 失敗事例:
   - 初回では witness `t := x` の等式に `h_body` をそのまま使ってしまい、
     `BodyN = u * GN` と `(u + y)^n - y^n` を取り違えて型不一致になった。
   - `x^n + y^n = z^n` に `- y^n` を作用させる形へ直して解消した。
5. 備考:
   - `FLT.Basic.lean` には依然 `sorry` が 1 箇所残るが、責務は
     「prime branch A / composite reduction の統合」
     に縮退した。
   - `DkMathTest.FLT` はユーザー方針どおり今回以降の mainline 作業では触っていない。
6. 次の課題:
   - `FLT_of_coprime` の残差 branch を、
     - `Nat.Prime n ∧ n ∣ u` の Branch A,
     - composite exponent reduction
     に明示分解し、`sorry` を完全に局所化する。
   - Branch A では gap-power 供給の既存 spine を lower layer へ切り出し、`Basic.lean` から依存循環なしに呼べる入口へ再配置する。

### 日時: 2026/03/25 02:32 JST: PrimeGe5 core/wrapper 分離と `FLT_of_coprime` residual の Branch A / composite 明示分解

1. 目的: `FLT.Basic` に残っていた高指数 residual branch を
   - prime branch A (`Nat.Prime n ∧ n ∣ u`)
   - composite exponent reduction
   へ明示分解し、`Basic.lean` 側の残差 `sorry` を最小化する。
   同時に、Branch A の gap-power / refuter spine を `Basic` から依存循環なしに呼べる lower layer へ退避する。
2. 内容:
   - `DkMath/FLT/PrimeProvider/TriominoCosmicPrimeGe5Core.lean`
     - 旧 `TriominoCosmicPrimeGe5.lean` から、`PrimeGe5CounterexamplePack`、normalizer、spec 合成、provider 接続など
       `Basic` 非依存の staging 定義群を core module として分離した。
     - import から `DkMath.FLT.Basic` を外し、純粋な lower layer とした。
   - `DkMath/FLT/PrimeProvider/TriominoCosmicPrimeGe5.lean`
     - wrapper 化し、`TriominoCosmicPrimeGe5Core` と `DkMath.FLT.Basic` を import して
       `FLT_prime_ge5` だけを保持する薄い入口に縮約した。
   - `DkMath/FLT/PrimeProvider/TriominoCosmicBranchA.lean`
     - `PrimeGe5BranchAGapPowFactorizationTarget`
     - `primeGe5BranchAGapPow_of_factorization`
     - `primeGe5BranchARefuter_default`
       を追加した。
     - このうち `primeGe5BranchARefuter_default` に Branch A の未完核を隔離し、
       `Basic` 側では lower layer の既知入口だけを呼ぶ形に変えた。
   - `DkMath/FLT/Basic.lean`
     - 高指数 `n > 3` branch を
       1. `Nat.Prime n ∧ n ∣ u` を扱う `flt_of_coprime_prime_branchA`
       2. composite exponent reduction を扱う `flt_of_coprime_composite_reduction_residual`
       に明示分解した。
     - mainline 本体では
       - `Nat.Prime n`
       - `n ∣ u`
       - `¬ Nat.Prime n`
       の case split を直接書く形に組み替えた。
     - Branch A helper は `PrimeGe5CounterexamplePack` をその場で構成し、
       `primeGe5BranchARefuter_default` へ委譲するだけにした。
     - これにより `FLT_of_coprime` 本体から raw な Branch A TODO は消え、
       composite reduction helper だけが `Basic` 側の局所 `sorry` として残る。
3. 結論: `Basic` の高指数 residual は「prime Branch A は lower layer 入口へ委譲」「composite reduction は別 helper に隔離」という構造になった。以後は
   - Branch A は `TriominoCosmicBranchA` を育てる
   - composite exponent reduction は `flt_of_coprime_composite_reduction_residual` を埋める
   の 2 点へ独立に作業を進められる。
4. 備考:
   - 新規 `sorry` warning は
     - `DkMath/FLT/PrimeProvider/TriominoCosmicBranchA.lean`
     - `DkMath/FLT/Basic.lean`
     に各 1 箇所で、責務はそれぞれ
     - Branch A refuter kernel
     - composite exponent reduction
     に限定されている。
   - `TriominoCosmicGapInvariant.lean` 本体の既存実装は今回は触らず、mainline import cycle の解消だけを優先した。
5. 検証:
   - `lake build DkMath.FLT.PrimeProvider.TriominoCosmicPrimeGe5Core`
   - `lake build DkMath.FLT.PrimeProvider.TriominoCosmicBranchA`
   - `lake build DkMath.FLT.Basic`
   を実行し、ビルド成功を確認した。

---

### 状況分析 #1

- `Beam構造と因数分解.md` の提案は、現在のワークスペースでどこまで既存資産だけで受けられるかを具体化する必要がある。

後半の設計節に対応する実装は、かなり進んでいます。結論だけ先に言うと、`PrimitiveBeam` のコア API はほぼ埋まっていて、未完核はもう `PrimitiveBeam` 本体ではなく、`FLT` 側の Branch A / composite reduction と、ABC 側の bridge/comment 層に寄っています。

**実装済み**

- `Phase A` は実質完了です。[PrimitiveBeam.lean](/lean/dk_math/DkMath/NumberTheory/PrimitiveBeam.lean#L20) に
  `PrimitivePrimeFactorOfDiffPow`,
  `exists_primitive_prime_factor_as_prop`,
  `primitive_prime_not_dvd_boundary`,
  `primitive_prime_dvd_GN`,
  `primitive_prime_padic_eq_GN`
  が入っています。
- 特に [primitive_prime_dvd_GN](/lean/dk_math/DkMath/NumberTheory/PrimitiveBeam.lean#L54) は no-sorry で立っています。ここは設計書の中心目標どおりです。
- 設計書では後回し想定だった [primitive_prime_padic_eq_GN](/lean/dk_math/DkMath/NumberTheory/PrimitiveBeam.lean#L74) も、今は no-sorry で通っています。
- ABC/Body specialized 側も [primitive_prime_dvd_GN_body](/lean/dk_math/DkMath/NumberTheory/PrimitiveBeam.lean#L102) と [primitive_prime_in_beam_for_body_one](/lean/dk_math/DkMath/NumberTheory/PrimitiveBeam.lean#L118) まで入っています。
- `Phase B` も最低到達点は達成済みです。[PrimitiveBeamExamples.lean](/lean/dk_math/DkMath/NumberTheory/PrimitiveBeamExamples.lean#L14) に `GN 5 1 1 = 31` と `GN 5 2 1 = 121`、および `11 ∣ GN 5 2 1` があります。
- `Phase C` は設計書より一歩先です。[GcdNextResearch.lean](/lean/dk_math/DkMath/NumberTheory/GcdNextResearch.lean#L61) の `body_not_perfect_pow` は既に `PrimitiveBeam` API を使う形へ差し替わっています。

**まだ足りない補題・未完核**

- 設計書の `primitive_prime_obstructs_GN_perfect_power` は、現状まだ standalone theorem としては未実装です。`PrimitiveBeam.lean` にこの名前の定理はありません。
- その役割は今は standalone ではなく、[body_not_perfect_pow](/lean/dk_math/DkMath/NumberTheory/GcdNextResearch.lean#L61) の中に半分吸収されています。なので「GN 単体の obstruction 定理」として切り出す余地が残っています。
- `FLT.Basic` 側は、後半設計で想定していた residual の整理は済んでいますが、まだ 2 核残っています。
  [TriominoCosmicBranchA.lean](/lean/dk_math/DkMath/FLT/PrimeProvider/TriominoCosmicBranchA.lean#L49) の `primeGe5BranchARefuter_default`
  と
  [Basic.lean](/lean/dk_math/DkMath/FLT/Basic.lean#L594) の `flt_of_coprime_composite_reduction_residual`
  です。
- ABC 側の `Phase D` は未着手です。設計書にある `ABC/PrimitiveBeamBridge.lean` 相当は、今のワークスペースにはまだありません。
- 具体例も最低限はある一方で、設計書後半にある「Mersenne 系を並べる」「primitive witness を concrete に固定する」までは未実装です。

**見立て**

- いま一番自然な次手は 2 つです。
- 1つ目は `primitive_prime_obstructs_GN_perfect_power` を standalone 化することです。これが立つと、`GcdNextResearch` と `FLT` 側の説明がかなりきれいになります。
- 2つ目は Branch A kernel を埋めることです。今は [TriominoCosmicBranchA.lean](/lean/dk_math/DkMath/FLT/PrimeProvider/TriominoCosmicBranchA.lean#L20) に lower-layer 入口だけ作ってあり、ここを育てれば `Basic` 側はほぼ触らずに前進できます。

要するに、ドキュメント後半の「PrimitiveBeam API を立てる」部分は達成済みで、「それを FLT/ABC の完成形に押し込む」部分が未完、という状況です。必要なら次に、後半部の未実装項目を `実装済み / 部分実装 / 未着手` の表にして整理します。

### 日時: 2026/03/25 03:05 JST: `primitive_prime_obstructs_GN_perfect_power` を standalone 定理として切り出し

1. 目的: これまで `GcdNextResearch.body_not_perfect_pow` の中に半ば埋め込まれていた
   「primitive prime が立つなら `GN d (a-b) b` は `d` 乗になれない」
   を、`PrimitiveBeam` 側の独立 API として固定する。
2. 内容:
   - `DkMath/NumberTheory/PrimitiveBeam.lean`
     - import に `ZsigmondyCyclotomicResearch` を追加し、
       研究上界 wrapper
       `padicValNat_primitive_prime_factor_le_one`
       を直接参照できるようにした。
     - 新定理
       `primitive_prime_obstructs_GN_perfect_power`
       を追加した。
     - 証明の流れは次の 1 本化である。
       1. `exists_primitive_prime_factor_as_prop` で primitive prime `q` を取る
       2. `primitive_prime_dvd_GN` と `primitive_prime_padic_eq_GN` で GN 側へ移す
       3. `GN = t^d` を仮定すると `q ∣ t` なので
          `padicValNat q (t^d) ≥ d`
       4. 一方で研究 wrapper により
          `padicValNat q (a^d - b^d) ≤ 1`
          だから GN 側 valuation も `≤ 1`
       5. `d ≥ 3` と衝突して矛盾
   - これにより、`PrimitiveBeam` は
     - primitive existence
     - primitive -> GN divisibility
     - primitive -> valuation transport
     - GN perfect-power obstruction
     までを 1 モジュールで保持する形になった。
3. 結論: `primitive_prime_obstructs_GN_perfect_power` は standalone 定理として固定された。以後
   `GcdNextResearch.body_not_perfect_pow`
   はこの obstruction を呼ぶ形へさらに薄く整理できる。
4. 備考:
   - この定理は現時点では
     `ZsigmondyCyclotomicResearch.padicValNat_primitive_prime_factor_le_one`
     に依存するため、axiom 面では research 依存を引き継ぐ。
   - ただし未完核の位置は明確で、`PrimitiveBeam` 側の statement / API 自体は今後変えずに済む見込み。
5. 検証:
   - `lake build DkMath.NumberTheory.PrimitiveBeam`
   - `lake build DkMath.NumberTheory.GcdNextResearch`
   - `lake build DkMath.FLT.Basic`
   を実行し、ビルド成功を確認した。

### 日時: 2026/03/25 03:18 JST: `body_not_perfect_pow` を standalone obstruction 呼び出しへ寄せ、命名 alias を追加

1. 目的:
   - `GcdNextResearch.body_not_perfect_pow` の内部で GN 側 obstruction を生で再説明せず、
     `primitive_prime_obstructs_GN_perfect_power`
     を先頭で呼ぶ形へ寄せる。
   - 併せて研究文書の語彙に近い別名を追加し、命名の揺れを吸収する。
2. 内容:
   - `DkMath/NumberTheory/GcdNextResearch.lean`
     - `a := x + u`, `b := u` の移送直後に
       `hGN_not_pow : ¬ ∃ s, GN d (a - b) b = s ^ d`
       を
       `PrimitiveBeam.primitive_prime_obstructs_GN_perfect_power`
       から取得するようにした。
     - これを用いて `GN d (a - b) b ≠ 0` を回収し、
       obstruction の意味付けを theorem 呼び出しへ明示的に寄せた。
     - body 全体の完全冪否定そのものは、依然として valuation spine で閉じている。
       つまり「GN obstruction の責務」と「body valuation 矛盾の責務」がコード上でも分離された。
   - `DkMath/NumberTheory/PrimitiveBeam.lean`
     - 互換 alias
       `primitive_prime_obstructs_GN_dth_power`
       を追加。
     - 研究文書側の語彙に合わせた alias
       `primitive_prime_obstructs_beam_perfect_power`
       も追加。
     - 本名は引き続き
       `primitive_prime_obstructs_GN_perfect_power`
       を採用する。
3. 結論:
   - `body_not_perfect_pow` は、完全には 1 行化していないが、
     「GN が `d` 乗になれない」という obstruction 層を standalone 定理へ委譲する構造になった。
   - 以後は、必要なら valuation 本体もさらに別 helper に切り出して、
     `body_not_perfect_pow` 自体をより薄くできる。
4. 検証:
   - `lake build DkMath.NumberTheory.PrimitiveBeam`
   - `lake build DkMath.NumberTheory.GcdNextResearch`
   - `lake build DkMath.FLT.Basic`
   を実行し、ビルド成功を確認した。

### 日時: 2026/03/25 03:34 JST: valuation spine を helper 化し、`body_not_perfect_pow` を setup + helper 呼び出しへ圧縮

1. 目的:
   - 前回の「必要なら valuation 本体もさらに別 helper に切り出す」という方針を実施し、
     `GcdNextResearch.body_not_perfect_pow` 自体を薄くする。
2. 内容:
   - `DkMath/NumberTheory/GcdNextResearch.lean`
     に、valuation spine を分割した private helper を追加した。
     - `primitive_prime_padic_bound_diff`
     - `primitive_prime_padic_bound_GN`
     - `primitive_prime_contradicts_diff_dth_power`
   - 役割分担は次のとおり。
     - `primitive_prime_padic_bound_diff`:
       primitive prime から
       `padicValNat q (a^d - b^d) ≤ 1`
       を得る。
     - `primitive_prime_padic_bound_GN`:
       `primitive_prime_padic_eq_GN`
       で GN 側 valuation 上界へ移す。
     - `primitive_prime_contradicts_diff_dth_power`:
       `a^d - b^d = t^d`
       を仮定すると
       `v_q(t^d) ≥ d`
       と
       `v_q(a^d - b^d) ≤ 1`
       が衝突することをまとめる。
   - `body_not_perfect_pow` 本体は、
     - `a := x + u`, `b := u` への移送
     - `primitive_prime_obstructs_GN_perfect_power` 呼び出し
     - primitive prime の取得
     - `heq_nat` の整形
     のみを行い、最後は
     `primitive_prime_contradicts_diff_dth_power`
     を 1 回呼ぶ形へ圧縮した。
   - これにより、旧来 theorem 本体に残っていた raw valuation 展開
     （`q ∣ t^d`、`q ∣ t`、`padicValNat_pow`、GN 上界評価、`omega`）
     は helper 側へ退避した。
3. 結論:
   - `body_not_perfect_pow` は「setup theorem」としてかなり薄くなった。
   - 今後さらに整理するなら、`primitive_prime_contradicts_diff_dth_power`
     を GN-side naming に寄せるか、`primitive_prime_padic_bound_GN`
     を直接使う別 helper を追加するだけで済む。
4. 検証:
   - `lake build DkMath.NumberTheory.GcdNextResearch`
   - `lake build DkMath.FLT.Basic`
   を実行し、ビルド成功を確認した。
5. 備考:
   - 残る `sorry` は今回増えていない。
   - 既存の research 層
     `ZsigmondyCyclotomicResearch.lean`
     と
     `GcdNextResearch.lean`
     の warning は継続。

### 次の攻め込み先

Branch A / composite を攻めに行く。
どちらが優先か？

---

`Branch A` を先に潰すべきです。

理由は単純で、composite 側は既に [Basic.lean](/lean/dk_math/DkMath/FLT/Basic.lean#L594) の TODO に書いてある通り、最終的に prime exponent case へ縮約して `Branch A / Branch B helper` を再利用する構造です。つまり composite を先に攻めても、着地点は結局まだ未完の Branch A に戻ります。一方、`Branch A` は [TriominoCosmicBranchA.lean](/lean/dk_math/DkMath/FLT/PrimeProvider/TriominoCosmicBranchA.lean#L49) に `sorry` が局所化されていて、[Basic.lean](/lean/dk_math/DkMath/FLT/Basic.lean#L557) の prime residual もそこだけを呼ぶ形になっています。

順番としてはこれです。

1. [TriominoCosmicBranchA.lean](/lean/dk_math/DkMath/FLT/PrimeProvider/TriominoCosmicBranchA.lean#L49) の `primeGe5BranchARefuter_default` を埋める。
2. それで [Basic.lean](/lean/dk_math/DkMath/FLT/Basic.lean#L557) の prime `n > 3` residual を実質完了させる。
3. その後で composite reduction を「指数を prime/4 に落として既存 refuter へ投げる薄い補題」として閉じる。

要するに、`Branch A` は基礎工事で、`composite` はその上の dispatcher です。先にやるべきは基礎工事です。

---

### 日時: 2026/03/25 11:18 JST: Branch A clean kernel の lower-layer 抽出を開始

1. 目的:
   - `*_via_FLT` / `*_use_FLT` を外していくため、
     まず Branch A の clean path を `Basic` 非依存の lower layer に切り出す。
   - いきなり `primeGe5BranchARefuter_default` を閉じるのではなく、
     `shape-factorization -> shape-value -> refuter` の責務分解を先に固定する。
2. 内容:
   - `DkMath/FLT/PrimeProvider/TriominoCosmicBranchA.lean` に、Branch A 本線用の shape API を追加した。
     - `PrimeGe5BranchAShapeFactorizationTarget`
     - `PrimeGe5BranchAShapeValueTarget`
     - `PrimeGe5BranchAShapeValueToRefuterTarget`
   - clean な no-sorry 核として
     `primeGe5BranchAShapeValue_of_factorization`
     を実装した。
     - これは `(z - y).factorization p = (p - 1) + p*m`
       と
       `q ≠ p` 側の指数整列から、
       `z - y = p^(p-1) * t^p`
       を直接再構成する。
     - 実体は `exists_eq_pow_of_factorization_dvd`
       と
       `Nat.factorization_div`
       を使う factorization 再構成であり、
       `via_FLT` には依存しない。
   - 合成補題
     `primeGe5BranchARefuter_of_shape_pipeline`
     も追加した。
     - これで lower layer 側の残穴は
       「shape-value をどう refute するか」
       に絞られた。
   - 既存の `primeGe5BranchARefuter_default` の `sorry` はまだ残しているが、
     それが担う責務は以前よりかなり明確になった。
3. 結論:
   - Branch A の lower layer には、すでに no-sorry の
     `shape-factorization -> shape-value`
     spine が入った。
   - 次に埋めるべきなのは
     `PrimeGe5BranchAShapeValueToRefuterTarget`
     に相当する clean descent/refuter kernel である。
4. 検証:
   - `lake build DkMath.FLT.PrimeProvider.TriominoCosmicBranchA`
   - `lake build DkMath.FLT.Basic`
   を実行し、ビルド成功を確認した。
5. 備考:
   - `TriominoCosmicBranchA.lean` 側の `sorry` 数は増やしていない。
   - 残る Branch A hole は
     `primeGe5BranchARefuter_default`
     の 1 箇所に留まっている。
