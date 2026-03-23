# Proof of the Uniqueness of Factorization - Implements History

cid: 69becbd2-3f3c-83ab-97af-666a8f8f4fb3

## 記録内容テンプレート（例）

### 日時: 2026/03/22 21:14 JST: タイトル

1. 目的:

2. 内容
   - (内容/説明)

3. 結論:
4. 失敗事例:
5. 備考:
6. 次の課題:

## 実装履歴

### 日時: 2026/03/22 21:14 JST: ワークスペース事前調査（既存補題の所在確認・利用可能定理の棚卸し）

1. 目的: 「自然数の因数分解の一意性証明」の実装計画を立てる前に、既存補題と再利用可能定理を特定する。
2. 内容:
   - `DkMath/Basic/Nat.lean` を調査し、以下を候補補題として確認。
     - `mem_support_factorization_iff`
     - `disjoint_support_of_coprime`
     - `support_mul_coprime`
     - `rad_mul_coprime`
   - `DkMath/CFBRC/Basic.lean` / `DkMath/CFBRC/Bridge.lean` を調査し、差分式から core / GN への除法移送補題を確認。
   - `DkMath/NumberTheory/Gcd/GN.lean` を調査し、`GN` と gcd / 付値連携補題の所在を確認。
   - 既存実装で使用実績のある Mathlib API を抽出。
     - `Nat.factorization_mul`
     - `Nat.mem_primeFactors`
     - `Nat.Prime.dvd_mul`
     - `Nat.dvd_gcd`, `Nat.gcd_dvd_left`, `Nat.gcd_dvd_right`
     - `Nat.exists_prime_and_dvd`
     - `Nat.coprime_iff_gcd_eq_one`
   - 計画書として `docs/draft/Proof_of_the_Uniq_of_Factorization-impl-1of2.md` に「## 16. Lean 実装計画（事前調査）」を追記。
3. 結論: 一意性証明は `Nat.factorization` の support ベースで実装可能であり、差分（`GN`）側補題を補強線として接続する方針が妥当。
4. 失敗事例:
   - なし（探索・整理フェーズのみ）。
5. 備考:
   - 今回は事前調査のみで、Lean コードの追加実装は未着手。
6. 次の課題:
   - 新規ファイル（候補: `DkMath/NumberTheory/UniqueFactorizationGN.lean`）を作成し、
     `factorization` の pointwise 等価を主軸に補題を段階実装する。

### 日時: 2026/03/22 21:31 JST: プロトタイプ実装（Mathlib 依存）として一意性骨格補題を追加

1. 目的: 「まずはプロトタイプを固める」方針に従い、Mathlib API を活用して自然数の因数分解一意性の中核補題を実装する。
2. 内容:
   - 新規ファイル `DkMath/NumberTheory/UniqueFactorizationGN.lean` を作成。
   - 実装した補題・定理:
     - `prime_mem_support_iff_dvd`
     - `support_eq_of_primewise_dvd_iff`
     - `factorization_eq_of_prime_pow_dvd_iff`
     - `unique_factorization_nat_via_prime_powers`
   - 中核依存として Mathlib の `Nat.Prime.pow_dvd_iff_le_factorization` を利用し、
     prime-power 除法同値から `factorization` の一致を導出する構造を確立。
   - `lake build DkMath.NumberTheory.UniqueFactorizationGN` でビルド成功を確認。
3. 結論: プロトタイプ段階として、因数分解一意性証明の Lean 骨格を稼働状態で確保できた。
4. 失敗事例:
   - 初回でファイル先頭コメントを C 形式 `/* ... */` で書いたため Lean parser エラー。
   - `/- ... -/` に修正して解消。
5. 備考:
   - 現時点は意図的に Mathlib 依存を許容し、証明構造を先に固定した。
6. 次の課題:
   - 追加定理を wrapper/bridge 層へ寄せ、将来の `DkMathlib` 独立化に向けて依存境界を明確化する。

### 日時: 2026/03/22 21:54 JST: `GN` 側「層所属一意性」補題を `UniqueFactorizationGN` へ接続

1. 目的: `GN` 側の層分離（boundary layer と kernel layer の非競合）を、プロトタイプ一意性モジュールへ直接接続する。
2. 内容:
   - `DkMath/NumberTheory/UniqueFactorizationGN.lean` に以下を追加。
     - `prime_dvd_left_not_dvd_GN_of_coprime_of_not_dvd_exp`
     - `prime_dvd_right_not_dvd_GN_swap_of_coprime_of_not_dvd_exp`
   - 既存 API `DkMath.NumberTheory.Gcd.gcd_gap_GN_dvd_exp_int` を再利用し、
     `z := x + u, y := u`（対称版は swap）で接続。
   - `lake build DkMath.NumberTheory.UniqueFactorizationGN` の成功を確認。
3. 結論: 因数分解一意性プロトタイプに、`GN` 側の層所属一意性（非例外素数の混線防止）を組み込めた。
4. 失敗事例:
   - 初版で `Nat.pos_of_dvd_of_pos` の使い方を誤りビルド失敗。
   - 正値前提（`0 < x` / `0 < u`）を明示し、証明を修正して解消。
5. 備考:
   - この段階は Mathlib 依存を許容し、証明パターンを先に安定化している。
6. 次の課題:
   - `GN d x u` と `GN d u x` の対称橋を明示 wrapper 化し、boundary side API へ統合する。

### 日時: 2026/03/22 22:05 JST: 残課題を「prime vs prime-power」と「次段ターゲット」に明文化

1. 目的: 現在達成済みの範囲（`k=1` 層分離）と未達範囲（prime-power 完全分離）を混同しないよう、計画書上で境界を明確化する。
2. 内容:
   - `docs/draft/Proof_of_the_Uniq_of_Factorization-impl-1of2.md` に以下を追記。
     - `16.8 まだ残っていること（明示）`
     - `16.9 次に狙うべき順序`
   - 特に以下を明示。
     - 現段階は `prime divisibility` の非競合であり、`prime-power` 完全分離ではない。
     - 次段は valuation 補題、二層圧縮 wrapper、例外素数（`q ∣ d`）の別レイヤ化。
3. 結論: 実装進捗の意味づけと次手が整理され、以後の補題拡張の優先順位が明確になった。
4. 失敗事例:
   - なし（設計・文書化フェーズ）。
5. 備考:
   - 数式表現は今後の Lean 命名候補（`boundaryLeft/right`, `kernel`）に対応しやすい形へ寄せた。
6. 次の課題:
   - `q ∤ d` 下の `v_q` ベース補題を最初の prime-power 接続点として実装する。

### 日時: 2026/03/22 22:10 JST: `q ∤ d` 下の `v_q` ベース補題を実装（prime-power 接続点）

1. 目的: `k=1` 層分離から prime-power 議論へ進む最初の接続として、`v_q(gcd(...))=0` 型補題を Lean 実装する。
2. 内容:
   - `DkMath/NumberTheory/UniqueFactorizationGN.lean` に以下を追加。
     - `prime_not_dvd_gcd_left_GN_of_coprime_of_not_dvd_exp`
     - `padicValNat_gcd_left_GN_eq_zero_of_coprime_of_not_dvd_exp`
     - `padicValNat_gcd_right_GN_swap_eq_zero_of_coprime_of_not_dvd_exp`
     - `not_primePow_dvd_gcd_left_GN_of_coprime_of_not_dvd_exp`
   - 既存の `prime_dvd_left_not_dvd_GN_of_coprime_of_not_dvd_exp` を再利用し、
     `¬ q ∣ gcd(...)` と `padicValNat.eq_zero_of_not_dvd` を接続。
   - `lake build DkMath.NumberTheory.UniqueFactorizationGN` 成功を確認。
3. 結論: `q ∤ d` の非例外素数に対して、`gcd` レベルで `v_q=0` を得る橋が実装でき、prime-power 側への遷移点が成立した。
4. 失敗事例:
   - `dvd_pow_self` の引数型（`k ≠ 0`）を `0 < k` のまま渡して失敗。
   - `Nat.pos_iff_ne_zero.mp hk` を介して解消。
5. 備考:
   - 右境界本体（`GN d x u`）と左境界対称（`GN d u x`）を分けて実装している。
6. 次の課題:
   - `boundaryLeft/right/kernel` naming の wrapper を導入し、対称版 API を統一する。

### 日時: 2026/03/22 22:58 JST: product レベル valuation と `boundary/kernel` wrapper を追加

1. 目的: `v_q(gcd(...))=0` から次段へ進めるため、`x*GN` / `x*u*GN` の valuation 加法形を実装し、圧縮 API を整備する。
2. 内容:
   - `DkMath/NumberTheory/UniqueFactorizationGN.lean` に wrapper 定義を追加。
     - `boundaryRight`, `boundaryLeft`, `kernelRight`, `kernelLeft`, `boundaryProd`
   - product valuation 補題を追加。
     - `padicValNat_mul_boundaryRight_kernelRight_eq_add`
     - `padicValNat_mul_boundaryProd_kernelRight_eq_add`
   - wrapper 入口の層分離補題を追加。
     - `prime_dvd_boundaryRight_not_dvd_kernelRight_of_coprime_of_not_dvd_exp`
     - `prime_dvd_boundaryLeft_not_dvd_kernelLeft_of_coprime_of_not_dvd_exp`
   - `lake build DkMath.NumberTheory.UniqueFactorizationGN` 成功を確認。
3. 結論: gcd レベルの分離結果を product valuation へ持ち上げる足場ができ、二層圧縮 API の入口が稼働状態になった。
4. 失敗事例:
   - 初版で wrapper 定義の未使用引数 warning と長行 warning が発生。
   - 引数名の調整とコメント改行で解消。
5. 備考:
   - `padicValNat.mul` の適用には `x ≠ 0`, `u ≠ 0`, `GN ≠ 0` を明示供給している。
6. 次の課題:
   - `boundaryProd` 側（`A := xu`）での `q^k` レベル API（`p^k ∣ A ↔ ...`）へ接続する。

### 日時: 2026/03/22 23:09 JST: `boundaryProd` の prime-power 読み出し補題を追加し、`kernelRight` 比較 wrapper を整備

1. 目的: `A := xu` 側の `q^k` API を具体化し、`boundaryProd` と `kernelRight` の比較入口を強化する。
2. 内容:
   - `DkMath/NumberTheory/UniqueFactorizationGN.lean` に以下を追加。
     - `primePow_dvd_boundaryProd_iff_exists_split`
     - `padicValNat_mul_boundaryProd_kernelRight_eq_add_wrapper`
   - 前者で `q^k ∣ boundaryProd x u` の分割表示
     `∃ i+j=k, q^i∣x, q^j∣u` を実装。
   - 後者で wrapper 形
     `v_q(boundaryProd * kernelRight) = v_q(boundaryProd) + v_q(kernelRight)`
     を明示。
   - `lake build DkMath.NumberTheory.UniqueFactorizationGN` 成功を確認。
3. 結論: `boundaryProd` 側の prime-power 読み出しが API 化され、一意性モジュールへの接続準備が一段進んだ。
4. 失敗事例:
   - なし（初回ビルドで本質エラーは発生せず）。
5. 備考:
   - valuation 加法自体は一般公式（`padicValNat.mul`）だが、GN 分解の寄与は
     boundary/kernel の構造化と non-overlap 条件の API 化にある、と整理した。
6. 次の課題:
   - `q^k ∣ boundaryProd` と `q^k ∣ kernelRight` の比較を、
     support 重なり制御（非例外素数）として補題化する。

### 日時: 2026/03/22 23:36 JST: `boundaryProd` の prime-power 判定に不等式 wrapper を追加

1. 目的: 存在分割 API（`∃ i+j=k`）に加えて、比較定理へ直接つなぎやすい `k ≤ ...` 形式を明示する。
2. 内容:
   - `DkMath/NumberTheory/UniqueFactorizationGN.lean` に以下を追加。
     - `padicValNat_boundaryProd_eq_add`
     - `primePow_dvd_boundaryProd_iff_le_padicVal_sum`
   - `boundaryProd = x*u` を介して
     `q^k ∣ boundaryProd x u ↔ k ≤ padicValNat q x + padicValNat q u`
     を実装。
   - `lake build DkMath.NumberTheory.UniqueFactorizationGN` 成功を確認。
3. 結論: `boundaryProd` の prime-power API が
   「存在分割版」と「不等式版」の二窓構成になり、factorization/suppport 比較へ接続しやすくなった。
4. 失敗事例:
   - 初版で `k ≤ padicValNat q (x*u)` 目標への書き換えが届かず失敗。
   - `hmul : padicValNat q (x*u) = ...` を明示して解消。
5. 備考:
   - valuation 加法の核は一般公式（`padicValNat.mul`）で、GN 側の寄与は
     wrapper 命名と比較導線の整備にある。
6. 次の課題:
   - `boundaryProd` と `kernelRight` の prime-power 非重複を
     `q ∤ d` 層で補題化する。

### 日時: 2026/03/23 00:04 JST: `boundaryProd` と `kernelRight` の prime-power 非重複を実装（`q ∤ d` 層）

1. 目的: `A := boundaryProd x u` と `B := kernelRight d x u` の比較で、
   `q^k` レベルの非重複を `q ∤ d` 層として明示 API 化する。
2. 内容:
   - `DkMath/NumberTheory/UniqueFactorizationGN.lean` に以下を追加。
     - `prime_dvd_right_not_dvd_GN_of_coprime`
     - `primePow_dvd_boundaryProd_not_dvd_kernelRight_of_coprime_of_not_dvd_exp`
     - `primePow_dvd_boundaryProd_not_primePow_dvd_kernelRight_of_coprime_of_not_dvd_exp`
   - 証明戦略:
     - `q^k ∣ boundaryProd`（`k>0`）から `q ∣ x*u` を得る。
     - `q ∣ x` 分岐は既存 `q ∤ d` 非競合補題へ接続。
     - `q ∣ u` 分岐は新規補題
       `q ∣ u → ¬ q ∣ GN d x u`（`Nat.Coprime x u` 下）で処理。
   - `lake build DkMath.NumberTheory.UniqueFactorizationGN` 成功を確認。
3. 結論: `boundaryProd` 側に現れた非例外素数の prime-power は
   `kernelRight` 側へ持ち越されない、という比較 API の最初の完成版が入った。
4. 失敗事例:
   - なし（追加補題は初回方針でビルド通過）。
5. 備考:
   - `q ∣ u` 分岐は `q ∤ d` を使わず成立し、`q ∣ x` 分岐で `q ∤ d` が本質的に効く。
6. 次の課題:
   - `boundaryProd` と `kernelRight` の非重複を
     `v_q` / support 比較 API（`k ≤ ...` 形）へ統合する。

### 日時: 2026/03/23 00:47 JST: 非重複を `v_q` / support 比較 API（`k ≤ ...` 形）へ統合

1. 目的: `boundaryProd` vs `kernelRight` の prime-power 非重複を、
   そのまま比較定理で使える `valuation` / `support` API に持ち上げる。
2. 内容:
   - `DkMath/NumberTheory/UniqueFactorizationGN.lean` に以下を追加。
     - `padicValNat_kernelRight_eq_zero_of_pos_le_padicVal_boundaryProd_of_coprime_of_not_dvd_exp`
     - `not_le_padicValNat_kernelRight_of_pos_le_padicVal_boundaryProd_of_coprime_of_not_dvd_exp`
     - `support_boundaryProd_disjoint_kernelRight_of_coprime_of_not_dvd_exp`
   - `k ≤ v_q(boundaryProd)`（`k>0`）から `q^k ∣ boundaryProd` を復元し、
     既存の prime-power 非重複補題へ接続して
     `v_q(kernelRight)=0` / `¬ k ≤ v_q(kernelRight)` を導出。
   - support 版では
     `q ∈ support(boundaryProd) -> q ∣ boundaryProd`
     と `q ∤ kernelRight` を組み合わせて
     `q ∉ support(kernelRight)` を証明。
   - `lake build DkMath.NumberTheory.UniqueFactorizationGN` 成功を確認。
3. 結論: 非重複の主張が
   `dvd` 形式から `k ≤ ...` valuation 形式・support 形式へ統合され、
   一意性モジュール側の比較 API と直接接続できる状態になった。
4. 失敗事例:
   - `¬ k ≤ 0` の証明で `Nat.not_succ_le_zero` を誤適用して型不一致。
   - `Nat.not_le_of_gt hk` に置換して解消。
5. 備考:
   - support 版は `kernelRight ≠ 0` を要するため、`2 ≤ d` と `x,u>0` を前提にしている。
6. 次の課題:
   - 例外素数（`q ∣ d`）レイヤを分離した比較 API を追加し、
     最終の factorization 比較定理へ接続する。

### 日時: 2026/03/23 01:01 JST: 例外素数レイヤ分離 API を追加し、最終 factorization 比較定理へ接続

1. 目的: 例外素数（`q ∣ d`）を非例外素数（`q ∤ d`）から分離管理した比較 API を導入し、
   最終の factorization 比較定理へ直接接続する。
2. 内容:
   - `DkMath/NumberTheory/UniqueFactorizationGN.lean` に以下を追加。
     - `PrimePowComparisonExceptionalLayer`
     - `PrimePowComparisonNonExceptionalLayer`
     - `factorization_eq_of_prime_pow_dvd_iff_split_layers`
     - `unique_factorization_nat_via_split_prime_layers`
   - 接続方式:
     - prime `q` ごとに `by_cases (q ∣ d)` で層分岐。
     - 例外層は `hExc`、非例外層は `hNonExc` を適用。
     - 既存の `factorization_eq_of_prime_pow_dvd_iff` /
       `unique_factorization_nat_via_prime_powers` へ橋渡し。
   - `lake build DkMath.NumberTheory.UniqueFactorizationGN` 成功を確認。
3. 結論: 例外素数を分離した比較 API が成立し、
   2 層仮定から `factorization` 一致・自然数一致へ到達できる導線が完成した。
4. 失敗事例:
   - 初版で `Nat.factorization_injective` を使ったが、当該定数が環境に存在せず失敗。
   - `unique_factorization_nat_via_prime_powers` を直接適用する構成に変更して解消。
5. 備考:
   - 本追加は「層分離 API」の骨格であり、各層仮定の供給（特に例外層）は次段で具体化する。
6. 次の課題:
   - 例外層 `hExc` を `boundaryProd/kernelRight` の具体的補題群で供給し、
     実データに対する end-to-end 比較定理を実装する。

### 日時: 2026/03/23 01:19 JST: `hExc` を `boundaryProd/kernelRight` 補題群で供給し、end-to-end 比較定理を実装

1. 目的: 抽象引数だった `hExc` を `boundaryProd/kernelRight` の具体補題群から構成し、
   実データ比較を最終定理 `m = n` まで接続する。
2. 内容:
   - `DkMath/NumberTheory/UniqueFactorizationGN.lean` を拡張。
   - 例外層の具体補題を追加:
     - `prime_dvd_boundaryRight_dvd_kernelRight_of_dvd_exp`
     - `prime_dvd_boundaryProd_dvd_kernelRight_of_dvd_exp_of_not_dvd_boundaryLeft`
   - 層供給 API を追加:
     - `exceptionalLayer_of_boundaryProd_kernelRight`
     - `nonExceptionalLayer_of_boundaryProd_kernelRight`
   - end-to-end 比較定理を追加:
     - `unique_factorization_nat_via_boundaryProd_kernelRight_split_layers_e2e`
     - `boundaryProd/kernelRight` 由来の層別比較仮定を束ねて
       `unique_factorization_nat_via_split_prime_layers` へ接続し、`m = n` を導出。
   - `lake build DkMath.NumberTheory.UniqueFactorizationGN` 成功を確認。
3. 結論: 例外層 `hExc` の供給経路が具体化され、層別 API から
   end-to-end 比較定理まで一気通しで到達できる実装になった。
4. 失敗事例:
   - なし（今回の追加では本質エラーなし）。
5. 備考:
   - 例外層の right-boundary -> kernel 接続に `DkMath.FLT.Core` の
     `GN_zmod_eq_head_of_dvd` を再利用した。
6. 次の課題:
   - 例外層比較仮定 `hExcBK` / 非例外層比較仮定 `hNonExcBK` を、
     さらに自動供給できる具体補題セットへ縮約する。

### 日時: 2026/03/23 01:30 JST: `hExcBK/hNonExcBK` を valuation 等式から自動供給する縮約版を実装

1. 目的: `hExcBK` / `hNonExcBK`（prime-power 同値仮定）を直接要求せず、
   具体的な valuation 等式補題から自動構成できる形へ縮約する。
2. 内容:
   - `DkMath/NumberTheory/UniqueFactorizationGN.lean` に以下を追加。
     - `exceptionalBK_of_padicValNat_eq_boundaryProd_kernelRight`
     - `nonExceptionalBK_of_padicValNat_eq_boundaryProd_kernelRight`
     - `exceptionalLayer_of_boundaryProd_kernelRight_autoBK`
     - `nonExceptionalLayer_of_boundaryProd_kernelRight_autoBK`
     - `unique_factorization_nat_via_boundaryProd_kernelRight_split_layers_e2e_autoBK`
   - 要点:
     - `hd2`, `x>0`, `u>0` から `boundaryProd ≠ 0`, `kernelRight ≠ 0` を確保。
     - `padicValNat_dvd_iff_le` を使って
       valuation 等式 `v_q(boundaryProd)=v_q(kernelRight)` から
       `q^k` 除法同値を生成。
     - 生成した同値を既存の `exceptionalLayer/nonExceptionalLayer` へ注入し、
       end-to-end 比較定理へ接続。
   - `lake build DkMath.NumberTheory.UniqueFactorizationGN` 成功を確認。
3. 結論: `hExcBK/hNonExcBK` は直接仮定から外れ、
   層別 valuation 等式で代替できる縮約 API になった。
4. 失敗事例:
   - 初版で `boundaryProd`/`kernelRight` の定義展開差により rewrite が失敗。
   - `hval : padicValNat q (x*u) = padicValNat q (GN d x u)` を明示して解消。
5. 備考:
   - 縮約後も比較対象は `boundaryProd` vs `kernelRight` のまま維持している。
6. 次の課題:
   - valuation 等式仮定（`hExcVal` / `hNonExcVal`）自体を
     さらに自動供給する具体補題連鎖を整備する。

### 日時: 2026/03/23 09:42 JST: `hExcBK/hNonExcBK` を `<=` / 0 化ベースでも自動供給できるよう拡張

1. 目的: `hExcBK` / `hNonExcBK` を valuation 等式だけでなく、
   より弱い具体仮定（例外層は両向き `<=`、非例外層は両側 0 化）からも自動構成できるようにする。
2. 内容:
   - `DkMath/NumberTheory/UniqueFactorizationGN.lean` に以下を追加。
     - `exceptionalBK_fwd_of_padicValNat_le_boundaryProd_kernelRight`
     - `exceptionalBK_rev_of_padicValNat_le_kernelRight_boundaryProd`
     - `exceptionalBK_of_padicValNat_le_le_boundaryProd_kernelRight`
     - `nonExceptionalBK_of_padicValNat_eq_zero_boundaryProd_kernelRight`
     - `exceptionalLayer_of_boundaryProd_kernelRight_autoBK_le`
     - `nonExceptionalLayer_of_boundaryProd_kernelRight_autoBK_zero`
     - `unique_factorization_nat_via_boundaryProd_kernelRight_split_layers_e2e_autoBK_le_zero`
   - 例外層は `v_q(boundaryProd) <= v_q(kernelRight)` と逆向き不等式を束ねて
     `q^k` 比較同値を生成。
   - 非例外層は `v_q(boundaryProd)=0 ∧ v_q(kernelRight)=0` から
     `q^k` 比較同値を生成。
   - `lake build DkMath.NumberTheory.UniqueFactorizationGN` 成功を確認。
3. 結論: `hExcBK/hNonExcBK` の供給窓が
   「valuation 等式版」に加えて「`<=` / 0 化版」でも成立し、
   実データ側の前提に合わせた接続がしやすくなった。
4. 失敗事例:
   - `nonExceptionalBK_of_padicValNat_eq_zero_boundaryProd_kernelRight` で、
     `simp` が `boundaryProd/kernelRight` の展開形と補題形を合わせ切れず未解決ゴールが発生。
   - `rw [hBz, hKz]` に切り替え、定義展開依存を除いて解消。
5. 備考:
   - 比較対象は引き続き `boundaryProd` vs `kernelRight` を維持し、
     層 API と end-to-end 定理の形は変えていない。
6. 次の課題:
   - `hExcLe` / `hExcLeRev` / `hNonExcZero` 自体を、
     `GN` 側の具体 valuation 補題から自動供給する連鎖を整備する。

### 日時: 2026/03/23 09:54 JST: `hExcLe/hExcLeRev/hNonExcZero` を GN concrete chain で自動導出

1. 目的: `hExcLe` / `hExcLeRev` / `hNonExcZero` を直接仮定せず、
   `GN` 側の具体 valuation/prime-divisibility 補題から自動生成できる導線を実装する。
2. 内容:
   - `DkMath/NumberTheory/UniqueFactorizationGN.lean` に以下を追加。
     - `exceptionalLe_of_padicValNat_eq_boundaryProd_kernelRight`
     - `exceptionalLeRev_of_padicValNat_eq_boundaryProd_kernelRight`
     - `nonExceptionalNotDvd_boundaryProd_of_not_dvd_boundarySides`
     - `nonExceptionalZero_of_not_dvd_boundaryProd_and_kernelRight`
     - `unique_factorization_nat_via_boundaryProd_kernelRight_split_layers_e2e_autoGNVal`
   - 導出設計:
     - 例外層は `hExcVal`（valuation 等式）から
       `hExcLe` / `hExcLeRev` を機械的に導出。
     - 非例外層は `boundaryProd` / `kernelRight` の具体 `¬dvd` 情報から
       `hNonExcZero` を導出。
     - 最後に `autoBK_le_zero` 系の end-to-end へ接続して `m = n` を返す。
   - `lake build DkMath.NumberTheory.UniqueFactorizationGN` 成功を確認。
3. 結論: `hExcLe/hExcLeRev/hNonExcZero` の手作業組み立てが不要になり、
   concrete な GN 側補題をそのまま流し込める接続 API が成立した。
4. 失敗事例:
   - なし（初回追加でビルド通過）。
5. 備考:
   - `hNonExcZero` の導出は理論上一般には強い仮定を要するため、
     非例外層では concrete `¬dvd` 補題を入力として受ける構成を採用。
6. 次の課題:
   - 非例外層の `kernelRight` 側 `¬dvd`（または 0 化）を
     より弱い仮定から供給する GN 補題連鎖を拡張する。

### 日時: 2026/03/23 10:16 JST: 非例外層 `kernelRight` 側 `¬dvd`/0化を弱化仮定から供給する chain を追加

1. 目的: 非例外層で `kernelRight` 側 `¬dvd` を直接仮定する形を弱め、
   valuation 比較と境界側情報から自動導出できる補題連鎖へ拡張する。
2. 内容:
   - `DkMath/NumberTheory/UniqueFactorizationGN.lean` に以下を追加。
     - `nonExceptionalNotDvd_kernelRight_of_padicValNat_le_boundaryProd_and_not_dvd_boundaryProd`
     - `nonExceptionalZero_of_padicValNat_le_boundaryProd_and_not_dvd_boundaryProd`
     - `nonExceptionalZero_of_padicValNat_le_boundaryProd_and_not_dvd_boundarySides`
     - `unique_factorization_nat_via_boundaryProd_kernelRight_split_layers_e2e_autoGNVal_weakKernel`
     - `unique_factorization_nat_via_boundaryProd_kernelRight_e2e_autoGNVal_weakKernel_boundarySides`
   - 設計要点:
     - `v_q(kernelRight) ≤ v_q(boundaryProd)` と `¬ q ∣ boundaryProd` から
       `v_q(kernelRight)=0`（したがって `¬ q ∣ kernelRight`）を導出。
     - `boundaryRight/Left` 側 `¬dvd` から `¬ q ∣ boundaryProd` を構成し、
       上記 chain へ接続。
     - end-to-end では、従来必要だった `hNonExcNotDvdKernelRight` を
       より弱い入力へ置き換えた wrapper を追加。
   - `lake build DkMath.NumberTheory.UniqueFactorizationGN` 成功を確認。
3. 結論: 非例外層 `kernelRight` 側の供給条件が弱化され、
   concrete 仮定からの自動導出経路が一段進んだ。
4. 失敗事例:
   - 初版で `simp [hBz]` が `padicValNat.eq_zero_iff` を過展開し型不一致。
   - `calc` で不等式を段階接続し、`Nat.le_zero.mp` で 0 化して解消。
5. 備考:
   - 新規 `boundarySides` wrapper 名は linter 長行制約を満たすよう短縮している。
6. 次の課題:
   - `hNonExcLeRev` 自体を、GN 側のさらに具体的な prime-power 非重複補題から
     自動供給する chain を整備する。

### 日時: 2026/03/23 13:11 JST: `hNonExcLeRev` を prime-power chain から自動供給する導線を追加

1. 目的: `hNonExcLeRev` を直接仮定せず、
   非例外層の concrete prime-power 連鎖から自動生成する chain を整備する。
2. 内容:
   - `DkMath/NumberTheory/UniqueFactorizationGN.lean` に以下を追加。
     - `nonExceptionalLeRev_of_primePow_kernelRight_to_boundaryProd`
     - `unique_factorization_nat_via_boundaryProd_kernelRight_e2e_autoGNVal_powChain_boundarySides`
   - 導出設計:
     - 入力は
       `q^k ∣ kernelRight -> q^k ∣ boundaryProd`（`q` prime, `q ∤ d`, `k>0`）。
     - `k := v_q(kernelRight)` を代入し、
       `padicValNat_dvd_iff_le` を使って `hNonExcLeRev` を導出。
     - 導出した `hNonExcLeRev` を既存の
       `...autoGNVal_weakKernel_boundarySides` へ渡して `m = n` を返す。
   - `lake build DkMath.NumberTheory.UniqueFactorizationGN` 成功を確認。
3. 結論: 非例外層は
   prime-power chain から valuation 比較へ落とす自動供給ルートを獲得した。
4. 失敗事例:
   - なし（初回実装でビルド通過）。
5. 備考:
   - 本段階は「chain の接続整備」であり、
     `hNonExcPowRev` 自体の具体供給補題は次段で詰める。
6. 次の課題:
   - `hNonExcPowRev`（kernel→boundary の prime-power 連鎖）を
     GN 側既存補題から生成する具体 wrapper を実装する。

### 日時: 2026/03/23 13:24 JST: `hNonExcPowRev` を GN 既存比較補題から供給する wrapper を追加

1. 目的: `hNonExcPowRev`（kernel→boundary の prime-power 連鎖）を
   直接仮定せず、GN 側既存補題から自動生成できるようにする。
2. 内容:
   - `DkMath/NumberTheory/UniqueFactorizationGN.lean` に以下を追加。
     - `nonExceptionalPowRev_of_nonExceptionalBK`
     - `nonExceptionalPowRev_of_padicValNat_eq_boundaryProd_kernelRight`
     - `unique_factorization_nat_via_boundaryProd_kernelRight_e2e_autoGNVal_powChain_from_nonExcVal`
   - 接続方式:
     - `hNonExcBK`（`boundaryProd ↔ kernelRight`）から `.2` 方向を取り出し
       `hNonExcPowRev` を構成。
     - `hNonExcVal` が与えられる場合は
       `nonExceptionalBK_of_padicValNat_eq_boundaryProd_kernelRight` で `hNonExcBK` 化して同様に抽出。
     - 抽出した `hNonExcPowRev` を既存の
       `...powChain_boundarySides` へ渡して `m = n` を導出。
   - `lake build DkMath.NumberTheory.UniqueFactorizationGN` 成功を確認。
3. 結論: `hNonExcPowRev` の concrete 供給経路ができ、
   非例外層 chain の入力前提がさらに整理された。
4. 失敗事例:
   - なし（初回追加でビルド通過）。
5. 備考:
   - 新規 end-to-end 名は linter 長行制約を満たすため短縮している。
6. 次の課題:
   - `hNonExcNotDvdRight/Left` 側も GN 既存補題から自動供給する
     boundary-side wrapper を強化する。

### 日時: 2026/03/23 17:38 JST: `hNonExcNotDvdRight/Left` の boundary-side 自動供給 wrapper を強化

1. 目的: `hNonExcNotDvdRight/Left` を直接仮定せず、
   GN 側既存補題から自動供給する chain を整備する。
2. 内容:
   - `DkMath/NumberTheory/UniqueFactorizationGN.lean` に以下を追加。
     - `nonExceptionalNotDvd_boundaryProd_of_nonExceptionalBK_of_coprime_of_not_dvd_exp`
     - `nonExceptionalNotDvd_boundarySides_of_not_dvd_boundaryProd`
     - `nonExceptionalNotDvd_boundarySides_of_nonExceptionalBK_of_coprime_of_not_dvd_exp`
     - `nonExceptionalNotDvd_boundarySides_from_nonExcVal`
     - `unique_factorization_nat_via_boundaryProd_kernelRight_e2e_autoGNVal_nonExcVal_boundarySides`
   - 導出方式:
     - `hNonExcBK` から `q ∣ boundaryProd -> q ∣ kernelRight` を得る。
     - GN 側非重複補題
       `primePow_dvd_boundaryProd_not_dvd_kernelRight_of_coprime_of_not_dvd_exp`
       （`k=1`）で `q ∣ kernelRight` と矛盾させ、`¬ q ∣ boundaryProd` を導出。
     - `¬ q ∣ boundaryProd` から `boundaryRight/Left` 側 `¬dvd` を抽出。
     - `hNonExcVal` 入力版は `hNonExcBK` 化して同 chain に接続。
   - `lake build DkMath.NumberTheory.UniqueFactorizationGN` 成功を確認。
3. 結論: `hNonExcNotDvdRight/Left` を手入力せず、
   GN 側比較補題から boundary-side 前提を供給できるようになった。
4. 失敗事例:
   - 初版で補題を前方配置し、後段定理への前方参照で解決不能となった。
   - 補題群を `primePow_dvd_boundaryProd_not_dvd_kernelRight...` 後へ再配置して解消。
5. 備考:
   - linter の長行警告回避のため、2 つの新規定理名を短縮した。
6. 次の課題:
   - `hNonExcNotDvdBoundaryProd` 側の供給も同様に、
     `hNonExcVal` / `hNonExcBK` から直接使える入力形へ整理する。

### 日時: 2026/03/23 17:46 JST: `hNonExcNotDvdBoundaryProd` の direct 供給 API を追加

1. 目的: `hNonExcNotDvdBoundaryProd` 側も
   `hNonExcVal` / `hNonExcBK` から直接使える入力形へ整理する。
2. 内容:
   - `DkMath/NumberTheory/UniqueFactorizationGN.lean` に以下を追加。
     - `nonExceptionalNotDvd_boundaryProd_from_nonExcBK`
     - `nonExceptionalNotDvd_boundaryProd_from_nonExcVal`
     - `unique_factorization_nat_via_boundaryProd_kernelRight_e2e_autoGNVal_nonExcBK_boundaryProd`
     - `unique_factorization_nat_via_boundaryProd_kernelRight_e2e_autoGNVal_nonExcVal_boundaryProd`
   - 整理方針:
     - `from_nonExcBK` は既存の長名補題を短名で包み、
       `hNonExcNotDvdBoundaryProd` 供給点を固定。
     - `from_nonExcVal` は
       `nonExceptionalBK_of_padicValNat_eq_boundaryProd_kernelRight` を介して
       `hNonExcBK` 化し、同じ供給点へ接続。
     - e2e wrapper では `hNonExcLeRev` と `hNonExcNotDvdBoundaryProd` を
       内部生成して `...split_layers_e2e_autoGNVal_weakKernel` に接続。
   - `lake build DkMath.NumberTheory.UniqueFactorizationGN` 成功を確認。
3. 結論: 非例外層 `boundaryProd` 側非除法は、
   `hNonExcVal` / `hNonExcBK` から直接投入できる API に整理できた。
4. 失敗事例:
   - なし（初回実装でビルド通過）。
5. 備考:
   - 既存の boundary-side 自動供給 wrapper と併用可能で、
     呼び出し側は `boundaryProd` 入口か `boundarySides` 入口を選べる。
6. 次の課題:
   - 例外層/非例外層の入口（`boundaryProd` / `boundarySides`）を
     最終 e2e API で統一する facade を検討する。

### 日時: 2026/03/23 17:58 JST: `boundaryProd / boundarySides` の統一 facade を追加

1. 目的: 例外層/非例外層の最終 e2e で、非例外層境界入口
   （`boundaryProd` / `boundarySides`）を単一 API で受けられるようにする。
2. 内容:
   - `DkMath/NumberTheory/UniqueFactorizationGN.lean` に以下を追加。
     - `NonExceptionalBoundaryEntrance`
     - `nonExceptionalNotDvd_boundaryProd_of_boundaryEntrance`
     - `unique_factorization_nat_via_boundaryProd_kernelRight_e2e_autoGNVal_weakKernel_boundaryFacade`
     - `unique_factorization_nat_via_boundaryProd_kernelRight_e2e_autoGNVal_nonExcVal_boundaryFacade`
     - `unique_factorization_nat_via_boundaryProd_kernelRight_e2e_autoGNVal_nonExcBK_boundaryFacade`
   - 設計:
     - facade は `boundaryProd` 直入力か `boundarySides` 入力を `Or` で保持。
     - `...of_boundaryEntrance` で `hNonExcNotDvdBoundaryProd` へ正規化。
     - 最終 e2e はこの正規化結果に集約し、`nonExcVal` / `nonExcBK` は
       `hNonExcLeRev` 供給だけを担う。
   - `lake build DkMath.NumberTheory.UniqueFactorizationGN` 成功を確認。
3. 結論: 非例外層境界の入口形を統一でき、
   最終 e2e で呼び出し側の分岐を減らせる状態になった。
4. 失敗事例:
   - 追加直後に長行警告（100 文字超過）2 件。
   - `exact` 行を改行して解消。
5. 備考:
   - 既存の `...boundaryProd` / `...boundarySides` wrapper は互換維持のため残置。
6. 次の課題:
   - facade 入口を基準に、旧 wrapper 群の段階的整理（thin wrapper 化）を検討する。

### 日時: 2026/03/23 18:05 JST: facade 基準で旧 wrapper 群の thin 化（段階 1）を実施

1. 目的: facade 入口を基準に、既存 wrapper を互換維持しつつ薄い委譲層へ寄せる。
2. 内容:
   - `DkMath/NumberTheory/UniqueFactorizationGN.lean` に以下を追加。
     - `nonExceptionalBoundaryEntrance_of_not_dvd_boundaryProd`
     - `nonExceptionalBoundaryEntrance_of_not_dvd_boundarySides`
   - 既存 wrapper の実装本体を facade 委譲へ置換。
     - `nonExceptionalNotDvd_boundarySides_of_nonExceptionalBK_of_coprime_of_not_dvd_exp`
     - `nonExceptionalNotDvd_boundarySides_from_nonExcVal`
     - `unique_factorization_nat_via_boundaryProd_kernelRight_e2e_autoGNVal_nonExcVal_boundarySides`
     - `unique_factorization_nat_via_boundaryProd_kernelRight_e2e_autoGNVal_nonExcBK_boundaryProd`
     - `unique_factorization_nat_via_boundaryProd_kernelRight_e2e_autoGNVal_nonExcVal_boundaryProd`
   - 置換方針:
     - 入口の形（`boundaryProd` / `boundarySides`）は constructor で facade 化。
     - 本体証明は `...boundaryFacade` 系へ委譲し、重複ロジックを削減。
   - `lake build DkMath.NumberTheory.UniqueFactorizationGN` 成功を確認。
3. 結論: 旧 wrapper 群は公開シグネチャを保ったまま、
   facade 入口中心の thin wrapper へ段階的に移行できた。
4. 失敗事例:
   - なし（初回置換でビルド通過）。
5. 備考:
   - 依存順を崩さないため、`weakKernel_boundarySides` 本体の facade 直接委譲は
     次段で再配置と合わせて検討する。
6. 次の課題:
   - `weakKernel_boundarySides` / `powChain_boundarySides` 側も
     facade 中心実装へ揃える再配置方針を詰める。

### 日時: 2026/03/23 18:25 JST: `boundarySides` 系を facade 中心実装へ再配置

1. 目的: `weakKernel_boundarySides` / `powChain_boundarySides` 側も
   facade 中心実装へ揃え、旧入口を薄い互換層にする。
2. 内容:
   - `DkMath/NumberTheory/UniqueFactorizationGN.lean` に共通コアを追加。
     - `unique_factorization_nat_e2e_autoGNVal_weakKernel_boundaryFacade_core`
   - 既存定理の本体を再配置・委譲化。
     - `..._weakKernel_boundarySides`
       - `nonExceptionalBoundaryEntrance_of_not_dvd_boundarySides` で facade 化し、
         共通コアへ委譲。
     - `..._weakKernel_boundaryFacade`
       - 共通コアへの薄い委譲に統一。
     - `..._powChain_boundarySides`
       - `hNonExcLeRev` 生成後に `boundarySides` を facade 化し、
         共通コアへ委譲。
   - `lake build DkMath.NumberTheory.UniqueFactorizationGN` 成功を確認。
3. 結論: `boundarySides` 入口も facade 中心の実装一本化に揃い、
   旧 wrapper は thin 層として整理が進んだ。
4. 失敗事例:
   - 追加直後に長行警告（定理名・参照名）4 件。
   - コア定理名を短縮し、呼び出し側参照も更新して解消。
5. 備考:
   - 公開シグネチャは維持しているため、呼び出し側互換性はそのまま。
6. 次の課題:
   - facade 経由が既定であることを明示するため、
     旧 wrapper の docstring に「compat/thin」ラベルを付けるか検討する。

### 日時: 2026/03/23 18:54 JST: 現在地をドキュメントで整理（完了域/未完域/次段）

1. 目的: 本来ゴール「素因数分解一意性の無限量化証明」に対する進捗を、
   実装・未実装の境界が明確な形で整理する。
2. 内容:
   - `Proof_of_the_Uniq_of_Factorization-impl-1of2.md` に
     「16.29 現在地の整理（完全自動 e2e に対する進捗）」を追加。
   - 整理観点を 3 つに分離。
     - 完了済み（理論コア・2層橋・facade 統一）
     - 未完（`hExcM/hExcK`・`hNonExcM/hNonExcK` の自動供給閉路）
     - 次段の実装順（段 A/B/C）
3. 結論: 「核証明は完了、残りは入力供給層の閉じ込み」という位置づけを
   文書上で固定できた。
4. 失敗事例:
   - なし（文書整理のみ）。
5. 備考:
   - 実装コードの変更は無し。ドキュメント整理のみ。
6. 次の課題:
   - 段 A として、例外層 `hExcM/hExcK` の concrete 自動供給 wrapper 設計を開始する。

### 日時: 2026/03/23 19:04 JST: 段 A（例外層 `hExcM/hExcK` concrete 自動供給）を実装

1. 目的: 例外層入力 `hExcM/hExcK` を手入力前提から外し、
   `GN` 側で与える valuation 等式（`hExcMVal/hExcKVal`）から自動供給できる形にする。
2. 内容:
   - `DkMath/NumberTheory/UniqueFactorizationGN.lean` に以下を追加。
     - `exceptionalPowComparison_of_padicValNat_eq`
       - `q ∣ d` 上の `v_q(a)=v_q(b)` から
         `q^k ∣ a ↔ q^k ∣ b` を与える汎用補題。
     - `exceptionalM_of_padicValNat_eq_m_boundaryProd`
       - `hExcMVal` から `hExcM` を生成。
     - `exceptionalK_of_padicValNat_eq_n_kernelRight`
       - `hExcKVal` から `hExcK` を生成。
     - `unique_factorization_nat_e2e_autoGNVal_nonExcVal_boundaryFacade_autoExcMK`
     - `unique_factorization_nat_e2e_autoGNVal_nonExcBK_boundaryFacade_autoExcMK`
       - 上記 2 本は `hExcM/hExcK` を内部生成して既存 facade e2e に委譲。
   - 併せて `unnecessarySimpa` 警告 1 件を `simp` へ置換して解消。
   - `lake build DkMath.NumberTheory.UniqueFactorizationGN` 成功を確認。
3. 結論: 段 A は実装段階へ進み、例外層 `hExcM/hExcK` の concrete 自動供給導線を確立できた。
4. 失敗事例:
   - 追加直後、linter の `unnecessarySimpa` 警告 1 件。
   - `simpa` を `simp` に置換して解消。
5. 備考:
   - 新 e2e は既存 facade API を再利用する薄い上位入口として設計。
   - 既存呼び出し互換性は維持。
6. 次の課題:
   - 段 B として、非例外層 `hNonExcM/hNonExcK` 側も
     concrete valuation 入力から自動供給する wrapper を実装する。

### 日時: 2026/03/23 19:23 JST: 段 B（非例外層 `hNonExcM/hNonExcK` concrete 自動供給）を実装

1. 目的: 非例外層入力 `hNonExcM/hNonExcK` を手入力前提から外し、
   `hNonExcMVal/hNonExcKVal`（valuation 等式）から自動供給できる形にする。
2. 内容:
   - `DkMath/NumberTheory/UniqueFactorizationGN.lean` に以下を追加。
     - `nonExceptionalPowComparison_of_padicValNat_eq`
       - `q ∤ d` 上の `v_q(a)=v_q(b)` から
         `q^k ∣ a ↔ q^k ∣ b` を与える汎用補題。
     - `nonExceptionalM_of_padicValNat_eq_m_boundaryProd`
       - `hNonExcMVal` から `hNonExcM` を生成。
     - `nonExceptionalK_of_padicValNat_eq_n_kernelRight`
       - `hNonExcKVal` から `hNonExcK` を生成。
     - `unique_factorization_nat_e2e_autoGNVal_nonExcVal_boundaryFacade_autoExcNonExcMK`
     - `unique_factorization_nat_e2e_autoGNVal_nonExcBK_boundaryFacade_autoExcNonExcMK`
       - 上記 2 本は段 A の `autoExcMK` wrapper に委譲しつつ、
         `hNonExcM/hNonExcK` を内部生成して接続。
   - `lake build DkMath.NumberTheory.UniqueFactorizationGN` 成功を確認。
3. 結論: 段 B で、非例外層 `m/n` 側比較入力の concrete 自動供給導線を確立できた。
4. 失敗事例:
   - なし（初回実装でビルド通過）。
5. 備考:
   - A/B を積んだことで、`m/n` 側比較入力の手動供給は
     例外層・非例外層ともに不要化した（valuation 入力で代替可能）。
6. 次の課題:
   - 段 C として、A/B を束ねた最終 facade 入口の一本化を進める。

### 日時: 2026/03/23 22:36 JST: 段 C（A/B を束ねた最終 facade 入口）を実装

1. 目的: 段 A/B の分岐（`hNonExcVal` 系 / `hNonExcBK` 系）を
   最終 e2e 入口で一本化し、呼び出し側の入口選択を facade 化する。
2. 内容:
   - `DkMath/NumberTheory/UniqueFactorizationGN.lean` に以下を追加。
     - `NonExceptionalBridgeEntrance`
       - 非例外層 bridge 入力を
         `hNonExcVal` or `hNonExcBK` の 2 形から統一する facade 型。
     - `nonExceptionalBridgeEntrance_of_nonExcVal`
     - `nonExceptionalBridgeEntrance_of_nonExcBK`
       - 上記 facade 型への constructor。
     - `unique_factorization_nat_e2e_autoGNVal_nonExcFacade_boundaryFacade_autoExcNonExcMK`
       - 段 A/B の concrete valuation 入力を保持したまま、
         `hNonExcBridge` の分岐を内部で処理して
         段 B の 2 wrapper へ委譲する最終単一入口。
   - `lake build DkMath.NumberTheory.UniqueFactorizationGN` 成功を確認。
3. 結論: 段 C により、最終 API で
   非例外層 bridge 入力（`Val`/`BK`）と boundary 入力の両方が facade 化され、
   A/B を束ねた単一 e2e 入口が成立した。
4. 失敗事例:
   - なし（初回実装でビルド通過）。
5. 備考:
   - 既存段 A/B 入口は互換保持のため残し、新入口は上位 facade として追加。
6. 次の課題:
   - 旧 wrapper 群を段階的に thin 化し、
     新 `...nonExcFacade_boundaryFacade...` を中心に呼び出し面を整理する。

### 日時: 2026/03/24 00:56 JST: 旧 wrapper 群の thin 化（第1段）を実施

1. 目的: 旧 wrapper 群を段階的に thin 化し、
   新 `...nonExcFacade_boundaryFacade...` を中心に呼び出し面を整理する。
2. 内容:
   - `DkMath/NumberTheory/UniqueFactorizationGN.lean` に中間統一入口を追加。
     - `unique_factorization_nat_via_boundaryProd_kernelRight_e2e_autoGNVal_nonExcFacade_boundaryFacade`
       - `hNonExcBridge : NonExceptionalBridgeEntrance` を受け、
         `nonExcVal`/`nonExcBK` 分岐を内部処理。
   - 既存 wrapper 3 本を thin 化（本体を上記統一入口へ委譲）。
     - `unique_factorization_nat_via_boundaryProd_kernelRight_e2e_autoGNVal_nonExcVal_boundarySides`
     - `unique_factorization_nat_via_boundaryProd_kernelRight_e2e_autoGNVal_nonExcBK_boundaryProd`
     - `unique_factorization_nat_via_boundaryProd_kernelRight_e2e_autoGNVal_nonExcVal_boundaryProd`
   - 置換方針:
     - 各 wrapper 内で `hNonExcBoundary` は従来どおり生成。
     - `hNonExcVal` または `hNonExcBK` から
       `hNonExcBridge` を構築し、統一入口へ接続。
   - `lake build DkMath.NumberTheory.UniqueFactorizationGN` 成功を確認。
3. 結論: 旧 wrapper 群の第1段 thin 化が完了し、
   非例外層 bridge 分岐は `nonExcFacade_boundaryFacade` へ集約できた。
4. 失敗事例:
   - なし（初回置換でビルド通過）。
5. 備考:
   - 公開シグネチャは維持。呼び出し側互換性はそのまま。
6. 次の課題:
   - 残る旧 wrapper についても、同入口への委譲化を順次進める。

### 日時: 2026/03/24 01:09 JST: 旧 wrapper 群の thin 化（第2段）を実施

1. 目的: 残る A/B 系 wrapper も同入口へ委譲し、
   `...nonExcFacade_boundaryFacade...` 中心の呼び出し面へ整理する。
2. 内容:
   - `DkMath/NumberTheory/UniqueFactorizationGN.lean` に
     共通入口 `unique_factorization_nat_e2e_autoGNVal_nonExcFacade_boundaryFacade_autoExcMK`
     を追加。
     - 例外層の `hExcM/hExcK` は valuation から内部生成。
     - 非例外層 bridge は `hNonExcBridge`（Val/BK facade）で受ける。
   - 既存 wrapper 4 本を thin 化（本体を上記共通入口へ委譲）。
     - `...nonExcVal_boundaryFacade_autoExcMK`
     - `...nonExcBK_boundaryFacade_autoExcMK`
     - `...nonExcVal_boundaryFacade_autoExcNonExcMK`
     - `...nonExcBK_boundaryFacade_autoExcNonExcMK`
   - 置換方針:
     - branch-specific 入力（Val/BK）から
       `nonExceptionalBridgeEntrance_of_nonExcVal/BK` で bridge facade を構築。
     - 既存シグネチャを保ったまま、共通入口へ委譲。
   - `lake build DkMath.NumberTheory.UniqueFactorizationGN` 成功を確認。
3. 結論: A/B 系の旧 wrapper まで thin 化が進み、
   非例外層分岐は `NonExceptionalBridgeEntrance` 経由へさらに集約できた。
4. 失敗事例:
   - なし（初回置換でビルド通過）。
5. 備考:
   - 互換維持のため旧公開名は残置。内部のみ委譲化。
6. 次の課題:
   - 互換 wrapper 群への `compat/thin` ラベル付けと、
     最終推奨入口のドキュメント導線を整理する。

### 日時: 2026/03/24 01:18 JST: `compat/thin` ラベル付けと推奨入口導線を整理

1. 目的: 互換 wrapper 群を識別可能にし、
   新規呼び出しが最終推奨入口へ収束する導線を明確化する。
2. 内容:
   - `DkMath/NumberTheory/UniqueFactorizationGN.lean` の docstring を更新。
     - 互換 wrapper 群に ``[compat/thin]`` を付与。
       - 対象例:
         - `...nonExcVal_boundaryFacade`
         - `...nonExcBK_boundaryFacade`
         - `...autoExcMK` / `...autoExcNonExcMK` の branch-specific 版
         - `...nonExcVal_boundarySides`
         - `...nonExcBK_boundaryProd`
         - `...nonExcVal_boundaryProd`
     - 最終入口
       `unique_factorization_nat_e2e_autoGNVal_nonExcFacade_boundaryFacade_autoExcNonExcMK`
       に ``[recommended]`` を付与。
     - 各 `compat/thin` wrapper に「新規コードで使うべき入口」を追記。
   - `Proof_of_the_Uniq_of_Factorization-impl-1of2.md` に
     「16.35 `compat/thin` ラベル付けと最終推奨入口の導線整理」を追加。
   - `lake build DkMath.NumberTheory.UniqueFactorizationGN` 成功を確認。
3. 結論: 互換層と推奨入口の境界が明示され、
   API 遷移方針をコード/文書の両面で固定できた。
4. 失敗事例:
   - なし（初回更新でビルド通過）。
5. 備考:
   - 署名互換性は維持。今回の変更は docstring と導線整理が主。
6. 次の課題:
   - `DkMath/Samples` 側に最終推奨入口を使う最小呼び出し例を追加し、
     実利用導線を確定する。

### 日時: 2026/03/24 01:35 JST: `DkMath/Samples` に最終推奨入口の最小例を追加

1. 目的: 最終推奨入口の実利用導線を `Samples` 側で固定し、
   呼び出し側の参照起点を明確化する。
2. 内容:
   - 新規ファイル追加:
     - `DkMath/Samples/UniqueFactorizationGNFacade.lean`
   - 収録例:
     - `unique_factorization_nat_e2e_autoGNVal_nonExcFacade_boundaryFacade_autoExcNonExcMK`
       の最小呼び出し例（入力受理型）。
     - `hNonExcVal` と `hNonExcNotDvdBoundaryProd` から
       facade 入口（bridge/boundary）を組み立てて同推奨入口へ接続する例。
   - 集約 import 更新:
     - `DkMath/Samples.lean` に
       `import DkMath.Samples.UniqueFactorizationGNFacade` を追加。
   - 検証:
     - `lake build DkMath.Samples.UniqueFactorizationGNFacade` 成功。
     - `lake build DkMath.Samples` 成功。
3. 結論: 最終推奨入口の呼び出し例を `Samples` に定着でき、
   実利用導線を確定した。
4. 失敗事例:
   - なし（初回追加でビルド通過）。
5. 備考:
   - 例は「値固定の具体計算」ではなく、
     API 形状をそのまま写す最小呼び出しテンプレートとして設計。
6. 次の課題:
   - `Samples` から最終推奨入口へ到達する README/目次導線を補足し、
     初見利用者の探索コストを下げる。
