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
