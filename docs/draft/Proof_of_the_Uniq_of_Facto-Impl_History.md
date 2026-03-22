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
