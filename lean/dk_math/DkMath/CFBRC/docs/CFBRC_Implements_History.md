# CFBRC Implements History

## CFBRC: Cosmic Formula Binomial Real Complex

- CFBRC の実装は、数式 $G_d(x,\theta)=(x+i\theta)^d-(i\theta)^d$ の構造解析と数値実験を目的としている。
- 実装は Lean 4 を用いて行われ、基本的な定義と性質を形式化するためのモジュール構成が採用されている。
- 主要なファイル構成は以下の通り:
  - `DkMath.lean`: CFBRC を含む全体のモジュール構成を定義。
  - `CFBRC.lean`: CFBRC の主要な定義と基本的な性質を形式化。
  - `CFBRC/Defs.lean`: CFBRC に関連する基本的な定義を集約。
  - `CFBRC/Basic.lean`: CFBRC の基本的な性質や定理を証明。
- 実装の目的は、数式の代数的構造を明確にし、数値実験の基盤を提供することである。
- 今後の展開として、より高度な性質の証明や数値実験の拡充が予定されている。

## 記録内容テンプレート（例）

### 日時: 2026/03/12 14:42: CFBRC の実装開始。基本的な定義と性質の形式化を行うためのファイル構成を決定

1. 目的: CFBRC の実装履歴の記録と要約
2. 内容:
   - CFBRC の実装の概要と目的
   - 主要なファイル構成とその役割
   - 実装の目的と今後の展開
3. 結論: CFBRC の実装は数式の構造解析と数値実験の基盤を提供するものであり、今後の展開が期待される。
4. 失敗事例: 特に大きな失敗はないが、数値実験の精度向上や複雑な性質の証明にはさらなる工夫が必要である。
5. 備考: 追加の詳細や数値実験の結果は、関連するドキュメントやノートブックに記録されている。
6. 次の課題: より高度な性質の証明や数値実験の拡充を行うこと。

## 実装履歴

※ここに上記テンプレートに沿った実装履歴を記録していく。

### 日時: 2026/03/12 15:03 JST: CFBRC prime core（`cyclotomicPrimeCore`）の Lean 実装と GN 連結定理群を追加

1. 目的: CFBRC の差冪コア `((x+u)^p-u^p)/x` を Lean 側で `DkMath.CFBRC.*` に定義し、既存 `GN` と exact に接続する。
2. 内容:
   - `DkMath.CFBRC.Defs` に `cyclotomicPrimeCore` を新規定義。
   - `DkMath.CFBRC.Basic` に以下の橋渡し定理を実装:
     - `add_pow_eq_mul_cyclotomicPrimeCore_add_gap`
     - `mul_cyclotomicPrimeCore_eq_mul_GN`
     - `cyclotomicPrimeCore_eq_GN_nat`
     - `dvd_cyclotomicPrimeCore_iff_dvd_GN_nat`
     - `prime_dvd_cyclotomicPrimeCore_of_dvd_sub_not_dvd_left`
   - 補助補題として `cyclotomicPrimeCore_succ`, `sub_eq_mul_cyclotomicPrimeCore_nat` を追加。
   - `lake build DkMath.CFBRC.Basic` でビルド成功を確認。
3. 結論: prime case の最小核（CFBRC core -> GN bridge）が `DkMath.CFBRC.*` 配下で稼働し、Nat 上の除法同値と素因子抽出まで接続完了。
4. 失敗事例:
   - 初回実装で Mathlib の import パス差異（`Mathlib.Algebra.BigOperators.Basic/Ring` 不在）により失敗。
   - `CommSemiring` 上の加法消去不足により、比較定理に `IsRightCancelAdd` 制約の明示が必要だった。
5. 備考:
   - 本実装は `GN` 再定義を行わず、`DkMath.CosmicFormulaBinom.cosmic_id_csr'` を基準に接続した。
   - prime 仮定そのもの（`Nat.Prime p`）を使う円分側意味づけ定理は次フェーズ。
6. 次の課題:
   - `Nat.Prime p` を仮定した円分多項式（`Φ_p(T)=∑T^k`）との意味づけ補題を追加する。
   - `DkMath.CFBRC` を入口にした上位 bridge（Zsigmondy / valuation 層）へ接続する。

### 日時: 2026/03/12 15:18 JST: Phase B を実装（prime cyclotomic の shifted homogeneous evaluation 補題）

1. 目的: `Nat.Prime p` 仮定の下で、`cyclotomicPrimeCore` を prime cyclotomic の shifted homogeneous evaluation として明示する。
2. 内容:
   - `DkMath.CFBRC.Basic` に `cyclotomicShiftedHomEval` を追加:
     - `∑_{k=0}^{p-1} coeff(Φ,k) * (x+u)^k * u^(p-1-k)` を定義。
   - `cyclotomicPrimeCore_eq_shiftedHomEval_cyclotomic_of_prime` を追加:
     - `hp : Nat.Prime p` から `Polynomial.cyclotomic_prime` を使い、
       `coeff(Φ_p,k)=1 (k<p)` を導出して core との一致を証明。
   - `lake build DkMath.CFBRC.Basic` でビルド成功を確認。
3. 結論: Phase B 要件
   「`cyclotomicPrimeCore` = prime cyclotomic の shifted homogeneous evaluation」
   を Lean 補題として実装完了。
4. 失敗事例: 大きな失敗なし。既存の Prime 連結 API と競合せずに導入できた。
5. 備考:
   - `cyclotomicShiftedHomEval` は `Polynomial ℤ` を受ける一般形なので、
     今後は prime case 以外の比較補題へも流用可能。
6. 次の課題:
   - `DkMath.CFBRC.*` から Zsigmondy / valuation 層への API 接続を進める。

### 日時: 2026/03/12 15:23 JST: Phase C を実装（Zsigmondy / valuation 層への bridge と再利用 API 露出）

1. 目的: `DkMath.CFBRC.*` から Zsigmondy / valuation 統合層へ依存を追加し、除法同値補題を再利用 API として公開する。
2. 内容:
   - `DkMath.CFBRC.Bridge` を新規追加し、`DkMath.NumberTheory.Gcd.GN` を import。
   - 再利用 API として以下を追加:
     - `prime_dvd_sub_pow_iff_dvd_cyclotomicPrimeCore_nat`
       （`q ∤ x` 下で `q ∣ ((x+u)^p-u^p) ↔ q ∣ cyclotomicPrimeCore`）
     - `padicValNat_sub_pow_eq_padicValNat_cyclotomicPrimeCore_of_not_dvd_boundary`
       （valuation 層の `padicValNat_sub_pow_eq_padicValNat_GN_of_not_dvd_gap` を core 側へ転送）
   - `DkMath.CFBRC` 入口ファイルに `import DkMath.CFBRC.Bridge` を追加。
   - `lake build DkMath.CFBRC.Bridge` と `lake build DkMath.CFBRC` でビルド成功を確認。
3. 結論: CFBRC core から Zsigmondy / valuation 層への接続が実装され、除法同値・付値同値を CFBRC API として直接再利用できる状態になった。
4. 失敗事例: 大きな失敗なし。既存 `Gcd.GN` API を薄い wrapper で安全に接続できた。
5. 備考:
   - 本フェーズは「橋渡し層の追加」に徹し、既存の数論証明本体（Zsigmondy / valuation）は改変していない。
6. 次の課題:
   - Phase D（general `d` product 版へ進むかの設計判断）を開始する。

### 日時: 2026/03/12 15:26 JST: Phase D 評価と分岐判断（general `d` product 版への進行判定）

1. 目的: `CFBRC_Discussion.md` のロードマップに照らし、general `d` product 版へ進むかを技術的に評価して分岐を確定する。
2. 内容:
   - 評価基準を整理:
     - prime core の exact bridge 完了（Phase A/B）
     - Zsigmondy / valuation 層への API 接続完了（Phase C）
     - `CFBRC_Discussion.md` の最終判定（prime の次は general `d` product）との整合
   - 分岐案を比較:
     - GO: general `d` の代数橋を先行実装
     - HOLD: valuation / squarefree 完了まで保留
   - 設計書へ分岐判断と次スコープを反映。
3. 結論: Branch D-GO を採用。general `d` の product 版へ進む。
4. 失敗事例: 実装エラーはなし（本作業は評価と意思決定の文書化）。
5. 備考:
   - 今回の決定は「代数橋は valuation 未完と独立に前進可能」という整理に基づく。
6. 次の課題:
   - general `d` 向けに `Homog(Φ_m)(X,Y)` 評価器と divisors product bridge の実装を開始する。

### 日時: 2026/03/12 15:37 JST: Phase D 実装着手（評価器 + divisors product bridge の kickoff）

1. 目的: D-GO 方針に沿って、general `d` product 版の最小核（評価器と product bridge）を `DkMath.CFBRC.*` に実装開始する。
2. 内容:
   - `DkMath.CFBRC.CyclotomicProduct` を新規追加。
   - 実装した定義・定理:
     - `cyclotomicEval`
     - `prod_cyclotomicEval_eq_geomSum`
     - `cyclotomicShiftedEval`
     - `cyclotomicDivisorsProductShifted`
     - `cyclotomicShiftedEval_one_eq_cyclotomicEval_add_one`
     - `cyclotomicDivisorsProductShifted_one_eq_geomSum`
     - `cyclotomicPrimeCore_one_eq_geomSum`
     - `cyclotomicDivisorsProductShifted_one_eq_cyclotomicPrimeCore`
   - `DkMath.CFBRC` 入口に `import DkMath.CFBRC.CyclotomicProduct` を追加。
   - `lake build DkMath.CFBRC.CyclotomicProduct` / `lake build DkMath.CFBRC` でビルド成功を確認。
3. 結論: general `d` product bridge の足場が CFBRC 側に成立した。まずは `u=1` 断面で divisors product と core の接続まで到達。
4. 失敗事例:
   - 初回実装で `Polynomial.cyclotomic` 由来の noncomputable 制約と、`eval₂` 展開の書き換え不一致でビルド失敗。
   - `noncomputable section` 化と `prod_congr` ベースの書き換えで解消。
5. 備考:
   - 今回は kickoff として `u=1` の橋を先に固定し、一般 `u` の完全斉次橋は次ステップで拡張する。
6. 次の課題:
   - `Homog(Φ_m)(X,Y)` の一般 `u` 接続を導入し、`GN(d,x,w)` 側への完全橋渡しを実装する。

### 日時: 2026/03/12 16:06 JST: `Homog(Φ_m)(X,Y)` の一般 `u` 接続（factor-level）を導入

1. 目的: general `u` 接続を導入するため、shifted evaluator を同次化評価へ寄せる。
2. 内容:
   - `DkMath.CFBRC.CyclotomicProduct` の `cyclotomicShiftedEval` を
     `Polynomial.homogenize` の評価として再定義。
   - `cyclotomicShiftedEval_one_eq_cyclotomicEval_add_one` を
     `Polynomial.eval_homogenize` に基づく証明へ更新。
   - 既存の `u=1` product bridge
     (`cyclotomicDivisorsProductShifted_one_eq_geomSum`,
      `cyclotomicDivisorsProductShifted_one_eq_cyclotomicPrimeCore`)
     が新定義の下でも成立することを確認。
   - `lake build DkMath.CFBRC.CyclotomicProduct` / `lake build DkMath.CFBRC` 成功。
3. 結論: `Homog(Φ_m)(X,Y)` の一般 `u` 局所接続（factor-level）は導入完了。
4. 失敗事例:
   - 初期案で general `d` global bridge（product 側）を同時に進めたが、
     補題依存が重く安定ビルドを崩したため、段階実装へ切り替えた。
5. 備考:
   - 今回は安定性優先で factor-level にスコープを絞り、
     global bridge は次作業へ分離した。
6. 次の課題:
   - general `d` での global product と `GN(d,x,w)` の完全同一化補題を実装する。

### 日時: 2026/03/12 16:10 JST: `GN(d,x,w)` 完全同一化補題を実装（`u=1` 断面）

1. 目的: 要求された `GN(d,x,w)` への complete identification を、現行スコープで厳密に実装する。
2. 内容:
   - `DkMath.CFBRC.CyclotomicProduct` に
     `cyclotomicDivisorsProductShifted_one_eq_GN` を追加。
   - 証明構成:
     - `cyclotomicDivisorsProductShifted_one_eq_cyclotomicPrimeCore`
     - `mul_cyclotomicPrimeCore_eq_mul_GN`
     - `x ≠ 0` による左消去
   - `lake build DkMath.CFBRC.CyclotomicProduct` / `lake build DkMath.CFBRC` 成功。
3. 結論: general `d` の divisors product shifted は、`u=1` 断面で `GN d x 1` と完全同一化できた。
4. 失敗事例: 特になし（追加補題は一発でビルド通過）。
5. 備考:
   - 現時点の「完全同一化」は `u=1` 断面で完了。
   - general `u` の global product = `GN(d,x,u)` は引き続き次段で拡張する。
6. 次の課題:
   - general `u` の global bridge を仕上げ、`GN(d,x,w)` 一般形へ拡張する。

### 日時: 2026/03/12 16:24 JST: general `u` の global bridge を実装し、`GN(d,x,w)` 一般形へ拡張

1. 目的: `Homog(Φ_m)(X,Y)` の factor-level 接続を global product へ持ち上げ、`GN(d,x,w)` 一般形へ橋渡しする。
2. 内容:
   - `DkMath.CFBRC.CyclotomicProduct` に general `u` 用の橋渡し補題を追加:
     - `cyclotomicShiftedEval_eq_cyclotomicEval_div_mul_pow`
     - `cyclotomicDegreeSum_eq_pred`
     - `geomSum_div_mul_pow_eq_cyclotomicPrimeCore`
     - `cyclotomicDivisorsProductShifted_eq_geomSum_div_mul_powDegreeSum`
     - `cyclotomicDivisorsProductShifted_eq_cyclotomicPrimeCore`
     - `cyclotomicDivisorsProductShifted_eq_GN_of_ne_zero`
   - 主要要点:
     - 各因子で `eval_homogenize` を使い
       `cyclotomicShiftedEval m x u = cyclotomicEval m ((x+u)/u) * u^(deg Φ_m)` を確立。
     - divisor 上の次数和を `∑_{m|d, m≠1} φ(m) = d-1` に還元。
     - `u ≠ 0` の下で product 側の `u^(d-1)` 因子を集約し、
       幾何級数側と `cyclotomicPrimeCore d x u` を同一化。
     - 既存 `mul_cyclotomicPrimeCore_eq_mul_GN` と左消去により
       `cyclotomicDivisorsProductShifted d x u = GN d x u` を導出。
   - `lake build DkMath.CFBRC.CyclotomicProduct` / `lake build DkMath.CFBRC` の成功を確認。
3. 結論: `u=1` 断面に限らず、`u ≠ 0` で general `d` global bridge から `GN(d,x,w)` 一般形への完全同一化が成立した。
4. 失敗事例:
   - `Finset.sum_erase_add` の加算順（`sum + f a`）と目標（`f a + sum`）の不一致で一度失敗。
   - `simpa [add_comm, add_left_comm, add_assoc]` で解消。
5. 備考:
   - 本補題は `[Field R]` と `u ≠ 0` を仮定している。
   - `u = 0` 境界は別ケースとして切り出して扱う設計を維持。
6. 次の課題:
   - `cyclotomicDivisorsProductShifted_eq_GN_of_ne_zero` を
     CFBRC 公開 API（`Bridge` 側）へ再輸出し、valuation 連携の一般 `u` 版を追加する。

### 日時: 2026/03/12 16:33 JST: Bridge 側へ再輸出 + valuation 連携 general `u` API 追加

1. 目的: `CyclotomicProduct` の general `u` 完全同一化を CFBRC 公開 API に載せ、valuation 接続も一般 `u` 版を明示的に提供する。
2. 内容:
   - 依存整理:
     - `DkMath.CFBRC.CyclotomicProduct` の import を `Bridge` から `Basic` へ変更（循環依存を回避）。
     - `DkMath.CFBRC.Bridge` から `DkMath.CFBRC.CyclotomicProduct` を import。
   - Bridge 公開 API 追加:
     - `cyclotomicDivisorsProductShifted_eq_GN_of_ne_zero_bridge`
       (`u ≠ 0` 下で divisors product shifted と `GN` の一致を再輸出)。
     - `padicValNat_sub_pow_eq_padicValNat_GN_of_not_dvd_boundary`
       (`(x+u)^d-u^d` と `GN d x u` の `q`-進付値一致; general `u`)。
   - 既存 valuation 補題
     `padicValNat_sub_pow_eq_padicValNat_cyclotomicPrimeCore_of_not_dvd_boundary`
     は、新規 `..._GN_of_not_dvd_boundary` を経由する形へ整理。
   - `lake build DkMath.CFBRC.Bridge` / `lake build DkMath.CFBRC` 成功。
3. 結論: `Bridge` を import するだけで、
   - general `u` の product→`GN` 同一化（公開 wrapper）
   - general `u` の valuation bridge（差の冪 ↔ `GN`、差の冪 ↔ core）
   が利用可能になった。
4. 失敗事例: 特になし（依存の組み替え後もビルドは安定通過）。
5. 備考:
   - valuation 補題は自然数上の `padicValNat` API のため、対象は引き続き Nat。
   - product 側は Field 上 API のまま保持し、Bridge では wrapper として再輸出。
6. 次の課題:
   - 必要に応じて `Bridge` 側の命名統一（`..._bridge` 接尾辞の整理）と
     Zsigmondy 直結 API（primitive prime existence 連携）を追加する。

### 日時: 2026/03/12 16:40 JST: Bridge 命名整理 + Zsigmondy 直結 API 追加

1. 目的: `Bridge` の命名を整理しつつ、原始素因子の存在（Zsigmondy 層A）を CFBRC 記法へ直結する API を追加する。
2. 内容:
   - 命名整理:
     - `cyclotomicDivisorsProductShifted_eq_GN_of_ne_zero_bridge` に
       deprecation 属性を付与し、標準名
       `cyclotomicDivisorsProductShifted_eq_GN_of_ne_zero`
       への移行を明示。
   - Zsigmondy 直結 API を `DkMath.CFBRC.Bridge` に追加:
     - `exists_primitive_prime_factor_sub_pow_of_prime_exp_boundary`
       (`a := x+u, b := u` で prime exponent の primitive prime existence を公開)。
     - `exists_primitive_prime_factor_dvd_cyclotomicPrimeCore_of_prime_exp_boundary`
       (上記 existence を `cyclotomicPrimeCore d x u` 除法へ接続)。
   - 追加 API は `prime_exp_not_dvd_diff_imp_primitive` を経由して
     `∀ 0<k<d, q ∤ ((x+u)^k - u^k)` まで返す形にした。
   - `lake build DkMath.CFBRC.Bridge` / `lake build DkMath.CFBRC` 成功。
3. 結論: CFBRC `Bridge` から、
   - 一般 `u` の product↔GN 同一化は標準名へ統一誘導され、
   - prime exponent の primitive prime existence が
     差分形・core 除法形の両方で直接利用可能になった。
4. 失敗事例: 特になし（追加補題は一度でビルド通過）。
5. 備考:
   - 新規 existence API は `Nat` 上で、`hcop : Nat.Coprime (x+u) u` と `¬ d ∣ x` を要求。
   - `hx : 0 < x` は `u < x+u` を導くために使っている。
6. 次の課題:
   - 必要なら `hcop : Nat.Coprime x u` 版 wrapper を追加し、
     前提を CFBRC 側でより自然な形へ揃える。

### 日時: 2026/03/12 16:55 JST: `hcop : Nat.Coprime x u` 版 wrapper を追加

1. 目的: CFBRC 側で自然な前提 `Nat.Coprime x u` を直接受ける形に API を揃える。
2. 内容:
   - `DkMath.CFBRC.Bridge` に以下の wrapper を追加:
     - `exists_primitive_prime_factor_sub_pow_of_prime_exp_boundary_of_coprime`
     - `exists_primitive_prime_factor_dvd_cyclotomicPrimeCore_of_prime_exp_boundary_of_coprime`
   - 変換は
     `Nat.Coprime x u -> Nat.Coprime (x + u) u`
     を `Nat.coprime_add_self_left` で行い、既存定理へ委譲。
   - 既存 API（`hcop : Nat.Coprime (x+u) u` 版）は保持し、後方互換を維持。
   - `lake build DkMath.CFBRC.Bridge` / `lake build DkMath.CFBRC` 成功。
3. 結論: CFBRC 利用側は自然な `Coprime x u` 前提で primitive-prime existence（差分形 / core 形）を直接呼び出せるようになった。
4. 失敗事例: 特になし（wrapper 追加のみでビルド安定）。
5. 備考:
   - `hx : 0 < x` は引き続き必要（`u < x + u` の導出に使用）。
6. 次の課題:
   - `valuation` 側にも同様の「前提正規化 wrapper」が必要なら追加する。

### 日時: 2026/03/12 16:59 JST: valuation 側の前提正規化 wrapper を追加

1. 目的: valuation 連携でも `Bridge` 利用時の前提を自然化し、`q ∤ x` を毎回手で導かずに済む API を追加する。
2. 内容:
   - `DkMath.CFBRC.Bridge` に以下を追加:
     - `padicValNat_sub_pow_eq_padicValNat_GN_of_coprime_of_dvd_right`
     - `padicValNat_sub_pow_eq_padicValNat_cyclotomicPrimeCore_of_coprime_of_dvd_right`
   - どちらも前提:
     - `hcop : Nat.Coprime x u`
     - `hqP : Nat.Prime q`
     - `hq_dvd_u : q ∣ u`
   - 内部で
     `q ∣ x -> q ∣ gcd x u -> q ∣ 1` による矛盾から `¬ q ∣ x` を導出し、
     既存の `..._of_not_dvd_boundary` 補題へ委譲。
   - `lake build DkMath.CFBRC.Bridge` / `lake build DkMath.CFBRC` 成功。
3. 結論: valuation 側でも「前提正規化 wrapper」が追加され、`Coprime x u` と `q ∣ u` から直接 bridge 補題を呼べるようになった。
4. 失敗事例: 特になし（wrapper 追加のみでビルド安定）。
5. 備考:
   - 今回は `q ∣ u` ケース向けの正規化。`q ∣ x` 側は対称版が必要なら別途追加可能。
6. 次の課題:
   - 必要なら対称版（`q ∣ x` から `¬ q ∣ u` を導く wrapper）も追加する。

### 日時: 2026/03/12 17:02 JST: valuation 前提正規化 wrapper の対称版を追加

1. 目的: `q ∣ x` 側でも、`Coprime x u` から対称に前提を正規化して valuation bridge を直接使えるようにする。
2. 内容:
   - `DkMath.CFBRC.Bridge` に以下を追加:
     - `padicValNat_sub_pow_eq_padicValNat_GN_of_coprime_of_dvd_left`
     - `padicValNat_sub_pow_eq_padicValNat_cyclotomicPrimeCore_of_coprime_of_dvd_left`
   - 前提:
     - `hcop : Nat.Coprime x u`
     - `hqP : Nat.Prime q`
     - `hq_dvd_x : q ∣ x`
   - 内部処理:
     - `q ∣ u` を仮定すると `q ∣ gcd x u = 1` で矛盾、よって `¬ q ∣ u`。
     - 既存の `..._of_not_dvd_boundary` を `(x,u)` を入れ替えた形
       （`((x+u)^d - x^d)`, `GN d u x`, `cyclotomicPrimeCore d u x`）で適用。
   - `lake build DkMath.CFBRC.Bridge` / `lake build DkMath.CFBRC` 成功。
3. 結論: valuation 正規化 API が左右対称に揃い、`q ∣ u` 側・`q ∣ x` 側の両ケースを wrapper で直接扱えるようになった。
4. 失敗事例: 特になし（追加補題は一度でビルド通過）。
5. 備考:
   - 対称版は式が `((x+u)^d - x^d)` となり、対応する右境界 `GN d u x` / `core d u x` に接続される。
6. 次の課題:
   - 必要なら左右を統一した高位 API（境界指定パラメータ付き）を設計する。

### 日時: 2026/03/12 17:06 JST: 左右統一の高位 API（境界 side 指定）を設計・実装

1. 目的: left/right の valuation bridge 群を、境界指定パラメータで統一して呼べる高位 API を整備する。
2. 内容:
   - `DkMath.CFBRC.Bridge` に設計要素を追加:
     - `BoundarySide` (`right` / `left`)
     - `boundaryDiffPow`
     - `boundaryGN`
     - `boundaryCyclotomicPrimeCore`
   - 高位 API を追加:
     - `padicValNat_boundaryDiffPow_eq_boundaryGN_of_coprime_of_dvd_boundary`
     - `padicValNat_boundaryDiffPow_eq_boundaryCyclotomicPrimeCore_of_coprime_of_dvd_boundary`
   - 設計方針:
     - side ごとに必要前提を
       `hq_dvd_boundary : match side with | right => q ∣ u | left => q ∣ x`
       で表現。
     - 証明本体は `cases side` で既存 left/right wrapper へ委譲し、
       低位 API との整合を保つ。
   - `lake build DkMath.CFBRC.Bridge` / `lake build DkMath.CFBRC` 成功。
3. 結論: 境界 side を引数にした統一 API が導入され、利用側は left/right の個別定理名を意識せずに valuation bridge を呼び出せるようになった。
4. 失敗事例: 特になし（既存 wrapper 群を再利用して安定実装）。
5. 備考:
   - 高位 API は Nat valuation の文脈（`Coprime x u`, `Prime q`, side 境界の除法）に合わせて設計。
6. 次の課題:
   - 必要なら同様の side 指定 API を divisibility / primitive-prime existence 側にも拡張する。

### 日時: 2026/03/12 17:17 JST: docstring 整備（第1弾: Basic / CyclotomicProduct）

1. 目的: `DkMath.CFBRC` の定理・補題について、数学的意味が追える docstring を順次付与する。
2. 内容:
   - `DkMath.CFBRC.Basic` の主要補題へ説明を追加:
     - prime cyclotomic との同一化
     - core の漸化式
     - Cosmic Formula 型恒等式
     - `GN` 同一化・除法同値・差冪分解・素数除法帰結
   - `DkMath.CFBRC.CyclotomicProduct` の主要補題へ説明を追加:
     - `cyclotomicDegreeSum` と次数和評価
     - 幾何和から core への接続
     - general `u` の global product bridge
     - `GN` への complete identification
   - 既存コード本体は不変更（コメント追加のみ）。
   - `lake build DkMath.CFBRC.Basic` / `lake build DkMath.CFBRC.CyclotomicProduct` /
     `lake build DkMath.CFBRC` 成功。
3. 結論: CFBRC の中心補題群に数学的 docstring が入り、定理の位置づけ・使い所を追いやすくなった。
4. 失敗事例: 特になし（コメント追加のみでビルド安定）。
5. 備考:
   - 次段では `Bridge` 側の既存 docstring も粒度を揃えて統一する予定。
6. 次の課題:
   - `Bridge.lean` の docstring を「前提・結論・接続先」のフォーマットで統一し、
     side 指定高位 API の利用例を短く補う。

### 日時: 2026/03/12 17:21 JST: docstring 整備（第2弾: Bridge）

1. 目的: `Bridge.lean` の docstring を「前提・結論・接続先」が分かる粒度へ統一する。
2. 内容:
   - `Bridge` 内の主要 API（除法同値 / Zsigmondy existence / valuation bridge / side 高位 API）
     の docstring を数学的説明に更新。
   - 具体的には以下を明示:
     - どの前提（`q ∤ x`, `Coprime`, `q ∣ boundary`）で
     - 何が結論（`padicValNat` 等式, primitive prime existence, core/GN 除法）
     - どの層へ接続（`Gcd.GN` / `cyclotomicPrimeCore` / Zsigmondy 層A）
   - `BoundarySide` と関連定義（`boundaryDiffPow`, `boundaryGN`, `boundaryCyclotomicPrimeCore`）
     も左右の意味が読める説明へ更新。
   - `lake build DkMath.CFBRC.Bridge` / `lake build DkMath.CFBRC` 成功。
3. 結論: CFBRC bridge 層の公開 API は、docstring だけで前提と数学的役割を追える状態になった。
4. 失敗事例: 特になし（コメント更新のみ）。
5. 備考:
   - 今回は API 名・定理本体を変更せず、ドキュメント表現のみ更新。
6. 次の課題:
   - `README.md` に Bridge 高位 API（`BoundarySide` ベース）の短い使用例を追加する。

### 日時: 2026/03/12 19:24 JST: README 充実化（紹介・解説・使用例）

1. 目的: CFBRC の入口ドキュメントを、理論概要と Lean 利用導線が分かる形へ拡張する。
2. 内容:
   - `DkMath/CFBRC/README.md` を全面改稿し、以下を追加:
     - CFBRC の狙い（代数層 / 円分層 / 数論層の橋渡し）
     - core 公式の解説
     - Lean 側モジュール構成 (`Defs` / `Basic` / `CyclotomicProduct` / `Bridge`)
     - Quick Start import
     - 使用例（Lean snippets）:
       - `cyclotomicPrimeCore = GN`
       - 素数除法同値
       - valuation bridge（右境界）
       - `BoundarySide` による左右統一 API
       - Zsigmondy primitive prime existence（core 形）
     - 関連ドキュメントへのリンク
   - 実装コード変更はなし（README 更新のみ）。
3. 結論: README 単体で、CFBRC の位置づけ・主要 API・典型的使用パターンを把握できる状態になった。
4. 失敗事例: 特になし。
5. 備考:
   - README のコード片は「最小利用イメージ」を優先した記述。
6. 次の課題:
   - 必要なら README に「Phase 別 API マップ（A/B/C/D）」を追加し、
     実装計画書との往復参照を強化する。

### 日時: 2026/03/12 20:17 JST: `hS0_not_sq` への cyclotomic-core bridge 補題を FLT 側へ追加

1. 目的: `d=3` での no-lift 仮定を `cyclotomicPrimeCore` から `S0_nat` へ直接移す薄い橋を実装する。
2. 内容:
   - `DkMath/FLT/CosmicPetalBridge.lean` に以下を追加:
     - `hS0_not_sq_of_noLift_cyclotomicPrimeCore_d3`
   - 補題の形:
     - 入力: `¬ q^2 ∣ cyclotomicPrimeCore 3 (c-b) b`（primitive branch 前提つき）
     - 出力: `¬ q^2 ∣ S0_nat c b`
   - 証明の接続:
     - `cyclotomicPrimeCore_eq_GN_nat`（`x:=c-b`）
     - `GN_three_sub_eq_S0_nat`
     - 上の同一化合成で `core -> S0` に転送
   - 依存追加:
     - `import DkMath.CFBRC.Basic` を `CosmicPetalBridge.lean` に追加。
   - 検証:
     - `lake build DkMath.FLT.CosmicPetalBridge`
     - `lake build DkMath.FLT.Main`
     ともに成功。
3. 結論: `hS0_not_sq` 供給経路として、`NoSqOnS0` 系・`GN` 系に加えて
   cyclotomic-core 経由の実装可能ルートをコード化できた。
4. 失敗事例:
   - 初回 `simpa` で `cyclotomicPrimeCore` 展開形（和表示）との型不一致が発生。
   - 展開形総和 `∑ ... (c-b+b)^x ...` と `S0_nat` の一致を中間補題化して解消。
5. 備考:
   - 本補題は no-lift provider 自体を与えるものではなく、provider から `S0` 形へ移す glue。
6. 次の課題:
   - `PrimeProvider` 側の no-lift / squarefree 仮定から本補題へ接続する wrapper を追加する。

### 日時: 2026/03/12 20:31 JST: PrimeProvider から `hS0_not_sq` への wrapper を追加

1. 目的: `PrimeProvider` 側で持っている `GN 3 (c-b) b` の no-lift / squarefree 仮定を、
   `Main` が要求する `hS0_not_sq` 形へ直接接続する。
2. 内容:
   - `DkMath/FLT/PrimeProvider/CosmicPetalBridgeGNNoWieferich.lean` に以下を追加:
     - `hS0_not_sq_of_noLift_GN_d3`
     - `hS0_not_sq_of_squarefree_GN_d3`
   - 証明接続:
     - no-lift 版は `cyclotomicPrimeCore_eq_GN_nat` で仮定を core 側へ移し、
       `hS0_not_sq_of_noLift_cyclotomicPrimeCore_d3` へ渡す。
     - squarefree 版は `not_sq_dvd_of_squarefree` で no-lift を抽出して
       no-lift wrapper に合成する。
   - 検証:
     - `lake build DkMath.FLT.PrimeProvider.CosmicPetalBridgeGNNoWieferich`
     - `lake build DkMath.FLT.Main`
     ともに成功。
3. 結論: PrimeProvider の仮定をそのまま `hS0_not_sq` に落とせる導線ができ、
   `Main` 側での仮定供給が薄い glue で統一できた。
4. 失敗事例:
   - 初回実装で `simpa` による展開が過剰に進み、`cyclotomicPrimeCore` 展開和と `GN` 展開和の型不一致が発生。
   - `rw [← hcore_eq_GN]` の明示書き換えへ変更して解消。
   - 追加で implicit dependent binder 推論が崩れたため、`intro q ...` を明示して解消。
5. 備考:
   - 既存の `triomino*` bridge 群を壊さず、`d=3` 向け補助 API として追記した。
6. 次の課題:
   - 必要なら同様の wrapper を `boundary` 高位 API（`BoundarySide`）へ揃えて公開する。

### 日時: 2026/03/12 20:45 JST: `BoundarySide` 高位 API へ同型 wrapper を追加公開

1. 目的: 右/左個別の valuation bridge と同じ粒度で、`BoundarySide` 側にも
   「gap 非除法前提」と「前提正規化（coprime + boundary 除法）」の二層 API を揃える。
2. 内容:
   - `DkMath/CFBRC/Bridge.lean` に高位 API を追加:
     - `padicValNat_boundaryDiffPow_eq_boundaryGN_of_not_dvd_gap`
     - `padicValNat_boundaryDiffPow_eq_boundaryCyclotomicPrimeCore_of_not_dvd_gap`
   - 既存の `..._of_coprime_of_dvd_boundary` 2本を整理:
     - `Nat.Coprime x u` と境界除法（`q ∣ u` or `q ∣ x`）から gap 非除法を導出
     - 新しい `..._of_not_dvd_gap` 高位 API へ委譲する構成へ変更
   - 左境界は変数入替え（`x ↔ u`）で既存右境界 bridge を再利用。
   - 検証:
     - `lake build DkMath.CFBRC.Bridge`
     - `lake build DkMath.CFBRC`
     ともに成功。
3. 結論: `BoundarySide` 公開 API が
   - 直接適用層（`not_dvd_gap`）
   - 前提正規化層（`coprime + dvd_boundary`）
   の二層で統一され、利用導線が右/左対称に揃った。
4. 失敗事例: 特になし（既存 API との後方互換を保ったまま拡張できた）。
5. 備考:
   - 今回は valuation bridge を対象に統一。`boundary` 側の存在論 API は未追加。
6. 次の課題:
   - 必要なら `BoundarySide` に対応した存在論（primitive prime existence）高位 API も検討する。

### 日時: 2026/03/12 20:58 JST: `BoundarySide` 対応の存在論（primitive prime existence）高位 API を追加

1. 目的: valuation だけでなく存在論（`∃ q`）も `BoundarySide` で左右統一し、
   `right/left` それぞれを単一入口から利用できるようにする。
2. 内容:
   - `DkMath/CFBRC/Bridge.lean` に以下を追加:
     - `exists_primitive_prime_factor_boundaryDiffPow_of_prime_exp_boundary_of_coprime`
     - `exists_primitive_prime_factor_dvd_boundaryCore_of_prime_exp_boundary_of_coprime`
   - API 仕様:
     - 入力: `side`, `Nat.Prime d`, `3 ≤ d`, `0 < x`, `0 < u`, `Nat.Coprime x u`,
       および side 依存の gap 条件（`right: ¬ d ∣ x`, `left: ¬ d ∣ u`）
     - 出力: side 指定の差分式 / core を割る primitive prime `q` と、
       `0 < k < d` に対する低次差分非除法（side 指定）を返す。
   - 実装方針:
     - `right` は既存の `_of_coprime` existence API へ直接委譲。
     - `left` は `x,u` を入れ替えて既存 API を再利用し、
       `Nat.add_comm` で差分式を side 形へ戻す。
   - 検証:
     - `lake build DkMath.CFBRC.Bridge`
     - `lake build DkMath.CFBRC`
     ともに成功。
3. 結論: `BoundarySide` 高位 API が valuation 層だけでなく存在論層でも揃い、
   CFBRC 公開導線の左右対称性が強化された。
4. 失敗事例:
   - 追加した theorem 名が長く style warning を出したため、
     core 版の公開名を短縮（`...boundaryCore...`）して解消。
5. 備考:
   - primitive 条件は `boundaryDiffPow side k x u` で統一して返す。
6. 次の課題:
   - 必要なら `BoundarySide` 版の no-lift / squarefree provider 接続も同様に追加する。

### 日時: 2026/03/20 01:07 JST: Triangular Permutation の `d=2` 実装（TrigBridge 4層）を CFBRC 配下へ追加

1. 目的: 設計書 `CFBRC_TriPerm_Lean_Design.md` に沿って、  
   `a'(a'+2x) = a^2 cos^2 φ = Re(G_2(a cos φ, a sin φ))` の Lean bridge を `DkMath.CFBRC` へ実装する。
2. 内容:
   - 新規ファイルを追加:
     - `DkMath/CFBRC/TrigBridge/Basic.lean`
     - `DkMath/CFBRC/TrigBridge/Trig.lean`
     - `DkMath/CFBRC/TrigBridge/Complex.lean`
     - `DkMath/CFBRC/TrigBridge/Main.lean`
   - 追加した主な定義・定理:
     - 定義: `body2`, `cfbrc`, `cfbrcR`
     - 代数層: `body2_factor`, `body2_sub`, `body2_sub_factor`
     - 三角層: `sq_sub_sin_eq_cos`, `body2_trig`, `body2_factor_trig`
     - 複素層: `cfbrc_two_re`, `cfbrc_two_im`, `cfbrc_two_re_polar`, `cfbrc_two_im_polar`
     - 主定理: `body2_eq_re_cfbrc2`, `factor_eq_re_cfbrc2`
   - 入口更新:
     - `DkMath/CFBRC.lean` に `import DkMath.CFBRC.TrigBridge.Main` を追加。
   - 検証:
     - `./lean-build.sh DkMath.CFBRC.TrigBridge.Basic`
     - `./lean-build.sh DkMath.CFBRC.TrigBridge.Trig`
     - `./lean-build.sh DkMath.CFBRC.TrigBridge.Complex`
     - `./lean-build.sh DkMath.CFBRC.TrigBridge.Main`
     - `./lean-build.sh DkMath.CFBRC`
     すべて成功。
3. 結論: CFBRC 配下に「代数 -> 三角 -> 複素 -> 主定理」の `d=2` bridge が実装され、  
   Triangular Permutation 設計の最小核が build 可能な形で固定された。
4. 失敗事例:
   - 初期 script で一部補題に `simp` 後の不要 `ring` が残り、`No goals to be solved` が発生。
   - `body2_sub` と `cfbrc_two_re` は `simp` のみで完結する形に調整して解消。
5. 備考:
   - 今回は `d=2` 専用橋を先に固定し、general `d` の実部一般式は未着手。
   - 再開時の起点:
     - 実装本体: `DkMath/CFBRC/TrigBridge/Main.lean`
     - 設計参照: `DkMath/CFBRC/docs/CFBRC_TriPerm_Lean_Design.md`
     - 理論背景: `DkMath/CFBRC/docs/CFBRC_Triangular Permutation.md`
6. 次の課題:
   - `README.md` に TrigBridge の短い使用例を追加する。
   - `cfbrc d` 一般に対する `Complex.re` 抽出の補助補題群（general `d`）を別ファイルで設計する。

### 日時: 2026/03/20 01:14 JST: README 反映 + `DkMathTest.CFBRC` を新設（TriPerm 検証導線の整備）

1. 目的: TrigBridge 実装を README に反映し、`DkMathTest.*` 側に CFBRC 専用の検証入口を追加する。
2. 内容:
   - `DkMath/CFBRC/README.md` を更新:
     - Lean Modules に `DkMath.CFBRC.TrigBridge.Main` を追加。
     - Quick Start に `import DkMath.CFBRC.TrigBridge.Main` の最小導線を追加。
     - Usage Examples に Triangular Permutation bridge（`d=2`）の例を追加。
   - `DkMathTest/CFBRC.lean` を新規作成:
     - `body2_eq_re_cfbrc2`, `factor_eq_re_cfbrc2` の回帰例
     - `prime_dvd_sub_pow_iff_dvd_cyclotomicPrimeCore_nat` の例
     - `cyclotomicPrimeCore_eq_GN_nat` の例
     - 代表定理の `#print axioms` を配置。
   - `DkMathTest.lean` に `import DkMathTest.CFBRC` を追加。
   - 検証:
     - `./lean-build.sh DkMathTest.CFBRC` 成功
     - `./lean-build.sh DkMathTest` 成功
3. 結論: README とテスト導線が TrigBridge 追加に追随し、  
   CFBRC の補題検証は `DkMathTest.CFBRC` から直接再実行できる状態になった。
4. 失敗事例:
   - ビルド失敗はなし。
   - `DkMathTest` 全体では既存 `ABC021` の `sorry` 警告が出るが、今回変更とは無関係（既知残件）。
5. 備考:
   - ユーザー要望「DkMathTest.* の CFBRC 整備」に対応し、`DkMathTest/CFBRC.lean` を新設。
   - 既存の公開入口 `DkMath/CFBRC.lean` は維持したまま、テスト側入口を追加した。
6. 次の課題:
   - `DkMathTest.CFBRC` に `BoundarySide` 高位 API の回帰例を追加する。
   - 必要なら `cfbrc d` 一般化作業に合わせて test ケースを `d=3` 以上へ拡張する。

### 日時: 2026/03/20 01:27 JST: `DkMathTest.CFBRC` に `BoundarySide` 高位 API 回帰例を追加

1. 目的: `BoundarySide` 統一 API（valuation / existence）を test 側で常時検証できるようにする。
2. 内容:
   - `DkMathTest/CFBRC.lean` に以下の回帰例を追加:
     - `padicValNat_boundaryDiffPow_eq_boundaryGN_of_coprime_of_dvd_boundary`
     - `padicValNat_boundaryDiffPow_eq_boundaryCyclotomicPrimeCore_of_coprime_of_dvd_boundary`
     - `exists_primitive_prime_factor_dvd_boundaryCore_of_prime_exp_boundary_of_coprime`
   - `#print axioms` を追加:
     - `padicValNat_boundaryDiffPow_eq_boundaryGN_of_coprime_of_dvd_boundary`
     - `exists_primitive_prime_factor_dvd_boundaryCore_of_prime_exp_boundary_of_coprime`
   - 検証:
     - `./lean-build.sh DkMathTest.CFBRC` 成功
     - `./lean-build.sh DkMathTest` 成功
3. 結論: `BoundarySide` の高位 API が test 層でも固定化され、  
   将来の API 変更・型崩れを `DkMathTest.CFBRC` で即検知できる状態になった。
4. 失敗事例:
   - ビルド失敗はなし。
   - `DkMathTest` 全体では既知の `ABC021` `sorry` 警告が継続（今回変更とは無関係）。
5. 備考:
   - 追加例は `side` 依存前提（`match side with ...`）をそのまま受ける形で記述し、
     API の使用形をドキュメント兼テストとして保持した。
6. 次の課題:
   - 必要なら `exists_primitive_prime_factor_boundaryDiffPow_of_prime_exp_boundary_of_coprime`
     の差分形も test 例に追加する。
   - `d=2` bridge 以外（general `d` 実部抽出）に着手する際は
     test 入口を `DkMathTest.CFBRC` に同時追加する。

### 日時: 2026/03/20 01:32 JST: `BoundarySide` 差分形 existence の回帰例を `DkMathTest.CFBRC` に追加

1. 目的: `BoundarySide` の存在論 API を core 形だけでなく差分形でも test 固定化する。
2. 内容:
   - `DkMathTest/CFBRC.lean` に以下を追加:
     - `exists_primitive_prime_factor_boundaryDiffPow_of_prime_exp_boundary_of_coprime`
       の回帰例（`side` 依存前提をそのまま受ける形）。
   - `#print axioms` を追加:
     - `exists_primitive_prime_factor_boundaryDiffPow_of_prime_exp_boundary_of_coprime`
   - 検証:
     - `./lean-build.sh DkMathTest.CFBRC` 成功
     - `./lean-build.sh DkMathTest` 成功
3. 結論: `BoundarySide` existence API は
   - core 形
   - 差分形
   の両方が `DkMathTest.CFBRC` で回帰検証される状態になった。
4. 失敗事例:
   - ビルド失敗はなし。
   - `DkMathTest` 全体では既知の `ABC021` `sorry` 警告のみ継続。
5. 備考:
   - 追加例により、`BoundarySide` API の公開名変更や依存前提変更を test で即検知可能。
6. 次の課題:
   - 必要なら `padicValNat_boundaryDiffPow_eq_boundary*_*_of_not_dvd_gap`
     系も `DkMathTest.CFBRC` に追加し、正規化 wrapper 前の層まで監視する。
   - `cfbrc d` general 化を開始する際は、`DkMathTest.CFBRC` に同時で最小検証例を追加する。

### 日時: 2026/03/20 01:36 JST: TrigBridge / Test に数学的 docstring を追加整備

1. 目的: CFBRC の Triangular Permutation 実装を、コードだけでなく docstring でも追える状態にする。
2. 内容:
   - `DkMath/CFBRC/TrigBridge/Basic.lean`:
     - ファイル冒頭に層の目的（代数層）を追加。
     - `body2_factor`, `body2_sub`, `body2_sub_factor` に数学的意味を追記。
   - `DkMath/CFBRC/TrigBridge/Trig.lean`:
     - 三角層の意図（`x = a sin φ` による位相化）を追加。
     - `sq_sub_sin_eq_cos`, `body2_trig`, `body2_factor_trig` に説明を追加。
   - `DkMath/CFBRC/TrigBridge/Complex.lean`:
     - 複素層の意図（`d=2` の `Re/Im` 固定）を追加。
     - `cfbrc_two_re/im` と極座標補題に説明を追加。
   - `DkMath/CFBRC/TrigBridge/Main.lean`:
     - 最終橋の連鎖式を冒頭 docstring で明示。
     - 主定理2本の意味を補足。
   - `DkMathTest/CFBRC.lean`:
     - ファイル冒頭に test 目的を追加。
     - `example` 群を用途別（`d=2` bridge / core-GN / BoundarySide valuation-existence）に区分コメント化。
   - 検証:
     - `./lean-build.sh DkMath.CFBRC.TrigBridge.Main` 成功
     - `./lean-build.sh DkMathTest.CFBRC` 成功
     - `./lean-build.sh DkMath.CFBRC` 成功
     - `./lean-build.sh DkMathTest` 成功
3. 結論: TrigBridge 実装は、式の意味・層構造・定理の位置づけを docstring から追える状態になった。
4. 失敗事例:
   - ビルド失敗はなし。
   - `DkMathTest` 全体では既知 `ABC021` の `sorry` 警告が継続（今回変更とは無関係）。
5. 備考:
   - 今回は API 本体を変えず、可読性向上のための説明追加に限定した。
6. 次の課題:
   - 必要なら `Bridge.lean` の高位 API 例（`BoundarySide`）を README に短く再掲し、
     ドキュメント導線を一本化する。
   - general `d` 拡張フェーズでは、新規補題ごとに「式の意味 + 接続先」を同じ docstring 形式で維持する。

### 日時: 2026/03/20 01:46 JST: `TrigBridge.General` を追加（general `d` の `Re/Im` 抽出補助）

1. 目的: `cfbrc d` の general `d` 拡張に向けて、`Complex.re`/`Complex.im` を追跡する再帰補助を先に固定する。
2. 内容:
   - `DkMath/CFBRC/TrigBridge/General.lean` を新規追加:
     - 補助定義: `cfbrcRe`, `cfbrcIm`
     - 基底値: `cfbrcRe_zero`, `cfbrcIm_zero`, `cfbrcRe_one`, `cfbrcIm_one`
     - 再帰分解: `cfbrcR_succ_decompose`
     - 実部/虚部再帰: `cfbrcRe_succ`, `cfbrcIm_succ`
     - 補助定義版再帰: `cfbrcRe_succ'`, `cfbrcIm_succ'`
   - `DkMath/CFBRC.lean` に
     - `import DkMath.CFBRC.TrigBridge.General`
     を追加し公開入口に接続。
   - `DkMathTest/CFBRC.lean` に general `d` 回帰例を追加:
     - `cfbrcRe 1 X Θ = X`
     - `cfbrcRe_succ'`, `cfbrcIm_succ'` の使用例
     - `#print axioms cfbrcRe_succ'` を追加。
   - `DkMath/CFBRC/README.md` を更新:
     - Lean Modules に `TrigBridge.General` を追加
     - Usage に general `d` の `Re/Im` 再帰例を追加。
   - 検証:
     - `./lean-build.sh DkMath.CFBRC.TrigBridge.General` 成功
     - `./lean-build.sh DkMath.CFBRC` 成功
     - `./lean-build.sh DkMathTest.CFBRC` 成功
     - `./lean-build.sh DkMathTest` 成功
3. 結論: `d=2` 固定橋に加え、general `d` へ進むための `Re/Im` 抽出レイヤが `TrigBridge.General` として整備された。
4. 失敗事例:
   - 初期 draft で `No goals to be solved`（`simp` 後の不要 `ring`）が発生。
   - `DkMathTest.CFBRC` に `unnecessarySimpa` 警告が1件発生。
   - いずれも proof script を簡約して解消。
5. 備考:
   - 今回の再帰式は `(iΘ)^d` の `Re/Im` を残した形で、将来の parity/閉形式導出に接続しやすい構成にした。
6. 次の課題:
   - `(iΘ)^d` の `Re/Im` を parity で整理する補題（偶奇・`mod 4`）を追加する。
   - `cfbrcRe_succ'` を使った general `d` の実部漸化式（`Θ=0`・`X=0` 断面）を先に固定する。

### 日時: 2026/03/20 01:57 JST: `(iΘ)^d` の偶奇補題を追加し、`cfbrcRe/Im` 再帰を偶奇分解

1. 目的: general `d` の `Re/Im` 抽出を実用化するため、`(iΘ)^d` 項を偶奇で閉じる補題を追加する。
2. 内容:
   - `DkMath/CFBRC/TrigBridge/General.lean` に追加:
     - 二乗評価: `pure_phase_sq_re`, `pure_phase_sq_im`
     - 偶数冪: `pure_phase_pow_even_re`, `pure_phase_pow_even_im`
     - 奇数冪: `pure_phase_pow_odd_re`, `pure_phase_pow_odd_im`
     - `cfbrcRe/Im` 偶奇再帰:
       - `cfbrcRe_odd_from_even`
       - `cfbrcIm_odd_from_even`
       - `cfbrcRe_even_from_odd`
       - `cfbrcIm_even_from_odd`
   - `DkMathTest/CFBRC.lean` に回帰例を追加:
     - `pure_phase_pow_odd_im`
     - `cfbrcIm_even_from_odd`
     - および `#print axioms pure_phase_pow_odd_im`
   - `DkMath/CFBRC/README.md` を更新:
     - `TrigBridge.General` の説明に偶奇補題を追記
     - Usage に `pure_phase_pow_odd_im` の例を追加
   - 検証:
     - `./lean-build.sh DkMath.CFBRC.TrigBridge.General` 成功
     - `./lean-build.sh DkMath.CFBRC` 成功
     - `./lean-build.sh DkMathTest.CFBRC` 成功
     - `./lean-build.sh DkMathTest` 成功
3. 結論: `cfbrcRe_succ'` / `cfbrcIm_succ'` の右端に残っていた `(iΘ)^d` 項を偶奇で評価できるようになり、general `d` の再帰解析が一段進んだ。
4. 失敗事例:
   - 初期案で `simp` ベース簡約が不安定（`No goals` / `simp made no progress`）。
   - 帰納法＋`Complex.mul_re/im` の明示展開へ切替えて安定化。
5. 備考:
   - 今回は `mod 4` まで分解せず、まず偶奇で使える最小核を固定した。
6. 次の課題:
   - `I^d` の `mod 4` 分解（`0,1,2,3` ケース）を追加し、
     `pure_phase_pow_*` をさらに閉形式化する。
   - `Θ = 0` / `X = 0` の断面補題を追加し、general `d` の境界挙動を先に固定する。

### 日時: 2026/03/20 02:07 JST: `mod 4` 補題を追加（`4n+r` で `(iΘ)^d` の `Re/Im` を閉形式化）

1. 目的: 偶奇補題を一段進め、`(iΘ)^d` の位相項を `4` 周期で直接使える形にする。
2. 内容:
   - `DkMath/CFBRC/TrigBridge/General.lean` に追加:
     - `neg_one_pow_even`, `neg_one_pow_odd`
     - `pure_phase_pow_mod4_zero_re`, `pure_phase_pow_mod4_zero_im`
     - `pure_phase_pow_mod4_one_re`, `pure_phase_pow_mod4_one_im`
     - `pure_phase_pow_mod4_two_re`, `pure_phase_pow_mod4_two_im`
     - `pure_phase_pow_mod4_three_re`, `pure_phase_pow_mod4_three_im`
   - `DkMathTest/CFBRC.lean` に回帰例を追加:
     - `pure_phase_pow_mod4_two_re`
     - `pure_phase_pow_mod4_three_im`
     - `#print axioms pure_phase_pow_mod4_three_im`
   - `DkMath/CFBRC/README.md` に `mod 4` 使用例を追記。
   - ビルド時の `unused simp arg` 警告（`General.lean`）を修正。
   - 検証:
     - `./lean-build.sh DkMath.CFBRC.TrigBridge.General` 成功
     - `./lean-build.sh DkMathTest.CFBRC` 成功
     - `./lean-build.sh DkMath.CFBRC` 成功
     - `./lean-build.sh DkMathTest` 成功
3. 結論: `Re/Im ((iΘ)^d)` が `4n+r` ごとに直接評価できるようになり、
   general `d` の再帰式で位相項を即座に閉じられる状態になった。
4. 失敗事例:
   - 初期案は `simp` 依存で不安定（`simp made no progress` / `No goals`）。
   - 帰納法＋明示展開（`Complex.mul_re/im`, `pow_add`）へ切り替えて安定化。
5. 備考:
   - `mod 4` 補題は偶奇補題の上に積んだため、今後の `I^d` 系補題でも再利用しやすい。
6. 次の課題:
   - `cfbrcRe/Im` について `d mod 4` ベースの再帰（または閉形式）を追加し、
     `X=0` / `Θ=0` 断面の簡約定理を整備する。
   - 必要なら `TrigBridge.Main` に general `d` 入口定理（`d=2` 特化との関係明示）を追加する。

### 日時: 2026/03/20 02:13 JST: `cfbrcRe/Im` の `d mod 4` 直接再帰を追加

1. 目的: `mod 4` 位相補題を `cfbrcRe/Im` 側へ反映し、`d` の合同類ごとに直接使える再帰式を提供する。
2. 内容:
   - `DkMath/CFBRC/TrigBridge/General.lean` に追加:
     - `cfbrcRe_mod4_one_from_zero`
     - `cfbrcIm_mod4_one_from_zero`
     - `cfbrcRe_mod4_two_from_one`
     - `cfbrcIm_mod4_two_from_one`
     - `cfbrcRe_mod4_three_from_two`
     - `cfbrcIm_mod4_three_from_two`
     - `cfbrcRe_mod4_four_from_three`
     - `cfbrcIm_mod4_four_from_three`
   - `DkMathTest/CFBRC.lean` に回帰例を追加:
     - `cfbrcRe_mod4_three_from_two`
     - `cfbrcIm_mod4_four_from_three`
     - `#print axioms cfbrcIm_mod4_four_from_three`
   - `DkMath/CFBRC/README.md` に
     - `cfbrcIm_mod4_four_from_three` の使用例を追加。
   - 実装中の型不一致（`simpa` の指数正規化差: `4*n` vs `n*4`）は、
     `calc` で明示変形して解消。
   - 検証:
     - `./lean-build.sh DkMath.CFBRC.TrigBridge.General` 成功
     - `./lean-build.sh DkMathTest.CFBRC` 成功
     - `./lean-build.sh DkMath.CFBRC` 成功
     - `./lean-build.sh DkMathTest` 成功
3. 結論: `cfbrcRe/Im` は `d mod 4` の各相で直接読める再帰形まで到達し、
   general `d` の手計算・自動化の両方で使いやすくなった。
4. 失敗事例:
   - 初期 `simpa` 実装で指数正規化の向き差（`4*n` と `n*4`）により型不一致が発生。
   - `calc` での明示書き換え（`d+1` 展開と位相項置換）に変更して安定化。
5. 備考:
   - 今回は再帰形の整備を優先し、閉形式（和の形）への変換は次段へ残した。
6. 次の課題:
   - `X = 0` / `Θ = 0` 断面で `cfbrcRe/Im` がどう簡約されるかの補題を追加する。
   - 必要なら `mod 4` 再帰を使って `cfbrcRe` の低次数（`d=3,4,5`）明示式を追加し、回帰テストへ固定する。

### 日時: 2026/03/20 02:18 JST: `X=0` / `Θ=0` 断面補題を追加

1. 目的: general `d` 補助の境界挙動を固定し、`cfbrcRe/Im` 再帰の端点を明確化する。
2. 内容:
   - `DkMath/CFBRC/TrigBridge/General.lean` に追加:
     - 実数冪の複素埋め込み補助:
       - `ofReal_pow_re`
       - `ofReal_pow_im`
     - `Θ = 0` 断面 (`d+1` 版):
       - `cfbrcR_succ_theta_zero`
       - `cfbrcRe_succ_theta_zero`
       - `cfbrcIm_succ_theta_zero`
     - `X = 0` 断面:
       - `cfbrcR_x_zero`
       - `cfbrcRe_x_zero`
       - `cfbrcIm_x_zero`
   - `DkMathTest/CFBRC.lean` に回帰例を追加:
     - `cfbrcRe_succ_theta_zero`
     - `cfbrcRe_x_zero`
     - `cfbrcIm_x_zero`
     - `#print axioms cfbrcRe_succ_theta_zero`
   - `DkMath/CFBRC/README.md` に `Θ=0` 断面の使用例を追加。
   - 検証:
     - `./lean-build.sh DkMath.CFBRC.TrigBridge.General` 成功
     - `./lean-build.sh DkMathTest.CFBRC` 成功
     - `./lean-build.sh DkMath.CFBRC` 成功
     - `./lean-build.sh DkMathTest` 成功
3. 結論: `X=0` / `Θ=0` の境界ケースが `General` に固定され、  
   `mod 4` 再帰と合わせて general `d` の追跡が端点まで閉じた。
4. 失敗事例:
   - `Complex.re ((X:ℂ)^d)` / `Complex.im ((X:ℂ)^d)` の `simp` 直接簡約が不安定。
   - 帰納法補助 `ofReal_pow_re/im` を導入して安定化。
5. 備考:
   - `Θ=0` は `d=0` 特異点 (`0^0`) を避けるため `d+1` 版で固定した。
6. 次の課題:
   - `mod 4` 再帰と断面補題を使って `cfbrcRe` / `cfbrcIm` の低次数明示式
     (`d=3,4,5`) を `General` または `Complex` に追加する。
   - 必要なら `Main` 側に「`d=2` は general 補題系の特殊化」という接続定理を追加する。

### 日時: 2026/03/20 02:38 JST: `d=3,4,5` 明示式の回帰固定と公開ドキュメント反映

1. 目的: 低次数明示式を `General` 実装に固定した上で、利用導線（テスト・README）を更新する。
2. 内容:
   - `DkMath/CFBRC/TrigBridge/General.lean`
     - 追加済み低次数補題を確定:
       - `cfbrcRe_three`, `cfbrcIm_three`
       - `cfbrcRe_four`, `cfbrcIm_four`
       - `cfbrcRe_five`, `cfbrcIm_five`
   - `DkMathTest/CFBRC.lean`
     - 上記 6 補題の `example` 回帰を追加。
     - 依存公理監視に `#print axioms cfbrcRe_five` を追加。
   - `DkMath/CFBRC/README.md`
     - general `d` 章に `cfbrcRe_five` / `cfbrcIm_five` の使用例を追加。
   - 検証:
     - `./lean-build.sh DkMath.CFBRC.TrigBridge.General` 成功
     - `./lean-build.sh DkMathTest.CFBRC` 成功
     - `./lean-build.sh DkMath.CFBRC` 成功
     - `./lean-build.sh DkMathTest` 成功
3. 結論: 低次数 (`d=3,4,5`) の実部・虚部明示式が、定理・回帰・README の 3 点で整合した状態になった。
4. 失敗事例:
   - 特になし（追加分は既存補題への `simpa` 回帰で安定）。
5. 備考:
   - 全体ビルド時の `ABC021` `sorry` 警告は既知の別件であり、今回変更範囲の退行ではない。
6. 次の課題:
   - `d=6,7` など次段の低次数明示式を同様に追加し、`mod 4` 再帰との対応を強化する。
   - `Main` 側で `d=2` が general 補題の特化であることを明示する接続補題を追加する。

### 日時: 2026/03/20 02:42 JST: `d=6,7` 明示式を追加し低次数帯を拡張

1. 目的: `d=3,4,5` に続き、低次数明示式を `d=6,7` まで拡張して手計算比較を容易にする。
2. 内容:
   - `DkMath/CFBRC/TrigBridge/General.lean` に追加:
     - `cfbrcRe_six`, `cfbrcIm_six`
     - `cfbrcRe_seven`, `cfbrcIm_seven`
   - `DkMathTest/CFBRC.lean` に回帰例を追加:
     - `cfbrcRe/Im` の `d=6,7` 明示式 `example`。
     - 依存公理監視に `#print axioms cfbrcIm_seven` を追加。
   - `DkMath/CFBRC/README.md` の general `d` 章へ
     - `cfbrcRe_seven` / `cfbrcIm_seven` の使用例を追加。
   - 検証:
     - `./lean-build.sh DkMath.CFBRC.TrigBridge.General`
     - `./lean-build.sh DkMathTest.CFBRC`
     - `./lean-build.sh DkMath.CFBRC`
     - `./lean-build.sh DkMathTest`
3. 結論: 低次数明示式の整備範囲が `d=7` まで拡張され、
   `mod 4` 再帰で追った結果を具体式で突き合わせる導線が強化された。
4. 失敗事例:
   - 特になし（`simp` + `ring` で安定に導出可能）。
5. 備考:
   - `d=6,7` でも `(iΘ)^d` 減算により定数項（純 `Θ` 項）が消える形が維持される。
6. 次の課題:
   - `Main` に「`d=2` は general 補題（`cfbrcRe_two` 相当）から得られる」接続補題を追加する。
   - 必要なら `d=8` 以降は再帰ベース自動化（`linarith`/`ring_nf` 連携）に寄せる。

### 日時: 2026/03/20 02:47 JST: `Main` に `d=2` の general 特化接続を追加

1. 目的: `d=2` の橋定理が `Complex` 専用補題だけでなく、`General` 再帰補題系の特殊化としても成立することを明示する。
2. 内容:
   - `DkMath/CFBRC/TrigBridge/Main.lean`
     - `import DkMath.CFBRC.TrigBridge.General` を追加。
     - `General` 由来の接続補題を追加:
       - `cfbrcRe_two_from_general`
       - `cfbrcIm_two_from_general`
       - `cfbrc_two_re_via_general`
       - `cfbrc_two_im_via_general`
       - `cfbrc_two_re_polar_via_general`
     - 既存の主定理
       - `body2_eq_re_cfbrc2`
       - `factor_eq_re_cfbrc2`
       の証明で `cfbrc_two_re_polar_via_general` を利用する形へ変更。
   - `DkMathTest/CFBRC.lean`
     - `cfbrc_two_re_via_general` / `cfbrc_two_im_via_general` の回帰 `example` を追加。
     - 依存公理監視に `#print axioms cfbrc_two_re_via_general` を追加。
   - `DkMath/CFBRC/README.md`
     - `d=2` 使用例セクションに `cfbrc_two_re_via_general` の例を追加。
   - 検証:
     - `./lean-build.sh DkMath.CFBRC.TrigBridge.Main` 成功
     - `./lean-build.sh DkMathTest.CFBRC` 成功
     - 追検証で全体:
       - `./lean-build.sh DkMath.CFBRC`
       - `./lean-build.sh DkMathTest`
3. 結論: `d=2` の橋は `Main <- General` の導線でも説明可能となり、
   `d=2` 特化と general `d` 補題系の接続がコード上で明示化された。
4. 失敗事例:
   - 特になし（`cfbrcRe_succ'` / `cfbrcIm_succ'` の `d=1` 代入で直ちに導出できた）。
5. 備考:
   - `Complex.lean` 側の `cfbrc_two_re` / `cfbrc_two_im` は残し、互換性を維持した。
6. 次の課題:
   - `d=8` 以降を手作業明示式で増やすか、再帰ベース自動生成（または補題テンプレート）へ移行するか方針を決める。
   - 必要なら `cfbrc_two_im_polar` 側も `via_general` 版を `Main` で利用する定理を追加する。

### 日時: 2026/03/20 02:55 JST: `cfbrc_two_im_polar` の `via_general` 導線を追加

1. 目的: `d=2` の虚部極座標公式も、`General` 再帰補題系から導く接続を `Main` に揃える。
2. 内容:
   - `DkMath/CFBRC/TrigBridge/Main.lean`
     - 追加:
       - `cfbrc_two_im_polar_via_general`
         - `cfbrc_two_im_via_general` を極座標代入して
           `Im (cfbrcR 2 (a cos φ) (a sin φ)) = 2 a^2 sin φ cos φ` を導出。
   - `DkMathTest/CFBRC.lean`
     - 回帰 `example` を追加:
       - `cfbrc_two_im_polar_via_general`
     - 依存公理監視に `#print axioms cfbrc_two_im_polar_via_general` を追加。
   - `DkMath/CFBRC/README.md`
     - `d=2` 使用例セクションに `cfbrc_two_im_polar_via_general` を追記。
   - 検証:
     - `./lean-build.sh DkMath.CFBRC.TrigBridge.Main`
     - `./lean-build.sh DkMathTest.CFBRC`
     - `./lean-build.sh DkMath.CFBRC`
     - `./lean-build.sh DkMathTest`
3. 結論: `d=2` の実部・虚部ともに `Main <- General` の導線が揃い、
   `Complex` 専用補題に依存しない説明経路が完成した。
4. 失敗事例:
   - 特になし（`rw` と `ring` で直ちに整合）。
5. 備考:
   - 既存の `Complex.cfbrc_two_im_polar` は保持して互換性を維持。
6. 次の課題:
   - `d=8` 以降の明示式整備を継続するか、再帰式主体の運用に寄せるかを決める。
   - 必要なら `d=2` で `via_general` と `Complex` 版の同値を示す補題を追加する。

### 日時: 2026/03/20 03:27 JST: `d=8` 以降向けの再帰テンプレート化と `d=2` 両経路回帰

1. 目的:
   - `d=8` 以降を手書き展開に頼らず、再帰テンプレートで機械的に進められる形へ移行する。
   - あわせて `d=2` について `via_general` と `Complex` 直補題の両経路を回帰で固定する。
2. 内容:
   - `DkMath/CFBRC/TrigBridge/General.lean`
     - 再帰テンプレートを追加:
       - `cfbrcRe_succ_template`
       - `cfbrcIm_succ_template`
     - テンプレート利用例として `d=8` 明示式を追加:
       - `cfbrcRe_eight_from_template`
       - `cfbrcIm_eight_from_template`
   - `DkMathTest/CFBRC.lean`
     - テンプレートの一般形 (`Re/Im`) を `example` で回帰固定。
     - `d=8` 明示式 (`cfbrcRe/Im_eight_from_template`) を回帰固定。
     - `d=2` について
       - `via_general` 経路 (`cfbrc_two_re_via_general`, `cfbrc_two_im_via_general`,
         `cfbrc_two_im_polar_via_general`)
       - `Complex` 経路 (`cfbrc_two_re`, `cfbrc_two_im`, `cfbrc_two_im_polar`)
       を並行回帰として追加。
     - 依存公理監視に:
       - `#print axioms cfbrcRe_succ_template`
       - `#print axioms cfbrcRe_eight_from_template`
       - `#print axioms cfbrc_two_re`
       - `#print axioms cfbrc_two_im_polar`
       を追加。
   - `DkMath/CFBRC/README.md`
     - `General` の説明に「再帰テンプレート」を追記。
     - Usage へテンプレート利用例と `d=8` 例を追記。
     - `d=2` セクションへ `cfbrc_two_re`（Complex 経路）例を追加。
   - 検証:
     - `./lean-build.sh DkMath.CFBRC.TrigBridge.General` 成功
     - `./lean-build.sh DkMathTest.CFBRC` 成功
     - `./lean-build.sh DkMath.CFBRC` 成功
     - `./lean-build.sh DkMathTest` 成功
3. 結論:
   - `d=8` 以降は「前段の式 + 位相項評価」を渡すテンプレートで拡張可能になり、
     明示式追加の実装負荷を下げられる状態になった。
   - `d=2` は `via_general` / `Complex` の両ルートが回帰上で同時に維持される。
4. 失敗事例:
   - 特になし（テンプレート適用は `simpa` + `ring` で安定）。
5. 備考:
   - `d=8` は手書き二項展開ではなく、`d=7` 明示式と `mod 4` 位相補題から導出した。
6. 次の課題:
   - テンプレートを使った `d=9,10` の段階的追加（必要なら自動化マクロ化）を検討する。
   - `mod 4` ごとの位相評価投入をまとめる補助テンプレート（4ケース）を追加する。

### 日時: 2026/03/20 03:37 JST: テンプレート運用で `d=9,10` まで拡張

1. 目的:
   - `d=8` 以降を再帰テンプレート主体で伸ばす方針を実運用し、
     `d=9,10` 明示式まで機械的に到達できることを確認する。
2. 内容:
   - `DkMath/CFBRC/TrigBridge/General.lean`
     - 追加（テンプレート導出）:
       - `cfbrcRe_nine_from_template`
       - `cfbrcIm_nine_from_template`
       - `cfbrcRe_ten_from_template`
       - `cfbrcIm_ten_from_template`
     - 位相項は `mod 4` 補題（`n=2`）を使用:
       - `Re((iΘ)^8)=Θ^8`, `Im((iΘ)^8)=0`
       - `Re((iΘ)^9)=0`, `Im((iΘ)^9)=Θ^9`
   - `DkMathTest/CFBRC.lean`
     - `d=9,10` の `cfbrcRe/Im` 回帰 `example` を追加。
     - 依存公理監視に `#print axioms cfbrcIm_ten_from_template` を追加。
   - `DkMath/CFBRC/README.md`
     - general `d` 使用例へ `d=9,10` 明示式を追記。
   - 検証:
     - `./lean-build.sh DkMath.CFBRC.TrigBridge.General` 成功
     - `./lean-build.sh DkMathTest.CFBRC` 成功
     - `./lean-build.sh DkMath.CFBRC` 成功
     - `./lean-build.sh DkMathTest` 成功
3. 結論:
   - `d=8` 以降の拡張は「前次数明示式 + 位相評価 + テンプレート」で進める実装パターンが確立した。
   - `d=10` まで同一パターンで到達できることを確認した。
4. 失敗事例:
   - 初回追加時に long-line 警告が発生（`General` と `DkMathTest` の長い式行）。
   - 改行整形で解消し、警告なし（変更範囲内）でビルド通過。
5. 備考:
   - 既知の `ABC021` `sorry` 警告は継続（今回変更範囲外）。
6. 次の課題:
   - `d=11,12` も同テンプレートで追加し、奇偶・`mod 4` の切替パターンをさらに固定する。
   - `mod 4` 位相投入まで吸収する高位テンプレート（`phaseRe/phaseIm` 自動選択）を検討する。

### 日時: 2026/03/20 03:44 JST: テンプレート運用を `d=11,12` へ拡張

1. 目的:
   - `d=9,10` で確立した再帰テンプレート運用を継続し、
     `d=11,12` 明示式まで同一パターンで到達する。
2. 内容:
   - `DkMath/CFBRC/TrigBridge/General.lean`
     - 追加:
       - `cfbrcRe_eleven_from_template`
       - `cfbrcIm_eleven_from_template`
       - `cfbrcRe_twelve_from_template`
       - `cfbrcIm_twelve_from_template`
     - 位相項評価:
       - `Re((iΘ)^10) = -Θ^10`, `Im((iΘ)^10) = 0`
       - `Re((iΘ)^11) = 0`, `Im((iΘ)^11) = -Θ^11`
       を `mod 4` 補題 (`n=2`) で投入。
   - `DkMathTest/CFBRC.lean`
     - `d=11,12` の `cfbrcRe/Im` 回帰 `example` を追加。
     - 依存公理監視に `#print axioms cfbrcIm_twelve_from_template` を追加。
   - `DkMath/CFBRC/README.md`
     - general `d` 使用例へ `d=11,12` を追記。
   - 検証:
     - `./lean-build.sh DkMath.CFBRC.TrigBridge.General` 成功
     - `./lean-build.sh DkMathTest.CFBRC` 成功
     - `./lean-build.sh DkMath.CFBRC` 成功
     - `./lean-build.sh DkMathTest` 成功
3. 結論:
   - `d=12` まで、`前次数明示式 + 位相評価 + テンプレート` の
     単一手順で拡張可能なことを確認。
4. 失敗事例:
   - 特になし（追加分は `simpa` + `ring` で安定）。
5. 備考:
   - 既知の `ABC021` `sorry` 警告は継続（今回変更範囲外）。
6. 次の課題:
   - `d=13,14` へ継続し、テンプレート適用の反復性をさらに確認する。
   - `phaseRe/phaseIm` を `mod 4` から自動選択する高位テンプレートの設計を進める。

### 日時: 2026/03/20  3:57 JST: choose_phase

**事前調査結果**

1. `choose` 展開の実装パターンは既に `CosmicFormula` 側にあり、`add_pow` + `Finset.sum_range_succ'` で安定して証明されています。  
   [CosmicFormulaBinom.lean:77](/lean/dk_math/DkMath/CosmicFormula/CosmicFormulaBinom.lean:77)  
   [CosmicFormulaBinom.lean:280](/lean/dk_math/DkMath/CosmicFormula/CosmicFormulaBinom.lean:280)

2. `Complex` の和の実部・虚部は `Complex.re_sum` / `Complex.im_sum` が使えます。  
   [Mathlib Data/Complex/BigOperators.lean:44](/lean/dk_math/.lake/packages/mathlib/Mathlib/Data/Complex/BigOperators.lean:44)

3. `add_pow` の形は  
   `(x + y)^n = ∑ m∈range (n+1), x^m * y^(n-m) * choose n m` です。  
   このまま `cfbrcR = (X+iΘ)^d - (iΘ)^d` へ接続できます。  
   [Mathlib Data/Nat/Choose/Sum.lean:76](/lean/dk_math/.lake/packages/mathlib/Mathlib/Data/Nat/Choose/Sum.lean:76)

4. 現在の `TrigBridge.General` は再帰・位相評価が十分に揃っており、閉形式証明の土台は完成済みです。  
   [General.lean:166](/lean/dk_math/DkMath/CFBRC/TrigBridge/General.lean:166)  
   [General.lean:186](/lean/dk_math/DkMath/CFBRC/TrigBridge/General.lean:186)

5. `Nat.cast_choose` は `DivisionSemiring` 要件の式なので主証明では使いません。`(Nat.choose d k : ℂ)` / `: ℝ` の直接キャストで進める方が安全です。

**実装計画（Nat.choose 昇格）**

1. 新規ファイル `DkMath/CFBRC/TrigBridge/ClosedForm.lean` を追加する。  
   `General.lean` は再帰エンジン、`ClosedForm.lean` は choose 主定理に分離。

2. まず複素閉形式を定義する（ルートA）。  
   `cfbrcClosed (d X Θ)` を `Finset.range d` の和で定義し、`cfbrcR d X Θ = cfbrcClosed d X Θ` を証明する。  
   証明は `add_pow` と `Finset.sum_range_succ'` ベース。

3. 次に実部・虚部の閉形式（raw版）を定義する。  
   `cfbrcReClosedRaw` / `cfbrcImClosedRaw` を `j` 走査の単一和で定義し、偶奇は `if` で処理する。  
   ここで `Complex.re_sum` / `Complex.im_sum` と既存の `pure_phase_pow_*` 補題を使って  
   `cfbrcRe = cfbrcReClosedRaw`, `cfbrcIm = cfbrcImClosedRaw` を先に確定する。

4. その後に見た目の良い本命 API へ昇格する。  
   `m` 走査（`2m`, `2m+1`）の `cfbrcReClosed` / `cfbrcImClosed` を定義し、raw版との同値を示す。  
   ユーザー提示の式を最終形として公開。

5. 低次数補題の役割を変更する。  
   `d=3..12` は削除せず「回帰・可読サンプル」に残し、主APIは choose 閉形式へ移す。

6. 反映対象。  
   `DkMathTest/CFBRC.lean` に closed form 回帰を追加。  
   `README.md` を choose 主体へ更新。  
   `CFBRC_Implements_History.md` に今回方針と進捗を記録。

7. 検証コマンド。  
   `./lean-build.sh DkMath.CFBRC.TrigBridge.ClosedForm`  
   `./lean-build.sh DkMathTest.CFBRC`  
   `./lean-build.sh DkMath.CFBRC`  
   `./lean-build.sh DkMathTest`

この計画で、次ターンは `ClosedForm.lean` 作成と `cfbrcR = cfbrcClosed` の証明から着手します。

### 日時: 2026/03/20 04:05 JST: `ClosedForm` 第1段（複素 choose 形 + Re/Im raw）を実装

1. 目的:
   - `Nat.choose` 昇格の初手として、`cfbrcR` の複素 closed form と
     `cfbrcRe/Im` の raw closed form を定義・同一化する。
2. 内容:
   - 新規ファイル `DkMath/CFBRC/TrigBridge/ClosedForm.lean` を追加。
   - 追加定義:
     - `cfbrcClosed`（複素 choose 和）
     - `cfbrcReClosedRaw`
     - `cfbrcImClosedRaw`
   - 追加定理:
     - `cfbrcR_eq_cfbrcClosed`
     - `cfbrcRe_eq_cfbrcReClosedRaw`
     - `cfbrcIm_eq_cfbrcImClosedRaw`
   - 実装要点:
     - `add_pow` + `Finset.sum_range_succ'` で `k=0` 項を分離して
       `(X+iΘ)^d-(iΘ)^d` を `range d` の和へ落とす。
     - `Complex.re_sum` / `Complex.im_sum` と
       `ofReal_pow_re/im` を使って項ごとに `Re/Im` を抽出。
   - 公開入口更新:
     - `DkMath/CFBRC.lean` に `import DkMath.CFBRC.TrigBridge.ClosedForm` を追加。
   - 回帰・ドキュメント:
     - `DkMathTest/CFBRC.lean` に
       `cfbrcR_eq_cfbrcClosed` / `cfbrcRe/Im_eq_*Raw` の `example` と
       `#print axioms` 追加。
     - `DkMath/CFBRC/README.md` に
       `TrigBridge.ClosedForm` のモジュール説明と使用例を追加。
   - 検証:
     - `./lean-build.sh DkMath.CFBRC.TrigBridge.ClosedForm` 成功
     - `./lean-build.sh DkMathTest.CFBRC` 成功
     - `./lean-build.sh DkMath.CFBRC` 成功
     - `./lean-build.sh DkMathTest` 成功
3. 結論:
   - choose 形式への移行は定義・同一化の第1段が完了。
   - 既存の低次数・テンプレート資産と共存したまま、closed form 系 API の導線を確立した。
4. 失敗事例:
   - 初回実装で `∑ k in ...` 記法が環境非対応（`∑ k ∈ ...` へ修正）。
   - `simp` が係数約分を試みて分岐ゴールを生成したため、
     `Complex.mul_re/im` の手動展開 + `ofReal_pow_re/im` + `ring` へ変更して安定化。
5. 備考:
   - 既知の `ABC021` `sorry` 警告は継続（今回変更範囲外）。
6. 次の課題:
   - `cfbrcReClosed` / `cfbrcImClosed`（偶奇分離版）を `Nat.choose` 形式で定義する。
   - `cfbrcRe/ImClosedRaw` との同値を証明し、最終 API を choose 版へ昇格する。

### 日時: 2026/03/20 04:31 JST: `ClosedForm` 第2段（偶奇分離 choose 形）を実装

1. 目的:
   - `Raw` 形式で止まっていた `Re/Im` 閉形式を、`2m` / `2m+1` の
     `Nat.choose` 主形式へ昇格する。
2. 内容:
   - `DkMath/CFBRC/TrigBridge/ClosedForm.lean` を拡張。
   - 追加定義:
     - `cfbrcReClosed`
     - `cfbrcImClosed`
   - 追加定理:
     - `cfbrcReClosedRaw_eq_cfbrcReClosed`
     - `cfbrcImClosedRaw_eq_cfbrcImClosed`
     - `cfbrcRe_eq_cfbrcReClosed`
     - `cfbrcIm_eq_cfbrcImClosed`
   - 補助補題（private）:
     - `Raw` 和の添字反転（`sum_range_reflect` + `Nat.choose_symm`）
     - 純位相 `Re/Im` の `if Even/Odd` 形
     - `if Even/Odd` 和を `range ((d+1)/2)` / `range (d/2)` に圧縮する一般補題
   - `DkMathTest/CFBRC.lean` に以下の回帰を追加:
     - `Raw -> Closed` 同値
     - `cfbrcRe/Im -> Closed` 同値
     - `#print axioms cfbrcRe_eq_cfbrcReClosed`
     - `#print axioms cfbrcIm_eq_cfbrcImClosed`
   - `DkMath/CFBRC/README.md` を更新:
     - `TrigBridge.ClosedForm` の説明を `Raw + 偶奇分離` へ拡張
     - 新同値の使用例を追加
3. 結論:
   - `choose` 昇格の第2段を完了。
   - `cfbrcRe/Im` は最終的に `Nat.choose` の偶奇分離主形式へ直接接続できる状態になった。
4. 失敗事例:
   - `sum_odd_if_eq` の even case で `simp` が進まない箇所があり、
     `¬ Odd (n+n)` を明示補題化して解消。
5. 備考:
   - 既知の `ABC021` `sorry` 警告は継続（今回変更範囲外）。
6. 次の課題:
   - `cfbrcClosed`（複素和）から `cfbrcReClosed` / `cfbrcImClosed` への直結 API を整備する。
   - 必要に応じて低次数補題（`d=3..12`）を `Closed` 形式経由の回帰へ寄せる。

### 日時: 2026/03/20 04:45 JST: `cfbrcClosed -> cfbrcRe/ImClosed` 直結補題を追加

1. 目的:
   - `cfbrcClosed` を起点に、実部・虚部の最終閉形式へ直接到達する API を追加する。
2. 内容:
   - `DkMath/CFBRC/TrigBridge/ClosedForm.lean` に以下を追加:
     - `cfbrcClosed_re_eq_cfbrcReClosed`
     - `cfbrcClosed_im_eq_cfbrcImClosed`
   - 証明方針:
     - `cfbrcR_eq_cfbrcClosed` で `cfbrcClosed` を `cfbrcR` へ戻し、
       既存の `cfbrcRe/Im_eq_cfbrcRe/ImClosed` を合成。
   - `DkMathTest/CFBRC.lean`:
     - 上記2補題の `example` を追加。
     - `#print axioms cfbrcClosed_re_eq_cfbrcReClosed`
     - `#print axioms cfbrcClosed_im_eq_cfbrcImClosed`
   - `DkMath/CFBRC/README.md`:
     - `Complex.re/im (cfbrcClosed ...)` から
       `cfbrcRe/ImClosed` へ直接接続する使用例を追記。
3. 結論:
   - `cfbrcClosed` の利用者は、`Re/Im` を取った時点で
     そのまま偶奇分離 `Nat.choose` 主形式へ落とせるようになった。
4. 失敗事例:
   - 特になし（既存同値の合成で安定）。
5. 備考:
   - 既知の `ABC021` `sorry` 警告は継続（今回変更範囲外）。
6. 次の課題:
   - 低次数回帰（`d=3..12`）を `cfbrcClosed_re/im_eq_cfbrcRe/ImClosed` 経由にも寄せる。

### 日時: 2026/03/20 04:56 JST: 低次数回帰（`d=3..12`）を `cfbrcClosed` 経由へ寄せた

1. 目的:
   - 既存の `d=3..12` 明示式回帰を、
     `Complex.re/im (cfbrcClosed d X Θ)` からも同じ式で検証できる形にする。
2. 内容:
   - `DkMathTest/CFBRC.lean` に private 補助補題を追加:
     - `cfbrcClosed_re_eq_cfbrcRe_via_closed`
     - `cfbrcClosed_im_eq_cfbrcIm_via_closed`
   - これらは
     - `cfbrcClosed_re/im_eq_cfbrcRe/ImClosed`
     - `cfbrcRe/Im_eq_cfbrcRe/ImClosed`
     を合成して、`cfbrcClosed` の `Re/Im` を `cfbrcRe/Im` に戻す橋として使う。
   - `d=3..12` について、以下の回帰 `example` を追加:
     - `Complex.re (cfbrcClosed d X Θ) =` 既存の明示式
     - `Complex.im (cfbrcClosed d X Θ) =` 既存の明示式
3. 結論:
   - 低次数回帰は
     - 旧経路（`cfbrcRe/Im d`）
     - 新経路（`cfbrcClosed -> Re/Im -> cfbrcRe/ImClosed`）
     の両方で固定された。
4. 失敗事例:
   - 特になし（既存低次数補題を `simpa` で再利用できた）。
5. 備考:
   - 既知の `ABC021` `sorry` 警告は継続（今回変更範囲外）。
6. 次の課題:
   - 必要なら `d=3..12` の `cfbrcRe/ImClosed d X Θ` そのものを主語にした回帰も追加する。

### 日時: 2026/03/20 05:11 JST: `cfbrcRe/ImClosed` 主語の低次数回帰 + README 役割明確化

1. 目的:
   - low-degree window を closed API 側へ寄せ切るため、
     `cfbrcReClosed` / `cfbrcImClosed` を主語にした `d=3..12` 回帰を追加する。
   - README 上で `General` と `ClosedForm` の役割分担を明示する。
2. 内容:
   - `DkMathTest/CFBRC.lean`:
     - private 補助補題を追加:
       - `cfbrcReClosed_eq_cfbrcRe_via_api`
       - `cfbrcImClosed_eq_cfbrcIm_via_api`
     - `d=3..12` について
       - `cfbrcReClosed d X Θ = ...`
       - `cfbrcImClosed d X Θ = ...`
       の回帰 `example` を追加。
   - `DkMath/CFBRC/README.md`:
     - `TrigBridge.General` を「証明エンジン / 内部基盤」と明記。
     - `TrigBridge.ClosedForm` を「主API」と明記。
     - Quick Start に
       `import DkMath.CFBRC.TrigBridge.ClosedForm`
       （general `d` 利用時の推奨）を追記。
3. 結論:
   - 低次数回帰は
     - `cfbrcRe/Im`
     - `Complex.re/im (cfbrcClosed ...)`
     - `cfbrcRe/ImClosed`
     の3経路で固定され、closed API 側への寄せが完了した。
4. 失敗事例:
   - 特になし（既存低次数補題を `simpa` 再利用）。
5. 備考:
   - 既知の `ABC021` `sorry` 警告は継続（今回変更範囲外）。
6. 次の課題:
   - 必要なら `cfbrcClosed` の和定義そのもの（`Nat.choose` 係数列）に対する係数回帰を追加する。

### 日時: 2026/03/20 05:24 JST: `cfbrcClosed` の係数列回帰（`d=3..12`）を追加

1. 目的:
   - `cfbrcClosed` の和定義そのものに対し、
     低次数で `Nat.choose` 係数列が正しく並ぶことを回帰で固定する。
2. 内容:
   - `DkMathTest/CFBRC.lean` に
     `cfbrcClosed d X Θ = Σ_{j=1..d} (d choose j) X^j (iΘ)^(d-j)`
     の具体展開を `d=3..12` まで追加。
   - 係数列（`choose` 行）を明示:
     - `d=8`: `8,28,56,70,56,28,8,1`
     - `d=10`: `10,45,120,210,252,210,120,45,10,1`
     - `d=12`: `12,66,220,495,792,924,792,495,220,66,12,1`
   - 各証明は同一テンプレート:
     - `simp [cfbrcClosed, Finset.sum_range_succ]`
     - `ring_nf`
     - `norm_num [Nat.choose]`
3. 結論:
   - `cfbrcClosed` の係数列回帰が入り、
     closed API の低次数検証は
     - `Re/Im` 明示式回帰
     - `cfbrcClosed` 係数列回帰
     の2面で固定された。
4. 失敗事例:
   - 初期案で `simp` の引数を増やしすぎると heartbeat timeout が発生。
   - `simp` を最小化し、`ring_nf` と `norm_num [Nat.choose]` で安定化。
5. 備考:
   - 既知の `ABC021` `sorry` 警告は継続（今回変更範囲外）。
6. 次の課題:
   - 必要なら設計書側（TriPerm Lean Design）にも
     `ClosedForm` 主API・係数列回帰の位置づけを反映する。

### 日時: 2026/03/20 05:35 JST: TriPerm Lean Design に `ClosedForm` 主APIと係数列回帰の位置づけを反映

1. 目的:
   - 設計書側の記述を現状実装（`General`/`ClosedForm`/回帰構成）に同期する。
2. 内容:
   - `DkMath/CFBRC/docs/CFBRC_TriPerm_Lean_Design.md` を更新:
     - 推奨ファイル構成に
       - `TrigBridge/General.lean`
       - `TrigBridge/ClosedForm.lean`
       - `DkMathTest/CFBRC.lean`
       を追加。
     - 役割分担を明記:
       - `General` = 証明エンジン
       - `ClosedForm` = 主API
     - 回帰位置づけを明記:
       - `d=3..12` の 3 経路回帰
       - `cfbrcClosed` の `Nat.choose` 係数列回帰
     - 「一段先の一般化設計」を現状反映へ更新し、
       将来の抽象化（係数列一般補題）を次手として整理。
3. 結論:
   - TriPerm Lean Design は、現行コードベースの整理方針
     （`ClosedForm` 主API・`General` 証明エンジン）と一致した。
4. 失敗事例:
   - 特になし（ドキュメント更新のみ）。
5. 備考:
   - 今回はドキュメント反映のみで Lean コード差分はなし。
6. 次の課題:
   - 必要なら `CFBRC_Triangular Permutation.md` 側にも同じ役割分担を要約反映する。

### 日時: 2026/03/20 05:49 JST: 係数列回帰を `Nat.choose` 一般補題へ接続して自動化

1. 目的:
   - 手書き係数列回帰の証明手順を一般補題へ接続し、回帰追加時の作業を自動化する。
2. 内容:
   - `DkMath/CFBRC/TrigBridge/ClosedForm.lean`:
     - `cfbrcClosed_choose_row` を追加。
     - `cfbrcClosed` を
       `∑ (d.choose (k+1)) * X^(k+1) * (iΘ)^(d-1-k)`
       の一般形として明示。
   - `DkMathTest/CFBRC.lean`:
     - 係数列回帰セクションにタクティックマクロ
       `cfbrc_closed_coeff`
       を導入。
     - 既存 `d=3..12` の各回帰証明を
       - `rw [cfbrcClosed_choose_row]`
       - `simp [Finset.sum_range_succ]`
       - `ring_nf` / `norm_num [Nat.choose]`
       の共通処理に一本化。
3. 結論:
   - 係数列回帰は手書き展開依存から脱し、
     `Nat.choose` 行の一般補題経由で機械的に再現できる形へ整理できた。
4. 失敗事例:
   - `d=3` のケースは `simp` だけで閉じるため、
     追加タクティックが「No goals」になる場面があった。
   - マクロ内を `try` で保護して解消。
5. 備考:
   - 既知の `ABC021` `sorry` 警告は継続（今回変更範囲外）。
6. 次の課題:
   - 必要なら `cfbrcClosed_choose_row` から `Finset.Icc` 形式への添字変換補題を追加する。
