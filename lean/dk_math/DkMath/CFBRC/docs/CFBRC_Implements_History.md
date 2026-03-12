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
