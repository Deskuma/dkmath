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
