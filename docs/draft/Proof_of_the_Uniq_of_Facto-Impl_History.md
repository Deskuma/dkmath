# Proof of the Uniqueness of Factorization - Implements History

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
