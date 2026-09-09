# 検証メモ

## 001: 調査

- 作業場所: `/home/deskuma/develop/lean/dkmath`。開始時の `git status --short` は空。
- 使用 toolchain: `leanprover/lean4:v4.32.2`。
- 指定の `logs/__dkmath-all.lean.txt.gz` を `zgrep` で検索し、平方窓の小素数因子定理と有限容量からの既存条件付き閉包を確認。その後に実ソースを確認。
- 再利用候補: `Nat.minFac_sq_le_self`, `Nat.minFac_prime`, `Nat.minFac_dvd`, `Nat.chineseRemainderOfFinset`, `primitiveConservationKernel_dichotomy_of_le_fine_squareBody`, `GNPositiveRepresentation.prime_degree_constraints`。
- 注意: 既存の Legendre 向け容量超過定理も入力に容量の不等式を要する。Goldbach の独立した生存証明とはならない。

## 002: Basic / Obstruction

- `./lean-build.sh DkMath.NumberTheory.Goldbach.Basic`: 成功。
- `Obstruction` 初回: 量化命題に対する `tauto` と `not_and` の展開形が不一致。明示的な witness の取り出しと構成に修正。
- `./lean-build.sh DkMath.NumberTheory.Goldbach.Obstruction`: 修正後成功。
- `sorry` による穴埋めは使用せず、定理の意味と仮定を保った局所的な修正を実施。

## 003: PrimeWorld / Capacity / Conservation / Signature

- `PrimeWorld` 初回: implicit な素数の束縛、`n=-n` を `simp` に渡した再帰、scoped `on` 記法を局所修正。
- `./lean-build.sh DkMath.NumberTheory.Goldbach.PrimeWorld`: 成功。
- `Capacity` 初回ビルドは成功したが `push_neg` の非推奨警告あり。`push Not` に変更して再検証。
- `./lean-build.sh DkMath.NumberTheory.Goldbach.Conservation DkMath.NumberTheory.Goldbach.Signature DkMath.NumberTheory.Goldbach.Capacity`: 成功、当該出力に警告なし。
- 数学的な条件変更はなし。自然数の減算や endpoint 例外は明示条件のまま維持。

## 004: Cardinality / Limitations

- CRT 単射・全射を `Finset.card_bij` で構成。dependent subtype の積は `Finset.prod_coe_sort` を明示適用して解決。
- 有限集合を含む計算は通常の `decide` では展開が停止したため `decide +kernel` を使用。外部実行結果の信頼や新規 axiom は導入しない。
- `./lean-build.sh DkMath.NumberTheory.Goldbach.Cardinality DkMath.NumberTheory.Goldbach.Limitations`: 成功。
- 追加の区間容量上界では、除法の単調性を型付き fact で使用し、商座標の射影等式も型を明示して局所修正。

## 005: 公開面・最終検証

- conventional な偶数ターゲットとの同値と、固定中心の有限 `Decidable` instance を追加。
- 剰余・商座標への単射から、各素数の区間障害数の具体的上界を証明。射影の目的式には `change` で型を明示。
- `Limitations` に既存 PCK の old-generated 分岐が合成数 `6` を含む証明を追加。
- `DkMath.NumberTheory.Goldbach` facade、root import、回帰コードを追加。
- 回帰の平方端点は admissible 条件も検査する `n=14,u=11`、端点 `3,25` に整えた。
- focused build は成功・警告なし。`2≤n≤100` の有限範囲証明は `decide +kernel` で検査。
- root build は成功。既存研究モジュールの `sorry` 警告のみ 5 件。
- 96 件の全名前付き owner 宣言と有限範囲定理、合計 97 件を `#print axioms` で監査。標準の 3 公理以外の依存なし。
- ビルドログと監査出力の要約および証拠ファイルは `report-005.md` を参照。
