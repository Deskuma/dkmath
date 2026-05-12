# History

cid: 69fcadff-fc5c-83a2-bd6b-5657e7fcf58a

- 時刻の打刻は `date` コマンドを使用して時間(時分秒)まで正確に行うこと。
- 新規履歴は **ファイル末尾** に追加すること。

## History Log

Archive

過去ログは、以下にアーカイブしてあります。

- History
  - [Archive 001](History-001.md)

## Note

タイムスタンプの打刻は `date` コマンドを使用して、実際の日時を正確に記録してください。例: `date "+%Y/%m/%d %H:%M JST"` など。

※コミット時間がより正確であり、異なる場合は、コミット時間を優先とする。

## Template

### 日時: `タイムスタンプ date コマンドを使用して年月日時分まで` JST (作業概要の見出し)

1. 目的:
   - （内容）
2. 実施:
   - （内容）
3. 結論:
   - （内容）
4. 検証:
   - （内容）
5. 失敗事例:
   - （内容）
6. 次の課題:
   - （内容）

---

### 日時: 2026/05/13 07:09 JST (Phase-R009 positive real finite product lemmas)

1. 目的:
   - `review/review-067.md` の提案に従い、`RealLogBudget` の product route へ進む前段として、実数値の正の有限積に関する小補題を追加する。
   - 自然数版や prime-power route へ戻る前に、実数版の `prod` / `log` 部分だけを安定させる。
2. 実施:
   - `RealLog.lean` に `real_finset_prod_pos_of_pos` を追加し、index 上で全項正なら有限積も正であることを示した。
   - `real_log_prod_eq_sum_log_of_pos` を追加し、正の実数有限積に対して `Real.log (I.prod a) = I.sum (fun i => Real.log (a i))` を示した。
   - 後続の product-budget-to-log-budget 証明で使いやすい向きとして、`real_sum_log_eq_log_prod_of_pos` を追加した。
3. 結論:
   - product route のうち、`sum log = log prod` と積の正性の土台が no-sorry で閉じた。
   - 次は `Phase-R010` として、`I.prod a ≤ N` から `I.sum log(a i) ≤ log N` を得る合成補題へ進める。
4. 検証:
   - `cd lean/dk_math && ./lean-build.sh DkMath.NumberTheory.PrimitiveSet.RealLog`
   - `cd lean/dk_math && ./lean-build.sh DkMath.NumberTheory.PrimitiveSet`
   - いずれも build 成功。
   - `rg "\\bsorry\\b|\\badmit\\b|^axiom\\b" lean/dk_math/DkMath/NumberTheory/PrimitiveSet lean/dk_math/DkMath/NumberTheory/PrimitiveSet.lean` は no hits。
5. 失敗事例:
   - 今回は build failure なし。

### 日時: 2026/05/13 07:02 JST (Phase-R008 product route design update)

1. 目的:
   - `review/review-066.md` の提案に従い、`RealLogBudget` の供給方法を本格実装する前に設計を分解する。
   - いきなり prime-power route に戻らず、product budget route として小補題群に分ける。
2. 実施:
   - `RealLogRoutePlan.md` の Phase-R005 節を、実装済みの external log budget として更新した。
   - Phase-R006, Phase-R007 の実装済み項目を設計書へ追記した。
   - Phase-R008 を `Product route design for log budget` として追加した。
   - `RealLogBudget I pOf n` の供給路を、実数版 `sum log = log prod`、log monotonicity、自然数版への戻し、重複制御の順に分解した。
3. 結論:
   - R005-R007 で外部 budget route は完了扱いとし、R008 以降は budget の起源を product route として扱う方針を固定した。
   - 次の Lean 実装では、自然数や prime-power に戻る前に、実数値の正の有限積に関する小補題から試すのが自然。
4. 検証:
   - docs 更新のみのため Lean build は実行しない。
   - `RealLogRoutePlan.md` の該当範囲を `sed` で確認した。
5. 次の課題:
   - Phase-R009 として、`sum log = log prod` または `log prod <= log N` のどちらを先に小補題化するか判断する。
   - product route が見えてから、`pOf` の重複制御や prime-power witness provider との接続に戻る。

### 日時: 2026/05/13 06:55 JST (Phase-R007 log ratio real provider)

1. 目的:
   - `review/review-065.md` の提案に従い、`log p / log n` 型の有限実数 weight を `RealWeightProvider` に載せる。
   - log budget の起源にはまだ入らず、既存の `RealLogNonnegOn`, `RealLogBudget`, `real_log_ratio_sum_le_one` を束ねる。
2. 実施:
   - `RealLog.lean` に `realLogRatioWeightProvider` を追加した。
   - provider の `index` は `I`、`weight q` は `Real.log (pOf q : ℝ) / Real.log (n : ℝ)` とした。
   - `RealLogNonnegOn I pOf` から分子非負性、`1 < n` から分母正性を得て `weight_nonneg` を示した。
   - `realLogRatioWeightProvider_subProbability` を追加し、`RealLogBudget I pOf n` から provider の `SubProbability` を示した。
3. 結論:
   - R 版の有限 real provider として `log p / log n` weight が no-sorry で構成された。
   - 次の本丸は `RealLogBudget I pOf n` をどの構造から導くかであり、積評価・重複制御・log 単調性を分けて設計する必要がある。
4. 検証:
   - `cd lean/dk_math && ./lean-build.sh DkMath.NumberTheory.PrimitiveSet.RealLog`
   - `cd lean/dk_math && ./lean-build.sh DkMath.NumberTheory.PrimitiveSet`
   - いずれも build 成功。
   - `rg "\\bsorry\\b|\\badmit\\b|^axiom\\b" lean/dk_math/DkMath/NumberTheory/PrimitiveSet lean/dk_math/DkMath/NumberTheory/PrimitiveSet.lean` は no hits。
5. 失敗事例:
   - 今回は build failure なし。

### 日時: 2026/05/13 01:40 JST (Phase-R006 log numerator nonnegativity on index)

1. 目的:
   - `review/review-064.md` の提案に従い、log ratio weight を provider に載せる前段として index 上の numerator 非負性を整理する。
   - `pOf q = 0` のようなケースを排除する条件を、外部仮定 predicate として分離する。
2. 実施:
   - `RealLog.lean` に `RealLogNonnegOn` を追加した。
   - `RealLogNonnegOn I pOf` を `∀ q, q ∈ I → 1 ≤ pOf q` として定義した。
   - `real_log_nat_nonneg_on` を追加し、`RealLogNonnegOn I pOf` から `∀ q ∈ I, 0 ≤ Real.log (pOf q : ℝ)` を示した。
   - 証明は既存の `real_log_nat_nonneg_of_one_le` に委譲した。
3. 結論:
   - `log(pOf q)` の各項非負性を index-local な theorem 名で参照できるようになった。
   - 次は `Phase-R007` として、`log p / log n` 型の weight を `RealWeightProvider` に載せる constructor と sub-probability theorem を検討できる。
4. 検証:
   - `cd lean/dk_math && ./lean-build.sh DkMath.NumberTheory.PrimitiveSet.RealLog`
   - `cd lean/dk_math && ./lean-build.sh DkMath.NumberTheory.PrimitiveSet`
   - いずれも build 成功。
   - `rg "\\bsorry\\b|\\badmit\\b|^axiom\\b" lean/dk_math/DkMath/NumberTheory/PrimitiveSet lean/dk_math/DkMath/NumberTheory/PrimitiveSet.lean` は no hits。
5. 失敗事例:
   - 今回は build failure なし。

### 日時: 2026/05/12 22:05 JST (Phase-R005 external log budget)

1. 目的:
   - `review/review-063.md` と `RealLogRoutePlan.md` の `Phase-R005` に従い、log budget をまず外部仮定として受け取る形で固定する。
   - prime-power labels から budget を導く本丸にはまだ入らず、純粋な finite log-ratio bound だけを閉じる。
2. 実施:
   - `RealLog.lean` に `RealLogBudget` を追加した。
   - `RealLogBudget I pOf n` を `Σ q in I, Real.log (pOf q : ℝ) ≤ Real.log (n : ℝ)` として定義した。
   - `real_log_ratio_sum_le_one` を追加し、`1 < n` と `RealLogBudget I pOf n` から `Σ q in I, Real.log (pOf q : ℝ) / Real.log (n : ℝ) ≤ 1` を示した。
   - 証明は `real_ratio_sum_le_one` と `real_log_nat_pos_of_one_lt` を接続するだけに留めた。
3. 結論:
   - R 版 route で初めて `log p / log n` 型の式が theorem statement に現れた。
   - log budget は外部入力として分離され、後続で prime-power labels や重複制御から導く余地を残した。
4. 検証:
   - `cd lean/dk_math && ./lean-build.sh DkMath.NumberTheory.PrimitiveSet.RealLog`
   - `cd lean/dk_math && ./lean-build.sh DkMath.NumberTheory.PrimitiveSet`
   - いずれも build 成功。
   - `rg "\\bsorry\\b|\\badmit\\b|^axiom\\b" lean/dk_math/DkMath/NumberTheory/PrimitiveSet lean/dk_math/DkMath/NumberTheory/PrimitiveSet.lean` は no hits。
5. 失敗事例:
   - 今回は build failure なし。
6. 次の課題:
   - `pOf q` の index 上非負性、または prime base 由来の `1 ≤ pOf q` をどう渡すかを整理する。
   - その後、real log ratio weight を `RealWeightProvider` へ載せる薄い constructor を検討する。

### 日時: 2026/05/12 21:59 JST (Phase-R004 real log positivity)

1. 目的:
   - `review/review-062.md` と `RealLogRoutePlan.md` の `Phase-R004` に従い、`Real.log` の自然数向け正値性補題を局所化する。
   - log budget にはまだ触れず、後続の ratio/log route に渡すための小さい theorem 名だけを固定する。
2. 実施:
   - `DkMath/NumberTheory/PrimitiveSet/RealLog.lean` を新規作成した。
   - `real_log_nat_nonneg_of_one_le` を追加し、`1 ≤ p` から `0 ≤ Real.log (p : ℝ)` を示した。
   - `real_log_nat_pos_of_one_lt` を追加し、`1 < n` から `0 < Real.log (n : ℝ)` を示した。
   - `DkMath/NumberTheory/PrimitiveSet.lean` に `RealLog` import を追加した。
3. 結論:
   - numerator 側の非負性と denominator 側の正性に使う自然数版 log 補題が no-sorry で閉じた。
   - 次は `Phase-R005` として log budget の扱いを設計する段階へ進める。
4. 検証:
   - `cd lean/dk_math && ./lean-build.sh DkMath.NumberTheory.PrimitiveSet.RealLog`
   - `cd lean/dk_math && ./lean-build.sh DkMath.NumberTheory.PrimitiveSet`
   - いずれも build 成功。
   - `rg "\\bsorry\\b|\\badmit\\b|^axiom\\b" lean/dk_math/DkMath/NumberTheory/PrimitiveSet lean/dk_math/DkMath/NumberTheory/PrimitiveSet.lean` は no hits。
5. 失敗事例:
   - 今回は build failure なし。

### 日時: 2026/05/12 21:43 JST (Phase-R003 real weight provider prototype)

1. 目的:
   - `review/review-061.md` と `RealLogRoutePlan.md` の `Phase-R003` に従い、R 版の薄い `RealWeightProvider` prototype を追加する。
   - 既存の `ℚ` 版 `WeightProvider` は型一般化せず、実数値 route を parallel prototype として分離する。
2. 実施:
   - `DkMath/NumberTheory/PrimitiveSet/RealWeightedPath.lean` を新規作成した。
   - `RealWeightProvider` を追加し、`index : Finset ι`, `weight : ι → ℝ`, `weight_nonneg` を持つ有限実数重み provider とした。
   - `RealWeightProvider.totalWeight` を追加した。
   - `RealWeightProvider.SubProbability` を追加し、`totalWeight ≤ 1` として定義した。
   - `RealWeightProvider.totalWeight_nonneg` を追加し、provider の総重みが非負であることを示した。
   - `RealWeightProvider.subProbability_of_budget` を追加し、直接の budget bound から sub-probability を得る入口を固定した。
   - `DkMath/NumberTheory/PrimitiveSet.lean` に `RealWeightedPath` import を追加した。
3. 結論:
   - R 版の `index / weight / nonnegativity / sub-probability` の器が no-sorry で閉じた。
   - 次は `Phase-R004` として `Real.log` の正値性を局所化する段階へ進める。
4. 検証:
   - `cd lean/dk_math && ./lean-build.sh DkMath.NumberTheory.PrimitiveSet.RealWeightedPath`
   - `cd lean/dk_math && ./lean-build.sh DkMath.NumberTheory.PrimitiveSet`
   - いずれも build 成功。
   - `rg "\\bsorry\\b|\\badmit\\b|^axiom\\b" lean/dk_math/DkMath/NumberTheory/PrimitiveSet lean/dk_math/DkMath/NumberTheory/PrimitiveSet.lean` は no hits。
5. 失敗事例:
   - 今回は build failure なし。

### 日時: 2026/05/12 18:06 JST (Phase-R002 real finite budget lemma)

1. 目的:
   - `review/review-060.md` と `RealLogRoutePlan.md` の `Phase-R002` に従い、実数 ratio-style route の純粋な有限和 budget lemma を追加する。
   - channel provider や `Real.log` にはまだ接続せず、`Finset` 上の再利用可能な補題として固定する。
2. 実施:
   - `RealWeight.lean` に `real_ratio_sum_le_one` を追加した。
   - theorem は `I : Finset ι`, `Aq : ι → ℝ`, `B : ℝ` に対し、`0 < B` と `I.sum Aq ≤ B` から `I.sum (fun q => Aq q / B) ≤ 1` を示す形にした。
   - `A`, `pOf`, `n` に依存しない抽象 `Aq` 版として置き、後続の real channel prototype から再利用しやすくした。
3. 結論:
   - R 版の ratio finite sum budget が、`Real.log` なしで no-sorry に閉じた。
   - 次は `Phase-R003` として、`ℚ` 版 `WeightProvider` を一般化せずに `RealWeightProvider` の薄い prototype を作る段階へ進める。
4. 検証:
   - `cd lean/dk_math && ./lean-build.sh DkMath.NumberTheory.PrimitiveSet.RealWeight`
   - `cd lean/dk_math && ./lean-build.sh DkMath.NumberTheory.PrimitiveSet`
   - いずれも build 成功。
   - `rg "\\bsorry\\b|\\badmit\\b|^axiom\\b" lean/dk_math/DkMath/NumberTheory/PrimitiveSet lean/dk_math/DkMath/NumberTheory/PrimitiveSet.lean` は no hits。
5. 失敗事例:
   - 初回 proof では `rw [Finset.sum_div]` の向きが逆で、target 内に該当パターンが見つからなかった。
   - `rw [← Finset.sum_div]` に修正して解決した。
   - theorem 型に不要な `[DecidableEq ι]` があり linter 警告が出たため、仮定から削除した。

### 日時: 2026/05/12 16:21 JST (Phase-R001 Real weight vocabulary)

1. 目的:
   - `RealLogRoutePlan.md` の `Phase-R001` に従い、R 版の最初の実装として実数値 base-prime toy weight の最小語彙を追加する。
   - `Real.log` にはまだ入らず、実数 ratio skeleton の非負性だけを固定する。
2. 実施:
   - `DkMath/NumberTheory/PrimitiveSet/RealWeight.lean` を新規作成した。
   - `RealBasePrimeToyWeight` を追加し、`ℕ -> ℕ -> ℝ` の重みが全点非負である predicate を定義した。
   - `realRatioBasePrimeWeight` を追加し、`A(p) / B(n)` 型の実数 ratio-style weight を定義した。
   - `realRatioBasePrimeWeight_realBasePrimeToyWeight` を追加し、`0 ≤ A p` と `0 < B n` から ratio-style weight の非負性を示した。
   - `DkMath/NumberTheory/PrimitiveSet.lean` に `RealWeight` import を追加し、公開 aggregator から参照できるようにした。
3. 結論:
   - R 版は `Phase-R001` として、`Real.log` なしの実数 ratio skeleton から開始できた。
   - 次は `Phase-R002` として、純粋な実数有限和 budget lemma に進むのが自然。
4. 検証:
   - `cd lean/dk_math && ./lean-build.sh DkMath.NumberTheory.PrimitiveSet.RealWeight`
   - `cd lean/dk_math && ./lean-build.sh DkMath.NumberTheory.PrimitiveSet`
   - いずれも build 成功。
   - `rg "\\bsorry\\b|\\badmit\\b|^axiom\\b" lean/dk_math/DkMath/NumberTheory/PrimitiveSet lean/dk_math/DkMath/NumberTheory/PrimitiveSet.lean` は no hits。
5. 失敗事例:
   - 初回 build では `realRatioBasePrimeWeight` が `Real.instDivInvMonoid` に依存するため noncomputable 指定が必要、というエラーになった。
   - `realRatioBasePrimeWeight` を `noncomputable def` に修正して解決した。

### 日時: 2026/05/12 16:14 JST (Phase numbering policy update before R001)

1. 目的:
   - R 版実装へ進む前に、Phase ナンバリング仕様を修正する。
   - `BH -> RH` のような英字継続は飛躍が大きいため廃止し、R 版は `R001` から番号管理する。
2. 実施:
   - `RealLogRoutePlan.md` に `Phase ナンバリング仕様` を追加した。
   - R 版の管理範囲を `Phase-R001` から `Phase-R999` までと明記した。
   - 旧案の `Phase RH`, `Phase RI`, `Phase RJ`, `Phase RK`, `Phase RL` を廃止する旨を明記した。
   - 実装 Phase 案の見出しを `Phase-R001` から `Phase-R005` に振り直した。
   - レビュー番号は従来通り `review-060.md` 以降を参照し、Phase 番号とは独立に扱うことを明記した。
3. 結論:
   - R 版は以後 `Phase-R001` から開始する。
   - review 文書は参照のみで、こちらから改変しない。
4. 検証:
   - `RealLogRoutePlan.md` 内の新ナンバリング節と Phase 見出しを `sed` / `rg` で確認した。
   - Lean 実装変更はないため build は実行しない。

### 日時: 2026/05/12 13:31 JST (Phase BH docs overview and real/log route plan)

1. 目的:
   - `review/review-058.md` とユーザー指示に従い、ここまでの N/Q 版の成果をトップページとして整理する。
   - N/Q 版から R 版、特に実数・対数 route へ進むための設計書を分離して作る。
2. 実施:
   - `README.md` を新規作成し、finite hitting / primitive set / weighted path / finite transition / divisor prime-power / witness-provider / ratio-style toy route の全体像をまとめた。
   - `README.md` に主要 theorem-facing names と `sampleTenRatioBaseWeight_route_summary` の位置づけを記載した。
   - N/Q 版で意図的に扱わないものとして `Real.log`, 実数 weight, 無限 primitive set, 漸近評価を明示した。
   - `RealLogRoutePlan.md` を新規作成し、R 版を Real ratio skeleton, Real channel bridge, Log candidate の三層に分けた。
   - R 版の Phase 案として RH/R I/RJ/RK/RL を記載し、最初は `Real.log` ではなく実数 ratio finite sum skeleton から始める方針を固定した。
3. 結論:
   - N/Q 版のトップ概要と、R 版実装前の設計書が分離された。
   - 次に Lean 実装へ戻る場合は、`RealLogRoutePlan.md` の Phase RH から着手できる。
4. 検証:
   - docs 追加のみのため Lean build は実行しない。
   - `README.md` と `RealLogRoutePlan.md` の先頭内容を `sed` で確認した。
5. 次の課題:
   - R 版に進む場合、`DkMath/NumberTheory/PrimitiveSet/RealWeight.lean` を候補として `RealBasePrimeToyWeight` と `realRatioBasePrimeWeight` から始める。
   - 既存 N/Q API の型一般化は避け、まず parallel prototype として進める。
