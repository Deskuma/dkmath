# History

cid: 6a048079-4b50-83ab-84be-eea6a384ee8d
cid: 6a19cf55-b490-83a5-9c83-ad0a1e52d42f
cid: 6a200cab-ec18-83a5-a6c9-16fe23e2d81e

## History Log Archive

### 日時: 2026/06/03 15:34 JST (DKMK-015A roadmap 追加)

1. 目的:
   - DKMK-015 として、finite geometric-sum / tail-bound theorem design の章を
     開始する。
   - DKMK-014J の
     `DyadicBandAnalyticEstimate.ofPointwiseGeometricMajorant_of_geomSumBound`
     へ接続するための theorem layer を整理する。
2. 実施:
   - `roadmap-DKMK-015.md` を追加した。
   - DKMK-015 の主題を、provider plumbing ではなく
     finite geometric-sum / tail-bound theorem design として整理した。
   - candidate layer として finite geometric-sum identity、
     finite geometric-sum upper bound、base-scaled bound、
     direct caller-facing theorem を分けた。
   - `ratio != 1`、`0 <= ratio`、`ratio < 1`、`0 <= base` は、
     それぞれ実際に消費する theorem にだけ置く方針を明記した。
3. 結論:
   - DKMK-015A は docs-only roadmap として完了した。
   - 次は DKMK-015B として、finite geometric-sum identity の exact shape を
     review する。
4. 検証:
   - `git diff --check`
   - long-line check on `roadmap-DKMK-015.md` and `History.md`
5. 失敗事例:
   - なし。
6. 次の課題:
   - finite geometric-sum identity を、equality theorem、
     denominator-cleared identity、upper-bound theorem のどれから始めるか決める。

---

### 日時: 2026/06/03 22:22 JST (DKMK-015B geometric-sum identity shape 追加)

1. 目的:
   - DKMK-015B として、finite geometric-sum identity の first exact shape を
     docs 上で固定する。
2. 実施:
   - `roadmap-DKMK-015.md` に
     DKMK-015B Finite Geometric-Sum Identity Exact Shape を追加した。
   - 最初の theorem は division form ではなく、
     denominator-cleared identity `geomSum_range_mul_one_sub` とした。
   - expected shape として
     `(1 - ratio) * sum ratio^k = 1 - ratio^(K + 1)` を記録した。
   - `ratio != 1` は division-form theorem まで遅らせる方針を明記した。
   - `0 <= ratio`、`ratio < 1` は upper-bound theorem 側に置く方針を
     再確認した。
3. 結論:
   - DKMK-015B は docs-only exact shape review として完了した。
   - DKMK-015 の最初の Lean-facing identity は、side condition を持たない
     denominator-cleared algebraic identity から始める方針になった。
4. 検証:
   - `git diff --check`
   - long-line check on `roadmap-DKMK-015.md` and `History.md`
5. 失敗事例:
   - なし。
6. 次の課題:
   - DKMK-015C として、`geomSum_range_mul_one_sub` を Lean 上に追加できるか
     既存 library theorem を確認し、軽ければ実装する。

---

### 日時: 2026/06/04 02:58 JST (DKMK-015C denominator-cleared identity 追加)

1. 目的:
   - DKMK-015C として、DKMK-015B で固定した
     `geomSum_range_mul_one_sub` を Lean 上に追加する。
2. 実施:
   - mathlib 既存 theorem として `mul_neg_geom_sum` を確認した。
   - `SourceMassTruncation.lean` に Real 版 wrapper
     `geomSum_range_mul_one_sub` を追加した。
   - statement は
     `(1 - ratio) * sum_{k in range (K + 1)} ratio ^ k =
       1 - ratio ^ (K + 1)` とした。
   - proof は `exact mul_neg_geom_sum ratio (K + 1)` で閉じた。
   - `roadmap-DKMK-015.md` に
     DKMK-015C Lean Denominator-Cleared Identity を追記した。
3. 結論:
   - finite geometric-sum の最初の algebraic identity layer が Lean 上で
     利用可能になった。
   - division-form theorem、`ratio != 1`、`0 <= ratio`、`ratio < 1`、
     base-scaled bound、route theorem、Mertens / big-O、
     logarithmic threshold、real-to-Nat rounding は追加していない。
4. 検証:
   - `lake build DkMath.NumberTheory.PrimitiveSet.SourceMassTruncation`
   - `lake build DkMath.NumberTheory.PrimitiveSet`
   - `git diff --check`
5. 失敗事例:
   - なし。
6. 次の課題:
   - DKMK-015D として、division form へ進むか、
     upper-bound theorem の exact shape へ進むかを review する。

---

### 日時: 2026/06/04 03:20 JST (DKMK-015D geometric-sum upper-bound shape 追加)

1. 目的:
   - DKMK-015D として、finite geometric-sum upper-bound theorem の
     exact shape を docs 上で固定する。
2. 実施:
   - `roadmap-DKMK-015.md` に
     DKMK-015D Finite Geometric-Sum Upper-Bound Exact Shape を追加した。
   - chosen theorem を `geomSum_range_le_one_div_one_sub` とした。
   - expected shape として、`0 <= ratio` と `ratio < 1` から
     `sum ratio^k <= 1 / (1 - ratio)` を出す theorem を記録した。
   - division-form equality ではなく、下流で必要な upper-bound theorem を
     先に固定する方針にした。
   - `0 <= ratio`、`ratio < 1` はこの theorem が初めて消費し、
     `ratio != 1` は明示仮定にしない方針を記録した。
   - later base-scaled layer として
     `base_mul_geomSum_range_le_of_base_mul_one_div_le` の shape を記録した。
3. 結論:
   - DKMK-015D は docs-only exact shape review として完了した。
   - DKMK-015 は denominator-cleared identity から order upper-bound layer へ
     進む方針になった。
4. 検証:
   - `git diff --check`
   - long-line check on `roadmap-DKMK-015.md` and `History.md`
5. 失敗事例:
   - なし。
6. 次の課題:
   - DKMK-015E として、`geomSum_range_le_one_div_one_sub` を Lean 上に
     実装できるか既存 theorem を確認し、軽ければ追加する。

---

### 日時: 2026/06/04 03:37 JST (DKMK-015E geometric-sum upper-bound 実装)

1. 目的:
   - DKMK-015E として、DKMK-015D で固定した
     `geomSum_range_le_one_div_one_sub` を Lean 上に追加する。
2. 実施:
   - `SourceMassTruncation.lean` に Real 版 theorem
     `geomSum_range_le_one_div_one_sub` を追加した。
   - statement は `0 <= ratio` と `ratio < 1` から
     `sum_{k in range (K + 1)} ratio ^ k <= 1 / (1 - ratio)` を出す形にした。
   - DKMK-015C の `geomSum_range_mul_one_sub` を使って
     `(1 - ratio) * sum ratio^k <= 1` を作った。
   - `sub_pos.mpr hr1` で `0 < 1 - ratio` を得て、
     `le_div_iff₀` で目的の upper-bound へ変形した。
   - `roadmap-DKMK-015.md` に
     DKMK-015E Lean Geometric-Sum Upper Bound を追記した。
3. 結論:
   - finite geometric-sum の order upper-bound layer が Lean 上で
     利用可能になった。
   - division-form equality、explicit `ratio != 1`、base-scaled bound、
     route theorem、Mertens / big-O、logarithmic threshold、
     real-to-Nat rounding は追加していない。
4. 検証:
   - `lake build DkMath.NumberTheory.PrimitiveSet.SourceMassTruncation`
   - `lake build DkMath.NumberTheory.PrimitiveSet`
   - `git diff --check`
   - long-line check on changed docs
5. 失敗事例:
   - `lake build` を repository top で実行して lakefile が見つからなかった。
     `lean/dk_math` に移動して再実行し、成功した。
6. 次の課題:
   - DKMK-015F として、`base_mul_geomSum_range_le_of_base_mul_one_div_le`
     の exact shape または Lean 実装へ進む。

---

### 日時: 2026/06/04 03:44 JST (DKMK-015F base-scaled geometric-sum bound 実装)

1. 目的:
   - DKMK-015F として、DKMK-015E の geometric-sum upper-bound を
     nonnegative base で scale する theorem を Lean 上に追加する。
2. 実施:
   - `SourceMassTruncation.lean` に Real 版 theorem
     `base_mul_geomSum_range_le_of_base_mul_one_div_le` を追加した。
   - statement は `0 <= base`、`0 <= ratio`、`ratio < 1`、
     `base * (1 / (1 - ratio)) <= 1 + error` から
     `base * sum ratio^k <= 1 + error` を出す形にした。
   - proof は `geomSum_range_le_one_div_one_sub` に
     `mul_le_mul_of_nonneg_left` を当て、
     `le_trans` で `hbudget` へ接続する薄い wrapper とした。
   - `roadmap-DKMK-015.md` に
     DKMK-015F Lean Base-Scaled Geometric-Sum Bound を追記した。
3. 結論:
   - DKMK-014J が要求する
     `base * sum ratio^k <= 1 + error` 型の provider-facing bound が
     Lean 上で利用可能になった。
   - division-form equality、explicit `ratio != 1`、route theorem、
     Mertens / big-O、logarithmic threshold、real-to-Nat rounding は
     追加していない。
4. 検証:
   - `lake build DkMath.NumberTheory.PrimitiveSet.SourceMassTruncation`
   - `lake build DkMath.NumberTheory.PrimitiveSet`
   - `git diff --check`
   - long-line check on changed docs
5. 失敗事例:
   - なし。
6. 次の課題:
   - DKMK-015G として、この base-scaled theorem を既存の
     DKMK-014J / dyadic provider route へどう接続するか review する。

---

### 日時: 2026/06/04 16:24 JST (DKMK-015G dyadic provider connection shape review)

1. 目的:
   - DKMK-015G として、DKMK-015F の base-scaled theorem を
     既存 dyadic provider route へ接続する次 theorem の shape を固定する。
2. 実施:
   - `roadmap-DKMK-015.md` に
     DKMK-015G Dyadic Provider Connection Shape Review を追記した。
   - 既存 provider
     `DyadicBandAnalyticEstimate.ofPointwiseGeometricMajorant_of_geomSumBound`
     が `base * sum ratio^k <= 1 + error` 型の finite-sum bound を
     受け取ることを再確認した。
   - 次 theorem 名を
     `ofPointwiseGeometricMajorant_of_baseGeomBudget` とする方針にした。
   - provider 側は `base ratio : Rat`、geometric-budget 側は `Real` に
     留め、接続 theorem で cast 境界を処理する方針にした。
   - `((base * sum ratio^k : Rat) : Real)` と
     `(base : Real) * sum ((ratio : Real) ^ k)` の同一視を
     次実装の主要境界として記録した。
3. 結論:
   - DKMK-015G は docs-only connection shape review として完了した。
   - 次は DKMK-015H として、この connection theorem を Lean 上に
     実装できるか確認する。
4. 検証:
   - `git diff --check`
   - long-line check on `roadmap-DKMK-015.md` and `History.md`
5. 失敗事例:
   - なし。
6. 次の課題:
   - DKMK-015H として、
     `DyadicBandAnalyticEstimate.ofPointwiseGeometricMajorant_of_baseGeomBudget`
     を実装し、既存 provider へ接続する。

---

### 日時: 2026/06/04 16:32 JST (DKMK-015H dyadic provider connection 実装)

1. 目的:
   - DKMK-015H として、DKMK-015G で固定した
     `DyadicBandAnalyticEstimate.ofPointwiseGeometricMajorant_of_baseGeomBudget`
     を Lean 上に追加する。
2. 実施:
   - `SourceMassTruncation.lean` の `DyadicBandAnalyticEstimate` namespace に
     theorem `ofPointwiseGeometricMajorant_of_baseGeomBudget` を追加した。
   - `base_mul_geomSum_range_le_of_base_mul_one_div_le` で Real 側の
     `base * sum ratio^k <= 1 + error` bound を作った。
   - `((base * sum ratio^k : Rat) : Real)` と
     `(base : Real) * sum ((ratio : Real) ^ k)` の cast 境界を
     局所補題 `hcast` として `simp` で閉じた。
   - 最後に既存 provider
     `ofPointwiseGeometricMajorant_of_geomSumBound` へ接続した。
   - `roadmap-DKMK-015.md` に
     DKMK-015H Lean Dyadic Provider Connection を追記した。
3. 結論:
   - DKMK-015 の Real geometric-budget route が、既存 DKMK-014J の
     rational dyadic provider route へ接続された。
   - caller は `base * (1 / (1 - ratio)) <= 1 + error` を Real 側で
     与えることで `DyadicBandAnalyticEstimate` を得られる。
   - 新 provider structure、duplicate low-level provider、
     division-form equality、Mertens / big-O、logarithmic threshold、
     real-to-Nat rounding は追加していない。
4. 検証:
   - `lake build DkMath.NumberTheory.PrimitiveSet.SourceMassTruncation`
   - `lake build DkMath.NumberTheory.PrimitiveSet`
   - `git diff --check`
   - long-line check on changed docs
5. 失敗事例:
   - なし。
6. 次の課題:
   - DKMK-015I として、DKMK-015 のまとめまたは次の route 接続方針を
     review する。

---

### 日時: 2026/06/04 16:42 JST (DKMK-015I chapter summary 追加)

1. 目的:
   - DKMK-015I として、DKMK-015B-H の finite geometric-sum /
     dyadic provider connection route を総括し、次の budget source 問題を
     明確にする。
2. 実施:
   - `report-DKMK-015.md` を追加した。
   - DKMK-015 の追加 Lean surface として
     `geomSum_range_mul_one_sub`、
     `geomSum_range_le_one_div_one_sub`、
     `base_mul_geomSum_range_le_of_base_mul_one_div_le`、
     `DyadicBandAnalyticEstimate.ofPointwiseGeometricMajorant_of_baseGeomBudget`
     を整理した。
   - caller path を
     `hinc_nonneg`、`hgeom`、`hbase`、`hr0`、`hr1`、`hbudget`
     から `DyadicBandAnalyticEstimate` へ入る形として記録した。
   - 次の主課題を
     `(base : Real) * (1 / (1 - (ratio : Real))) <= 1 + error`
     の供給源設計として明記した。
   - `roadmap-DKMK-015.md` に
     DKMK-015I Chapter Summary And Next Budget Source を追記した。
3. 結論:
   - DKMK-015 は
     `geometric budget -> finite sum bound -> dyadic source-mass provider`
     の実用 API 章として区切れる状態になった。
   - 次章では finite geometric sum ではなく、上位 route が `hbudget` を
     どう供給するかを扱う。
4. 検証:
   - `git diff --check`
   - long-line check on changed docs
5. 失敗事例:
   - なし。
6. 次の課題:
   - 次章として、`hbudget` の abstract budget provider または
     concrete `base` / `ratio` 設計を review する。

---

### 日時: 2026/06/04 17:16 JST (DKMK-016A roadmap 追加)

1. 目的:
   - DKMK-016 を開始し、DKMK-015 で残った
     `hbudget : (base : Real) * (1 / (1 - (ratio : Real))) <= 1 + error`
     の供給源設計を次章の主題として固定する。
2. 実施:
   - `roadmap-DKMK-016.md` を追加した。
   - 章題を Geometric Budget Source とした。
   - DKMK-016A の first interface shape として
     `GeometricBudgetSource` structure の候補を記録した。
   - package する要素を `base : Rat`、`ratio : Rat`、`error : Real`、
     `hbase`、`hr0`、`hr1`、`hbudget` とした。
   - 後続 connection theorem 候補として
     `DyadicBandAnalyticEstimate.ofPointwiseGeometricMajorant_of_budgetSource`
     を記録した。
3. 結論:
   - DKMK-016 は finite geometric sum ではなく、
     geometric budget source の抽象 surface 設計から始める方針になった。
   - Mertens / big-O / logarithmic threshold / real-to-Nat rounding は
     まだ non-goal として維持する。
4. 検証:
   - `git diff --check`
   - long-line check on `roadmap-DKMK-016.md` and `History.md`
5. 失敗事例:
   - なし。
6. 次の課題:
   - DKMK-016B として、`GeometricBudgetSource` を Lean 上に
     追加できるか review する。

---

### 日時: 2026/06/04 17:37 JST (DKMK-016B GeometricBudgetSource 実装)

1. 目的:
   - DKMK-016B として、DKMK-016A で固定した
     `GeometricBudgetSource` と budget-source wrapper を Lean 上に追加する。
2. 実施:
   - `SourceMassTruncation.lean` に structure `GeometricBudgetSource` を
     追加した。
   - fields は `base : Rat`、`ratio : Rat`、`error : Real`、
     `hbase`、`hr0`、`hr1`、`hbudget` とした。
   - `DyadicBandAnalyticEstimate` namespace に theorem
     `ofPointwiseGeometricMajorant_of_budgetSource` を追加した。
   - proof は既存
     `ofPointwiseGeometricMajorant_of_baseGeomBudget` へ
     `B.base`、`B.ratio`、`B.hbase`、`B.hr0`、`B.hr1`、`B.hbudget`
     を渡す薄い wrapper とした。
   - `roadmap-DKMK-016.md` に
     DKMK-016B Lean Abstract Budget Source を追記した。
3. 結論:
   - `hbudget` 供給源を抽象 package として受け取り、
     DKMK-015H の dyadic provider connection へ渡す API ができた。
   - concrete `base` / `ratio`、Mertens / big-O、logarithmic threshold、
     real-to-Nat rounding、dependent `GeometricBudgetSourceFor` は
     追加していない。
4. 検証:
   - `lake build DkMath.NumberTheory.PrimitiveSet.SourceMassTruncation`
   - `lake build DkMath.NumberTheory.PrimitiveSet`
   - `git diff --check`
   - long-line check on changed docs
5. 失敗事例:
   - なし。
6. 次の課題:
   - DKMK-016C として、具体的な budget constructor へ進む前に、
     `GeometricBudgetSource` の constructor / usage docs を review する。

---

### 日時: 2026/06/04 17:42 JST (DKMK-016C usage review 追加)

1. 目的:
   - DKMK-016C として、具体 constructor へ進む前に
     `GeometricBudgetSource` の作り方と provider wrapper の使い方を
     docs 上で固定する。
2. 実施:
   - `roadmap-DKMK-016.md` に
     DKMK-016C GeometricBudgetSource Usage Review を追記した。
   - `B : GeometricBudgetSource` が package する fields と side conditions を
     construction pattern として整理した。
   - `DyadicBandAnalyticEstimate.ofPointwiseGeometricMajorant_of_budgetSource`
     の caller usage を例示した。
   - `GeometricBudgetSource` と wrapper の責務分担を記録した。
   - 将来 `base`、`ratio`、`error` が `x` または `K` に依存するときだけ
     `GeometricBudgetSourceFor` 型の indexed package を検討する方針にした。
3. 結論:
   - DKMK-016C は docs-only usage review として完了した。
   - 現時点では unindexed `GeometricBudgetSource` を preferred API とする。
4. 検証:
   - `git diff --check`
   - long-line check on `roadmap-DKMK-016.md` and `History.md`
5. 失敗事例:
   - なし。
6. 次の課題:
   - DKMK-016D として、小さな constructor theorem を追加するか、
     concrete `base` / `ratio` candidate の review へ進むかを決める。

---

### 日時: 2026/06/04 17:46 JST (DKMK-016D concrete candidate review 追加)

1. 目的:
   - DKMK-016D として、`GeometricBudgetSource` の最初の concrete
     `base` / `ratio` candidate を review する。
2. 実施:
   - `roadmap-DKMK-016.md` に
     DKMK-016D Concrete Base/Ratio Candidate Review を追記した。
   - 候補として direct record construction、zero-ratio sanity constructor、
     external positive ratio constructor、analytic budget constructor を
     比較した。
   - 次の Lean target として `GeometricBudgetSource.ofZeroRatio` を
     推奨候補にした。
   - `ratio = 0` の場合、budget が
     `(base : Real) <= 1 + error` に簡約されることを記録した。
   - この constructor は analytic result ではなく API sanity constructor と
     位置づけた。
3. 結論:
   - DKMK-016D は docs-only concrete candidate review として完了した。
   - 次は DKMK-016E として、`GeometricBudgetSource.ofZeroRatio` を
     Lean 上に追加できるか確認する。
4. 検証:
   - `git diff --check`
   - long-line check on `roadmap-DKMK-016.md` and `History.md`
5. 失敗事例:
   - なし。
6. 次の課題:
   - DKMK-016E として、`GeometricBudgetSource.ofZeroRatio` を実装する。

---

### 日時: 2026/06/04 19:57 JST (DKMK-016E zero-ratio budget source 追加)

1. 目的:
   - DKMK-016E として、`GeometricBudgetSource` の最初の小さな
     constructor API を Lean 上に追加する。
2. 実施:
   - `SourceMassTruncation.lean` に
     `GeometricBudgetSource.ofZeroRatio` を追加した。
   - `ratio := 0` とし、`hr0` と `hr1` は `norm_num` で閉じた。
   - `hbudget` は
     `(base : Real) * (1 / (1 - (0 : Real))) <= 1 + error`
     を caller supplied の `(base : Real) <= 1 + error` に簡約して閉じた。
   - `roadmap-DKMK-016.md` に
     DKMK-016E Lean Zero-Ratio Budget Source を追記した。
3. 結論:
   - zero-ratio case で `GeometricBudgetSource` を構築する API ができた。
   - これは analytic estimate ではなく、abstract budget package の
     sanity constructor である。
4. 検証:
   - `lake build DkMath.NumberTheory.PrimitiveSet.SourceMassTruncation`
   - `lake build DkMath.NumberTheory.PrimitiveSet`
   - `git diff --check`
   - long-line check on changed files
5. 失敗事例:
   - 最初に `theorem GeometricBudgetSource.ofZeroRatio` として書いたが、
     Lean は theorem の型に `Prop` を要求するため失敗した。
   - 返り値は `GeometricBudgetSource` という data なので、`def` に変更して
     通した。
6. 次の課題:
   - DKMK-016F として、positive ratio constructor に進むか、
     current constructor を budget wrapper usage に接続する小さな example を
     追加するかを review する。

---

### 日時: 2026/06/04 20:14 JST (DKMK-016F zero-ratio usage wrapper 追加)

1. 目的:
   - DKMK-016F として、`GeometricBudgetSource.ofZeroRatio` を
     budget-source provider wrapper へ通す caller 経路を Lean 上で確認する。
2. 実施:
   - `SourceMassTruncation.lean` に
     `DyadicBandAnalyticEstimate.ofPointwiseZeroRatioMajorant` を追加した。
   - proof では
     `GeometricBudgetSource.ofZeroRatio base error hbase hbudget` を構築し、
     `DyadicBandAnalyticEstimate.ofPointwiseGeometricMajorant_of_budgetSource`
     へ渡した。
   - `hgeom` は
     `increment k <= base * (0 : Rat) ^ k`
     の形で受け取り、zero-ratio source の unfolding により既存 wrapper の
     `B.base * B.ratio ^ k` に合わせた。
   - `roadmap-DKMK-016.md` に
     DKMK-016F Zero-Ratio Usage Wrapper を追記した。
3. 結論:
   - `ofZeroRatio -> of_budgetSource -> DyadicBandAnalyticEstimate` の
     caller route が小さな wrapper theorem として通った。
   - positive-ratio constructor へ進む前に、abstract budget package の
     使用感を Lean 上で確認できた。
4. 検証:
   - `lake build DkMath.NumberTheory.PrimitiveSet.SourceMassTruncation`
   - `lake build DkMath.NumberTheory.PrimitiveSet`
   - `git diff --check`
   - long-line check on changed files
5. 失敗事例:
   - なし。
6. 次の課題:
   - DKMK-016G として positive-ratio constructor の shape を review する。
   - あるいは、zero-ratio wrapper から truncation envelope まで接続する
     追加 usage theorem が必要か確認する。

---

### 日時: 2026/06/04 21:20 JST (DKMK-016G positive-ratio constructor review 追加)

1. 目的:
   - DKMK-016G として、非退化な positive-ratio constructor の shape を
     Lean 実装前に review する。
2. 実施:
   - `roadmap-DKMK-016.md` に
     DKMK-016G Positive-Ratio Constructor Shape Review を追記した。
   - 候補 `GeometricBudgetSource.ofBudget` は record syntax とほぼ同じで、
     analytic estimate ではなく readability constructor と位置づけた。
   - DKMK-016E の学びを反映し、constructor 候補は `theorem` ではなく
     `def` として記録した。
   - 既存の DKMK-016D 候補スニペットも `def` 表記に整えた。
3. 結論:
   - 次の Lean target は
     `def GeometricBudgetSource.ofBudget` が妥当。
   - ただし、その step では provider wrapper、finite-sum theorem、
     analytic estimate を追加しない。
4. 検証:
   - `git diff --check`
   - long-line check on `roadmap-DKMK-016.md` and `History.md`
5. 失敗事例:
   - なし。
6. 次の課題:
   - DKMK-016H として `GeometricBudgetSource.ofBudget` を Lean 上に追加する。

---

### 日時: 2026/06/05 02:42 JST (DKMK-016H explicit budget constructor 追加)

1. 目的:
   - DKMK-016H として、`GeometricBudgetSource.ofBudget` を Lean 上に追加する。
2. 実施:
   - `SourceMassTruncation.lean` の `GeometricBudgetSource` namespace に
     `def ofBudget` を追加した。
   - `base`、`ratio`、`error`、`hbase`、`hr0`、`hr1`、`hbudget` を
     そのまま package する direct record construction とした。
   - `roadmap-DKMK-016.md` に
     DKMK-016H Lean Explicit Budget Constructor を追記した。
3. 結論:
   - 明示的な one-over-one-minus budget proof から
     `GeometricBudgetSource` を作る named constructor ができた。
   - これは analytic estimate ではなく readability constructor である。
4. 検証:
   - `lake build DkMath.NumberTheory.PrimitiveSet.SourceMassTruncation`
   - `lake build DkMath.NumberTheory.PrimitiveSet`
   - `git diff --check`
   - long-line check on changed files
5. 失敗事例:
   - なし。
6. 次の課題:
   - concrete `base` / `ratio` candidate review へ進む。
   - 必要なら `ofBudget` を使った small usage example を追加するか確認する。

---

### 日時: 2026/06/05 02:57 JST (DKMK-016I base/ratio candidate review 追加)

1. 目的:
   - DKMK-016I として、constructor API から concrete `base` / `ratio`
     candidate design へ進む。
2. 実施:
   - `roadmap-DKMK-016.md` に
     DKMK-016I Concrete Base/Ratio Candidate Review を追記した。
   - 候補として logarithmic base with dyadic ratio、logarithmic base with
     prime-dependent ratio、first-band mass with uniform decay、
     tail-mass envelope as base を比較した。
   - 次の design target として
     first-band upper bound と uniform decay bound から
     `GeometricBudgetSource.ofBudget` へ進む interface を推奨した。
3. 結論:
   - 次は concrete analytic theorem ではなく、first-band/decay estimate を
     `GeometricBudgetSource` に渡す interface review が妥当。
   - Mertens、big-O、logarithmic threshold、rounding、rational approximation は
     まだ導入しない。
4. 検証:
   - `git diff --check`
   - long-line check on `roadmap-DKMK-016.md` and `History.md`
5. 失敗事例:
   - なし。
6. 次の課題:
   - DKMK-016J として first-band / uniform-decay budget interface の shape を
     review する。

---

### 日時: 2026/06/05 03:02 JST (DKMK-016J first-band decay interface review 追加)

1. 目的:
   - DKMK-016J として、Candidate C の first-band / uniform-decay interface を
     Lean 実装前に整理する。
2. 実施:
   - `roadmap-DKMK-016.md` に
     DKMK-016J First-Band / Uniform-Decay Interface Review を追記した。
   - obligation を budget obligation と pointwise decay obligation に分けた。
   - `GeometricBudgetSource` は budget obligation を package し、
     `hgeom` は increment-specific な pointwise control として外に置く方針を
     固定した。
   - 新構造体 `FirstBandDecayBudgetInput` は
     `GeometricBudgetSource` と重複するため、現時点では追加しない方針にした。
3. 結論:
   - 次に意味のある Lean target は constructor ではなく、
     first-band bound と uniform decay から `hgeom` を作る theorem shape である。
4. 検証:
   - `git diff --check`
   - long-line check on `roadmap-DKMK-016.md` and `History.md`
5. 失敗事例:
   - なし。
6. 次の課題:
   - DKMK-016K として
     `pointwiseGeometricMajorant_of_firstBand_decay` の theorem shape を
     review する。

---

### 日時: 2026/06/05 03:06 JST (DKMK-016K pointwise majorant shape review 追加)

1. 目的:
   - DKMK-016K として、
     `pointwiseGeometricMajorant_of_firstBand_decay` の theorem shape を
     Lean 実装前に固定する。
2. 実施:
   - `roadmap-DKMK-016.md` に
     DKMK-016K Pointwise Geometric Majorant Shape Review を追記した。
   - theorem は `hgeom` の生成だけを担当し、`hinc_nonneg` は provider 側の
     別入力として残す方針にした。
   - `hdecay` の範囲は `Finset.range K` とし、結論は
     `Finset.range (K + 1)` 上の pointwise majorant とした。
   - 実装リスクは数学ではなく Nat indexing と Rat algebra にあると整理した。
3. 結論:
   - 次の Lean target は `hinc_nonneg` なしの
     `pointwiseGeometricMajorant_of_firstBand_decay` が妥当。
4. 検証:
   - `git diff --check`
   - long-line check on `roadmap-DKMK-016.md` and `History.md`
5. 失敗事例:
   - なし。
6. 次の課題:
   - DKMK-016L として
     `pointwiseGeometricMajorant_of_firstBand_decay` を Lean 上に実装する。

---

### 日時: 2026/06/05 03:12 JST (DKMK-016L pointwise majorant 実装)

1. 目的:
   - DKMK-016L として、
     `pointwiseGeometricMajorant_of_firstBand_decay` を Lean 上に追加する。
2. 実施:
   - `SourceMassTruncation.lean` に
     `pointwiseGeometricMajorant_of_firstBand_decay` を追加した。
   - theorem は `hinc_nonneg` を受け取らず、`hgeom` の生成だけを担当する。
   - proof では内部補題
     `forall k, k <= K -> increment k <= base * ratio^k`
     を帰納法で示した。
   - successor case では `k + 1 <= K` から `k < K` を作り、
     `hdecay k` を適用した。
   - `hr0` により左から `ratio` を掛けた不等式を保ち、最後の Rat algebra は
     `ring_nf` で閉じた。
   - `roadmap-DKMK-016.md` に
     DKMK-016L Lean Pointwise Geometric Majorant を追記した。
3. 結論:
   - first-band bound と uniform step decay から provider 用の `hgeom` を
     作る Lean theorem ができた。
   - provider wrapper への接続はまだ追加していない。
4. 検証:
   - `lake build DkMath.NumberTheory.PrimitiveSet.SourceMassTruncation`
   - `lake build DkMath.NumberTheory.PrimitiveSet`
   - `git diff --check`
   - long-line check on changed files
5. 失敗事例:
   - なし。
6. 次の課題:
   - DKMK-016M として、この `hgeom` theorem を
     `GeometricBudgetSource` と provider wrapper へ接続する theorem shape を
     review する。

---

### 日時: 2026/06/05 06:47 JST (DKMK-016M provider wrapper shape review 追加)

1. 目的:
   - DKMK-016M として、`pointwiseGeometricMajorant_of_firstBand_decay` を
     `GeometricBudgetSource` と provider wrapper へ接続する theorem shape を
     Lean 実装前に固定する。
2. 実施:
   - `roadmap-DKMK-016.md` に
     DKMK-016M First-Band Decay Provider Wrapper Shape Review を追記した。
   - 次の Lean target として
     `DyadicBandAnalyticEstimate.ofFirstBandDecayBudgetSource` を提案した。
   - `B.hr0 : 0 <= (B.ratio : Real)` から
     `hr0_rat : 0 <= B.ratio` を作る cast boundary を明示した。
   - wrapper は budget proof と increment nonnegativity を証明せず、
     `hgeom` 生成と既存 budget-source provider wrapper への接続だけを
     担当する方針にした。
3. 結論:
   - 次は `ofFirstBandDecayBudgetSource` を Lean 上に追加するのが妥当。
   - 主なリスクは数学ではなく Rat / Real cast 境界である。
4. 検証:
   - `git diff --check`
   - long-line check on `roadmap-DKMK-016.md` and `History.md`
5. 失敗事例:
   - なし。
6. 次の課題:
   - DKMK-016N として `DyadicBandAnalyticEstimate.ofFirstBandDecayBudgetSource`
     を Lean 上に実装する。

---

### 日時: 2026/06/05 07:00 JST (DKMK-016N provider wrapper 実装)

1. 目的:
   - DKMK-016N として
     `DyadicBandAnalyticEstimate.ofFirstBandDecayBudgetSource` を Lean 上に
     追加する。
2. 実施:
   - `SourceMassTruncation.lean` に
     `DyadicBandAnalyticEstimate.ofFirstBandDecayBudgetSource` を追加した。
   - `B.hr0 : 0 <= (B.ratio : Real)` から
     `hr0_rat : 0 <= B.ratio` への cast は `exact_mod_cast B.hr0` で閉じた。
   - `pointwiseGeometricMajorant_of_firstBand_decay` で `hgeom` を生成し、
     既存の
     `DyadicBandAnalyticEstimate.ofPointwiseGeometricMajorant_of_budgetSource`
     へ渡した。
   - `roadmap-DKMK-016.md` に
     DKMK-016N Lean First-Band Decay Provider Wrapper を追記した。
3. 結論:
   - `GeometricBudgetSource + hinc_nonneg + first-band bound + uniform decay`
     から `DyadicBandAnalyticEstimate` へ到達する provider-facing wrapper が
     Lean 上で通った。
4. 検証:
   - `lake build DkMath.NumberTheory.PrimitiveSet.SourceMassTruncation`
   - `lake build DkMath.NumberTheory.PrimitiveSet`
   - `git diff --check`
   - long-line check on changed files
5. 失敗事例:
   - なし。
6. 次の課題:
   - DKMK-016O として、この provider wrapper を truncation envelope へ
     接続するか、DKMK-016 のまとめに進むかを review する。

---

### 日時: 2026/06/05 07:05 JST (DKMK-016O truncation branch review 追加)

1. 目的:
   - DKMK-016O として、DKMK-016N の provider wrapper を
     truncation envelope へ直接接続するか、章まとめへ進むかを review する。
2. 実施:
   - `roadmap-DKMK-016.md` に
     DKMK-016O Truncation-Envelope Branch Review を追記した。
   - 既存の
     `DyadicBandAnalyticEstimate.toTruncationEnvelopeEstimate` により、
     N の出力はすでに truncation envelope へ接続可能であることを確認した。
   - thin truncation wrapper は便利だが新しい数学的内容はないと整理した。
3. 結論:
   - 次は追加 Lean wrapper ではなく、DKMK-016 の章まとめへ進む方針にした。
   - truncation wrapper は caller code が煩雑になった時点で追加すればよい。
4. 検証:
   - `git diff --check`
   - long-line check on `roadmap-DKMK-016.md` and `History.md`
5. 失敗事例:
   - なし。
6. 次の課題:
   - DKMK-016P として、章のまとめと次章への analytic input を整理する。

---

### 日時: 2026/06/05 07:12 JST (DKMK-016P chapter summary 追加)

1. 目的:
   - DKMK-016P として、DKMK-016 の Lean API、final route、
     responsibility split、non-goals、次章 analytic input を整理する。
2. 実施:
   - `roadmap-DKMK-016.md` に DKMK-016P Chapter Summary を追記した。
   - 追加された Lean surface を budget source、budget-source provider、
     zero-ratio sanity route、first-band / uniform-decay route、
     downstream bridge に分けて整理した。
   - final caller route を
     `GeometricBudgetSource.ofBudget`、
     `pointwiseGeometricMajorant_of_firstBand_decay`、
     `DyadicBandAnalyticEstimate.ofFirstBandDecayBudgetSource`、
     `DyadicBandAnalyticEstimate.toTruncationEnvelopeEstimate`
     の流れとして記録した。
   - budget layer / pointwise layer / provider layer / downstream layer の
     responsibility split を明示した。
   - 次章の analytic input candidates を first-band upper bound、
     uniform decay、`GeometricBudgetSource.ofBudget` の concrete budget proof
     として記録した。
3. 結論:
   - DKMK-016 は API plumbing と first-band/uniform-decay provider route の
     章として自然な停止点に到達した。
   - 次は追加 wrapper ではなく concrete analytic input source の review へ進む。
4. 検証:
   - `git diff --check`
   - long-line check on `roadmap-DKMK-016.md` and `History.md`
5. 失敗事例:
   - なし。
6. 次の課題:
   - concrete analytic input source の roadmap/review へ進む。

---

### 日時: 2026/06/05 07:39 JST (DKMK-017 roadmap 開始)

1. 目的:
   - DKMK-017 の開始にあたり、作業粒度を大きくし、実装・自己診断・
     検証結果をまとめて報告する運用へ切り替える。
2. 実施:
   - `roadmap-DKMK-017.md` を新規作成した。
   - DKMK-017 を Analytic Input Source 章として位置付けた。
   - docs-only review の連続を抑え、Lean 実装 bundle 単位で進める方針を
     明記した。
   - reviewer 判断を仰ぐタイミングと、自己判断で進めるタイミングを分けた。
   - 最初の bundle target として、first-band bound、uniform decay、
     concrete budget proof source の入力 surface 調査を置いた。
3. 結論:
   - DKMK-017 では、細かな wrapper や constructor を個別 review せず、
     route-shape が変わる判断点でのみ厚く相談する。
   - 次は Lean 側で analytic input source surface を実験し、どこまで実装可能かを
     bundle として報告する。
4. 検証:
   - `git diff --check`
   - long-line check on `roadmap-DKMK-017.md` and `History.md`
5. 失敗事例:
   - なし。
6. 次の課題:
   - DKMK-017 の first implementation bundle として、analytic input source
     surface を Lean で試す。

---

### 日時: 2026/06/05 08:04 JST (DKMK-017A implementation bundle)

1. 目的:
   - DKMK-017A として、first-band / uniform-decay / budget source をまとめる
     analytic input package が Lean 上で有効か試す。
2. 実施:
   - `SourceMassTruncation.lean` に
     `FirstBandDecayBudgetSource` を追加した。
   - `DyadicBandAnalyticEstimate.ofFirstBandDecayBudgetSourcePackage` を追加し、
     既存の
     `DyadicBandAnalyticEstimate.ofFirstBandDecayBudgetSource`
     へ直接委譲した。
   - `roadmap-DKMK-017.md` に DKMK-017A First Implementation Bundle を
     追記した。
3. 結論:
   - combined source は、DKMK-016 の責務分担を置き換えるものではなく、
     analytic input boundary の package として採用可能。
   - Rat / Real cast 問題はこの bundle では発生しなかった。
   - 新しい truncation wrapper は追加しない。
4. 検証:
   - `lake build DkMath.NumberTheory.PrimitiveSet.SourceMassTruncation`
   - `lake build DkMath.NumberTheory.PrimitiveSet`
   - `git diff --check`
   - long-line check on changed docs
5. 失敗事例:
   - なし。
6. 次の課題:
   - `FirstBandDecayBudgetSource` へ流し込む具体的 source constructor または
     helper lemma を検討する。

---

### 日時: 2026/06/05 08:15 JST (DKMK-017B source constructor bundle)

1. 目的:
   - DKMK-017B として、`FirstBandDecayBudgetSource` に流し込む
     concrete source constructor が Lean 上で有効か試す。
2. 実施:
   - `FirstBandDecayBudgetSource.ofBudgetSource` を追加した。
   - `FirstBandDecayBudgetSource.ofBudgetAndDecay` を追加し、
     `GeometricBudgetSource.ofBudget` から package を作れるようにした。
   - `roadmap-DKMK-017.md` に DKMK-017B Source Constructor Bundle を
     追記した。
3. 結論:
   - record syntax だけでも表現可能だが、constructor を置くことで
     analytic input boundary が明確になった。
   - `ofBudgetSource` と `ofBudgetAndDecay` は採用する。
4. 検証:
   - `lake build DkMath.NumberTheory.PrimitiveSet.SourceMassTruncation`
   - `lake build DkMath.NumberTheory.PrimitiveSet`
   - `git diff --check`
   - long-line check on changed docs
5. 失敗事例:
   - 最初は `FirstBandDecayBudgetSource` namespace を
     `GeometricBudgetSource.ofBudget` より前に置いたため、Lean が
     unknown constant として失敗した。
   - constructor 群を `end GeometricBudgetSource` の後へ移して解消した。
6. 次の課題:
   - budget proof そのものを供給する helper lemma または concrete source を
     検討する。

---

### 日時: 2026/06/05 08:23 JST (DKMK-017C budget inequality helper bundle)

1. 目的:
   - DKMK-017C として、`GeometricBudgetSource.hbudget` を作るための
     Real 側 helper lemma と constructor を Lean 上で試す。
2. 実施:
   - `geometricBudget_le_of_base_le_mul_one_sub` を追加した。
   - `geometricBudget_le_one_add_error_of_base_le_one_sub` を追加した。
   - `GeometricBudgetSource.ofDenomClearedBudget` を追加した。
   - `GeometricBudgetSource.ofBaseLeOneSub` を追加した。
   - `roadmap-DKMK-017.md` に DKMK-017C Budget Inequality Helper Bundle を
     追記した。
3. 結論:
   - denominator-cleared form
     `(base : Real) <= (1 + error) * (1 - (ratio : Real))`
     から hbudget を作る route は Lean 上で通った。
   - `ratio < 1` から `0 < 1 - ratio` を作り、`div_le_iff₀` で閉じた。
   - `base <= 1 - ratio` の特殊形は `0 <= error` を追加すれば通る。
4. 検証:
   - `lake build DkMath.NumberTheory.PrimitiveSet.SourceMassTruncation`
   - `lake build DkMath.NumberTheory.PrimitiveSet`
   - `git diff --check`
   - long-line check on changed docs
5. 失敗事例:
   - なし。
6. 次の課題:
   - budget source constructor と `FirstBandDecayBudgetSource` constructor を
     さらに合成するか、hbase0 / hdecay の供給 helper へ進むかを判断する。

---

### 日時: 2026/06/05 09:04 JST (DKMK-017D Nat-bound source helper bundle)

1. 目的:
   - DKMK-017D として、`hinc_nonneg` と `hdecay` を Nat 境界の仮定から
     provider が消費する `Finset.range` shape へ変換できるか試す。
2. 実施:
   - `rangeSuccNonneg_of_le` を追加した。
   - `rangeDecay_of_lt` を追加した。
   - `FirstBandDecayBudgetSource.ofBudgetSourceNatBounds` を追加した。
   - `roadmap-DKMK-017.md` に DKMK-017D Nat-Bound Source Helper Bundle を
     追記した。
3. 結論:
   - `k <= K` 形式の nonnegativity と `k < K` 形式の decay を、
     既存 provider route の `Finset.range` 入力へ変換できた。
   - decay は割り算型にせず、既存の multiplicative inequality のままにした。
   - そのため `increment k > 0` の追加仮定は不要だった。
4. 検証:
   - `lake build DkMath.NumberTheory.PrimitiveSet.SourceMassTruncation`
   - `lake build DkMath.NumberTheory.PrimitiveSet`
   - `git diff --check`
   - long-line check on changed docs
5. 失敗事例:
   - なし。
6. 次の課題:
   - `hbase0` の供給 helper、または Nat-bound constructor と
     denominator-cleared budget constructor の合成可否を検討する。

---

### 日時: 2026/06/05 09:13 JST (DKMK-017E first-band self-base bundle)

1. 目的:
   - DKMK-017E として、first-band upper bound `hbase0` を
     `base := increment 0` により閉じられるか Lean 上で試す。
   - library-facing wrapper として、denominator-cleared budget と
     Nat-bound source constructor の合成も試す。
2. 実施:
   - `FirstBandDecayBudgetSource.ofDenomClearedBudgetNatBounds` を追加した。
   - `FirstBandDecayBudgetSource.ofSelfBaseDenomClearedBudgetNatBounds` を
     追加した。
   - self-base constructor では、`hinc_nonneg 0 (Nat.zero_le K)` から
     `0 <= (increment 0 : Real)` を作り、`hbase0` は `le_rfl` で閉じた。
   - `roadmap-DKMK-017.md` に DKMK-017E First-Band Self-Base Bundle を
     追記した。
3. 結論:
   - `base := increment 0` による first-band bound の自動化は Lean 上で通った。
   - ただし budget obligation は
     `(increment 0 : Real) <= (1 + error) * (1 - (ratio : Real))`
     へ移る。
   - library 化の観点から、composition wrapper は採用する。
4. 検証:
   - `lake build DkMath.NumberTheory.PrimitiveSet.SourceMassTruncation`
   - `lake build DkMath.NumberTheory.PrimitiveSet`
   - `git diff --check`
   - long-line check on changed docs
5. 失敗事例:
   - なし。
6. 次の課題:
   - DKMK-017A-E の source surface をまとめ、次に concrete analytic source
     へ進むか、追加 wrapper を最小限足すか判断する。

---

### 日時: 2026/06/05 10:53 JST (DKMK-017F truncation wrapper checkpoint)

1. 目的:
   - DKMK-017F として、abstract source surface から truncation envelope までの
     library-facing wrapper を最小限追加できるか試す。
2. 実施:
   - `TruncationEnvelopeEstimate.ofFirstBandDecayBudgetSourcePackage` を追加した。
   - `TruncationEnvelopeEstimate.ofSelfBaseDenomClearedBudgetNatBounds` を追加した。
   - package-to-envelope wrapper は
     `DyadicBandAnalyticEstimate.ofFirstBandDecayBudgetSourcePackage` と
     `DyadicBandAnalyticEstimate.toTruncationEnvelopeEstimate` を合成した。
   - self-base route は
     `FirstBandDecayBudgetSource.ofSelfBaseDenomClearedBudgetNatBounds` を
     envelope wrapper へ渡す形で閉じた。
   - `roadmap-DKMK-017.md` に DKMK-017F Truncation Wrapper Checkpoint を
     追記した。
3. 結論:
   - 標準 route を truncation envelope boundary まで一段で示す wrapper は通った。
   - 追加 analytic obligation はない。
   - library 化の観点から、この最小 downstream wrapper は採用する。
4. 検証:
   - `lake build DkMath.NumberTheory.PrimitiveSet.SourceMassTruncation`
   - `lake build DkMath.NumberTheory.PrimitiveSet`
   - `git diff --check`
   - long-line check on changed docs
5. 失敗事例:
   - なし。
6. 次の課題:
   - DKMK-017A-F の source surface をまとめ、concrete analytic source へ
     進む準備をする。

---

### 日時: 2026/06/05 14:17 JST (DKMK-017G source surface checkpoint)

1. 目的:
   - DKMK-017G として、DKMK-017A-F の abstract source surface を軽く整理し、
     concrete analytic source へ進む準備をする。
2. 実施:
   - `roadmap-DKMK-017.md` に DKMK-017G Source Surface Checkpoint を
     追記した。
   - 標準 route を
     `TruncationEnvelopeEstimate.ofSelfBaseDenomClearedBudgetNatBounds`
     へ集約して整理した。
   - general route として
     `GeometricBudgetSource.ofDenomClearedBudget` から
     `TruncationEnvelopeEstimate.ofFirstBandDecayBudgetSourcePackage`
     へ至る流れも記録した。
   - 残る concrete analytic input を `hbaseBudget`, `hinc_nonneg`,
     `hdecay` の三つに絞って記録した。
3. 結論:
   - DKMK-017A-F により abstract source surface は十分に整った。
   - wrapper 追加はここで一旦止め、次は concrete `increment` candidate の調査へ
     進む。
4. 検証:
   - `git diff --check`
   - long-line check on `roadmap-DKMK-017.md` and `History.md`
5. 失敗事例:
   - なし。
6. 次の課題:
   - 既存の candidate definitions を調査し、concrete analytic source の
     first Lean target を選ぶ。

---

### 日時: 2026/06/05 14:24 JST (DKMK-017H increment candidate discovery)

1. 目的:
   - concrete `increment : Nat -> Rat` candidate を既存 PrimitiveSet /
     SourceMassTruncation 周辺から探す。
2. 実施:
   - `SourceMassTruncation.lean`, `DescentBridge.lean`,
     `LogCapacityHittingBridge.lean`, `WeightedPathFamily.lean`,
     `WeightProvider.lean` と近傍 module を検索した。
   - `finiteStepTail...`, `twoStepTailFiniteIncrement`, `sampleBool...` 系を
     candidate として分類した。
3. 結論:
   - 既存の concrete dyadic-band `Nat -> Rat` increment は見つからなかった。
   - 既存 concrete candidates は `Bool -> Rat` や arbitrary `ι -> Rat` であり、
     DKMK-017 standard route の `Nat -> Rat` には直接合わない。
   - 次は `geometricIncrement base ratio : Nat -> Rat` のような concrete
     dyadic-band candidate を Lean に導入し、まず `hinc_nonneg` を試すのが
     妥当。
4. 検証:
   - `git diff --check`
   - long-line check on `roadmap-DKMK-017.md` and `History.md`
5. 失敗事例:
   - なし。
6. 次の課題:
   - DKMK-017I として `geometricIncrement` candidate と `hinc_nonneg` lemma
     を試す。

---

### 日時: 2026/06/05 15:00 JST (DKMK-017I geometric increment route test)

1. 目的:
   - DKMK-017I として、concrete dyadic-band
     `increment : Nat -> Rat` candidate を Lean に導入し、標準 route が
     実際に通るか検証する。
2. 実施:
   - `SourceMassTruncation.lean` に `geometricIncrement` を追加した。
   - `geometricIncrement_nonneg`, `geometricIncrement_zero`,
     `geometricIncrement_decay`, `geometricIncrement_decay_le` を追加した。
   - `FirstBandDecayBudgetSource.ofGeometricIncrement` を追加した。
   - `TruncationEnvelopeEstimate.ofGeometricIncrement` を追加し、
     concrete candidate から envelope まで接続した。
3. 結論:
   - `geometricIncrement base ratio : Nat -> Rat` は DKMK-017 の最初の
     concrete test source として採用できる。
   - `hinc_nonneg` は `0 <= base`, `0 <= ratio` から閉じる。
   - `hdecay` は定義展開による equality から閉じる。
   - 残る主要 analytic input は
     `(base : Real) <= (1 + error) * (1 - (ratio : Real))` である。
4. 検証:
   - `lake build DkMath.NumberTheory.PrimitiveSet.SourceMassTruncation`
   - `lake build DkMath.NumberTheory.PrimitiveSet`
   - `git diff --check`
   - long-line check on `roadmap-DKMK-017.md` and `History.md`
5. 失敗事例:
   - なし。
6. 次の課題:
   - first-band budget を useful な `base`, `ratio`, `error` から導くか、
     `base = 1 - ratio` などの canonical specialization を試す。

---

### 日時: 2026/06/05 15:15 JST (DKMK-017J canonical first-band budget)

1. 目的:
   - DKMK-017J として、`base = 1 - ratio` の canonical specialization から
     first-band budget を Lean で閉じ、envelope まで接続する。
2. 実施:
   - `geometricIncrement_baseEqOneSub_budget` を追加した。
   - `FirstBandDecayBudgetSource.ofGeometricIncrementBaseEqOneSub` を追加した。
   - `TruncationEnvelopeEstimate.ofGeometricIncrementBaseEqOneSub` を追加した。
3. 結論:
   - `base = 1 - ratio`, `0 <= ratio`, `(ratio : Real) < 1`,
     `0 <= error` から、concrete geometric increment は
     `TruncationEnvelopeEstimate` まで通る。
   - `base` の非負性は `base = 1 - ratio` と `(ratio : Real) < 1` から
     閉じる。
   - DKMK-017I で残っていた first-band budget は、この canonical source では
     caller-side obligation から外せた。
4. 検証:
   - `lake build DkMath.NumberTheory.PrimitiveSet.SourceMassTruncation`
   - `lake build DkMath.NumberTheory.PrimitiveSet`
   - `git diff --check`
   - long-line check on `roadmap-DKMK-017.md` and `History.md`
5. 失敗事例:
   - なし。
6. 次の課題:
   - explicit `base` を持たない `base := 1 - ratio` 型の theorem を足すか、
     finite-step mass route との接続へ進むか判断する。

---

### 日時: 2026/06/05 15:22 JST (DKMK-017K finite-step route connection)

1. 目的:
   - DKMK-017K として、DKMK-017J の canonical geometric envelope が
     既存 finite-step mass route に消費されるか確認する。
2. 実施:
   - `TruncationEnvelopeEstimate.geometricIncrementBaseEqOneSub_weightedHitMass_le_one_add_error`
     を追加した。
   - `TruncationEnvelopeEstimate.ofGeometricIncrementBaseEqOneSub` を
     `TruncationEnvelopeEstimate.finiteStepTail_weightedHitMass_le_one_add_error`
     へ渡し、quotient-path weightedHitMass bound まで接続した。
3. 結論:
   - canonical geometric source は finite-step tail mass を経由して
     `weightedHitMass A <= 1 + error` まで通る。
   - DKMK-017J の envelope は終端ではなく、既存 finite-step route に
     実際に消費される。
   - geometric source の route-validation 役割は十分に完了した。
4. 検証:
   - `lake build DkMath.NumberTheory.PrimitiveSet.SourceMassTruncation`
   - `lake build DkMath.NumberTheory.PrimitiveSet`
   - `git diff --check`
   - long-line check on `roadmap-DKMK-017.md` and `History.md`
5. 失敗事例:
   - なし。
6. 次の課題:
   - DKMK-017 を route-validation complete としてまとめるか、
     logarithmic / capacity-derived source candidate の検討へ進む。

---

### 日時: 2026/06/05 15:30 JST (DKMK-017L route-validation close)

1. 目的:
   - DKMK-017 を route-validation complete として軽くまとめ、次分岐を
     analytic source replacement へ向ける。
2. 実施:
   - `report-DKMK-017.md` を追加した。
   - `roadmap-DKMK-017.md` に DKMK-017L Route-Validation Close を追記した。
   - DKMK-017A-K の到達 route を
     `geometricIncrement -> TruncationEnvelopeEstimate -> finiteStepTailNatMassSpace
      -> weightedHitMass bound`
     として整理した。
3. 結論:
   - DKMK-017 は route-validation complete として閉じてよい。
   - geometric source は canonical test source として採用するが、最終的な
     analytic/logarithmic source ではない。
   - 以後は convenience wrapper を増やすより、geometric source を置き換える
     analytic source candidate を探す。
4. 検証:
   - `git diff --check`
   - long-line check on `report-DKMK-017.md`, `roadmap-DKMK-017.md`, and
     `History.md`
5. 失敗事例:
   - なし。
6. 次の課題:
   - logarithmic source, capacity-derived source, dyadic band mass estimate,
     quotient-path local decay source のどれを次の実装候補にするか選ぶ。

---
