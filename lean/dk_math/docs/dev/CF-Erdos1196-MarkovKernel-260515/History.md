# History

cid: 6a048079-4b50-83ab-84be-eea6a384ee8d
cid: 6a19cf55-b490-83a5-9c83-ad0a1e52d42f
cid: 6a200cab-ec18-83a5-a6c9-16fe23e2d81e

- 時刻の打刻は `date` コマンドを使用して時間(時分秒)まで正確に行うこと。
- 新規履歴は **ファイル末尾** に追加すること。

## History Log

Archive

過去ログは、以下にアーカイブしてあります。

- History
  - [Archive-1](History-001.md) - DKMK-001 to 009
  - [Archive-2](History-002.md) - DKMK-010 to 014
  - [Archive-3](History-003.md) - DKMK-015 to 017

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

### 日時: 2026/06/06 03:50 JST (DKMK-018A analytic source replacement start)

1. 目的:
   - DKMK-018 を開始し、geometric test source を置き換える analytic source
     candidate を比較する。
2. 実施:
   - `roadmap-DKMK-018.md` を追加した。
   - `RealLog.lean`, `ValuationBudget.lean`, `LogCapacityKernel.lean`,
     `SourceMassTruncation.lean` 周辺を検索した。
   - Real log-ratio route, multiplicity / valuation budget route,
     capacity-derived route, DKMK-017 dyadic route を candidate として分類した。
3. 結論:
   - 最も近い meaningful candidate は Real log-ratio / capacity-derived source。
   - 既存 Real 側には nonnegativity と sub-probability がある。
   - 現行 DKMK-017 route は `Nat -> Rat` increment を消費するため、主要な
     obstacle は `Real analytic weight -> Rat finite-step increment` の bridge。
   - 次は Real-valued analytic majorant が既存 Rat route を certify できるか、
     最小 bridge surface を Lean で試す。
4. 検証:
   - `git diff --check`
   - long-line check on `roadmap-DKMK-018.md` and `History.md`
5. 失敗事例:
   - なし。
6. 次の課題:
   - `TruncationEnvelopeEstimate` または `DyadicBandAnalyticEstimate` 周辺に
     Real-majorant bridge を最小実装できるか試す。

---

### 日時: 2026/06/06 04:04 JST (DKMK-018B Real-majorant bridge)

1. 目的:
   - Real-valued analytic majorant が既存 Rat finite-step route を certify
     できるか Lean で確認する。
2. 実施:
   - `TruncationEnvelopeEstimate.ofRealMajorant` を追加した。
   - `DyadicBandAnalyticEstimate.ofRealMajorant` を追加した。
   - `TruncationEnvelopeEstimate.ofRealWeightProviderMajorant` を追加し、
     `RealWeightProvider` を次 checkpoint の source として使える形にした。
3. 結論:
   - Real-valued majorant から rational `TruncationEnvelopeEstimate` は閉じる。
   - dyadic-band 版も閉じる。
   - `RealWeightProvider.SubProbability` と `0 <= error` からも envelope を
     作れるため、LogCapacityKernel / RealLog provider を次に接続できる。
   - 現時点では Real-native finite-step mass refactor は不要。
4. 検証:
   - `lake build DkMath.NumberTheory.PrimitiveSet.SourceMassTruncation`
   - `lake build DkMath.NumberTheory.PrimitiveSet`
   - `git diff --check`
   - long-line check on `roadmap-DKMK-018.md` and `History.md`
5. 失敗事例:
   - なし。
6. 次の課題:
   - `PrimePowerWitnessProvider.logCapacityKernelRealWeightProvider` などの
     concrete Real provider を DKMK-018B bridge に接続する。

---

### 日時: 2026/06/06 05:20 JST (DKMK-018C log-capacity provider attachment)

1. 目的:
   - `PrimePowerWitnessProvider.logCapacityKernelRealWeightProvider` を
     DKMK-018B bridge に接続し、concrete Real provider が Rat envelope へ
     届くか確認する。
2. 実施:
   - `PrimePowerWitnessProvider.logCapacityKernel_truncationEnvelope_of_ratMajorizedIncrement`
     を追加した。
   - `PrimePowerWitnessProvider.logCapacityKernel_truncationEnvelope_zeroIncrement`
     を追加した。
3. 結論:
   - LogCapacityKernel の Real provider は
     `TruncationEnvelopeEstimate.ofRealWeightProviderMajorant` に接続できる。
   - zero increment の smoke connection は通った。
   - 非自明な Rat increment は外部仮定
     `(increment q : Real) <= provider.weight q` として受ける surface まで
     通った。
   - 次の焦点は rationalization policy。
4. 検証:
   - `lake build DkMath.NumberTheory.PrimitiveSet.SourceMassTruncation`
   - `lake build DkMath.NumberTheory.PrimitiveSet`
   - `git diff --check`
   - long-line check on `roadmap-DKMK-018.md` and `History.md`
5. 失敗事例:
   - なし。
6. 次の課題:
   - finite index 上の rational lower approximation を作るか、
     assumed-rationalization route を main theorem surface として採用するか
     判断する。

---

### 日時: 2026/06/06 12:36 JST (DKMK-018D positive rational under-approximation)

1. 目的:
   - 正値な `RealWeightProvider` weight の下に、非ゼロの rational increment を
     finite index 上で構成できるか確認する。
2. 実施:
   - `RealWeightProvider.exists_positive_rat_below` を追加した。
   - `RealWeightProvider.positiveRatIncrementBelow` を追加した。
   - `RealWeightProvider.positiveRatIncrementBelow_pos` を追加した。
   - `RealWeightProvider.positiveRatIncrementBelow_le_weight` を追加した。
   - `RealWeightProvider.truncationEnvelope_of_positiveRatIncrementBelow` を
     追加した。
3. 結論:
   - `forall i in P.index, 0 < P.weight i` があれば、
     `0 < increment i` かつ `(increment i : Real) <= P.weight i` を満たす
     rational increment を構成できる。
   - その increment は既存の rational `TruncationEnvelopeEstimate` route に
     接続できる。
   - Real-native finite-step mass refactor は現時点では不要。
   - LogCapacityKernel へ具体適用するには、provider weight の strict positivity
     または positive-weight support restriction が次の入力になる。
4. 検証:
   - `lake build DkMath.NumberTheory.PrimitiveSet.SourceMassTruncation`
5. 失敗事例:
   - なし。
6. 次の課題:
   - `logCapacityKernelRealWeightProvider` の index 上で strict positivity を
     取り出せるか調査する。

---
