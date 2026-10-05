# Validation 014

Lean v4.34.1、nested Lake cwd `lean/dk_math` で検証した。

|検証|結果・範囲|
|---|---|
|`lake build DkMath.NumberTheory.Legendre.ParitySafeSqrtRoughCensus`|PASS、9051 jobs。Factorization の新 2 定理、Strata、Singleton、Census の最終 production を含む。[log](logs/build-production-014.txt)|
|`lake build DkMath.NumberTheory.Legendre`|PASS、9086 jobs。[log](logs/build-facade-014.txt)|
|`lake build DkMath`|PASS、10389 jobs。[log](logs/build-root-014.txt)|
|`LegendreSqrtRoughCensusRegression`|PASS。両 repeated side、cube、external cofactor、triple、zero anchor を検証。最終 AxiomAudit の import と各宣言監査にも含まれる。[log](logs/axiom-audit-014.txt)。|
|CensusCounts / CensusCalibration|PASS、9057 jobs、六点の production cards、exact fiber sums、census endpoints。[log](logs/build-calibration-014.txt)|
|public declaration axioms|PASS、9094 jobs、119/119 項目。許容した依存は `propext`, `Classical.choice`, `Quot.sound` のみ。`sorryAx` なし。[log](logs/axiom-audit-014.txt)|
|forbidden token / header / whitespace|最終 artifact check PASS。9 Lean ファイルの統一ヘッダー/marker、production/test の禁則語、tracked/new file の whitespace を確認。[log](logs/artifact-audit-014.txt)|
|bounded discovery|PASS、429 odd prime anchors 3..3000、数学的分類の反例なし。全 rows/fibers を保存。|

production の public 宣言は 69：Factorization の新規 2、Strata 16、Singleton 26、Census 25。校正・regression の明示的宣言と新校正 record の型・constructor・全 10 projection を加えた audit manifest は 119 項目。[manifest](logs/declaration-coverage-014.json) と `LegendreSqrtRoughCensusAxiomAudit.lean` を自動生成し、同一行の `@[simp] theorem` も列挙している。

root build の既存警告は 5 件：`CosmicFormula/TriominoFLT.lean:1919`、`ZsigmondyCyclotomicResearch.lean:147`、`FLT/PrimeProvider/TriominoCosmicBranchA.lean:4187`、`GcdNextResearch.lean:850`、`FLT/Kummer/CyclotomicPrincipalization.lean:5389`。今回の変更対象ではなく、プロジェクト全体が placeholder-free とは主張しない。新規 production 69 件の transitive axiom 監査は全件 PASS で、これらの placeholder に依存しない。

外部 q の全 prime evaluation は途中で停止し、最終校正は singleton bijection と checked strata から Cross を回収する構成にした。独立な 3 fiber は `Nat.prime_def_le_sqrt` に基づく有限 predicate で kernel 評価する。処理中の旧プロセス残存は PID を確認して解消した。途中停止や compiler repair は数学的反例と区別して [findings](findings-014.md) に記録した。


`python3 checks/check-014.py` は manifest の全件一致、119 宣言の完全な公理集合、禁則語、ヘッダー、git diff/check と untracked Lean の no-index check、429 diagnostic rows、六点の報告表、最終 Outcome A 行、ローカルリンクを検証する。

監査ログには replayed facade import が既存 5 宣言の公理も印字するため、parser は manifest の 119 項目が全て存在することを確認した上で、その完全な集合だけを検査する。import が印字した既存宣言を今回の新規宣言数へ加えない。
