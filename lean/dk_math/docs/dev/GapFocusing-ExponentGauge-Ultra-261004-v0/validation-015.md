# Validation 015

Lean v4.34.1、nested Lake cwd `lean/dk_math` で検証した。

|検証|結果・対象|
|---|---|
|focused production + calibration + regression build|PASS、9063 jobs。新 production 3 モジュールと両 test module。[log](evidence/MANIFEST.md#log-9dc168d8d8514114)|
|final regression build|PASS、9058 jobs。最小 rejected/multiowner の witness と bounded minimality、補正なしの保存則の否定を含む。[log](evidence/MANIFEST.md#log-db2413e512758ef1)|
|`lake build DkMath.NumberTheory.Legendre`|PASS、9089 jobs。[log](evidence/MANIFEST.md#log-0a9d891be7ceffdc)|
|`lake build DkMath`|PASS、10392 jobs。[log](evidence/MANIFEST.md#log-378b66cfb6660933)|
|`lake build DkMathTest.NumberTheory.LegendreSqrtQuotientAxiomAudit`|PASS、9099 jobs。全 public 宣言を #check/#print axioms。[log](evidence/MANIFEST.md#log-397c573d7dfcffdd)|
|公理集合|77/77 宣言の完全な集合を manifest と照合。production47、tests30。許容集合は `propext`, `Classical.choice`, `Quot.sound` のみ。全新規宣言に sorryAx なし。|
|source/header/whitespace/artifacts|[check-015.py](checks/check-015.py) で manifest 全件一致、禁則語、7 Lean ファイルの copyright header/import-adjacent marker、tracked/untracked whitespace、文書リンク、校正表、保存則、最終判定を確認。[log](evidence/MANIFEST.md#log-c82a1e965f554123)|
|bounded diagnostics|429 odd prime anchors、3..3000。すべての aggregate/per-owner row を保存。3-prime budget410 successes、19 failures に対する追加11 probe19 successes。[JSON](evidence/MANIFEST.md#log-49301e24aaa80b1b)・[text](evidence/MANIFEST.md#log-8b48cbe6d2909b6e)・[next basis](evidence/MANIFEST.md#log-b6f09ce8ccd07a15)|

[manifest](evidence/MANIFEST.md#log-a3b84fc5ea3bdc4c) は 3 production module と 2 test module の public def/abbrev/theorem を列挙する。AxiomAudit と manifest は `python3 checks/check-015.py --generate` で生成した。import replay に含まれる旧 facade の公理印字は今回の宣言集合に数えず、今回の77件がすべて存在することを確認した上でその依存集合を検査する。

新規 declaration の数学的検証対象は、exact carrier、prime/composite/rejected partition、seat packet、roughness iff、composite正常形と prime-factor activation、1/2/3 owner multiplicity、above-n restriction、corrected global law、Nat-safe isolation、range regrouping、odd-prime capacity、small-prime lower bound、census consumer である。

6 anchor の total/rejection/routed values は production carriers に接続した kernel theorem。追加1031 は Qtotal661・J>=363・R316 の3入力から endpoint と U>=18 を導く。追加1031について Cross、全 E、全 I、全 U を評価していない。診断にある1031の exact Cross138 等を kernel census として主張しない。

root build は既存5件の警告を replay した：`ZsigmondyCyclotomicResearch.lean:147`、`FLT/PrimeProvider/TriominoCosmicBranchA.lean:4187`、`GcdNextResearch.lean:850`、`FLT/Kummer/CyclotomicPrincipalization.lean:5389`、`CosmicFormula/TriominoFLT.lean:1919`。今回の変更箇所ではなく、新47 production 宣言の transitive axiom check はこれらに依存しない。プロジェクト全体が placeholder-free であるとは主張しない。

`discover-015.py` は bounded diagnostics 専用で、production proof は Python の結果を oracle として使わない。特に追加11による19 failure の解消は diagnostic であり、今回の kernel endpoint 数と分ける。
