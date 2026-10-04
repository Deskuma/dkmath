# Instruction 004 validation

Lean / Mathlib: v4.34.1。作業・検証の cwd は `lean/dk_math`。

## 最終 build

```text
lake build DkMath.NumberTheory.Legendre.CyclotomicPersistence \
  DkMath.NumberTheory.Legendre.ParitySafePersistence \
  DkMathTest.NumberTheory.LegendreCyclotomicPersistence \
  DkMath.NumberTheory.Legendre DkMath.NumberTheory.GapFocusing DkMath
```

成功、exit 0、10368 Lake jobs。[最終ログ](logs/build-final-004.txt) を最終ソースに対する検証の正本とする。jobs は依存を含む Lake の件数であり、新規ファイル数・新規 compilation 数ではない。新規 production 2 modules と 11 回帰定理に warning/error はない。

全 DkMath build は既存の五箇所の未証明宣言 warning を再表示した。新規証明の依存は次の全件公理監査で個別に確認した。これら既存研究 endpoint を今回の証明に使用していない。

`LegendrePersistenceInventory.lean` を `lake env lean` で実行し、[既存 API の型](logs/source-inventory-004.txt) を確認した。

## 全件公理監査

[LegendrePersistenceAxiomAudit.lean](../../../DkMathTest/NumberTheory/LegendrePersistenceAxiomAudit.lean) に、production と回帰ソースから抽出した全宣言の `#check` と `#print axioms` を列挙した。`lake env lean` は exit 0。

- CyclotomicPersistence: 16/16 public declarations。
- ParitySafePersistence: 23/23 public declarations。
- 名前付き回帰: 11/11 declarations。
- 合計 50/50、source 名と実際の出力を機械照合した。
- 全依存集合が `{propext, Classical.choice, Quot.sound}` の部分集合。空集合も含む。
- `sorryAx` と custom axiom dependency はない。

[公理出力](logs/axiom-audit-004.txt)、[coverage manifest](logs/declaration-coverage-004.json)、[照合結果](logs/axiom-coverage-004.txt)。

## 禁止 token と差分

変更 production 全三ファイル（新規二 modules と既存 facade）および名前付き回帰ファイルを走査。`sorry`, `sorryAx`, `admit`, `axiom`, `native_decide`, `unsafe` は全て zero matches。[走査結果](logs/forbidden-token-scan-004.txt)。監査ファイルの `#print axioms` は検査コマンドで、追加公理宣言ではない。

`git diff --check` と、新規未追跡ファイルに対する `git diff --no-index --check /dev/null <file>` を実行した。結果は [差分検査ログ](logs/diff-check-004.txt) に記録した。

## 回帰の対象

q=3 の residue class と order 2、次殻での非持続、任意開始の有限 run、T=0、長さ q の一周期を確認した。実際の二座席の持続を用いて unweighted frequency bound を否定した。下側の parity reversal、固定座席 weight の 9 versus 44、fresh があるのに production support excess が 0 となる例も kernel checked。

最後の回帰は20遷移で required lower seats 245、weighted cap 169 を計算し、既存 full-cover 仮定を保持したまま fresh lower incidences が76以上と証明する。`decide` の有限 kernel 計算を用い、native decision を使っていない。

検証範囲はこれらの有限・条件付き定理。Legendre、full-cover failure、analytic estimates、既存残余 capacity の strict 改善は証明していない。
